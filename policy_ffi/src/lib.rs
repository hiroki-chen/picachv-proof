use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Debug,
    hash::Hash,
    sync::{atomic::AtomicUsize, atomic::Ordering, Arc, RwLock},
};

use lazy_static::{__Deref, lazy_static};
use libloading::{os::unix::Symbol, Library};
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    expr::GroupByMethod,
    get_lock,
    types::{ExecutorRefId, ExecutorType, FunctionArguments},
};

lazy_static! {
    pub static ref EXECUTOR_LIB: LibraryManager<ExecutorRefId> = LibraryManager::new();
    pub static ref EXECUTOR_ID: AtomicUsize = AtomicUsize::new(0);
}

/// The signature of the function symbol.
type Function = fn(args: *const u8, args_len: usize) -> i64;
type ExecutorCreator =
    fn(executor_type: usize, args: *const u8, args_len: usize, p_executor: *mut usize) -> i64;

/// Loads the executors from the shared library and returns the id to these executors.
pub fn load_executor_lib(
    path: &str,
    args: FunctionArguments,
) -> PolicyCarryingResult<ExecutorRefId> {
    let next_id = ExecutorRefId(EXECUTOR_ID.fetch_add(1, Ordering::Release));

    EXECUTOR_LIB.load_executor_lib(path, next_id, args)?;
    Ok(next_id)
}

/// Tries to create a new executor from the loaded module with a given id indicating the executor set,
/// executor type, and the function arguments passed to the executor instance.
///
/// # Examples
///
/// ```
/// use policy_core::{args, types::ExecutorRefId};
/// use policy_ffi::create_executor;
///
/// trait Foo: Sized {
///     fn foo(&self) {
///         println!("Hello World!");
///     }
/// }
///
/// let executor =
///     create_executor::<Box<dyn Foo>>(ExecutorRefId(0), ExecutorType::Filter, args!()).unwrap();
///
/// executor.foo();
/// ```
///
/// # FFI Safety
///
/// Rust provides no abi stablility, so we must compile the executor module and the core library by the
/// same Rust toolchain. Otherwise, the memory layout of the compiled trait object might appear different-
/// ly. This is a limitation.
///
/// Also, to guarantee that the trait object can be returned from the external library, we wrap it in a
/// nested [`Box`]: `Box<Box<dyn Executor>>` since fat pointers cannot be simply passed by FFI interfaces.
///
/// # Notes
///
/// The function is ignorant of the [`Box`]-ed object because [`Box`] is always [`Sized`]. As long as the
/// caller specifies `U` (which only accepts types whose sizes are determined at compilation time) as some
/// smart pointers that can carry a fat pointer, this function is safe (i.e., exhibits no undefined behavi-
/// or at runtime).
pub fn create_executor<U: Sized>(
    id: ExecutorRefId,
    executor_type: ExecutorType,
    args: FunctionArguments,
) -> PolicyCarryingResult<Box<U>> {
    EXECUTOR_LIB.create_executor(&id, executor_type, args)
}

/// Tries to call the corresponding function from the loaded module by a given id set `id` and a name `name`.
///
/// # Examples
///
/// ```
/// use policy_core::args;
/// use policy_ffi::create_function;
///
/// let v = vec![];
/// let mut output = 0usize;
/// let mut output_len = 0usize;
/// let f = call_function(ExecutorRefId(0), "sum", args!{
///     "arr": v.as_ptr(),
///     "len": v.len(),
///     "out": &mut output as *mut usize as usize,
///     "out_len": &mut output_len as *mut usize as usize,
///     
/// }).expect("Symbol not found!");
///
/// // Call `f` as you want.
///
/// println!("{}", f());
/// ```
///
/// # FFI Safety
///
/// The size of function pointers are always guaranteed to be `std::mem::size_of::<usize>()` on any platforms.
/// The only thing we need to care about is the correctness of the function *signature*. It is the caller's
/// responsibility to ensure that intended function's prototype matches the that in the library.
/// ```
pub fn call_function(
    id: ExecutorRefId,
    ty: GroupByMethod,
    args: FunctionArguments,
) -> PolicyCarryingResult<()> {
    let f = EXECUTOR_LIB.create_function(&id, ty)?;
    let args = serde_json::to_string(&args)
        .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))?;

    match f(args.as_ptr(), args.len()) {
        0 => Ok(()),
        ret => Err(PolicyCarryingError::CommandFailed(ret)),
    }
}

/// The library manager for bookkeeping the loaded shared libraries.
pub struct LibraryManager<T>
where
    T: Sized,
{
    libs: Arc<RwLock<HashMap<T, Arc<Library>>>>,
}

impl<T> LibraryManager<T>
where
    T: Sized,
{
    pub fn new() -> Self {
        Self {
            libs: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl<T> LibraryManager<T>
where
    T: Sized + PartialOrd + Eq + Hash + Debug,
{
    /// Loads the library into the manager.
    pub fn load_executor_lib(
        &self,
        path: &str,
        id: T,
        args: FunctionArguments,
    ) -> PolicyCarryingResult<()> {
        let lib =
            unsafe { Library::new(path).map_err(|e| PolicyCarryingError::FsError(e.to_string()))? };
        let f = unsafe { lib.get::<Function>(b"on_load") }
            .map_err(|e| PolicyCarryingError::SymbolNotFound(e.to_string()))?;
        let args = serde_json::to_string(&args)
            .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))?;

        let ret = f(args.as_ptr(), args.len());
        if ret != 0 {
            return Err(PolicyCarryingError::InvalidInput);
        }

        let mut lock = get_lock!(self.libs, write);
        match lock.entry(id) {
            Entry::Occupied(_) => return Err(PolicyCarryingError::AlreadyLoaded),
            Entry::Vacant(entry) => {
                entry.insert(Arc::new(lib));
            }
        }

        Ok(())
    }

    /// If a module is no longer needed, call this function to properly uninstall it.
    pub fn unload_executor_lib(&self, id: T, args: FunctionArguments) -> PolicyCarryingResult<()> {
        let mut lock = get_lock!(self.libs, write);

        match lock.get_mut(&id) {
            Some(lib) => {
                if Arc::strong_count(lib) == 0 {
                    let f = unsafe { lib.get::<Function>(b"on_unload") }.map_err(|_| {
                        PolicyCarryingError::SymbolNotFound("`on_unload` not found".into())
                    })?;
                    let args = serde_json::to_string(&args)
                        .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))?;

                    let ret = f(args.as_ptr(), args.len());
                    if ret != 0 {
                        return Err(PolicyCarryingError::CommandFailed(ret));
                    }

                    lock.remove(&id);
                }

                Ok(())
            }
            None => Err(PolicyCarryingError::SymbolNotFound(format!(
                "{id:?} not found"
            ))),
        }
    }

    /// Returns a function pointer to the library.
    pub fn create_function(&self, id: &T, ty: GroupByMethod) -> PolicyCarryingResult<Function> {
        match ty {
            GroupByMethod::Min => self.get_symbol::<Function>(id, "agg_min"),
            GroupByMethod::Max => self.get_symbol::<Function>(id, "agg_max"),
            GroupByMethod::Sum => self.get_symbol::<Function>(id, "agg_sum"),
            GroupByMethod::Mean => self.get_symbol::<Function>(id, "agg_mean"),
            _ => todo!(),
        }
        .map(|symbol| symbol.deref().clone())
    }

    /// Creates a new executor from the library.
    pub fn create_executor<U: Sized>(
        &self,
        id: &T,
        executor_type: ExecutorType,
        args: FunctionArguments,
    ) -> PolicyCarryingResult<Box<U>> {
        let f = self.get_symbol::<ExecutorCreator>(id, "create_executor")?;
        let mut executor = 0usize;
        let args = serde_json::to_string(&args)
            .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))?;

        match f(
            executor_type as usize,
            args.as_ptr(),
            args.len(),
            &mut executor,
        ) {
            0 => Ok(unsafe { Box::from_raw(executor as *mut U) }),
            ret => Err(PolicyCarryingError::CommandFailed(ret)),
        }
    }

    fn get_symbol<U: Sized>(&self, id: &T, name: &str) -> PolicyCarryingResult<Symbol<U>> {
        let lock = get_lock!(self.libs, read);
        match lock.get(id) {
            Some(lib) => unsafe {
                lib.get::<U>(name.as_bytes())
                    .map_err(|e| PolicyCarryingError::SymbolNotFound(e.to_string()))
                    .map(|s| s.into_raw().clone())
            },
            // .map(|s| unsafe { s.into_raw().clone() }),
            None => Err(PolicyCarryingError::SymbolNotFound(format!(
                "{id:?} not loaded"
            ))),
        }
    }
}
