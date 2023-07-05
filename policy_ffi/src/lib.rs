use std::{
    collections::{hash_map::Entry, HashMap},
    ffi::{c_char, CStr},
    fmt::Debug,
    hash::Hash,
    sync::{atomic::AtomicUsize, atomic::Ordering, Arc, RwLock},
};

use lazy_static::{__Deref, lazy_static};
use libloading::{os::unix::Symbol, Library};
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult, StatusCode},
    expr::GroupByMethod,
    get_lock,
    types::{ExecutorRefId, FunctionArguments, OpaquePtr},
};

static RUSTC_VERSION: &str = env!("RUSTC_VERSION");

lazy_static! {
    pub static ref EXECUTOR_LIB: LibraryManager<ExecutorRefId> = LibraryManager::new();
    pub static ref EXECUTOR_ID: AtomicUsize = AtomicUsize::new(0);
}

/// The signature of the function symbol used by load and unload.
///
/// # Arguments
///
/// - `args`: The pointer to the argument buffer. A serialized [`FunctionArguments`].
/// - `args_len`: The length of the buffer.
type LibFunction = fn(args: *const u8, args_len: usize) -> StatusCode;

/// The signature of the function symbol that exports the rustc version used to build
/// the library.
///
/// # Arguments
///
/// - `buf`: The caller allocated buffer for holding the string.
/// - `len`: The length of bytes copied to the buffer.
type Version = fn(buf: *const u8, len: *mut usize);

/// The signature of the user defined functions that may apply to the arrays.
///
/// # Arguments
///
/// - `input`: The pointer to the input buffer. A serialized [`FunctionArguments`].
/// - `input_len`: The length of the input buffer.
/// - `output`: The caller-allocated output buffer. A serialized [`FunctionArguments`].
/// - `output_len`: The pointer to the output buffer length. Modified by the callee.
///
/// # Output
/// The output of the user defined function is designed to be as general as possible by using [`FunctionArguments`].
/// It contains the following fields:
///
/// - `output`: The pointer to the [`Box`]-ed trait object.
type UserDefinedFunction =
    fn(input: *const u8, input_len: usize, output: *mut u8, output_len: *mut usize) -> StatusCode;

/// The signature of the function that executes the physical plan via an opaque handle.
///
/// # Arguments
///
/// - `executor`: The opaque pointer to the executor which might be a boxed pointer.
/// - `df`: The output buffer for holding the data frame.
/// - `df_len`: The length of the output buffer len.
type ExecutorFunction = fn(executor: OpaquePtr, df: *mut u8, df_len: *mut usize) -> StatusCode;

/// The signature of the function that creates new executors.
///
/// # Arguments
///
/// - `args`: The pointer to the argument buffer. A serialized [`FunctionArguments`].
/// - `args_len`: The length of the argument buffer.
/// - `p_executor`: The pointer to the created executor. Note that this is a pointer to a smart pointer
///                 [`Box<dyn T>`] where `T` may be [`Sized`], i.e., `p_executor` is `*mut *mut Box<T>`.
///                 Wrapping the executor in a nested pointer is to ensure that fat pointers can be passed
///                 via FFI interfaces. Recall the memory layout of a trait object: it contains a pointer
///                 to the concrete type and a pointer to the vtable for dynamic dispatch.
///                 This pointer is *opaque*.
type ExecutorCreator =
    fn(args: *const u8, args_len: usize, p_executor: *mut OpaquePtr) -> StatusCode;

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
/// executor type, and the function arguments passed to the executor instance. This function returns an
/// opaque pointer to the executor allocated in the external library.
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
///     create_executor(ExecutorRefId(0), ExecutorType::Filter, args!()).unwrap();
///
/// /* Do something with the opaque pointer `executor` */
///
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
pub fn create_executor(
    id: ExecutorRefId,
    args: FunctionArguments,
) -> PolicyCarryingResult<OpaquePtr> {
    EXECUTOR_LIB.create_executor(&id, args)
}

/// Tries to get the corresponding function from the loaded module by a given id set `id` and a type.
///
/// # Examples
///
/// ```
/// use policy_core::args;
/// use policy_ffi::create_function;
///
/// let v = vec![];
/// let mut output = vec![0u8; 4096];
/// let mut output_len = 0usize;
/// let f = get_udf(ExecutorRefId(0), "sum", args!{
///     "input": v.as_ptr(),
///     "input_len": v.len(),
///     "output": output.as_mut_ptr
///     "output_len": &mut output_len,
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
///
/// ```
pub fn get_udf(id: ExecutorRefId, ty: GroupByMethod) -> PolicyCarryingResult<UserDefinedFunction> {
    EXECUTOR_LIB.get_udf(&id, ty)
}

/// Tries to get the function symbol for executing the physical plan.
pub fn get_execution(id: ExecutorRefId) -> PolicyCarryingResult<ExecutorFunction> {
    EXECUTOR_LIB
        .get_symbol::<ExecutorFunction>(&id, "execute")
        .map(|symbol| symbol.deref().clone())
}

/// The library manager for bookkeeping the loaded shared libraries.
pub struct LibraryManager<T: Sized> {
    libs: Arc<RwLock<HashMap<T, Arc<Library>>>>,
}

impl<T: Sized> LibraryManager<T> {
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

        // Check version
        let mut version = vec![0; 0x200];
        let version = unsafe {
            let mut len = 0usize;
            lib.get::<Version>(b"rustc_version")
                .map_err(|e| PolicyCarryingError::SymbolNotFound(e.to_string()))?(
                version.as_mut_ptr(),
                &mut len,
            );

            std::str::from_utf8_unchecked(&version[..len])
        };
        if version != RUSTC_VERSION {
            return Err(PolicyCarryingError::VersionMismatch(version.to_string()));
        }

        let f = unsafe { lib.get::<LibFunction>(b"on_load") }
            .map_err(|e| PolicyCarryingError::SymbolNotFound(e.to_string()))?;
        let args = serde_json::to_string(&args)
            .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))?;

        let ret = f(args.as_ptr(), args.len());
        if ret != StatusCode::Ok {
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
                    let f = unsafe { lib.get::<LibFunction>(b"on_unload") }.map_err(|_| {
                        PolicyCarryingError::SymbolNotFound("`on_unload` not found".into())
                    })?;
                    let args = serde_json::to_string(&args)
                        .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))?;

                    let ret = f(args.as_ptr(), args.len());
                    if ret != StatusCode::Ok {
                        return Err(ret.into());
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

    /// Returns a user defined function pointer to the library.
    pub fn get_udf(&self, id: &T, ty: GroupByMethod) -> PolicyCarryingResult<UserDefinedFunction> {
        match ty {
            GroupByMethod::Min => self.get_symbol::<UserDefinedFunction>(id, "agg_min"),
            GroupByMethod::Max => self.get_symbol::<UserDefinedFunction>(id, "agg_max"),
            GroupByMethod::Sum => self.get_symbol::<UserDefinedFunction>(id, "agg_sum"),
            GroupByMethod::Mean => self.get_symbol::<UserDefinedFunction>(id, "agg_mean"),
            _ => Err(PolicyCarryingError::OperationNotSupported),
        }
        .map(|symbol| symbol.deref().clone())
    }

    /// Creates a new executor from the library.
    pub fn create_executor(
        &self,
        id: &T,
        args: FunctionArguments,
    ) -> PolicyCarryingResult<OpaquePtr> {
        let f = self.get_symbol::<ExecutorCreator>(id, "create_executor")?;
        let mut executor = std::ptr::null_mut();
        let args = serde_json::to_string(&args)
            .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))?;

        match f(args.as_ptr(), args.len(), &mut executor) {
            StatusCode::Ok => Ok(executor),
            ret => Err(ret.into()),
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
