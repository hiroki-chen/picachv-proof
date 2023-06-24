use std::{
    collections::HashMap,
    fmt::Debug,
    ops::Add,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, RwLock,
    },
};

use lazy_static::lazy_static;
use libloading::Library;
use policy_core::{
    data_type::PrimitiveDataType,
    error::{PolicyCarryingError, PolicyCarryingResult},
};

use crate::{field::FieldDataArray, DataFrame};

static API_COUNT: AtomicUsize = AtomicUsize::new(0);

lazy_static! {
    pub(crate) static ref API_MANAGER: Arc<RwLock<ApiModuleManager>> =
        Arc::new(RwLock::new(ApiModuleManager::new()));
    pub(crate) static ref API_ID_MAP: Arc<RwLock<HashMap<ApiRefId, String>>> =
        Arc::new(RwLock::new(HashMap::new()));
}

pub type ApiRef = Arc<dyn PolicyApiSet>;

/// An id for bookkeeping the data access Api Set.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct ApiRefId(pub usize);

/// Gets the next available API id.
pub fn next_api_id() -> usize {
    API_COUNT.fetch_add(1, Ordering::Release)
}

/// Gets the current available API id.
pub fn cur_api_id() -> usize {
    API_COUNT.load(Ordering::Acquire)
}

/// This functions will register new API implementation from the plugin that can be loaded at runtime. Note
/// however, that the API must be compiled separately with the same Rust toolchain to be ABI-safe.
pub fn register_api(path: &str, name: &str) -> PolicyCarryingResult<ApiRefId> {
    let id = next_api_id();
    match API_MANAGER.write() {
        Ok(mut lock) => {
            lock.load(path, name)?;
            Ok(ApiRefId(id))
        }
        Err(_) => Err(PolicyCarryingError::Unknown),
    }
}

/// This is called at the executor level when we want to get the [`PolicyApiSet`] for data access.
pub fn get_api(id: ApiRefId) -> PolicyCarryingResult<ApiRef> {
    let name = API_ID_MAP
        .read()
        .map_err(|_| PolicyCarryingError::Unknown)?
        .get(&id)
        .ok_or(PolicyCarryingError::OperationNotAllowed(
            "this api set is not registerd".into(),
        ))?;

    todo!()
}

// Some common APIs that can be used implement the `PolicyCompliantApiSet`'s trait methods.

/// An identity function transformation.
pub fn pcd_identity<T>(input: FieldDataArray<T>) -> PolicyCarryingResult<FieldDataArray<T>>
where
    T: PrimitiveDataType + Debug + Send + Sync + Clone + 'static,
{
    Ok(input)
}

/// Returns the maximum value of the array. Deal with f64?
pub fn pcd_max<T>(input: &FieldDataArray<T>) -> PolicyCarryingResult<T>
where
    T: PrimitiveDataType + PartialOrd + Debug + Send + Sync + Clone + 'static,
{
    input
        .into_iter()
        .max_by(|&lhs, &rhs| lhs.partial_cmp(rhs).unwrap()) // May panic when NaN
        .cloned()
        .ok_or(PolicyCarryingError::ImpossibleOperation(
            "Input is empty".into(),
        ))
}

/// Sums up the value.
pub fn pcd_sum<R, T>(
    input: &FieldDataArray<T>,
    init: R,
    upper: Option<T>,
) -> PolicyCarryingResult<R>
where
    T: PrimitiveDataType + Add<R, Output = R> + PartialOrd + Debug + Send + Sync + Clone + 'static,
{
    // Can we really add on utf8 strings?
    if !(input.data_type().is_numeric() || input.data_type().is_utf8()) {
        Err(PolicyCarryingError::ImpossibleOperation(
            "Cannot add on non-numeric types".into(),
        ))
    } else {
        // A bad thing is, we cannot directly call `sum()` on iterator on a generic type `T`,
        // but we may call the `fold()` method to aggregate all the elements together.
        Ok(input.iter().fold(init, |acc, e| {
            let cur = match upper {
                Some(ref upper) => {
                    if upper >= e {
                        e.clone()
                    } else {
                        upper.clone()
                    }
                }
                None => e.clone(),
            };

            cur + acc
        }))
    }
}

#[derive(Clone, Debug)]
pub enum JoinType {
    Left,
    Right,
}

#[derive(Clone, Debug, Default)]
pub enum ApiRequest {
    #[default]
    Invalid,
    
}

/// The 'real' implementation of all the allowed APIs for a policy-carrying data. By default,
/// all the operations called directly on a [`PolicyApiSet`] will invoke the provided methods
/// implemented by this trait. It is also recommended that the concrete data is stored within
/// the struct that implements this trait for optimal security.
///
/// Note that [`PolicyApiSet`] shoud be both [`Send`] and [`Sync`] because we want to ensure
/// executing the data analysis operations lazily; thus it requires synchronization and sharing.
pub trait PolicyApiSet: Send + Sync {
    fn name(&self) -> &'static str;

    fn load(&self) {
        panic!("not implemented");
    }

    fn unload(&self) {
        panic!("not implemented");
    }

    /// The entry function of the api set.
    fn entry(&self, req: ApiRequest) -> PolicyCarryingResult<DataFrame> {
        Err(PolicyCarryingError::OperationNotAllowed(format!(
            "this operation cannot be done: {req:?}!"
        )))
    }
}

/// An ApiSet that simply forbids everything and should not used for any other purposes except for testing.
pub struct ApiSetSink;

impl PolicyApiSet for ApiSetSink {
    fn name(&self) -> &'static str {
        "api_sink"
    }
}

/// Returns a pointer to the trait object.
type Loader = fn(name: *const u8, len: usize, ptr: *mut u64) -> i64;

pub struct ApiModuleManager {
    plugins: HashMap<String, Box<Arc<dyn PolicyApiSet>>>,
    libs: HashMap<String, Library>,
}

impl Drop for ApiModuleManager {
    fn drop(&mut self) {
        if !self.plugins.is_empty() || !self.libs.is_empty() {
            self.unload_all()
        }
    }
}

impl ApiModuleManager {
    /// Constructs a new API module manager.
    #[inline]
    pub fn new() -> ApiModuleManager {
        ApiModuleManager {
            plugins: HashMap::new(),
            libs: HashMap::new(),
        }
    }

    /// Loads a plugin.
    pub fn load(&mut self, path: &str, plugin_name: &str) -> PolicyCarryingResult<()> {
        let lib =
            unsafe { Library::new(path).map_err(|e| PolicyCarryingError::FsError(e.to_string())) }?;
        let constructor = unsafe {
            lib.get::<Loader>(b"load_module")
                .map_err(|e| PolicyCarryingError::SymbolNotFound(e.to_string()))
        }?;

        let mut plugin_ptr = 0;
        let plugin = match constructor(plugin_name.as_ptr(), plugin_name.len(), &mut plugin_ptr) {
            0 => unsafe { Box::from_raw(plugin_ptr as *mut Arc<dyn PolicyApiSet>) },
            _ => return Err(PolicyCarryingError::Unknown),
        };

        println!("{}", plugin.name());
        self.libs.insert(plugin_name.into(), lib);
        self.plugins.insert(plugin_name.into(), plugin);
        Ok(())
    }

    pub fn unload(&mut self, plugin_name: &str) -> PolicyCarryingResult<()> {
        self.plugins.retain(|plugin, _| plugin != plugin_name);

        Ok(())
    }

    pub fn get(&self, name: &str) -> PolicyCarryingResult<Box<Arc<dyn PolicyApiSet>>> {
        self.plugins
            .get(name)
            .cloned()
            .ok_or(PolicyCarryingError::SymbolNotFound(name.into()))
    }

    fn unload_all(&mut self) {
        for (name, plugin) in self.plugins.drain() {
            println!("unloading the plugin {}", name);

            // We do not own it!
            plugin.unload();
        }

        for (_, lib) in self.libs.drain() {
            drop(lib);
        }
    }
}

#[cfg(test)]
mod test {}
