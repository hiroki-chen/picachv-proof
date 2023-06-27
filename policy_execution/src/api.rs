use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Debug,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, RwLock,
    },
};

use lazy_static::lazy_static;
use libloading::Library;
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    ApiRefId,
};

use policy_carrying_data::{get_rwlock, DataFrame, DataFrameRRef, FieldDataRRef};

use crate::plan::physical_expr::PhysicalExprRef;

static API_COUNT: AtomicUsize = AtomicUsize::new(0);

lazy_static! {
    pub(crate) static ref API_MANAGER: Arc<RwLock<ApiModuleManager>> =
        Arc::new(RwLock::new(ApiModuleManager::new()));
    pub(crate) static ref API_ID_MAP: Arc<RwLock<HashMap<ApiRefId, String>>> =
        Arc::new(RwLock::new(HashMap::new()));
}

pub type ApiRef = Arc<dyn PolicyApiSet>;

#[derive(Clone, Debug, Default)]
pub enum ApiRequest {
    /// Filter.
    Filter {
        by: FieldDataRRef,
        has_windows: bool,
    },
    /// Scan the data frame.
    Scan,
    /// Do projection.
    Projection { columns: Arc<Vec<String>> },
    /// An invalid request as a default value.
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

    /// Some prelude function that should be called when the module is loaded.
    fn load(&self) {
        unimplemented!()
    }

    /// Some epilogue function that should be called when the module is unloaded.
    fn unload(&self) {
        unimplemented!()
    }

    /// Loads the data.
    fn load_data(&self) -> PolicyCarryingResult<()> {
        unimplemented!()
    }

    /// Evalautes the phyiscal expression on a given dataframe reference [`DataFrameRRef`].
    fn evaluate(
        &self,
        _df: DataFrameRRef,
        _expr: PhysicalExprRef,
    ) -> PolicyCarryingResult<FieldDataRRef> {
        unimplemented!()
    }

    /// The entry function of the api set.
    fn entry(
        &self,
        _df: Option<DataFrameRRef>,
        req: ApiRequest,
    ) -> PolicyCarryingResult<DataFrameRRef> {
        Err(PolicyCarryingError::OperationNotAllowed(format!(
            "this operation cannot be done: {req:?}!"
        )))
    }

    /// Collects the dataframe.
    fn collect(&self, _df: DataFrameRRef) -> PolicyCarryingResult<DataFrame> {
        Err(PolicyCarryingError::OperationNotAllowed(format!(
            "this collection cannot be done!"
        )))
    }
}

/// Returns a pointer to the trait object.
type Loader = fn(name: *const u8, len: usize, ptr: *mut u64) -> i64;

pub struct ApiModuleManager {
    plugins: HashMap<String, Arc<dyn PolicyApiSet>>,
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
        self.plugins.insert(plugin_name.into(), *plugin);

        Ok(())
    }

    pub fn unload(&mut self, plugin_name: &str) -> PolicyCarryingResult<()> {
        self.plugins.retain(|plugin, _| plugin != plugin_name);

        Ok(())
    }

    pub fn get(&self, name: &str) -> PolicyCarryingResult<Arc<dyn PolicyApiSet>> {
        self.plugins
            .get(name)
            .cloned()
            .ok_or(PolicyCarryingError::SymbolNotFound(name.into()))
    }

    pub fn add(&mut self, plugin: Arc<dyn PolicyApiSet>) -> PolicyCarryingResult<()> {
        let name = plugin.name();

        match self.plugins.entry(name.into()) {
            Entry::Occupied(_) => Err(PolicyCarryingError::ImpossibleOperation(
                "duplicate key".into(),
            )),
            Entry::Vacant(e) => {
                e.insert(plugin);
                Ok(())
            }
        }
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
    let mut lock = get_rwlock!(API_MANAGER, write, PolicyCarryingError::Unknown);

    lock.load(path, name)?;
    Ok(ApiRefId(id))
}

/// This is called at the executor level when we want to get the [`PolicyApiSet`] for data access.
pub fn get_api(id: ApiRefId) -> PolicyCarryingResult<ApiRef> {
    let lock = API_ID_MAP
        .read()
        .map_err(|_| PolicyCarryingError::Unknown)?;
    let name = lock
        .get(&id)
        .ok_or(PolicyCarryingError::OperationNotAllowed(
            "this api set is not registerd".into(),
        ))?;

    get_rwlock!(API_MANAGER, read, PolicyCarryingError::Unknown).get(name)
}
