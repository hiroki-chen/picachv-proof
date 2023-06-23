use std::{pin::Pin, sync::Arc};

use policy_carrying_data::{
    api::{ApiRequest, PolicyApiSet},
    pcd, DataFrame,
};
use policy_core::error::PolicyCarryingResult;

static PLUGIN_NAME: &str = "foo";

#[no_mangle]
extern "C" fn load_module(name: *const u8, len: usize, ptr: *mut u64) -> i32 {
    let name = unsafe {
        let str = std::slice::from_raw_parts(name, len);
        std::str::from_utf8_unchecked(str)
    };

    if name != PLUGIN_NAME {
        eprintln!("error: loading a wrong module");
        // Error!
        1
    } else {
        // Double pointer to ensure that we do not lose information in a fat pointer.
        let wrapped = Box::pin(Arc::new(PluginImpl) as Arc<dyn PolicyApiSet>);

        unsafe {
            // Consume the box and leave the ownership to the caller.
            *ptr = Box::into_raw(Pin::into_inner_unchecked(wrapped)) as u64;
        }

        0
    }
}

#[derive(Clone, Default)]
#[repr(C)]
pub struct PluginImpl;

impl PolicyApiSet for PluginImpl {
    fn name(&self) -> &'static str {
        "foo"
    }

    fn load(&self) {
        eprintln!("doing a series of things.");
    }

    fn unload(&self) {
        eprintln!("undoing a series of things.");
    }

    fn entry(&self, _req: ApiRequest) -> PolicyCarryingResult<DataFrame> {
        let pcd = pcd! {
            "column_1" => DataType::Int8: [1, 2, 3, 4, 5, 6, 7, 8],
            "column_2" => DataType::Float64: [1.0, 2.0, 3.0, 4.0, 22.3, 22.3, 22.3, 22.3],
        };

        Ok(pcd)
    }
}
