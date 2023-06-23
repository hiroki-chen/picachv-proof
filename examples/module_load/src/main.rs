use policy_carrying_data::api::{ApiModuleManager, ApiRequest};

fn main() {
    let mut pm = ApiModuleManager::new();

    pm.load("../../target/release/libmodule_lib.so", "foo")
        .unwrap();

    let df = pm.get("foo").unwrap().entry(ApiRequest::Invalid).unwrap();

    println!("{df}");
}
