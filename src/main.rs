fn main() {
    println!("Hello, world!");

    let pcd1, pcd2: PCD;

    let pcd = APCD::from(vec![pcd1, pcd2]);
}

pub trait Policy {}

pub struct PCD<T> where T: Policy {
    policy: Policy,
    data: T
    state: State<Policy>
}

struct APCD<T> where T: Policy {
    policy: Policy,
    data: Vec<&T>,
    state: State<Policy>
}

impl APCD {
    fn from<T: Policy>(data: Vec<&T: Policy>) -> Self {
        let mut policy = Policy::top();
        for d in data {
            policy = policy.join(d.policy);
        }
    }
}

dp!(field_type: ty, dp_params: float) {}

P(state) => forall (field_type: ty, dp_params: float) => policy_compliant(dp!(field_type: ty, dp_params: float))
