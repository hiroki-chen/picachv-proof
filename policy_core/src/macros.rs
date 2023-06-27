#[macro_export]
macro_rules! get_lock {
    ($lock:expr, $op:ident) => {
        match $lock.$op() {
            Ok(lock) => lock,
            Err(_) => return Err($crate::error::PolicyCarryingError::Unknown),
        }
    };
}
