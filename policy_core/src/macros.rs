#[macro_export]
macro_rules! get_lock {
    ($lock:expr, $op:ident) => {
        match $lock.$op() {
            Ok(lock) => lock,
            Err(_) => return Err($crate::error::PolicyCarryingError::Unknown),
        }
    };
}

#[macro_export]
macro_rules! args {
    ($($key:tt : $value:expr),* $(,)?) => {{
        let mut arg = $crate::types::FunctionArguments {
            inner: Default::default(),
        };

        $(
            arg.inner.insert($key.into(), $value.into());
        )*

        arg
    }};
}
