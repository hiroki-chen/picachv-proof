use std::sync::Arc;

/// Moves `T` out of the pointer to the [`Box`]-ed `T`.
pub fn move_box_ptr<T: ?Sized>(box_ptr: *mut Box<T>) -> Box<T> {
    unsafe { *Box::from_raw(box_ptr) }
}

/// Moves `T` out of the pointer to the [`Arc`]-ed `T`.
pub fn move_arc_ptr<T: ?Sized>(box_ptr: *mut Arc<T>) -> Arc<T> {
    unsafe { *Box::from_raw(box_ptr) }
}
