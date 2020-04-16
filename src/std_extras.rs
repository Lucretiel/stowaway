use std::sync::{Arc, Weak as ArcWeak};

use crate::Stowable;

macro_rules! stowable_ptr {
    (impl <$generic:ident> for $($type:ty)*) => {$(
        unsafe impl<$generic: ?Sized> Stowable for $type {}
    )*}
}

stowable_ptr! {
    impl <T> for
    Arc<T> Option<Arc<T>>
    ArcWeak<T> Option<ArcWeak<T>>
}
