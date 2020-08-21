use std::sync::Arc;
use stowaway::Stowable;

#[test]
#[cfg(feature = "derive")]
fn test_derive() {
    #[derive(Stowable)]
    struct _Empty;

    #[derive(Stowable)]
    struct _Empty2();

    #[derive(Stowable)]
    struct _Empty3 {};

    #[derive(Stowable)]
    struct _Test {
        data: usize,
    }

    #[derive(Stowable)]
    struct _Test2(usize);

    #[derive(Stowable)]
    struct _HoldsPtr<T> {
        ptr: Arc<T>,
    }

    #[derive(Stowable)]
    struct _HoldsPtr2<T>(Arc<T>);
}
