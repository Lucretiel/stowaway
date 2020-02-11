#![no_std]

//! Stowaway is a library for efficiently storing values in a pointer. The
//! main use case for stowaway is as a helpful way to interoperate with
//! libraries that require opaque data to be passed via pointer, such as C
//! libraries expecting a `void*`, `std::RawWaker`, and `boost::context`.
//!
//! The central feature of this library is value packing in a [`Stowaway`]
//! struct. If `T` is not larger than a pointer (that is, if
//! `sizeof(T) <= sizeof(*T))`, then the value is packed directly into the
//! bytes of an opaque pointer value (specifically, a `*mut ()`). This
//! value can then be passed as the context pointer for C-like interfaces,
//! and then converted back into a [`Stowaway`] on the other end.
//!
//! # Lifecycle
//!
//! The basic lifecycle of a [`Stowaway`] value is as follows:
//!
//! - Create a [`Stowaway`] with [`Stowaway::new`]. This will pack the value
//!   into the space of a pointer, or box it if it's too big.
//! - Convert that value into a pointer with [`Stowaway::into_raw`].
//! - Store that value somewhere, such as in a `RawWaker`, or as a `void*` in
//!   a C API. Recover the value somewhere else.
//! - Convert the pointer back into a [`Stowaway`] with [`Stowaway::from_raw`].
//!   This takes back ownership of the value, so make sure to only do it once,
//!   and discard the pointer afterwards.
//! - Covert the [`Stowaway`] back into a `T`, or use it as a container with
//!   `Deref` / `AsRef` / `DerefMut` / `AsMut`.
//!
//! ## Simple example:
//!
//! ```
//! use stowaway::Stowaway;
//!
//! fn demo_lifecycle<T: Clone + std::fmt::Debug + Eq>(value: T) {
//!     let cloned = value.clone();
//!
//!     let stowed: Stowaway<T> = Stowaway::new(value);
//!     let storage = Stowaway::into_raw(stowed);
//!     // At this point, the storage pointer would be passed into a C API,
//!     // and recovered somewhere else
//!     let new_stowed: Stowaway<T> = unsafe { Stowaway::from_raw(storage) };
//!     let unstowed: T = Stowaway::into_inner(new_stowed);
//!
//!     assert_eq!(unstowed, cloned);
//! }
//!
//! // A small value, like a u16, is stored directly in the pointer. No
//! // allocations are performed in this example.
//! demo_lifecycle(137u16);
//!
//! // A large value, like  `Vec` (which internally is a data pointer and a
//! // pair of usize) cannot fit in a pointer, and will therefore be boxed
//! // when stored in `Stowaway`
//! demo_lifecycle(vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
//! ```
//!
//! # C-like API Example
//!
//! In this example, we create a fake "C like" API. We will store in this API
//! a series of function pointers and context data pointers, which will then
//! be called all at once.
//!
//! ```
//! # use std::cell::RefCell;
//! # use std::fmt::Write;
//! use stowaway::Stowaway;
//!
//! // Fake stdout
//! static mut stdout: String = String::new();
//!
//! #[derive(Default)]
//! struct EventList {
//!     events: Vec<(fn(*mut ()), *mut())>
//! }
//!
//! impl EventList {
//!     // our fake C API: add a function pointer and a *mut () to a list
//!     // of callbacks to run.
//!     fn add_event(&mut self, fptr: fn(*mut ()), ctx: *mut()) {
//!         self.events.push((fptr, ctx));
//!     }
//!
//!     // For each function pointer added with add_event, call the function
//!     // with the context pointer.
//!     fn run_all_events(self) {
//!         self.events.into_iter().for_each(|(fptr, ctx)| {
//!             fptr(ctx);
//!         })
//!     }
//! }
//!
//! let mut event_list = EventList::default();
//!
//! // Add some events to the list
//!
//! // Event 1: print a simple number. u16 should easily fit in a pointer,
//! // so this won't allocate anything
//! fn print_u16(value: *mut()) {
//!     unsafe {
//!         let value: Stowaway<u16> = unsafe { Stowaway::from_raw(value) };
//!         writeln!(&mut stdout, "A number: {}", *value).unwrap();
//!     }
//! }
//!
//! event_list.add_event(print_u16, Stowaway::into_raw(Stowaway::new(10u16)));
//! event_list.add_event(print_u16, Stowaway::into_raw(Stowaway::new(20u16)));
//!
//! // Event 2: Print a large array (`[u64; 8]`). This won't definitely won't fit
//! // in a pointer, so stowaway will automatically allocate it for us
//! fn print_big_array(value:  *mut()) {
//!     unsafe {
//!         let value: Stowaway<[u64; 8]> = unsafe { Stowaway::from_raw(value) };
//!         writeln!(&mut stdout, "8 large numbers: {:?}", *value).unwrap();
//!     }
//! }
//!
//! let data: [u64; 8] = [1, 1, 2, 3, 5, 8, 13, 21];
//! event_list.add_event(print_big_array, Stowaway::into_raw(Stowaway::new(data)));
//!
//! let data: [u64; 8] = [34, 55, 89, 144, 233, 377, 610, 987];
//! event_list.add_event(print_big_array, Stowaway::into_raw(Stowaway::new(data)));
//!
//! // Execute all the events
//! event_list.run_all_events();
//!
//! unsafe {
//!     assert_eq!(stdout,
//!         "A number: 10\n\
//!          A number: 20\n\
//!          8 large numbers: [1, 1, 2, 3, 5, 8, 13, 21]\n\
//!          8 large numbers: [34, 55, 89, 144, 233, 377, 610, 987]\n"
//!     );
//! }
//! ```

extern crate alloc;

use alloc::boxed::Box;
use core::fmt;
use core::mem::{self, MaybeUninit};
use core::ops::{Deref, DerefMut};
use core::ptr;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum SizeClass {
    Zero,
    Packed,
    Boxed,
}

use SizeClass::*;

/// A maybe-allocated container. This struct stores a single `T` value, either
/// by boxing it or (if `T` is small enough) by packing it directly into the bytes
/// of a raw pointer.
///
/// See the [module level documentation][crate] for more information.
///
/// # Example
///
/// ```
/// use stowaway::Stowaway;
///
/// let value1: usize = 256;
/// let value1_stowed = Stowaway::new(value1);
/// let storage: *mut() = Stowaway::into_raw(value1_stowed);
/// let value2_stowed = unsafe { Stowaway::from_raw(storage) };
/// let value2: usize = Stowaway::into_inner(value2_stowed);
///
/// assert_eq!(value1, value2);
/// ```
// TODO: Find a way to test that this actually does what it claims; that is,
// that it boxes large values and copies small ones.
#[repr(transparent)]
pub struct Stowaway<T> {
    // TODO: Reimplemnt this as union, once we can have non-copy fields in a
    // union.
    storage: *mut T,
}

impl<T> Stowaway<T> {
    /// If true, we're packing a T into a *mut T. Otherwise, we're
    /// using a box.
    ///
    /// TODO: make this a const fn when `if` is allowed in const
    #[inline(always)]
    fn size_class() -> SizeClass {
        assert_eq!(
            mem::size_of::<*mut T>(),
            mem::size_of::<*mut ()>(),
            "Cannot currently stow pointers to DSTs"
        );

        if mem::align_of::<T>() > mem::align_of::<*mut T>() {
            // Need to unconditionally box values that don't match our
            // alignment, even if sizeof(T) <= sizeof(Self)
            Boxed
        } else if mem::size_of::<T>() == 0 {
            Zero
        } else if mem::size_of::<T>() <= mem::size_of::<*mut T>() {
            Packed
        } else {
            Boxed
        }
    }

    /// Create a new `Stowaway`. If `T` can fit into a pointer, it will be
    /// stored directly in the struct; otherwise, it will be boxed and the
    /// `Box` will be stored in the struct. See the
    /// [module level documentation][crate] for more information.
    #[inline]
    pub fn new(value: T) -> Self {
        let storage = match Self::size_class() {
            // Box is known to not allocate for ZSTs, so we defer to it for
            // managing in-place zero size values.
            //
            // TODO: make sure this is actually true. Dissasembly inspection
            // reveals that it is at the time of this writing, but it's unclear
            // if Box guarantees it an an API level. See Lucretiel/stowaway/#5
            // for details.
            Boxed | Zero => Box::into_raw(Box::new(value)),
            Packed => {
                // Need to init (zero) all bytes. Even if sizeof(T) == sizeof(*T),
                // T may contain unused/uninit padding bytes. TODO: figure out a way
                // to initialize these bytes (to the satisfaction of defined
                // behavior) without zeroing them, if possible.
                let mut blob: MaybeUninit<*mut T> = MaybeUninit::zeroed();

                let ptr = blob.as_mut_ptr();

                unsafe {
                    // Safety: We know that the underlying bytes are unused, and
                    // that there are enough of them, and that blob takes ownership
                    // of value. This write call is paired with a `read` call in
                    // `into_inner`.
                    ptr::write(ptr as *mut T, value);

                    // Safety: all the bytes of blob were initialized, either
                    // as zero or with `value`
                    blob.assume_init()
                }
            }
        };

        Self { storage }
    }

    /// Recreate a [`Stowaway`] from a raw pointer from a previous call
    /// to [`into_raw`][Stowaway::into_raw] or [`stow`]. The pointer **must**
    /// be discarded after the call to this function, because the returned
    /// [`Stowaway`] takes back ownership of the underlying `T` value.
    ///
    /// # Safety
    ///
    /// This function has similar safety requirements as [`std::ptr::read`],
    /// and [`Box::from_raw`] with the added caveat that the only valid way to
    /// create a `storage` pointer is with the [`stow`] or
    /// [`Stowaway::into_raw`] functions:
    ///
    /// - The `storage` value **must**  have come from a previous `into_raw`
    ///   or `stow` call for a value of exactly the same `T`.
    /// - This particular `storage` value **must not** be used to create
    ///   any additional `Stowaway` values. Note that this applies even for
    ///   `Copy` types, because the value may have been boxed.
    /// - You must take care to not recreate a [`Stowaway`] across a thread
    ///   boundary for non-`Send` types.
    #[inline]
    pub unsafe fn from_raw(storage: *mut ()) -> Self {
        Self {
            storage: storage as *mut T,
        }
    }

    /// Unwrap this [`Stowaway`] and get the underlying value.
    #[inline]
    pub fn into_inner(stowed: Self) -> T {
        let storage = stowed.storage;
        mem::forget(stowed);

        match Self::size_class() {
            // Safety: we previously created a box in `new`
            Boxed | Zero => *unsafe { Box::from_raw(storage) },
            Packed => {
                // This can all be done with transmute_copy, but:
                // - I prefer to make sure the right casts are happening (
                //   T vs *T vs **T)
                // - transmute_copy uses an unaligned read, which we don't need
                // - I prefer to pair read/write calls, as opposed to using
                //   `write` in `new` but `transmute` here.
                let ptr_to_storage: *const *mut T = &storage;
                let ptr_to_value: *const T = ptr_to_storage as *const T;

                // Safety:
                //
                // - This value was previously placed in storage by a call to `new`
                // - It won't be double-freed, because we did a forget earlier.
                unsafe { ptr::read(ptr_to_value) }
            }
        }
    }

    /// Get the storage pointer. Note that this is NOT a valid pointer,
    /// and can never be safely dereferenced or written to. The only safe
    /// thing to do with this pointer to to convert it back into a [`Stowaway`]
    /// (for instance, on the other side of an ffi boundary) with `from_raw`,
    /// or directly back into a `T` with [`unstow`].
    ///
    /// The returned value has ownership of the underlying `T` value.
    /// therefore, it must be dropped as soon as possible after converting
    /// it back into a [`Stowaway`]. In particular, it is undefined behavior
    /// to create two [`Stowaway`] instances from the same raw pointer (even
    /// if `T` is `Copy`!).
    #[inline]
    pub fn into_raw(stowed: Self) -> *mut () {
        let storage = stowed.storage;
        mem::forget(stowed);
        storage as *mut ()
    }
}
// These tests are designed to detect undefined behavior in miri under naive,
// incorrect implementations of Stowaway.
#[cfg(test)]
mod test_for_uninit_bytes {
    use crate::{stow, unstow};
    #[test]
    fn zst() {
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        struct Zst;
        let x = Zst;
        let stowed = stow(x);
        let unstowed = unsafe { unstow(stowed) };
        assert_eq!(x, unstowed);
    }
    #[test]
    fn small_t() {
        let x: u8 = 7;
        let stowed = stow(x);
        let unstowed = unsafe { unstow(stowed) };
        assert_eq!(x, unstowed);
    }
    #[test]
    fn t_with_gaps_32() {
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        struct Gaps32 {
            a: u8,
            b: u16,
        }
        let x = Gaps32 { a: 7, b: 42 };
        let stowed = stow(x);
        let unstowed = unsafe { unstow(stowed) };
        assert_eq!(x, unstowed);
    }
    #[test]
    fn t_with_gaps_64() {
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        struct Gaps64 {
            a: u8,
            b: u32,
        }
        let x = Gaps64 { a: 7, b: 42 };
        let stowed = stow(x);
        let unstowed = unsafe { unstow(stowed) };
        assert_eq!(x, unstowed);
    }
}

impl<T> Drop for Stowaway<T> {
    fn drop(&mut self) {
        // TODO: Deduplicate drop, into_inner, and as_ref
        match Self::size_class() {
            // Safety: this box was previously created by Self::new
            Boxed | Zero => drop(unsafe { Box::from_raw(self.storage) }),
            Packed => {
                let storage = self.storage;
                let ptr_to_storage: *const *mut T = &storage;
                let ptr_to_value: *const T = ptr_to_storage as *const T;

                // Safety:
                //
                // - This value was previously placed in storage by a call to `new`
                drop(unsafe { ptr::read(ptr_to_value) });
            }
        }
    }
}

#[cfg(test)]
mod test_drop {
    use crate::Stowaway;
    use core::cell::Cell;
    use core::mem;
    use core::sync::atomic::{AtomicU32, Ordering};

    struct DropCounter<'a> {
        counter: &'a Cell<u32>,
    }

    impl<'a> Drop for DropCounter<'a> {
        fn drop(&mut self) {
            self.counter.set(self.counter.get() + 1);
        }
    }

    #[test]
    fn zero_size_value() {
        static COUNTER: AtomicU32 = AtomicU32::new(0);

        #[derive(Debug)]
        struct StaticDropCounter;

        impl Drop for StaticDropCounter {
            fn drop(&mut self) {
                COUNTER.fetch_add(1, Ordering::SeqCst);
            }
        }

        {
            let value = StaticDropCounter;
            assert_eq!(COUNTER.load(Ordering::SeqCst), 0);

            let stowed_value = Stowaway::new(value);
            assert_eq!(COUNTER.load(Ordering::SeqCst), 0);

            let storage = Stowaway::into_raw(stowed_value);
            assert_eq!(COUNTER.load(Ordering::SeqCst), 0);

            let stowed_value = unsafe { Stowaway::<StaticDropCounter>::from_raw(storage) };
            assert_eq!(COUNTER.load(Ordering::SeqCst), 0);

            mem::drop(stowed_value);
            assert_eq!(COUNTER.load(Ordering::SeqCst), 1);
        }
    }

    #[test]
    fn small_stowed_value() {
        let counter: Cell<u32> = Cell::new(0);

        // Create a value, cycle it through the Stowaway lifecycle, and
        // ensure it was dropped exactly once.
        let value = DropCounter { counter: &counter };
        assert_eq!(counter.get(), 0);

        let stowed_value = Stowaway::new(value);
        assert_eq!(counter.get(), 0);

        let storage = Stowaway::into_raw(stowed_value);
        assert_eq!(counter.get(), 0);

        let stowed_value = unsafe { Stowaway::<DropCounter>::from_raw(storage) };
        assert_eq!(counter.get(), 0);

        mem::drop(stowed_value);
        assert_eq!(counter.get(), 1);
    }

    #[test]
    fn small_raw_value() {
        let counter: Cell<u32> = Cell::new(0);

        // Create a value, cycle it through the Stowaway lifecycle, and
        // ensure it was dropped exactly once.
        let value = DropCounter { counter: &counter };
        assert_eq!(counter.get(), 0);

        let stowed_value = Stowaway::new(value);
        assert_eq!(counter.get(), 0);

        let storage = Stowaway::into_raw(stowed_value);
        assert_eq!(counter.get(), 0);

        let stowed_value = unsafe { Stowaway::<DropCounter>::from_raw(storage) };
        assert_eq!(counter.get(), 0);

        let raw_value: DropCounter = Stowaway::into_inner(stowed_value);
        assert_eq!(counter.get(), 0);

        mem::drop(raw_value);
        assert_eq!(counter.get(), 1);
    }

    #[test]
    fn large_stowed_value() {
        let counter: Cell<u32> = Cell::new(0);

        // Create a large array of DropCounters, cycle it through the
        // Stowaway lifecycle, and ensure it was dropped exactly once.
        let value: [DropCounter; 16] = [
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
        ];
        assert_eq!(counter.get(), 0);

        let stowed_value = Stowaway::new(value);
        assert_eq!(counter.get(), 0);

        let storage = Stowaway::into_raw(stowed_value);
        assert_eq!(counter.get(), 0);

        let stowed_value = unsafe { Stowaway::<[DropCounter; 16]>::from_raw(storage) };
        assert_eq!(counter.get(), 0);

        mem::drop(stowed_value);
        assert_eq!(counter.get(), 16);
    }

    #[test]
    fn large_raw_stowed_value() {
        let counter: Cell<u32> = Cell::new(0);

        // Create a large array of DropCounters, cycle it through the
        // Stowaway lifecycle, and ensure it was dropped exactly once.
        let value: [DropCounter; 16] = [
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
            DropCounter { counter: &counter },
        ];
        assert_eq!(counter.get(), 0);

        let stowed_value = Stowaway::new(value);
        assert_eq!(counter.get(), 0);

        let storage = Stowaway::into_raw(stowed_value);
        assert_eq!(counter.get(), 0);

        let stowed_value = unsafe { Stowaway::<[DropCounter; 16]>::from_raw(storage) };
        assert_eq!(counter.get(), 0);

        let raw_value: [DropCounter; 16] = Stowaway::into_inner(stowed_value);
        assert_eq!(counter.get(), 0);

        mem::drop(raw_value);
        assert_eq!(counter.get(), 16);
    }
}

impl<T: Default> Default for Stowaway<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> From<T> for Stowaway<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> AsRef<T> for Stowaway<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        let ptr_to_storage = match Self::size_class() {
            // In the box case, storage IS a valid pointer, so simply
            // dereference it
            Boxed | Zero => self.storage,
            Packed => (&self.storage) as *const *mut T as *const T,
        };

        unsafe { &*ptr_to_storage }
    }
}

impl<T> AsMut<T> for Stowaway<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut T {
        let ptr_to_storage = match Self::size_class() {
            // In the box case, storage IS a valid pointer, so simply
            // dereference it
            Boxed | Zero => self.storage,
            Packed => (&mut self.storage) as *mut *mut T as *mut T,
        };

        unsafe { &mut *ptr_to_storage }
    }
}

impl<T> Deref for Stowaway<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<T> DerefMut for Stowaway<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        self.as_mut()
    }
}

impl<T: Clone> Clone for Stowaway<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self::new(self.as_ref().clone())
    }

    #[inline]
    fn clone_from(&mut self, other: &Self) {
        self.as_mut().clone_from(other.as_ref());
    }
}

impl<T: fmt::Debug> fmt::Debug for Stowaway<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Stowaway")
            .field("inner", self.as_ref())
            .field("type", &Self::size_class())
            .finish()
    }
}

unsafe impl<T: Send> Send for Stowaway<T> {}
unsafe impl<T: Sync> Sync for Stowaway<T> {}

/// Stow a value into a `*mut ()`. This function will store the value's bytes
/// directly into the pointer if it will fit; otherwise it will box the value
/// and return the raw pointer. The value can be unstowed with a call to
/// [`unstow`], or converted into a [`Stowaway`] with [`Stowaway::from_raw`]
///
/// This is the equivalent of `Stowaway::into_raw(Stowaway::new(value))`
#[inline]
pub fn stow<T>(value: T) -> *mut () {
    Stowaway::into_raw(Stowaway::new(value))
}

/// Restore a value that was previously stowed, either with [`stow`] or with
/// [`Stowaway::into_raw`]. The `storage` pointer **must** be discarded after
/// the call to this function, as this function takes back ownership of the
/// inner `T` value.
///
/// If you don't need a `T` value– that is, if an `&T` or `&mut T` would
/// suffice– consider using [`Stowaway::from_raw`] instead, as that will omit
/// the extra copy out of the box if the value is boxed.
///
/// This is the equivalent of `Stowaway::into_inner(Stowaway::from_raw(storage))`
///
/// # Safety
///
/// This function has similar safety requirements as [`std::ptr::read`]
/// and [`Box::from_raw`] with the added caveat that the only valid way to
/// create a `storage` pointer is with the [`stow`] or [`Stowaway::into_raw`]
/// functions:
///
/// - The `storage` value **must** have come from a previous [`stow`] or
/// [`Stowaway::into_raw`] call for a value of exactly the same `T`.
/// - This particular `storage` value **must not** be restored again. Note that
/// this applies even for `Copy` types, because the value may have been boxed.
/// - This function does not respect marker traits; you must take care not to
/// pass a non-`Send` type to a different thread.
#[inline]
pub unsafe fn unstow<T>(storage: *mut ()) -> T {
    Stowaway::into_inner(Stowaway::from_raw(storage))
}

/// Get a reference to a value that was previously stowed, either with [`stow`]
/// or with [`Stowaway::into_raw`]. This function does *not* take ownership
/// of the value in `storage`, but it does create a shared reference to it, so
/// you must take care to not separately take ownership of it somewhere else,
/// or create a mutable reference to it. It is safe to create multiple shared
/// references with the same `storage`, though take care to respect `Sync` in
/// threaded applications.
///
/// # Interior mutability
///
/// Many C-like APIs will provide copies of the `void*` context pointer to
/// their functions. While constructing shared references with these copies is
/// sound, keep in mind that changes made (for example, through a Cell) may
/// not be reflected in other references unless the underlying API propogates
/// them. In general you should use a `Box` rather than a `Stowaway` if you
/// need shared mutablility through a pointer like this.
///
/// # Safety
///
/// This function has similar safety requirements as turning a pointer into
/// a reference.
///
/// - The `storage` value **must** have come from a previous [`stow`] or
/// [`Stowaway::into_raw`] call for a value of exactly the same `T`.
/// - You **must** not unstow the value or create a mutable reference to it
/// while this or any other shared reference to it exist.
/// - This function does not respect marker traits; you must take care not
/// to create a shared reference to a non-`Sync` type across a thread boundary.
///
/// # Example
///
/// ```
/// use stowaway::{ref_from_stowed, stow, unstow};
///
/// let value: i16 = 143;
/// let mut storage = stow(value);
/// {
///     let value_ref_1: &i16 = unsafe { ref_from_stowed(&storage) };
///     let value_ref_2: &i16 = unsafe { ref_from_stowed(&storage) };
///     assert_eq!(value_ref_1, &143);
///     assert_eq!(value_ref_2, &143);
/// }
///
/// // Need to make sure we drop the value;
/// let value: i16 = unsafe { unstow(storage) };
/// ```
#[inline]
pub unsafe fn ref_from_stowed<'a, T>(storage_ref: &'a *mut ()) -> &'a T {
    // Safety: because we use repr(transparent), this is a safe conversion
    let stowaway_ref: &'a Stowaway<T> = &*(storage_ref as *const *mut () as *const Stowaway<T>);
    stowaway_ref.as_ref()
}

#[test]
fn test_ref_from_stowed_small() {
    let value: u16 = 173;
    let storage = stow(value);

    {
        let value_ref_1: &u16 = unsafe { ref_from_stowed(&storage) };
        let value_ref_2: &u16 = unsafe { ref_from_stowed(&storage) };

        assert_eq!(*value_ref_1, 173);
        assert_eq!(*value_ref_2, 173);
    }

    // drop stowed
    let _stowed: Stowaway<u16> = unsafe { Stowaway::from_raw(storage) };
}

#[test]
fn test_ref_from_stowed_large() {
    use alloc::vec;
    use alloc::vec::Vec;

    let value: Vec<i64> = vec![3245, 5675, 4653, 1234, 7345];
    let storage = stow(value);

    {
        let value_ref_1: &Vec<i64> = unsafe { ref_from_stowed(&storage) };
        let value_ref_2: &Vec<i64> = unsafe { ref_from_stowed(&storage) };

        assert_eq!(value_ref_1[3], 1234);
        assert_eq!(value_ref_2[1], 5675);
    }

    // drop stowed
    let _stowed: Stowaway<Vec<i64>> = unsafe { Stowaway::from_raw(storage) };
}

/// Get a mutable reference to a value that was previously stowed, either with
/// [`stow`] or with [`Stowaway::into_raw`]. This function does *not* take
/// ownership of the value in `storage`, but it does create a mutable reference
/// to it, so you must take care to not separately take ownership of it
/// somewhere else, or create any other shared or mutable references to it.
///
/// # Safety
///
/// This function has similar safety requirements as turning a mutable pointer
/// into a mutable reference.
///
/// - The `storage` value **must** have come from a previous [`stow`] or
/// [`Stowaway::into_raw`] call for a value of exactly the same `T`.
/// - You **must** not unstow the value or create any other mutable or shared
/// references to it while this mutable reference exists.
/// - This function does not respect marker traits; you must take care not
/// to create a mutable reference across a thread boundary unless
/// `&mut T: Send`.
///
/// # Example
///
/// ```
/// use stowaway::{mut_ref_from_stowed, stow, unstow};
///
/// let value: Vec<i64> = vec![1, 2, 3, 4];
/// let mut storage = stow(value);
/// {
///     let value_ref: &mut Vec<i64> = unsafe { mut_ref_from_stowed(&mut storage) };
///     value_ref.push(5);
///     value_ref.push(6);
/// }
/// let value: Vec<i64> = unsafe { unstow(storage) };
/// assert_eq!(&value, &[1, 2, 3, 4, 5, 6]);
/// ```
#[inline]
pub unsafe fn mut_ref_from_stowed<'a, T>(storage_ref: &'a mut *mut ()) -> &'a mut T {
    // Safety: because we use repr(transparent), this is a safe conversion
    let stowaway_ref: &'a mut Stowaway<T> = &mut *(storage_ref as *mut *mut () as *mut Stowaway<T>);
    stowaway_ref.as_mut()
}

#[test]
fn test_mut_ref_from_stowed_small() {
    let value: u16 = 173;
    let mut storage = stow(value);

    {
        let value_ref: &mut u16 = unsafe { mut_ref_from_stowed(&mut storage) };
        *value_ref += 55;
    }

    // drop stowed
    let value: u16 = unsafe { unstow(storage) };
    assert_eq!(value, 228);
}

#[test]
fn test_mut_ref_from_stowed_large() {
    use alloc::vec;
    use alloc::vec::Vec;

    let value: Vec<i64> = vec![3245, 5675, 4653, 1234, 7345];
    let mut storage = stow(value);

    {
        let value_ref: &mut Vec<i64> = unsafe { mut_ref_from_stowed(&mut storage) };
        value_ref.push(10);
        value_ref.push(12);
    }

    // drop stowed
    let value: Vec<i64> = unsafe { unstow(storage) };
    assert_eq!(&value, &[3245, 5675, 4653, 1234, 7345, 10, 12]);
}
