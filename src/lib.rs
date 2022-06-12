#![feature(generic_const_exprs)]

use std::ops::{Add, Sub};

/// Number of bits in `usize`.
const USIZE_BITS: usize = usize::BITS as usize;

/// Error type of the crate
#[derive(Debug)]
pub enum StackBitSetError {
    IndexOutOfBounds,
}

/// Computes the number of `usize` chunks needed for a bitset of `n` elements.
pub const fn usize_count(n: usize) -> usize {
    (n / USIZE_BITS) + if n % USIZE_BITS == 0 { 0 } else { 1 }
}

pub const fn const_min(a: usize, b: usize) -> usize {
    if a < b {
        a
    } else {
        b
    }
}

/// BitSet with compile-time size. It does not require any allocation
/// and is entirely stored on the stack.
///
/// The only field is an array of `usize`. Each element is stored in a bit
///
/// # Examples
///
/// ```rust
/// use stack_bitset::StackBitSet;
///
/// let mut a: StackBitSet<42> = StackBitSet::new();
/// a.set(12).unwrap();
/// assert!(a.get(12).unwrap());
/// ```
///
#[derive(Clone, Copy, Debug)]
pub struct StackBitSet<const N: usize>
where
    [(); usize_count(N)]: Sized,
{
    data: [usize; usize_count(N)],
}

impl<const N: usize> Default for StackBitSet<N>
where
    [(); usize_count(N)]: Sized,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> StackBitSet<N>
where
    [(); usize_count(N)]: Sized,
{
    /// Create a new empty instance of the bitset
    pub fn new() -> Self {
        StackBitSet {
            data: [0usize; usize_count(N)],
        }
    }

    /// Returns whether the elements at index `idx` in the bitset is set
    pub fn get(&self, idx: usize) -> Result<bool, StackBitSetError> {
        if let Some(chunk) = self.data.get(idx / USIZE_BITS).filter(|_| idx < N) {
            Ok(chunk & (1 << (idx % USIZE_BITS)) != 0)
        } else {
            Err(StackBitSetError::IndexOutOfBounds)
        }
    }

    /// sets the elements at index `idx` in the bitset
    pub fn set(&mut self, idx: usize) -> Result<(), StackBitSetError> {
        if let Some(chunk) = self.data.get_mut(idx / USIZE_BITS).filter(|_| idx < N) {
            *chunk |= 1 << (idx % USIZE_BITS);
            Ok(())
        } else {
            Err(StackBitSetError::IndexOutOfBounds)
        }
    }

    /// Resets the element at index `idx` in the bitset
    pub fn reset(&mut self, idx: usize) -> Result<(), StackBitSetError> {
        if let Some(chunk) = self.data.get_mut(idx / USIZE_BITS).filter(|_| idx < N) {
            *chunk &= !(1 << (idx % USIZE_BITS));
            Ok(())
        } else {
            Err(StackBitSetError::IndexOutOfBounds)
        }
    }
}

impl<const N: usize> StackBitSet<N>
where
    [(); usize_count(N)]: Sized,
{
    pub fn union<const M: usize>(&self, other: &StackBitSet<M>) -> StackBitSet<{ const_min(N, M) }>
    where
        [(); usize_count(M)]: Sized,
        [(); usize_count(const_min(N, M))]: Sized,
    {
        let mut res = StackBitSet::new();
        for i in 0..(const_min(N, M)) {
            if self.get(i).unwrap() || other.get(i).unwrap() {
                res.set(i).unwrap();
            }
        }
        res
    }
    pub fn intersection<const M: usize>(
        &self,
        other: &StackBitSet<M>,
    ) -> StackBitSet<{ const_min(N, M) }>
    where
        [(); usize_count(M)]: Sized,
        [(); usize_count(const_min(N, M))]: Sized,
    {
        let mut res = StackBitSet::new();
        for i in 0..(const_min(N, M)) {
            if self.get(i).unwrap() && other.get(i).unwrap() {
                res.set(i).unwrap();
            }
        }
        res
    }
    pub fn difference<const M: usize>(
        &self,
        other: &StackBitSet<M>,
    ) -> StackBitSet<{ const_min(N, M) }>
    where
        [(); usize_count(M)]: Sized,
        [(); usize_count(const_min(N, M))]: Sized,
    {
        let mut res = StackBitSet::new();
        for i in 0..(const_min(N, M)) {
            if self.get(i).unwrap() {
                res.set(i).unwrap();
            }
            if other.get(i).unwrap() {
                res.reset(i).unwrap();
            }
        }
        res
    }
    pub fn complement(&self) -> StackBitSet<N> {
        let mut res = StackBitSet::new();
        for i in 0..N {
            if !self.get(i).unwrap() {
                res.set(i).unwrap();
            }
        }
        res
    }
    pub fn is_subset<const M: usize>(&self, other: &StackBitSet<M>) -> bool
    where
        [(); usize_count(M)]: Sized,
    {
        for i in 0..N {
            if (i < M && (!other.get(i).unwrap() && self.get(i).unwrap()))
                || (i >= M && self.get(i).unwrap())
            {
                return false;
            }
        }
        !self.is_equal(other)
    }
    pub fn is_equal<const M: usize>(&self, other: &StackBitSet<M>) -> bool
    where
        [(); usize_count(M)]: Sized,
    {
        for i in 0..(N + M - const_min(N, M)) {
            if i < N && i < M && (other.get(i).unwrap() ^ self.get(i).unwrap()) {
                println!("1");
                return false;
            } else if i >= M && i < N && self.get(i).unwrap() {
                println!("2");
                return false;
            } else if i >= N && i < M && other.get(i).unwrap() {
                println!("3");
                return false;
            }
        }
        true
    }
    pub fn is_superset<const M: usize>(&self, other: &StackBitSet<M>) -> bool
    where
        [(); usize_count(M)]: Sized,
    {
        !self.is_equal(other) && !self.is_subset(other)
    }
}

impl<const N: usize, const M: usize> Add<&StackBitSet<M>> for StackBitSet<N>
where
    [(); usize_count(N)]: Sized,
    [(); usize_count(M)]: Sized,
    [(); usize_count(const_min(N, M))]: Sized,
{
    type Output = StackBitSet<{ const_min(N, M) }>;

    fn add(self, other: &StackBitSet<M>) -> Self::Output {
        self.union(other)
    }
}

macro_rules! add_impl {
    ($($t:ty)*) => ($(

        impl<const N: usize> Add<$t> for StackBitSet<N>
where
    [(); usize_count(N)]: Sized,
{
    type Output = StackBitSet<N>;

    fn add(mut self, other: $t) -> StackBitSet<N> {
        self.set(other as usize).unwrap();
        self
    }
}
    )*)
}

add_impl! { usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }

macro_rules! sub_impl {
    ($($t:ty)*) => ($(

        impl<const N: usize> Sub<$t> for StackBitSet<N>
where
    [(); usize_count(N)]: Sized,
{
    type Output = StackBitSet<N>;

    fn sub(mut self, other: $t) -> StackBitSet<N> {
        self.reset(other as usize).unwrap();
        self
    }
}
    )*)
}

sub_impl! { usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }

#[cfg(test)]
mod tests {
    use crate::StackBitSet;
    #[test]
    fn bitset_create() {
        let _a: StackBitSet<42> = StackBitSet::new();
    }

    #[test]
    fn set_reset_bit() {
        let mut a: StackBitSet<42> = StackBitSet::new();
        assert!(!a.get(12).unwrap());
        a.set(12).unwrap();
        assert!(a.get(12).unwrap());
        a.reset(12).unwrap();
        assert!(!a.get(12).unwrap());
    }

    #[test]
    fn equality() {
        let mut a: StackBitSet<42> = StackBitSet::new();
        let mut b: StackBitSet<69> = StackBitSet::new();
        assert!(a.is_equal(&b));
        a.set(12).unwrap();
        assert!(!a.is_equal(&b));
        b.set(12).unwrap();
        assert!(a.is_equal(&b));
    }

    #[test]
    fn union() {
        let mut a: StackBitSet<42> = StackBitSet::new();
        let mut b: StackBitSet<69> = StackBitSet::new();
        a.set(12).unwrap();
        b.set(29).unwrap();
        let mut c: StackBitSet<37> = StackBitSet::new();
        c.set(12).unwrap();
        c.set(29).unwrap();
        assert!(c.is_equal(&(a.union(&b))));
        assert!(a.is_subset(&c));
        assert!(b.is_subset(&c));
        let d: StackBitSet<93> = StackBitSet::new();
        assert!((c.intersection(&a)).intersection(&b).is_equal(&d));
    }

    #[test]
    fn subset() {
        let mut a: StackBitSet<42> = StackBitSet::new();
        let mut b: StackBitSet<69> = StackBitSet::new();
        a.set(12).unwrap();
        b.set(12).unwrap();
        b.set(29).unwrap();

        assert!(a.is_subset(&b));
        assert!(!b.is_subset(&a));
        assert!(b.is_superset(&a));
        assert!(!b.is_equal(&a));
    }
}
