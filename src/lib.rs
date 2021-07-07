#![feature(const_generics)]
#![feature(const_evaluatable_checked)]

const USIZE_BITS: usize = usize::BITS as usize;

#[derive(Debug)]
pub enum StackBitSetError {
    IndexOutOfBounds,
}

pub const fn usize_count(n: usize) -> usize {
    (n / USIZE_BITS) + if n % USIZE_BITS == 0 { 0 } else { 1 }
}

#[derive(Clone, Copy, Debug)]
pub struct StackBitSet<const N: usize>
where
    [(); usize_count(N)]: Sized,
{
    data: [usize; usize_count(N)],
}

impl<const N: usize> StackBitSet<N>
where
    [(); usize_count(N)]: Sized,
{
    pub fn new() -> Self {
        StackBitSet {
            data: [0usize; usize_count(N)],
        }
    }
    pub fn get(&self, idx: usize) -> Result<bool, StackBitSetError> {
        if idx < N {
            Ok(self.get_unchecked(idx))
        } else {
            Err(StackBitSetError::IndexOutOfBounds)
        }
    }
    fn get_unchecked(&self, idx: usize) -> bool {
        let chunk = self.data[idx / USIZE_BITS];
        // ! Make sure this is the right cast
        chunk & (1 << (idx % USIZE_BITS)) != 0
    }
    pub fn set(&mut self, idx: usize) -> Result<(), StackBitSetError> {
        if idx < N {
            Ok(self.set_unchecked(idx))
        } else {
            Err(StackBitSetError::IndexOutOfBounds)
        }
    }
    fn set_unchecked(&mut self, idx: usize) {
        let chunk = unsafe { self.data.get_unchecked_mut(idx / USIZE_BITS) };
        *chunk = *chunk | (1 << (idx % USIZE_BITS))
    }
    pub fn reset(&mut self, idx: usize) -> Result<(), StackBitSetError> {
        if idx < N {
            Ok(self.reset_unchecked(idx))
        } else {
            Err(StackBitSetError::IndexOutOfBounds)
        }
    }
    fn reset_unchecked(&mut self, idx: usize) {
        let chunk = unsafe { self.data.get_unchecked_mut(idx / USIZE_BITS) };
        *chunk = *chunk & !(1 << (idx % USIZE_BITS))
    }
}

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
}
