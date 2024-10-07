#![feature(array_try_from_fn)]

use std::borrow::BorrowMut;
use std::marker::PhantomData;
use std::num::NonZero;
use std::ops::Deref;
use std::ptr::NonNull;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ReadError {
    TooShort,
    InvalidValue,
}

pub unsafe trait ReadScalar: Sized {
    fn read_checked(bytes: &[u8]) -> Result<(Self, &[u8]), ReadError>;

    unsafe fn read_unchecked(ptr: NonNull<u8>) -> (Self, NonNull<u8>);
}

macro_rules! read_scalar_primitives {
    ($($tys:ty),*) => {
        $(

        unsafe impl ReadScalar for $tys {
            fn read_checked(bytes: &[u8]) -> Result<(Self, &[u8]), ReadError> {
                let Some((value, rest)) = bytes.split_at_checked(size_of::<Self>()) else {
                    return Err(ReadError::TooShort);
                };
                let value = unsafe { value.as_ptr().cast::<Self>().read_unaligned() };
                Ok((value, rest))
            }

            unsafe fn read_unchecked(ptr: NonNull<u8>) -> (Self, NonNull<u8>) {
                let ptr = ptr.cast::<Self>();
                let value = ptr.read_unaligned();
                let rest = ptr.add(1).cast();
                (value, rest)
            }
        }

        unsafe impl ReadScalar for NonZero<$tys> {
            fn read_checked(bytes: &[u8]) -> Result<(Self, &[u8]), ReadError> {
                let (value, rest) = <$tys>::read_checked(bytes)?;
                let Some(value) = NonZero::new(value) else {
                    return Err(ReadError::InvalidValue);
                };
                Ok((value, rest))
            }

            unsafe fn read_unchecked(ptr: NonNull<u8>) -> (Self, NonNull<u8>) {
                let ptr = ptr.cast::<Self>();
                let value = ptr.read_unaligned();
                let rest = ptr.add(1).cast();
                (value, rest)
            }
        }

        )*
    };
}

read_scalar_primitives!(u8, u16, u32, u64, u128, usize);
read_scalar_primitives!(i8, i16, i32, i64, i128, isize);

unsafe impl ReadScalar for bool {
    fn read_checked(bytes: &[u8]) -> Result<(Self, &[u8]), ReadError> {
        let (byte, rest) = u8::read_checked(bytes)?;
        match byte {
            0 => Ok((false, rest)),
            1 => Ok((true, rest)),
            _ => Err(ReadError::InvalidValue),
        }
    }

    unsafe fn read_unchecked(ptr: NonNull<u8>) -> (Self, NonNull<u8>) {
        let value = ptr.cast::<bool>().read_unaligned();
        let rest = ptr.add(1).cast();
        (value, rest)
    }
}

unsafe impl ReadScalar for char {
    fn read_checked(bytes: &[u8]) -> Result<(Self, &[u8]), ReadError> {
        let (uint, rest) = u32::read_checked(bytes)?;
        match char::from_u32(uint) {
            Some(value) => Ok((value, rest)),
            None => Err(ReadError::InvalidValue),
        }
    }

    unsafe fn read_unchecked(ptr: NonNull<u8>) -> (Self, NonNull<u8>) {
        let value = ptr.cast::<char>().read_unaligned();
        let rest = ptr.add(1).cast();
        (value, rest)
    }
}

unsafe impl ReadScalar for f32 {
    fn read_checked(bytes: &[u8]) -> Result<(Self, &[u8]), ReadError> {
        let (value, rest) = u32::read_checked(bytes)?;
        Ok((f32::from_bits(value), rest))
    }

    unsafe fn read_unchecked(ptr: NonNull<u8>) -> (Self, NonNull<u8>) {
        let ptr = ptr.cast::<f32>();
        let value = ptr.read_unaligned();
        let rest = ptr.add(1).cast();
        (value, rest)
    }
}

unsafe impl ReadScalar for f64 {
    fn read_checked(bytes: &[u8]) -> Result<(Self, &[u8]), ReadError> {
        let (value, rest) = u64::read_checked(bytes)?;
        Ok((f64::from_bits(value), rest))
    }

    unsafe fn read_unchecked(ptr: NonNull<u8>) -> (Self, NonNull<u8>) {
        let ptr = ptr.cast::<f64>();
        let value = ptr.read_unaligned();
        let rest = ptr.add(1).cast();
        (value, rest)
    }
}

unsafe impl<T: ReadScalar, const N: usize> ReadScalar for [T; N] {
    fn read_checked(mut bytes: &[u8]) -> Result<(Self, &[u8]), ReadError> {
        let value = std::array::try_from_fn(|_| {
            let (value, rest) = T::read_checked(bytes)?;
            bytes = rest;
            Ok(value)
        })?;
        Ok((value, bytes))
    }

    unsafe fn read_unchecked(ptr: NonNull<u8>) -> (Self, NonNull<u8>) {
        let ptr = ptr.cast::<Self>();
        let value = ptr.read_unaligned();
        let rest = ptr.add(1).cast();
        (value, rest)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Tree<'this> {
    Leaf(u32),
    Node(&'this Tree<'this>, &'this Tree<'this>),
}

pub enum TreeTag {
    Leaf = 0,
    Node = 1,
}

unsafe impl ReadScalar for TreeTag {
    fn read_checked(bytes: &[u8]) -> Result<(Self, &[u8]), ReadError> {
        let (value, rest) = u8::read_checked(bytes)?;
        let value = match value {
            0 => TreeTag::Leaf,
            1 => TreeTag::Node,
            _ => return Err(ReadError::InvalidValue),
        };
        Ok((value, rest))
    }

    unsafe fn read_unchecked(ptr: NonNull<u8>) -> (Self, NonNull<u8>) {
        let value = ptr.cast::<Self>().read_unaligned();
        let rest = ptr.add(1).cast();
        (value, rest)
    }
}

pub struct TreeBuilder {
    bytes: Vec<u8>,
}

impl Default for TreeBuilder {
    fn default() -> Self { Self::new() }
}

impl TreeBuilder {
    pub fn new() -> Self { Self { bytes: Vec::new() } }

    pub fn finish(self) -> Vec<u8> { self.bytes }

    pub fn leaf(&mut self, value: u32) {
        self.bytes.push(TreeTag::Leaf as u8);
        self.bytes.extend_from_slice(&value.to_ne_bytes());
    }

    pub fn start_node(&mut self) { self.bytes.push(TreeTag::Node as u8); }
}

impl Tree<'_> {
    fn to_dense(&self) -> Vec<u8> {
        let mut builder = TreeBuilder::new();
        self.to_dense_rec(&mut builder);
        builder.finish()
    }

    fn to_dense_rec(&self, builder: &mut TreeBuilder) {
        match self {
            Tree::Leaf(n) => builder.leaf(*n),
            Tree::Node(lhs, rhs) => {
                builder.start_node();
                let lhs_len_idx = builder.bytes.len();
                builder.bytes.extend_from_slice(&0usize.to_ne_bytes());
                lhs.to_dense_rec(builder);
                let lhs_len = builder.bytes.len() - lhs_len_idx - 8;
                builder.bytes[lhs_len_idx..lhs_len_idx + 8].copy_from_slice(&lhs_len.to_ne_bytes());
                rhs.to_dense_rec(builder);
            }
        }
    }

    fn validate_rec(bytes: &[u8]) -> Result<&[u8], ReadError> {
        let (tag, bytes) = TreeTag::read_checked(bytes)?;
        match tag {
            TreeTag::Leaf => {
                let (_, bytes) = u32::read_checked(bytes)?;
                Ok(bytes)
            }
            TreeTag::Node => {
                let (_lhs_len, bytes) = usize::read_checked(bytes)?;
                let bytes = Tree::validate_rec(bytes)?;
                let bytes = Tree::validate_rec(bytes)?;
                Ok(bytes)
            }
        }
    }

    fn validate(bytes: &[u8]) -> Result<(), ReadError> { Tree::validate_rec(bytes).map(|_| ()) }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TreeView<'bytes> {
    Leaf(u32),
    Node(TreePtr<'bytes>, TreePtr<'bytes>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct TreePtr<'bytes> {
    ptr: NonNull<u8>,
    phantom: PhantomData<&'bytes [u8]>,
}

impl<'bytes> TreePtr<'bytes> {
    unsafe fn new(ptr: NonNull<u8>) -> Self {
        Self {
            ptr,
            phantom: PhantomData,
        }
    }

    fn view(&self) -> TreeView<'bytes> {
        unsafe {
            let ptr = self.ptr;
            let (tag, ptr) = TreeTag::read_unchecked(ptr);
            match tag {
                TreeTag::Leaf => {
                    let (value, _ptr) = u32::read_unchecked(ptr);
                    TreeView::Leaf(value)
                }
                TreeTag::Node => {
                    let (lhs_len, lhs_ptr) = usize::read_unchecked(ptr);
                    let rhs_ptr = lhs_ptr.add(lhs_len);
                    let lhs_ptr = TreePtr::new(lhs_ptr);
                    let rhs_ptr = TreePtr::new(rhs_ptr);
                    TreeView::Node(lhs_ptr, rhs_ptr)
                }
            }
        }
    }
}

impl Tree<'_> {
    pub fn from_dense<'bytes>(bytes: &'bytes [u8]) -> Result<TreePtr<'bytes>, ReadError> {
        let () = Tree::validate(bytes)?;
        let ptr = unsafe { NonNull::new_unchecked(bytes.as_ptr().cast_mut()) };
        unsafe { Ok(Self::from_dense_unchecked(ptr)) }
    }

    pub unsafe fn from_dense_unchecked<'bytes>(ptr: NonNull<u8>) -> TreePtr<'bytes> {
        TreePtr::new(ptr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_dense_leaf() {
        let tree = Tree::Leaf(42);
        let dense = tree.to_dense();
        assert_eq!(dense, [TreeTag::Leaf as u8, 42, 0, 0, 0]);
        assert_eq!(dense.len(), 5);

        let tree = Tree::Leaf(0xAA_BB_CC_DD);
        let dense = tree.to_dense();
        #[rustfmt::skip]
        assert_eq!(
            dense,
            [
                TreeTag::Leaf as u8,     // tag
                0xDD, 0xCC, 0xBB, 0xAA, // leaf value
            ]
        );
        assert_eq!(dense.len(), 5);
    }

    #[test]
    fn to_dense_node() {
        let tree = Tree::Node(&Tree::Leaf(42), &Tree::Leaf(24));

        let dense = tree.to_dense();
        #[rustfmt::skip]
        assert_eq!(
            dense,
            [
                TreeTag::Node as u8,
                5, 0, 0, 0, 0, 0, 0, 0,
                TreeTag::Leaf as u8,
                42, 0, 0, 0,
                TreeTag::Leaf as u8,
                24, 0, 0, 0,
            ]
        );
        assert_eq!(dense.len(), 19);

        let tree = Tree::Node(
            &Tree::Leaf(42),
            &Tree::Node(&Tree::Leaf(100), &Tree::Leaf(200)),
        );

        let dense = tree.to_dense();
        #[rustfmt::skip]
        assert_eq!(
            dense,
            [
                TreeTag::Node as u8,
                5, 0, 0, 0, 0, 0, 0, 0,
                TreeTag::Leaf as u8,
                42, 0, 0, 0,
                TreeTag::Node as u8,
                5, 0, 0, 0, 0, 0, 0, 0,
                TreeTag::Leaf as u8,
                100, 0, 0, 0,
                TreeTag::Leaf as u8,
                200, 0, 0, 0,
            ]
        );
        assert_eq!(dense.len(), 33);
    }

    #[test]
    fn validate_leaf() {
        let bytes = [TreeTag::Leaf as u8, 42, 0, 0, 0];
        assert_eq!(Tree::validate(&bytes), Ok(()));

        let bytes = [TreeTag::Leaf as u8, 42, 0, 0];
        assert_eq!(Tree::validate(&bytes), Err(ReadError::TooShort));

        let bytes = [TreeTag::Leaf as u8, 42, 0];
        assert_eq!(Tree::validate(&bytes), Err(ReadError::TooShort));

        let bytes = [TreeTag::Leaf as u8, 42];
        assert_eq!(Tree::validate(&bytes), Err(ReadError::TooShort));

        let bytes = [TreeTag::Leaf as u8];
        assert_eq!(Tree::validate(&bytes), Err(ReadError::TooShort));

        let bytes = [3];
        assert_eq!(Tree::validate(&bytes), Err(ReadError::InvalidValue));

        let bytes = [];
        assert_eq!(Tree::validate(&bytes), Err(ReadError::TooShort));
    }

    #[test]
    fn validate_node() {
        #[rustfmt::skip]
        assert_eq!(
            Tree::validate(&[
                TreeTag::Node as u8,
                5, 0, 0, 0, 0, 0, 0, 0,
                TreeTag::Leaf as u8,
                42, 0, 0, 0,
                TreeTag::Leaf as u8,
                24, 0, 0, 0,
            ]),
            Ok(())
        );

        #[rustfmt::skip]
        assert_eq!(
            Tree::validate(&[
                3,
                TreeTag::Leaf as u8,
                42, 0, 0, 0,
                TreeTag::Leaf as u8,
                24, 0, 0, 0,
            ]),
            Err(ReadError::InvalidValue)
        );

        #[rustfmt::skip]
        assert_eq!(
            Tree::validate(&[
                1,
            ]),
            Err(ReadError::TooShort)
        );

        #[rustfmt::skip]
        assert_eq!(
            Tree::validate(&[
                TreeTag::Node as u8,
                TreeTag::Leaf as u8,
                42, 0, 0, 0,
            ]),
            Err(ReadError::TooShort)
        );
    }

    #[test]
    fn view_leaf() {
        let bytes = [TreeTag::Leaf as u8, 42, 0, 0, 0];
        let tree_ref = Tree::from_dense(&bytes).unwrap();
        assert_eq!(tree_ref.view(), TreeView::Leaf(42));
    }
}
