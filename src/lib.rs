#![feature(array_try_from_fn)]

use std::num::NonZero;
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
