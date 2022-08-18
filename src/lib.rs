use std::{
    any::TypeId,
    error::Error,
    io::{Read, Write},
    mem::{size_of, transmute, MaybeUninit},
    str,
};

type GenErr = Box<dyn Error>;

pub trait ReadBin: Sized {
    fn read_bin(from: &mut impl Read) -> Result<Self, GenErr>;
}

pub trait ReadBinBox {
    fn read_bin_box(from: &mut impl Read) -> Result<Box<Self>, GenErr>;
}

pub trait WriteBin {
    fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), GenErr>;
}

fn is_byte<T: 'static>() -> bool {
    (TypeId::of::<T>() == TypeId::of::<u8>()) || (TypeId::of::<T>() == TypeId::of::<i8>())
}

macro_rules! num_rw_impl {
    ($($SelfT:ty),+ $(,)?) => {$(
        impl ReadBin for $SelfT {
            fn read_bin(from: &mut impl Read) -> Result<Self, GenErr> {
                let mut buf = [0; size_of::<Self>()];
                from.read_exact(buf.as_mut_slice())?;
                Ok(Self::from_le_bytes(buf))
            }
        }

        impl WriteBin for $SelfT {
            fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), GenErr> {
                Ok(to.write_all(Self::to_le_bytes(*value).as_slice())?)
            }
        }
    )*};
}

num_rw_impl!(isize, usize, u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, f32, f64);

impl ReadBin for bool {
    fn read_bin(from: &mut impl Read) -> Result<Self, GenErr> {
        Ok(u8::read_bin(from)? > 0)
    }
}

impl WriteBin for bool {
    fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), GenErr> {
        let value = if *value { 1 } else { 0 };
        u8::write_bin(&value, to)
    }
}

impl ReadBin for char {
    fn read_bin(from: &mut impl Read) -> Result<Self, GenErr> {
        Ok(char::try_from(u32::read_bin(from)?)?)
    }
}

impl WriteBin for char {
    fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), GenErr> {
        u32::write_bin(&(*value as u32), to)
    }
}

impl<T: ReadBin + 'static> ReadBinBox for [T] {
    fn read_bin_box(from: &mut impl Read) -> Result<Box<Self>, GenErr> {
        Ok(Vec::read_bin(from)?.into_boxed_slice())
    }
}

impl<T: WriteBin + 'static> WriteBin for [T] {
    fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), GenErr> {
        u32::write_bin(&value.len().try_into()?, to)?;

        if value.len() == 0 {
            return Ok(());
        }

        if is_byte::<T>() {
            // SAFETY: We know that `T` is `u8` or `i8` so can safely reinterpret.
            to.write_all(unsafe { transmute(value) })?;
        } else {
            for elem in value {
                T::write_bin(elem, to)?;
            }
        }

        Ok(())
    }
}

impl ReadBinBox for str {
    fn read_bin_box(from: &mut impl Read) -> Result<Box<Self>, GenErr> {
        Ok(Box::from(str::from_utf8(Vec::read_bin(from)?.as_slice())?))
    }
}

impl WriteBin for str {
    fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), GenErr> {
        WriteBin::write_bin(value.as_bytes(), to)
    }
}

impl ReadBin for String {
    fn read_bin(from: &mut impl Read) -> Result<Self, GenErr> {
        let buf = Vec::read_bin(from)?;
        Ok(Self::from_utf8(buf)?)
    }
}

impl WriteBin for String {
    fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), GenErr> {
        WriteBin::write_bin(value.as_str(), to)
    }
}

impl<T: ReadBin + 'static> ReadBin for Vec<T> {
    fn read_bin(from: &mut impl Read) -> Result<Self, GenErr> {
        let len = u32::read_bin(from)? as usize;

        if len == 0 {
            return Ok(Vec::new());
        }

        let mut vec = Vec::with_capacity(len);

        if is_byte::<T>() {
            // SAFETY: Bytes will be overwritten by the reader.
            unsafe { vec.set_len(len) };
            // SAFETY: We know that `T` is `u8` or `i8` so can safely reinterpret.
            from.read_exact(unsafe { transmute(vec.as_mut_slice()) })?;
        } else {
            for _ in 0..len {
                vec.push(T::read_bin(from)?);
            }
        }

        Ok(vec)
    }
}

impl<T: WriteBin + 'static> WriteBin for Vec<T> {
    fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), GenErr> {
        WriteBin::write_bin(value.as_slice(), to)
    }
}

impl<T: ReadBin + 'static, const N: usize> ReadBin for [T; N] {
    fn read_bin(from: &mut impl Read) -> Result<Self, GenErr> {
        if N == 0 {
            // SAFETY: The length is 0, no initialization required.
            return Ok(unsafe { MaybeUninit::uninit().assume_init() });
        }

        // SAFETY: The array elements are `MaybeUninit`s, which do not require initialization.
        let mut arr: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };

        if is_byte::<T>() {
            // SAFETY: We know that `T` is `u8` or `i8` so can safely reinterpret.
            from.read_exact(unsafe { transmute(arr.as_mut_slice()) })?;
        } else {
            for elem in &mut arr {
                elem.write(T::read_bin(from)?);
            }
        }

        // SAFETY: All elements should be initialized at this point.
        // `mem::transmute` does not allow this
        // but reinterpreting `[MaybeUninit<T>; N]` as `[T; N]` should be safe.
        Ok(unsafe { arr.as_ptr().cast::<[T; N]>().read() })
    }
}

impl<T: WriteBin + 'static, const N: usize> WriteBin for [T; N] {
    fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), GenErr> {
        if N == 0 {
            return Ok(());
        }

        if is_byte::<T>() {
            // SAFETY: We know that `T` is `u8` or `i8` so can safely reinterpret.
            to.write_all(unsafe { transmute(value.as_slice()) })?;
        } else {
            for elem in value {
                T::write_bin(elem, to)?;
            }
        }

        Ok(())
    }
}

impl<T: ReadBin> ReadBinBox for T {
    fn read_bin_box(from: &mut impl Read) -> Result<Box<Self>, GenErr> {
        Ok(Box::new(Self::read_bin(from)?))
    }
}

impl<T: ReadBinBox + ?Sized> ReadBin for Box<T> {
    fn read_bin(from: &mut impl Read) -> Result<Self, GenErr> {
        T::read_bin_box(from)
    }
}

impl<T: WriteBin + ?Sized> WriteBin for Box<T> {
    fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), GenErr> {
        T::write_bin(value.as_ref(), to)
    }
}

impl<T: WriteBin + ?Sized> WriteBin for &T {
    fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), GenErr> {
        T::write_bin(*value, to)
    }
}
