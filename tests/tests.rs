use std::{
    error::Error,
    fmt::Debug,
    io::{Cursor, Read, Seek, SeekFrom, Write},
};

use ::gen_bin_rw::*;

fn mock_file() -> impl Read + Write + Seek {
    Cursor::new(Vec::new())
}

fn rw_test(input: impl ReadBin + WriteBin + PartialEq + Debug) -> Result<(), Box<dyn Error>> {
    let mut file = mock_file();
    WriteBin::write_bin(&input, &mut file)?;

    file.seek(SeekFrom::Start(0))?;
    let output = ReadBin::read_bin(&mut file)?;

    assert_eq!(input, output);
    Ok(())
}

macro_rules! rw_test_values {
    ($($value:expr),+ $(,)?) => {
        $(rw_test($value)?;)*
    };
}

macro_rules! num_test {
    ($($T:ty),+ $(,)?) => {$(
        rw_test_values!(
            42 as $T,
            [1 as $T, 2 as $T, 3 as $T],
            vec![1 as $T, 2 as $T, 3 as $T],
            Vec::<$T>::new(),
            Box::new(42 as $T),
            Box::new([1 as $T, 2 as $T, 3 as $T]),
            Box::new([1 as $T, 2 as $T, 3 as $T]) as Box<[$T]>,
        );
    )*};
}

#[test]
fn numeric() -> Result<(), Box<dyn Error>> {
    num_test!(isize, usize, u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, f32, f64);
    Ok(())
}

#[test]
fn bool() -> Result<(), Box<dyn Error>> {
    rw_test_values!(
        true,
        [true, false],
        vec![true, false],
        Vec::<bool>::new(),
        Box::new(true),
        Box::new([true, false]),
        Box::new([true, false]) as Box<[bool]>,
    );

    Ok(())
}

#[test]
fn char() -> Result<(), Box<dyn Error>> {
    rw_test_values!(
        'A',
        ['A', 'B', 'C'],
        vec!['A', 'B', 'C'],
        Vec::<char>::new(),
        Box::new('A'),
        Box::new(['A', 'B', 'C']),
        Box::new(['A', 'B', 'C']) as Box<[char]>,
    );

    Ok(())
}

#[test]
fn string() -> Result<(), Box<dyn Error>> {
    rw_test_values!(
        "String test".to_owned(),
        ["foo".to_owned(), "bar".to_owned()],
        vec!["vec".to_owned(), "str".to_owned()],
        Vec::<String>::new(),
        Box::<str>::from("str in the box!"),
    );

    Ok(())
}

#[derive(PartialEq, Debug)]
struct CustomType {
    b: bool,
    i: i32,
    f: f64,
    s: String,
}

impl ReadBin for CustomType {
    fn read_bin(from: &mut impl Read) -> Result<Self, Box<dyn Error>> {
        Ok(Self {
            b: ReadBin::read_bin(from)?,
            i: ReadBin::read_bin(from)?,
            f: ReadBin::read_bin(from)?,
            s: ReadBin::read_bin(from)?,
        })
    }
}

impl WriteBin for CustomType {
    fn write_bin(value: &Self, to: &mut impl Write) -> Result<(), Box<dyn Error>> {
        WriteBin::write_bin(&value.b, to)?;
        WriteBin::write_bin(&value.i, to)?;
        WriteBin::write_bin(&value.f, to)?;
        WriteBin::write_bin(&value.s, to)?;
        Ok(())
    }
}

#[test]
fn custom() -> Result<(), Box<dyn Error>> {
    rw_test(CustomType {
        b: true,
        i: 42,
        f: 1.0,
        s: "String".to_owned(),
    })
}
