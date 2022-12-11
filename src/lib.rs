#![deny(missing_docs)]

//! This crate provides a [BrailleAsciiString] wrapper around an [AsciiString]
//! representing a string encoded in the [Braille
//! Ascii](https://en.wikipedia.org/wiki/Braille_ASCII) format (commonly used in
//! Braille Ready Files). Functions are provided to convert between unicode Braille
//! pattern strings and Braille ASCII encoded strings.

use std::{
    error::Error,
    fmt::{Debug, Display},
};

use ascii::{AsciiChar, AsciiStr, AsciiString};

pub use ascii;

const BRAILLE_ASCII_TO_UNICODE: [char; 96] = [
    '⠀', '⠮', '⠐', '⠼', '⠫', '⠩', '⠯', '⠄', '⠷', '⠾', '⠡', '⠬', '⠠', '⠤', '⠨', '⠌', '⠴', '⠂', '⠆',
    '⠒', '⠲', '⠢', '⠖', '⠶', '⠦', '⠔', '⠱', '⠰', '⠣', '⠿', '⠜', '⠹', '⠈', '⠁', '⠃', '⠉', '⠙', '⠑',
    '⠋', '⠛', '⠓', '⠊', '⠚', '⠅', '⠇', '⠍', '⠝', '⠕', '⠏', '⠟', '⠗', '⠎', '⠞', '⠥', '⠧', '⠺', '⠭',
    '⠽', '⠵', '⠪', '⠳', '⠻', '⠘', '⠸', '⠈', '⠁', '⠃', '⠉', '⠙', '⠑', '⠋', '⠛', '⠓', '⠊', '⠚', '⠅',
    '⠇', '⠍', '⠝', '⠕', '⠏', '⠟', '⠗', '⠎', '⠞', '⠥', '⠧', '⠺', '⠭', '⠽', '⠵', '⠪', '⠳', '⠻', '⠘',
    '⠸',
];

const BRAILLE_CELL_TO_BRAILLE_ASCII: &[u8; 64] =
    b" A1B'K2L@CIF/MSP\"E3H9O6R^DJG>NTQ,*5<-U8V.%[$+X!&;:4\\0Z7(_?W]#Y)=";

/// An error indicating that an invalid character was found.
///
/// Any character outside of the six-dot Unicode Braille patterns that is not
/// an ASCII control character (ASCII values 0-31) or space is considered
/// invalid.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct FromUnicodeError<T> {
    index: usize,
    source: T,
}

impl<T> Display for FromUnicodeError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "the char at index {} is not Braille or an ASCII control character",
            self.index
        )
    }
}

impl<T> Debug for FromUnicodeError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

impl<T> Error for FromUnicodeError<T> {}

/// A type representing an owned ASCII string that encodes a sequence of Braille
/// cells.
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BrailleAsciiString {
    inner: AsciiString,
}

impl BrailleAsciiString {
    /// Creates a new, empty string.
    pub fn new() -> Self {
        Default::default()
    }

    /// Wraps `s` in a [BrailleAsciiString]
    pub fn from_ascii(s: AsciiString) -> Self {
        BrailleAsciiString { inner: s }
    }

    /// Converts `t` from Unicode Braille patterns to Braille ASCII encoding.
    ///
    /// `t` must contain only 6-dot Unicode Braille patterns and/or ASCII
    /// control characters and spaces.
    pub fn from_unicode_braille<T: AsRef<str>>(t: T) -> Result<Self, FromUnicodeError<T>> {
        let s = t.as_ref();
        let mut bytes = Vec::with_capacity(s.chars().count());
        for (i, c) in s.char_indices() {
            if c <= ' ' {
                bytes.push(c as u8);
            } else if ('\u{2800}'..'\u{2840}').contains(&c) {
                let j = (u32::from(c) - 0x2800) as u8;
                bytes.push(BRAILLE_CELL_TO_BRAILLE_ASCII[usize::from(j)]);
            } else {
                return Err(FromUnicodeError {
                    index: i,
                    source: t,
                });
            }
        }
        Ok(BrailleAsciiString {
            inner: unsafe { AsciiString::from_ascii_unchecked(bytes) },
        })
    }

    /// Extracts an [AsciiStr] slice containing the entire string.
    pub fn as_ascii(&self) -> &AsciiStr {
        &self.inner
    }

    /// Extracts a mutable [AsciiStr] slice containing the entire string.
    pub fn as_ascii_mut(&mut self) -> &mut AsciiStr {
        &mut self.inner
    }

    /// Consumes the `BrailleAsciiString` and returns the underlying [AsciiString].
    pub fn into_ascii(self) -> AsciiString {
        self.inner
    }

    /// Converts the `BrailleAsciiString` to a `String` with Unicode Braille patterns.
    pub fn to_unicode_braille(&self) -> String {
        self.inner
            .chars()
            .map(|ch| {
                if ch < AsciiChar::Space {
                    ch.as_char()
                } else {
                    let i = usize::from(ch.as_byte() - 0x20);
                    BRAILLE_ASCII_TO_UNICODE[i]
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TOM_SAWYER_ASCII: &str = r#"
  ,,! ,,ADV5TURES ,,( ,,TOM ,,SAWY] 
  ,,BY 
  ,,M>K ,,TWA9 
  7,SAMUEL ,LANGHORNE ,CLEM5S7   
  ;,P ;,R ;,E ;,F ,A ;,C ;,E 
  ,,MO/ (! ADV5TURES RECORD$ 9 ? BOOK
RE,Y O3URR$2 "O OR TWO 7 EXP]I;ES ( MY
[N1 ! RE/ ^? ( BOYS :O 7 S*OOLMATES (
M9E4 ,HUCK ,F9N IS DRAWN F LIFE2 ,TOM
,SAWY] AL1 B N F AN 9DIVIDUAL--HE IS A
-B9A- TION (! "*I/ICS ( ?REE BOYS :OM ,I
KNEW1 & "!=E 2L;GS 6! -POSITE ORD] (   
>*I- TECTURE4  
  ,! ODD SUP]/I;NS T\*$ ^U 7 ALL PREVA-
L5T AM;G *N & SLAVES 9 ! ,WE/ AT ! P]IOD
( ? /ORY--T IS 6SAY1 ?IRTY OR =TY YE>S
AGO4   
  ,AL? MY BOOK IS 9T5D$ MA9LY =! EN-
T]TA9;T ( BOYS & GIRLS1 ,I HOPE X W N 2
%UNN$ 0M5 & WOM5 ON T A3.T1 = "P ( MY
PLAN HAS BE5 6TRY 6PL1SANTLY REM9D 
ADULTS ( :AT !Y ONCE 7 !MVS1 &( H[ !Y
FELT & ?"\ & TALK$1 & :AT QUE] 5T]PRISES
!Y "S"TS 5GAG$ IN4    
  ,,! ,,AU?OR4  
  ,,H>T=D1 #AHGF4 
  ;,T ,O ;,M ;,S ,A ;,W ;,Y ;,E ;,R    
--------------------------------------#B
"#;

    const TOM_SAWYER_BRAILLE: &str = r#"
⠀⠀⠠⠠⠮⠀⠠⠠⠁⠙⠧⠢⠞⠥⠗⠑⠎⠀⠠⠠⠷⠀⠠⠠⠞⠕⠍⠀⠠⠠⠎⠁⠺⠽⠻⠀
⠀⠀⠠⠠⠃⠽⠀
⠀⠀⠠⠠⠍⠜⠅⠀⠠⠠⠞⠺⠁⠔⠀
⠀⠀⠶⠠⠎⠁⠍⠥⠑⠇⠀⠠⠇⠁⠝⠛⠓⠕⠗⠝⠑⠀⠠⠉⠇⠑⠍⠢⠎⠶⠀⠀⠀
⠀⠀⠰⠠⠏⠀⠰⠠⠗⠀⠰⠠⠑⠀⠰⠠⠋⠀⠠⠁⠀⠰⠠⠉⠀⠰⠠⠑⠀
⠀⠀⠠⠠⠍⠕⠌⠀⠷⠮⠀⠁⠙⠧⠢⠞⠥⠗⠑⠎⠀⠗⠑⠉⠕⠗⠙⠫⠀⠔⠀⠹⠀⠃⠕⠕⠅
⠗⠑⠠⠽⠀⠕⠒⠥⠗⠗⠫⠆⠀⠐⠕⠀⠕⠗⠀⠞⠺⠕⠀⠶⠀⠑⠭⠏⠻⠊⠰⠑⠎⠀⠷⠀⠍⠽
⠪⠝⠂⠀⠮⠀⠗⠑⠌⠀⠘⠹⠀⠷⠀⠃⠕⠽⠎⠀⠱⠕⠀⠶⠀⠎⠡⠕⠕⠇⠍⠁⠞⠑⠎⠀⠷
⠍⠔⠑⠲⠀⠠⠓⠥⠉⠅⠀⠠⠋⠔⠝⠀⠊⠎⠀⠙⠗⠁⠺⠝⠀⠋⠀⠇⠊⠋⠑⠆⠀⠠⠞⠕⠍
⠠⠎⠁⠺⠽⠻⠀⠁⠇⠂⠀⠃⠀⠝⠀⠋⠀⠁⠝⠀⠔⠙⠊⠧⠊⠙⠥⠁⠇⠤⠤⠓⠑⠀⠊⠎⠀⠁
⠤⠃⠔⠁⠤⠀⠞⠊⠕⠝⠀⠷⠮⠀⠐⠡⠊⠌⠊⠉⠎⠀⠷⠀⠹⠗⠑⠑⠀⠃⠕⠽⠎⠀⠱⠕⠍⠀⠠⠊
⠅⠝⠑⠺⠂⠀⠯⠀⠐⠮⠿⠑⠀⠆⠇⠰⠛⠎⠀⠖⠮⠀⠤⠏⠕⠎⠊⠞⠑⠀⠕⠗⠙⠻⠀⠷⠀⠀⠀
⠜⠡⠊⠤⠀⠞⠑⠉⠞⠥⠗⠑⠲⠀⠀
⠀⠀⠠⠮⠀⠕⠙⠙⠀⠎⠥⠏⠻⠌⠊⠰⠝⠎⠀⠞⠳⠡⠫⠀⠘⠥⠀⠶⠀⠁⠇⠇⠀⠏⠗⠑⠧⠁⠤
⠇⠢⠞⠀⠁⠍⠰⠛⠀⠡⠝⠀⠯⠀⠎⠇⠁⠧⠑⠎⠀⠔⠀⠮⠀⠠⠺⠑⠌⠀⠁⠞⠀⠮⠀⠏⠻⠊⠕⠙
⠷⠀⠹⠀⠌⠕⠗⠽⠤⠤⠞⠀⠊⠎⠀⠖⠎⠁⠽⠂⠀⠹⠊⠗⠞⠽⠀⠕⠗⠀⠿⠞⠽⠀⠽⠑⠜⠎
⠁⠛⠕⠲⠀⠀⠀
⠀⠀⠠⠁⠇⠹⠀⠍⠽⠀⠃⠕⠕⠅⠀⠊⠎⠀⠔⠞⠢⠙⠫⠀⠍⠁⠔⠇⠽⠀⠿⠮⠀⠑⠝⠤
⠞⠻⠞⠁⠔⠰⠞⠀⠷⠀⠃⠕⠽⠎⠀⠯⠀⠛⠊⠗⠇⠎⠂⠀⠠⠊⠀⠓⠕⠏⠑⠀⠭⠀⠺⠀⠝⠀⠆
⠩⠥⠝⠝⠫⠀⠴⠍⠢⠀⠯⠀⠺⠕⠍⠢⠀⠕⠝⠀⠞⠀⠁⠒⠨⠞⠂⠀⠿⠀⠐⠏⠀⠷⠀⠍⠽
⠏⠇⠁⠝⠀⠓⠁⠎⠀⠃⠑⠢⠀⠖⠞⠗⠽⠀⠖⠏⠇⠂⠎⠁⠝⠞⠇⠽⠀⠗⠑⠍⠔⠙⠀
⠁⠙⠥⠇⠞⠎⠀⠷⠀⠱⠁⠞⠀⠮⠽⠀⠕⠝⠉⠑⠀⠶⠀⠮⠍⠧⠎⠂⠀⠯⠷⠀⠓⠪⠀⠮⠽
⠋⠑⠇⠞⠀⠯⠀⠹⠐⠳⠀⠯⠀⠞⠁⠇⠅⠫⠂⠀⠯⠀⠱⠁⠞⠀⠟⠥⠑⠻⠀⠢⠞⠻⠏⠗⠊⠎⠑⠎
⠮⠽⠀⠐⠎⠐⠞⠎⠀⠢⠛⠁⠛⠫⠀⠊⠝⠲⠀⠀⠀⠀
⠀⠀⠠⠠⠮⠀⠠⠠⠁⠥⠹⠕⠗⠲⠀⠀
⠀⠀⠠⠠⠓⠜⠞⠿⠙⠂⠀⠼⠁⠓⠛⠋⠲⠀
⠀⠀⠰⠠⠞⠀⠠⠕⠀⠰⠠⠍⠀⠰⠠⠎⠀⠠⠁⠀⠰⠠⠺⠀⠰⠠⠽⠀⠰⠠⠑⠀⠰⠠⠗⠀⠀⠀⠀
⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠼⠃
"#;

    #[test]
    fn test_to_unicode_braille() {
        let ascii = AsciiString::from_ascii(
            " A1B'K2L@CIF/MSP\"E3H9O6R^DJG>NTQ,*5<-U8V.%[$+X!&;:4\\0Z7(_?W]#Y)=",
        )
        .unwrap();
        let val = BrailleAsciiString::from_ascii(ascii);
        let expected = "⠀⠁⠂⠃⠄⠅⠆⠇⠈⠉⠊⠋⠌⠍⠎⠏⠐⠑⠒⠓⠔⠕⠖⠗⠘⠙⠚⠛⠜⠝⠞⠟⠠⠡⠢⠣⠤⠥⠦⠧⠨⠩⠪⠫⠬⠭⠮⠯⠰⠱⠲⠳⠴⠵⠶⠷⠸⠹⠺⠻⠼⠽⠾⠿";
        assert_eq!(val.to_unicode_braille(), expected);

        let ascii = AsciiString::from_ascii(TOM_SAWYER_ASCII).unwrap();
        let tom_sawyer = BrailleAsciiString::from_ascii(ascii);

        assert_eq!(tom_sawyer.to_unicode_braille(), TOM_SAWYER_BRAILLE);
    }

    #[test]
    fn test_from_unicode_braille() {
        let val = BrailleAsciiString::from_unicode_braille(
            "⠀⠁⠂⠃⠄⠅⠆⠇⠈⠉⠊⠋⠌⠍⠎⠏⠐⠑⠒⠓⠔⠕⠖⠗⠘⠙⠚⠛⠜⠝⠞⠟⠠⠡⠢⠣⠤⠥⠦⠧⠨⠩⠪⠫⠬⠭⠮⠯⠰⠱⠲⠳⠴⠵⠶⠷⠸⠹⠺⠻⠼⠽⠾⠿",
        )
        .unwrap();
        let expected = " A1B'K2L@CIF/MSP\"E3H9O6R^DJG>NTQ,*5<-U8V.%[$+X!&;:4\\0Z7(_?W]#Y)=";
        assert_eq!(val.as_ascii().as_str(), expected);

        let val = BrailleAsciiString::from_unicode_braille(TOM_SAWYER_BRAILLE).unwrap();
        assert_eq!(val.as_ascii().as_str(), TOM_SAWYER_ASCII);
    }
}
