//! UEFI Char16 based String Types and Converters
//!
//! This module implements two basic types `[&EfiStr16]` and `[EfiString16]`, which relate to each
//! other just as `[&str]` relates to `[String]`. Unlike the strings in the rust standard library,
//! these types implement UCS-2'ish strings, as used in UEFI systems.
//!
//! While the UEFI Specification clearly states that `Efi::Char16` based strings must be UCS-2,
//! firmware is known to violate this. In fact, any 0-terminated `u16` array might be exposed in
//! such strings. Therefore, the `EfiStr16` type implements a string based on any `u16` array, and
//! provides converters to and from the standard rust types.

/// An error indicating wrongly placed Nuls.
///
/// This error is used to indicate that a source slice had invalidly placed Nul entries, lacked a
/// terminating Nul, etc.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum FromSliceWithNulError {
    /// Indicates that there was an interior Nul entry in the slice.
    ///
    /// Only terminating Nul entries are allowed. This error indicates there was a Nul entry which
    /// was not the string terminator. The embedded value encodes the position in the original
    /// source array where this interior Nul entry was found.
    InteriorNul(usize),

    /// Indicates that the source slice was not Nul terminated.
    ///
    /// All source slices must be Nul terminated. This error indicates that a conversion was tried
    /// on a slice that was not Nul terminated.
    NotNulTerminated,
}

/// String slice based on UCS-2 strings as defined by UEFI.
///
/// The EfiStr16 is similar to `[CStr]` or `[OsStr]` in the rust standard library, but it
/// implements a string type similar to UCS-2, as defined by the UEFI specification. The type does
/// neither match UTF-16 nor UCS-2, but is something of a mixture of both. While the UEFI
/// specification clearly states UCS-2 is used, this is not what happens to be used in practice.
///
/// The `EfiStr16` type considers any array of `u16` as a valid string, as long as it is
/// terminated by a 0 entry, and it does not contain any other 0 entry. The individual entries
/// must be encoded as native-endian 16-bit unsigned integers.
#[derive(Eq, Ord, PartialEq, PartialOrd)]
pub struct EfiStr16 {
    inner: [u16],
}

/// A type representing an owned, C-compatible, UEFI-compatible, Nul-terminated string with no
/// interior Nul-bytes.
///
/// The `EfiString16` type is to `&EfiStr16` what `[String]` is to `[&str]`. That is, it
/// represents a string that owns its content, rather than borrowing it.
///
/// The `EfiString16` type can represent exactly the same values as `EfiStr16`.
#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct EfiString16 {
    inner: alloc::boxed::Box<[u16]>,
}

impl EfiStr16 {
    /// Create Str16 from pointer to u16.
    ///
    /// This takes a pointer to a `Char16` string as defined by the UEFI specification. It is a
    /// C-string based on 16-bit integers and terminated by a 16-bit 0 entry.
    ///
    /// This function turns this C-string into a slice of `[EfiStr16]`. The returned slice does
    /// not own the backing memory, but points to the original C-string.
    ///
    /// # Safety
    ///
    /// This function is unsafe for several reasons:
    ///
    ///  * The caller must guarantee the backing memory of the C-string outlives the livetime
    ///    `'a`.
    ///  * The memory pointer to by `ptr` must be a valid, zero-terminated C-string based on
    ///    16-bit integers.
    ///
    /// The caller must guarantee that the pointer points to a nul-terminated
    /// native-endian UTF-16 string. The string should either originate in
    /// UEFI, or be restricted to the subset of UTF-16 that the UEFI spec
    /// allows.
    pub unsafe fn from_ptr<'a>(ptr: *const u16) -> &'a EfiStr16 {
        let mut len: isize = 0;

        while ptr.offset(len).read() != 0 {
            len += 1;
        }

        Self::from_slice_with_nul_unchecked(
            core::slice::from_raw_parts(ptr, len as usize + 1)
        )
    }

    /// Create Str16 from a slice of u16.
    ///
    /// This turns a slice of `u16` into a `Str16`. The original slice is borrowed by the newly
    /// returned `Str16`. The input is not verified for validity. It is the caller's
    /// responsibility to adhere to the safety guarantees.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the caller has to guarantee that the passed slice contains
    /// a 0 terminator as its last entry. Furthermore, it must not contain any other 0 entry.
    pub unsafe fn from_slice_with_nul_unchecked<'a>(slice: &[u16]) -> &EfiStr16 {
        &*(slice as *const [u16] as *const EfiStr16)
    }

    /// Create Str16 from a slice of u16.
    ///
    /// This turns a slice of `u16` into a `Str16`. The original slice is borrowed by the newly
    /// returned `Str16`. The input is verified to be a 0-terminated slice, with no other 0
    /// characters embedded in the string.
    pub fn from_slice_with_nul<'a>(slice: &[u16]) -> Result<&EfiStr16, FromSliceWithNulError> {
        let n = slice.len();

        for i in 0..n {
            if slice[i] == 0 {
                if i + 1 == n {
                    return unsafe { Ok(Self::from_slice_with_nul_unchecked(slice)) };
                } else {
                    return Err(FromSliceWithNulError::InteriorNul(i));
                }
            }
        }

        Err(FromSliceWithNulError::NotNulTerminated)
    }

    /// Convert string slice to a raw pointer.
    ///
    /// This converts the string slice to a raw pointer. The pointer references the memory inside
    /// of `self`. Therefore, the pointer becomes stale as soon as `self` goes out of scope.
    pub fn as_ptr(&self) -> *const u16 {
        self.inner.as_ptr()
    }

    /// Convert string slice to a u16 slice including the terminating 0 character.
    ///
    /// This returns a slice of `u16`, which borrows the backing memory of the input string. The
    /// slice includes the terminating 0 character.
    pub fn as_slice_with_nul(&self) -> &[u16] {
        &self.inner
    }

    /// Convert string slice to a u16 slice excluding the terminating 0 character.
    ///
    /// This returns a slice of `u16`, which borrows the backing memory of the input string. The
    /// slice does not includes the terminating 0 character.
    pub fn as_slice(&self) -> &[u16] {
        let s = self.as_slice_with_nul();
        &s[..s.len() - 1]
    }

    /// Converts an `EfiStr16` into a `[String]`.
    ///
    /// This converts the input string into a standard rust string. This always requires a memory
    /// allocation since the backing data needs to be converted from 16-bit based UCS-2 to 8-bit
    /// based UTF-8.
    ///
    /// The `EfiStr16` type is a lot less strict on its encoding. Therefore, not all instances can
    /// be converted to valid UTF-8. If the input string is invalid, this function will raise an
    /// error. Use `to_string_lossy()` if you want the conversion to replace invalid characters.
    pub fn to_string(&self) -> Result<alloc::string::String, alloc::string::FromUtf16Error> {
        alloc::string::String::from_utf16(self.as_slice())
    }

    /// Converts an `EfiStr16` into a `[String]`, replacing invalid characters with the Unicode
    /// replacement character.
    ///
    /// This function works like `to_string()` but whenever invalid characters are found in the
    /// input string, they are replaced with the Unicode Replacement Character.
    pub fn to_string_lossy(&self) -> alloc::string::String {
        alloc::string::String::from_utf16_lossy(self.as_slice())
    }
}

// Default value for an EfiStr16 is the empty string with just a zero terminator.
impl Default for &EfiStr16 {
    fn default() -> Self {
        const DEFAULT: &[u16] = &[0];
        unsafe { EfiStr16::from_slice_with_nul_unchecked(DEFAULT) }
    }
}

// Quirk to make `Box<EfiStr16>` use the default of `&EfiStr16`.
impl Default for alloc::boxed::Box<EfiStr16> {
    fn default() -> Self {
        <&EfiStr16 as Default>::default().into()
    }
}

// Creating a box from an `&EfiStr16` simply allocates the backing array.
impl From<&EfiStr16> for alloc::boxed::Box<EfiStr16> {
    fn from(s: &EfiStr16) -> alloc::boxed::Box<EfiStr16> {
        let boxed: alloc::boxed::Box<[u16]> = alloc::boxed::Box::from(s.as_slice_with_nul());
        unsafe {
            alloc::boxed::Box::from_raw(
                alloc::boxed::Box::into_raw(boxed) as *mut EfiStr16
            )
        }
    }
}

// Quirk to make `Box<EfiStr16>` use `From<&EfiStr16>`.
impl Clone for alloc::boxed::Box<EfiStr16> {
    fn clone(&self) -> Self {
        (**self).into()
    }
}

// Print EfiStr16 in ASCII-compatible mode, escape anything else as '\u<hex>`.
impl core::fmt::Debug for EfiStr16 {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        fn hexify_4bit(v: u8) -> char {
            match v {
                0x0..=0x9 => (b'0' + v) as char,
                0xa..=0xf => (b'a' + (v - 0xa)) as char,
                _ => panic!{},
            }
        }

        fn hexify_16bit(v: u16) -> [char; 4] {
            [
                hexify_4bit(((v >> 12) & 0x000f) as u8),
                hexify_4bit(((v >>  8) & 0x000f) as u8),
                hexify_4bit(((v >>  4) & 0x000f) as u8),
                hexify_4bit(((v >>  0) & 0x000f) as u8),
            ]
        }

        write!(f, "\"")?;
        for entry in self.as_slice().iter() {
            match *entry {
                0x0000..=0x00ff => {
                    for c in core::ascii::escape_default(*entry as u8) {
                        core::fmt::Write::write_char(f, c as char)?;
                    }
                },
                _ => {
                    let a = hexify_16bit(*entry);

                    write!(f, "\\u")?;
                    core::fmt::Write::write_char(f, a[0])?;
                    core::fmt::Write::write_char(f, a[1])?;
                    core::fmt::Write::write_char(f, a[2])?;
                    core::fmt::Write::write_char(f, a[3])?;
                },
            }
        }
        write!(f, "\"")
    }
}

impl EfiString16 {
    // XXX: To be implemented.
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn efistr16_constructors() {
        let original: &[u16] = &[0x0041, 0x0042, 0x0043, 0x0044, 0x0045, 0x0046, 0];

        {
            let s = unsafe { EfiStr16::from_ptr(original.as_ptr()) };

            assert_eq!{s.as_ptr(), original.as_ptr()};
            assert_eq!{s.as_slice().len(), 6};
            assert_eq!{s.as_slice()[0], 0x41};
            assert_eq!{s.as_slice_with_nul(), original};
        }

        {
            let s = unsafe { EfiStr16::from_slice_with_nul_unchecked(original) };

            assert_eq!{s.as_ptr(), original.as_ptr()};
            assert_eq!{s.as_slice().len(), 6};
            assert_eq!{s.as_slice()[0], 0x41};
            assert_eq!{s.as_slice_with_nul(), original};
        }

        {
            let s = EfiStr16::from_slice_with_nul(original).unwrap();

            assert_eq!{s.as_ptr(), original.as_ptr()};
            assert_eq!{s.as_slice().len(), 6};
            assert_eq!{s.as_slice()[0], 0x41};
            assert_eq!{s.as_slice_with_nul(), original};
        }

        {
            assert_eq!{
                EfiStr16::from_slice_with_nul(
                    &[],
                ).err().unwrap(),
                FromSliceWithNulError::NotNulTerminated,
            };

            assert_eq!{
                EfiStr16::from_slice_with_nul(
                    &[0x0041],
                ).err().unwrap(),
                FromSliceWithNulError::NotNulTerminated,
            };

            assert!{
                EfiStr16::from_slice_with_nul(
                    &[0x0041, 0x0000],
                ).is_ok()
            };

            assert_eq!{
                EfiStr16::from_slice_with_nul(
                    &[0x0000, 0x0041, 0x0000],
                ).err().unwrap(),
                FromSliceWithNulError::InteriorNul(0),
            };

            assert_eq!{
                EfiStr16::from_slice_with_nul(
                    &[0x0041, 0x0000, 0x0000],
                ).err().unwrap(),
                FromSliceWithNulError::InteriorNul(1),
            };

            assert_eq!{
                EfiStr16::from_slice_with_nul(
                    &[0x0000, 0x0041, 0x0000, 0x0042, 0x0000],
                ).err().unwrap(),
                FromSliceWithNulError::InteriorNul(0),
            };
        }

        {
            let s: &EfiStr16 = Default::default();

            assert_eq!{s.as_slice_with_nul(), &[0]};
        }
    }

    #[test]
    fn efistr16_compare() {
        let slice: &[u16] = &[
            0x0041, 0x0042, 0x0043, 0x0044, 0x0045, 0x0046, 0,
            0x0041, 0x0042, 0x0043, 0x0044, 0x0045, 0x0046, 0,
        ];
        let string1 = unsafe { EfiStr16::from_slice_with_nul_unchecked(&slice[0..7]) };
        let string2 = unsafe { EfiStr16::from_slice_with_nul_unchecked(&slice[7..14]) };

        assert_eq!{string1, string2};
        assert_eq!{string1.cmp(string2), core::cmp::Ordering::Equal};
    }

    #[test]
    fn efistr16_converters() {
        let slice_good: &[u16] = &[0x0041, 0x0042, 0x0043, 0x0044, 0x0045, 0x0046, 0];
        let slice_bad: &[u16] = &[0x0041, 0x0042, 0x0043, 0x0044, 0x0045, 0xd800, 0];
        let string_good: &EfiStr16 = unsafe { EfiStr16::from_slice_with_nul_unchecked(slice_good) };
        let string_bad: &EfiStr16 = unsafe { EfiStr16::from_slice_with_nul_unchecked(slice_bad) };

        assert_eq!{string_good.to_string().unwrap(), "ABCDEF"};
        assert!{string_bad.to_string().is_err()};

        assert_eq!{string_good.to_string_lossy(), "ABCDEF"};
        assert_eq!{string_bad.to_string_lossy(), "ABCDE�"};
    }

    #[test]
    fn efistr16_debug() {
        let slice: &[u16] = &[
            0x0041, 0x0042, 0x0043, 0x0044, 0x0045, 0x0046,
            0x0001, 0x000a, 0xabcd,
            0,
        ];
        let string = unsafe { EfiStr16::from_slice_with_nul_unchecked(slice) };

        assert_eq!{
            format!{"{:?}", string},
            "\"ABCDEF\\x01\\n\\uabcd\"",
        };
    }

    #[test]
    fn efistr16_box() {
        let slice: &[u16] = &[0x0041, 0x0042, 0x0043, 0x0044, 0x0045, 0x0046, 0];
        let string = unsafe { EfiStr16::from_slice_with_nul_unchecked(slice) };
        let boxed: alloc::boxed::Box<EfiStr16> = alloc::boxed::Box::from(string);

        assert_eq!{string.as_slice_with_nul(), slice};
        assert_eq!{boxed.as_slice_with_nul(), slice};
        assert_eq!{boxed.clone().as_slice_with_nul(), slice};
        assert_eq!{
            <alloc::boxed::Box<EfiStr16> as Default>::default().as_slice_with_nul(),
            <&EfiStr16 as Default>::default().as_slice_with_nul(),
        };
    }
}
