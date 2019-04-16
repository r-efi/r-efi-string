# r-efi-string - UEFI String Types and Converters

## CHANGES WITH 0.1.0:

        * Initial release of r-efi-string.

        * New `str16::EfiStr16` type, which is similar to `std::ffi::CStr` and
          wraps a 0-terminated UEFI string based on something resembling
          UTF-16.

        * The `str16::EfiString16` type is still only a stub and not included
          in this release.

        Contributions from: David Herrmann, Tom Gundersen

        - Tübingen, 2019-04-16
