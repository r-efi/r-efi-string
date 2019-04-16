r-efi-string
============

UEFI String Types and Converters

The r-efi-string project implements string types according to the Unicode
strings described in the UEFI specification, as well as converters to/from
common rust types. The UEFI specification defines several different string
types. The most common one is UCS-2 based, but neither follows a strict UCS-2
nor UTF-16 standard. Furthermore, it defines a UTF-8 based string as well as an
ISO-8859-1 based string.

### Project

 * **Website**: <https://r-util.github.io/r-efi>
 * **Bug Tracker**: <https://github.com/r-util/r-efi-string/issues>

### Requirements

The requirements for this project are:

 * `rustc >= 1.36.0`

### Build

To build this project, run:

```sh
cargo build
```

### Repository:

 - **web**:   <https://github.com/r-util/r-efi-string>
 - **https**: `https://github.com/r-util/r-efi-string.git`
 - **ssh**:   `git@github.com:r-util/r-efi-string.git`

### License:

 - **Apache-2.0** OR **LGPL-2.1-or-later**
 - See AUTHORS file for details.
