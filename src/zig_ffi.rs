//! Minimal C ABI used by the Zig port's test harness.
//!
//! This module is intentionally small and only exists to let the Zig code reuse this crate's
//! existing parsing/encoding behavior while the Zig implementation is developed.

use crate::result::IonFailure;
use crate::{v1_0, Element, ElementWriter, Format, IonData, IonError, IonResult, SExp, TextFormat, Value, Writer};
use std::cell::RefCell;

thread_local! {
    static LAST_ERROR: RefCell<String> = RefCell::new(String::new());
}

fn clear_error() {
    LAST_ERROR.with(|cell| cell.borrow_mut().clear());
}

fn set_error(message: impl std::fmt::Display) {
    LAST_ERROR.with(|cell| {
        *cell.borrow_mut() = message.to_string();
    });
}

fn with_bytes<'a>(data: *const u8, len: usize) -> IonResult<&'a [u8]> {
    if data.is_null() && len != 0 {
        return Err(IonError::illegal_operation(
            "received null pointer with non-zero length",
        ));
    }
    // SAFETY: caller promises the pointer/length describes readable memory for the duration
    // of this call.
    Ok(unsafe { std::slice::from_raw_parts(data, len) })
}

#[no_mangle]
pub extern "C" fn ionrs_clear_error() {
    clear_error();
}

#[no_mangle]
pub extern "C" fn ionrs_last_error_ptr() -> *const u8 {
    LAST_ERROR.with(|cell| cell.borrow().as_bytes().as_ptr())
}

#[no_mangle]
pub extern "C" fn ionrs_last_error_len() -> usize {
    LAST_ERROR.with(|cell| cell.borrow().len())
}

fn format_from_int(code: u32) -> IonResult<Format> {
    Ok(match code {
        0 => Format::Binary,
        1 => Format::Text(TextFormat::Compact),
        2 => Format::Text(TextFormat::Lines),
        3 => Format::Text(TextFormat::Pretty),
        _ => {
            return Err(IonError::illegal_operation(format!(
                "unknown format code: {code}"
            )))
        }
    })
}

fn serialize(format: Format, elements: &crate::Sequence) -> IonResult<Vec<u8>> {
    let mut buffer = Vec::with_capacity(2048);
    match format {
        Format::Text(kind) => {
            let mut writer = Writer::new(v1_0::Text.with_format(kind), buffer)?;
            writer.write_elements(elements)?;
            buffer = writer.close()?;
        }
        Format::Binary => {
            let mut writer = Writer::new(v1_0::Binary, buffer)?;
            writer.write_elements(elements)?;
            buffer = writer.close()?;
        }
    }
    Ok(buffer)
}

#[no_mangle]
pub extern "C" fn ionrs_parse_ok(data: *const u8, len: usize) -> bool {
    clear_error();
    let result = (|| -> IonResult<()> {
        let bytes = with_bytes(data, len)?;
        let _ = Element::read_all(bytes)?;
        Ok(())
    })();

    match result {
        Ok(()) => true,
        Err(e) => {
            set_error(e);
            false
        }
    }
}

#[no_mangle]
pub extern "C" fn ionrs_roundtrip_eq(data: *const u8, len: usize, format1: u32, format2: u32) -> bool {
    clear_error();
    let result = (|| -> IonResult<()> {
        let bytes = with_bytes(data, len)?;
        let source_elements = Element::read_all(bytes)?;

        let format1 = format_from_int(format1)?;
        let format2 = format_from_int(format2)?;

        let bytes1 = serialize(format1, &source_elements)?;
        let first_write = Element::read_all(&bytes1)?;

        let bytes2 = serialize(format2, &first_write)?;
        let second_write = Element::read_all(&bytes2)?;

        if !IonData::eq(&source_elements, &second_write) {
            return Err(IonError::illegal_operation(
                "IonData::eq failed after roundtrip",
            ));
        }
        Ok(())
    })();

    match result {
        Ok(()) => true,
        Err(e) => {
            set_error(e);
            false
        }
    }
}

fn read_embedded_doc_as_sequence(elem: &Element) -> IonResult<crate::Sequence> {
    match elem.value() {
        Value::String(text) => Element::read_all(text.text().as_bytes()),
        Value::Blob(bytes) => Element::read_all(bytes.as_ref()),
        _ => Err(IonError::illegal_operation(
            "expected embedded document to be an Ion String or Ion Blob",
        )),
    }
}

fn check_group_equivs(bytes: &[u8], expect_equivs: bool) -> IonResult<()> {
    let group_lists = Element::read_all(bytes)?;

    for group_container in group_lists.iter() {
        let is_embedded = group_container.annotations().contains("embedded_documents");
        match group_container.value() {
            Value::List(group) | Value::SExp(group) => {
                let group = if is_embedded {
                    group
                        .iter()
                        .map(read_embedded_doc_as_sequence)
                        .collect::<IonResult<Vec<_>>>()?
                        .into_iter()
                        .map(|seq| Element::from(SExp::from(seq)))
                        .collect::<Vec<_>>()
                        .into()
                } else {
                    group.to_owned()
                };

                for (this_index, this) in group.elements().enumerate() {
                    for (that_index, that) in group.elements().enumerate() {
                        let eq = IonData::eq(this, that);
                        if this_index == that_index {
                            if !eq {
                                return Err(IonError::illegal_operation(
                                    "identity comparison was not IonEq",
                                ));
                            }
                            continue;
                        }
                        if expect_equivs && !eq {
                            return Err(IonError::illegal_operation(
                                "expected values to be IonEq but they were not",
                            ));
                        }
                        if !expect_equivs && eq {
                            return Err(IonError::illegal_operation(
                                "expected values to NOT be IonEq but they were",
                            ));
                        }
                    }
                }
            }
            Value::Struct(group) => {
                let mut fields: Vec<Element> = Vec::new();
                for (_fname, value) in group.fields() {
                    let value = if is_embedded {
                        let seq = read_embedded_doc_as_sequence(value)?;
                        Element::from(SExp::from(seq))
                    } else {
                        value.to_owned()
                    };
                    fields.push(value);
                }

                for (this_index, this) in fields.iter().enumerate() {
                    for (that_index, that) in fields.iter().enumerate() {
                        let eq = IonData::eq(this, that);
                        if this_index == that_index {
                            if !eq {
                                return Err(IonError::illegal_operation(
                                    "identity comparison was not IonEq",
                                ));
                            }
                            continue;
                        }
                        if expect_equivs && !eq {
                            return Err(IonError::illegal_operation(
                                "expected struct field values to be IonEq but they were not",
                            ));
                        }
                        if !expect_equivs && eq {
                            return Err(IonError::illegal_operation(
                                "expected struct field values to NOT be IonEq but they were",
                            ));
                        }
                    }
                }
            }
            _ => {
                return Err(IonError::illegal_operation(
                    "expected a sequence or struct for group container",
                ))
            }
        }
    }

    Ok(())
}

#[no_mangle]
pub extern "C" fn ionrs_check_equivs(data: *const u8, len: usize) -> bool {
    clear_error();
    let result = (|| -> IonResult<()> {
        let bytes = with_bytes(data, len)?;
        check_group_equivs(bytes, true)
    })();
    match result {
        Ok(()) => true,
        Err(e) => {
            set_error(e);
            false
        }
    }
}

#[no_mangle]
pub extern "C" fn ionrs_check_non_equivs(data: *const u8, len: usize) -> bool {
    clear_error();
    let result = (|| -> IonResult<()> {
        let bytes = with_bytes(data, len)?;
        check_group_equivs(bytes, false)
    })();
    match result {
        Ok(()) => true,
        Err(e) => {
            set_error(e);
            false
        }
    }
}
