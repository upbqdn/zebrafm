//! CompactSize64 encoder/decoder, mirroring
//! `zebra-chain/src/serialization/compact_size.rs`.
//!
//! The Rust source uses `byteorder` + `io::Read`/`io::Write`; Aeneas cannot
//! ingest those, so this crate replaces the I/O boundary with `&[u8]` and
//! `Vec<u8>` directly. The semantic content of the encoding is preserved.

/// The four bands of the CompactSize64 encoding.
pub const MAX_PROTOCOL_MESSAGE_LEN: u32 = 2 * 1024 * 1024;

/// `CompactSize64::zcash_serialize`: writes the canonical bytes for `n`.
pub fn encode(n: u64) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    if n <= 0xfc {
        out.push(n as u8);
    } else if n <= 0xffff {
        out.push(0xfd);
        out.push((n & 0xff) as u8);
        out.push(((n >> 8) & 0xff) as u8);
    } else if n <= 0xffff_ffff {
        out.push(0xfe);
        out.push((n & 0xff) as u8);
        out.push(((n >> 8) & 0xff) as u8);
        out.push(((n >> 16) & 0xff) as u8);
        out.push(((n >> 24) & 0xff) as u8);
    } else {
        out.push(0xff);
        out.push((n & 0xff) as u8);
        out.push(((n >> 8) & 0xff) as u8);
        out.push(((n >> 16) & 0xff) as u8);
        out.push(((n >> 24) & 0xff) as u8);
        out.push(((n >> 32) & 0xff) as u8);
        out.push(((n >> 40) & 0xff) as u8);
        out.push(((n >> 48) & 0xff) as u8);
        out.push(((n >> 56) & 0xff) as u8);
    }
    out
}

/// Two-byte little-endian decode.
pub fn from_le2(b0: u8, b1: u8) -> u16 {
    (b0 as u16) | ((b1 as u16) << 8)
}

/// Four-byte little-endian decode.
pub fn from_le4(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    (b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24)
}

/// Eight-byte little-endian decode.
pub fn from_le8(
    b0: u8, b1: u8, b2: u8, b3: u8,
    b4: u8, b5: u8, b6: u8, b7: u8,
) -> u64 {
    (b0 as u64) | ((b1 as u64) << 8) | ((b2 as u64) << 16) | ((b3 as u64) << 24)
        | ((b4 as u64) << 32) | ((b5 as u64) << 40) | ((b6 as u64) << 48) | ((b7 as u64) << 56)
}

/// `CompactSize64::zcash_deserialize`: reads from a `&[u8]`, returns the
/// decoded value and the remaining bytes, or `None` for malformed /
/// non-canonical input.
pub fn decode(bytes: &[u8]) -> Option<(u64, Vec<u8>)> {
    if bytes.is_empty() {
        return None;
    }
    let b = bytes[0];
    if b <= 0xfc {
        Some((b as u64, bytes[1..].to_vec()))
    } else if b == 0xfd {
        if bytes.len() < 3 {
            return None;
        }
        let n = from_le2(bytes[1], bytes[2]);
        if (n as u64) >= 0xfd {
            Some((n as u64, bytes[3..].to_vec()))
        } else {
            None
        }
    } else if b == 0xfe {
        if bytes.len() < 5 {
            return None;
        }
        let n = from_le4(bytes[1], bytes[2], bytes[3], bytes[4]);
        if (n as u64) >= 0x10000 {
            Some((n as u64, bytes[5..].to_vec()))
        } else {
            None
        }
    } else {
        if bytes.len() < 9 {
            return None;
        }
        let n = from_le8(
            bytes[1], bytes[2], bytes[3], bytes[4],
            bytes[5], bytes[6], bytes[7], bytes[8],
        );
        if n >= 0x100000000 {
            Some((n, bytes[9..].to_vec()))
        } else {
            None
        }
    }
}

/// `CompactSizeMessage::try_from<usize>` with the `MAX_PROTOCOL_MESSAGE_LEN` cap.
pub fn message_try_from(n: u32) -> Option<u32> {
    if n <= MAX_PROTOCOL_MESSAGE_LEN {
        Some(n)
    } else {
        None
    }
}
