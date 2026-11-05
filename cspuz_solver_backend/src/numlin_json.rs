//! Small JSON boundary for the C ABI, without adding dependencies to the native crate.
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
pub enum Json {
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<Json>),
    Object(BTreeMap<String, Json>),
}
impl Json {
    pub fn get(&self, key: &str) -> &Json {
        match self { Self::Object(v) => v.get(key).unwrap_or(&Self::Null), _ => &Self::Null }
    }
    pub fn number(&self, default: f64) -> f64 {
        match self { Self::Number(v) => *v, Self::String(v) => v.parse().ok().filter(|v: &f64| v.is_finite()).unwrap_or(default), _ => default }
    }
    pub fn boolean(&self, default: bool) -> bool {
        match self { Self::Bool(v) => *v, Self::Number(v) => *v != 0.0, Self::String(v) if v == "true" || v == "1" => true, Self::String(v) if v == "false" || v == "0" => false, _ => default }
    }
    pub fn string<'a>(&'a self, default: &'a str) -> &'a str {
        match self { Self::String(v) if !v.is_empty() => v, _ => default }
    }
    pub fn array(&self) -> Result<&[Json], String> {
        match self { Self::Array(v) => Ok(v), _ => Err("expected JSON array".into()) }
    }
}
pub fn quote(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c { '"' => out.push_str("\\\""), '\\' => out.push_str("\\\\"), '\n' => out.push_str("\\n"), '\r' => out.push_str("\\r"), '\t' => out.push_str("\\t"), c if c < ' ' => out.push_str(&format!("\\u{:04x}", c as u32)), c => out.push(c) }
    }
    out.push('"'); out
}
pub fn parse(s: &str) -> Result<Json, String> {
    struct Parser<'a> { s: &'a [u8], i: usize }
    impl Parser<'_> {
        fn ws(&mut self) { while self.i < self.s.len() && self.s[self.i].is_ascii_whitespace() { self.i += 1; } }
        fn take(&mut self, b: u8) -> bool { self.ws(); if self.s.get(self.i) == Some(&b) { self.i += 1; true } else { false } }
        fn hex(&mut self) -> Result<u16, String> {
            let bytes = self.s.get(self.i..self.i+4).ok_or("truncated unicode escape")?;
            let v = u16::from_str_radix(std::str::from_utf8(bytes).map_err(|_| "unicode escape")?, 16).map_err(|_| "unicode escape")?;
            self.i += 4; Ok(v)
        }
        fn string(&mut self) -> Result<String, String> {
            if !self.take(b'"') { return Err("expected string".into()); }
            let mut out = Vec::new();
            loop {
                let b = *self.s.get(self.i).ok_or("unterminated string")?; self.i += 1;
                match b {
                    b'"' => return String::from_utf8(out).map_err(|_| "invalid UTF-8".into()),
                    b'\\' => {
                        let b = *self.s.get(self.i).ok_or("truncated escape")?; self.i += 1;
                        match b {
                            b'"' | b'\\' | b'/' => out.push(b), b'n' => out.push(b'\n'), b'r' => out.push(b'\r'), b't' => out.push(b'\t'), b'b' => out.push(8), b'f' => out.push(12),
                            b'u' => {
                                let a = self.hex()?;
                                let code = if (0xd800..=0xdbff).contains(&a) {
                                    if self.s.get(self.i..self.i+2) != Some(b"\\u") { return Err("missing low surrogate".into()); }
                                    self.i += 2; let b = self.hex()?;
                                    if !(0xdc00..=0xdfff).contains(&b) { return Err("invalid surrogate".into()); }
                                    0x10000 + ((a as u32 - 0xd800) << 10) + b as u32 - 0xdc00
                                } else { a as u32 };
                                let c = char::from_u32(code).ok_or("invalid unicode")?;
                                let mut buf = [0; 4]; out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
                            }
                            _ => return Err("invalid escape".into()),
                        }
                    }
                    0..=31 => return Err("control character in string".into()),
                    _ => out.push(b),
                }
            }
        }
        fn value(&mut self, depth: usize) -> Result<Json, String> {
            if depth > 64 { return Err("JSON nesting too deep".into()); }
            self.ws();
            match self.s.get(self.i).copied() {
                Some(b'"') => Ok(Json::String(self.string()?)),
                Some(b'{') => {
                    self.i += 1; let mut out = BTreeMap::new();
                    if self.take(b'}') { return Ok(Json::Object(out)); }
                    loop { let k = self.string()?; if !self.take(b':') { return Err("expected colon".into()); } out.insert(k, self.value(depth+1)?); if self.take(b'}') { break; } if !self.take(b',') { return Err("expected comma".into()); } }
                    Ok(Json::Object(out))
                }
                Some(b'[') => {
                    self.i += 1; let mut out = Vec::new();
                    if self.take(b']') { return Ok(Json::Array(out)); }
                    loop { out.push(self.value(depth+1)?); if self.take(b']') { break; } if !self.take(b',') { return Err("expected comma".into()); } }
                    Ok(Json::Array(out))
                }
                Some(b'n') | Some(b't') | Some(b'f') => {
                    for (word, value) in [("null", Json::Null), ("true", Json::Bool(true)), ("false", Json::Bool(false))] {
                        if self.s[self.i..].starts_with(word.as_bytes()) { self.i += word.len(); return Ok(value); }
                    }
                    Err("invalid literal".into())
                }
                Some(b'-' | b'0'..=b'9') => {
                    let start = self.i;
                    while self.s.get(self.i).map(|b| b.is_ascii_digit() || b"-+.eE".contains(b)).unwrap_or(false) { self.i += 1; }
                    let n = std::str::from_utf8(&self.s[start..self.i]).unwrap().parse::<f64>().map_err(|_| "invalid number")?;
                    if !n.is_finite() { return Err("non-finite number".into()); }
                    Ok(Json::Number(n))
                }
                _ => Err("expected JSON value".into()),
            }
        }
    }
    let mut p = Parser { s: s.as_bytes(), i: 0 };
    let v = p.value(0)?; p.ws();
    if p.i != p.s.len() { return Err("trailing JSON data".into()); }
    Ok(v)
}
