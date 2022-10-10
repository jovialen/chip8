#[derive(Debug)]
pub struct Rom {
    data: Vec<u8>,
}

impl<'a> From<&'a std::path::Path> for Rom {
    fn from(path: &'a std::path::Path) -> Self {
        let data = std::fs::read(path).expect("Failed to read ROM file");
        Rom { data }
    }
}
