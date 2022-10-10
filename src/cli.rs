use clap::Parser;

#[derive(Parser, Debug)]
pub struct Args {
    pub rom: std::path::PathBuf,
}
