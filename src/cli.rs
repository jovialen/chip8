use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Clockspeed to run the emulator at in hertz.
    #[arg(short = 'H', long, default_value_t = 60)]
    pub hz: u32,

    /// Path to the ROM file with the program to run.
    pub rom: std::path::PathBuf,
}
