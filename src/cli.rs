use clap::Parser;
use hex_color::HexColor;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Clockspeed to run the emulator at in hertz.
    #[arg(short = 'H', long, default_value_t = 60)]
    pub hz: u32,

    /// Foreground color hex code
    #[arg(short = 'f', long = "foreground", default_value_t = HexColor::WHITE)]
    pub foreground_color: HexColor,

    /// Background color hex code
    #[arg(short = 'b', long = "background", default_value_t = HexColor::BLACK)]
    pub background_color: HexColor,

    /// Path to the ROM file with the program to run.
    #[arg(short = 'r', long = "rom")]
    pub rom: Option<std::path::PathBuf>,
}
