mod chip;
mod cli;

use chip::Chip8;
use clap::Parser;

fn main() {
    let args = cli::Args::parse();

    let rom = std::fs::read(args.rom).expect("Failed to read ROM file");
    let mut chip = Chip8::new();
    chip.load(&rom);

    println!("{:#x?}", rom);
}
