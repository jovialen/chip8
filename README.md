# Chip8 Emulator

An implementation of the [Chip8](https://en.wikipedia.org/wiki/CHIP-8) interpreter by Joseph Weisbecker in Rust.

<p align="center">
  <img width="600"
       alt="Example Window"
       src="./extra/example_window.png">
</p>

## Use

To use this project, [the Rust programming language](https://www.rust-lang.org/) must be downloaded and installed on your system.

Either download or clone the repository to your local machine, and then build and run it with [cargo](https://doc.rust-lang.org/cargo/index.html).

```console
foo@bar:~$ ./chip8-emu [OPTIONS] <ROM>
```

To see all available options, use the help flag.

```console
foo@bar:~$ ./chip8-emu --help
```

## ROMs

This project only contains the emulator, and not any ROMs to run on it. Many interesting Chip8 ROMs can be found [here](https://github.com/kripod/chip8-roms).

## Keypad mapping

**On the original Chip8**

|     |     |     |     |
| --- | --- | --- | --- |
| 1   | 2   | 3   | C   |
| 4   | 5   | 6   | D   |
| 7   | 8   | 9   | E   |
| A   | 0   | B   | F   |

**On keyboard**

|     |     |     |     |
| --- | --- | --- | --- |
| 1   | 2   | 3   | 4   |
| Q   | W   | E   | R   |
| A   | S   | D   | F   |
| Z   | X   | C   | V   |
