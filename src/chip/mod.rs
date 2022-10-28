mod instruction;
mod time;

use hex_color::HexColor;
use instruction::Instruction;
use log::{info, warn};
use time::Timer;

/// The total size of emulator the CPU RAM.
pub const RAM_SIZE: usize = 0x1000;
/// Memory location in RAM for the start of the font data.
pub const RAM_FONT_SPACE_START: usize = 0x0;
/// Memory location in RAM for the start of ROM programs.
pub const RAM_PROGRAM_SPACE_START: usize = 0x200;
/// Width (in pixels) of the emulator display.
pub const DISPLAY_WIDTH: usize = 64;
/// Height (in pixels) of the emulator display.
pub const DISPLAY_HEIGHT: usize = 32;
/// Size (in pixels) of the entire emulator display.
pub const DISPLAY_SIZE: usize = DISPLAY_WIDTH * DISPLAY_HEIGHT;

/// The index of the CPU flag register.
const FLAG_REGISTER: usize = 0xF;

/// Raw data for 4x5 font atlas.
#[rustfmt::skip]
const FONT_ATLAS: [u8; 5 * 16] = [
    0xF0, 0x90, 0x90, 0x90, 0xF0, // 0
    0x20, 0x60, 0x20, 0x20, 0x70, // 1
    0xF0, 0x10, 0xF0, 0x80, 0xF0, // 2
    0xF0, 0x10, 0xF0, 0x10, 0xF0, // 3
    0x90, 0x90, 0xF0, 0x10, 0x10, // 4
    0xF0, 0x80, 0xF0, 0x10, 0xF0, // 5
    0xF0, 0x80, 0xF0, 0x90, 0xF0, // 6
    0xF0, 0x10, 0x20, 0x40, 0x40, // 7
    0xF0, 0x90, 0xF0, 0x90, 0xF0, // 8
    0xF0, 0x90, 0xF0, 0x10, 0xF0, // 9
    0xF0, 0x90, 0xF0, 0x90, 0x90, // A
    0xE0, 0x90, 0xE0, 0x90, 0xE0, // B
    0xF0, 0x80, 0x80, 0x80, 0xF0, // C
    0xE0, 0x90, 0x90, 0x90, 0xE0, // D
    0xF0, 0x80, 0xF0, 0x80, 0xF0, // E
    0xF0, 0x80, 0xF0, 0x80, 0x80, // F
];

/// Single instance of the Chip8 emulator.
pub struct Chip8 {
    // Cpu
    /// CPU RAM.
    ///
    /// The CPU has a RAM memory with a size set by [`RAM_SIZE`], where the
    /// first bytes up to [`RAM_PROGRAM_SPACE_START`] are reserved for the
    /// interpreter, loaded programs start at [`RAM_PROGRAM_SPACE_START`], and
    /// the rest of the memory is available to the programs running.
    ram: [u8; RAM_SIZE],
    /// CPU registers.
    ///
    /// 16 8-bit registers, all available for read-write access, but the
    /// [`FLAG_REGISTER`] is used by various instructions.
    registers: [u8; 16],
    /// Index pointer register.
    ///
    /// Points to a point in RAM memory.
    index: usize,
    /// Program counter.
    ///
    /// Points to the point in RAM memory where the current program instruction
    /// is stored.
    pc: usize,
    /// Callstack.
    ///
    /// The stack stores the return addresses ([`Chip8::pc`]) of subroutine
    /// calls.
    ///
    /// On the original Chip8, the stack had a max size of 16 entries, but here
    /// a vector is used allowing for programs to have an (near) unlimited
    /// allowed depth in function calls.
    stack: Vec<usize>,
    /// Program timer.
    ///
    /// A general timer that does nothing but count down at 60HZ until it
    /// reaches 0.
    program_timer: Timer,
    /// Sound timer.
    ///
    /// Similar to the [`Chip8::program_timer`], however whenever the sound
    /// timer is not 0, the Chip will produce a beeping sound.
    sound_timer: Timer,

    // Display
    /// Display VRAM.
    vram: [u8; DISPLAY_SIZE],
    /// Display draw flag.
    ///
    /// Set if the internal display has been updated since the last draw call.
    should_draw: bool,

    // Keyboard
    /// Keypad key states.
    ///
    /// Whether or not the keypad keys are pressed or not.
    keys: [bool; 16],
    /// The register, if any, currently waiting for a key on the keypad to be
    /// pressed.
    waiting_for_input: Option<usize>,
}

impl Chip8 {
    /// Create a new Chip8 instance.
    ///
    /// This will create an Chip8 without any loaded program.
    pub fn new() -> Self {
        let mut ram = [0; RAM_SIZE];

        // Copy font atlas into ram
        ram[RAM_FONT_SPACE_START..(RAM_FONT_SPACE_START + 80)].copy_from_slice(&FONT_ATLAS);

        Self {
            ram,
            registers: [0; 16],
            index: 0,
            pc: RAM_PROGRAM_SPACE_START,
            stack: Vec::with_capacity(16),
            program_timer: Timer::new(),
            sound_timer: Timer::new(),
            vram: [0; DISPLAY_SIZE],
            should_draw: false,
            keys: [false; 16],
            waiting_for_input: None,
        }
    }

    /// Load a program ROM into the CPU RAM.
    ///
    /// # Arguments
    ///
    /// * `program` - A vector containing the compiled source of a Chip8 ROM.
    pub fn load(&mut self, program: &Vec<u8>) {
        info!("Loading program into ROM (len: {})", program.len());
        for (i, v) in program.iter().enumerate() {
            self.ram[RAM_PROGRAM_SPACE_START + i] = *v;
        }
    }

    /// Perform a single CPU clock cycle.
    ///
    /// This function will quietly return if one of the CPU registers is
    /// currently waiting for a keypad keypress.
    ///
    /// Increments the program counter.
    pub fn cycle(&mut self) {
        if self.waiting_for_input.is_none() {
            let instruction = self.fetch_opcode();

            info!(
                "pc: {:<4x} opcode: {:<2x} {:<4x} instruction: {:x?}",
                self.pc,
                self.ram[self.pc],
                self.ram[self.pc + 1],
                instruction
            );

            self.next();
            self.interpret(instruction);
        }
    }

    /// If the display wants to redraw the framebuffer.
    ///
    /// This will be true if the internal display has been updated since the
    /// last draw call.
    pub fn should_draw(&self) -> bool {
        self.should_draw
    }

    /// If any registers is currently waiting for a keypad input.
    pub fn waiting_for_input(&self) -> bool {
        self.waiting_for_input.is_some()
    }

    /// Draw the current internal display to a framebuffer.
    ///
    /// # Arguments
    ///
    /// * `target` - The frame of a valid [`pixels::Pixels`] struct.
    /// * `foreground_color` - The color to use for enabled pixels.
    /// * `background_color` - The color to use for disabled pixels.
    ///
    /// # Examples
    ///
    /// ```
    /// let chip = Chip8::new();
    /// let pixels: Pixels = todo!();
    /// chip.draw(pixels.get_frame(), HexColor::WHITE, HexColor::BLACK);
    /// pixels.render().expect("Failed render.");
    /// ```
    pub fn draw(
        &mut self,
        target: &mut [u8],
        foreground_color: HexColor,
        background_color: HexColor,
    ) {
        for (i, pix) in target.chunks_exact_mut(4).enumerate() {
            let pixel = self.vram[i];

            let color = if pixel != 0x00 {
                let f = foreground_color;
                [f.r, f.g, f.b, f.a]
            } else {
                let b = background_color;
                [b.r, b.g, b.b, b.a]
            };
            pix.copy_from_slice(&color);
        }
        self.should_draw = false;
    }

    /// Set the state of one of the keypad keys.
    ///
    /// # Arguments
    ///
    /// * `key` - The hexcode keypad to set. 0x0 to 0xF.
    /// * `pressed` - If the key is pressed.
    pub fn set_key(&mut self, key: usize, pressed: bool) {
        if pressed && self.waiting_for_input.is_some() {
            self.registers[self.waiting_for_input.unwrap() as usize] = key as u8;
            self.waiting_for_input = None;
        }

        self.keys[key] = pressed;
    }

    /// Get the instruction from the opcode at the current location of the
    /// [program counter](`Chip8::pc`).
    ///
    /// Does not increment the program counter.
    fn fetch_opcode(&self) -> Instruction {
        let bytes = [self.ram[self.pc], self.ram[self.pc + 1]];
        Instruction::from_be_bytes(bytes)
    }

    /// Increment the [program counter](`Chip8::pc`) once.
    fn next(&mut self) {
        self.pc += 2;
    }

    /// Interpret an instruction on the CPU.
    ///
    /// Does not increment the program counter.
    fn interpret(&mut self, instruction: Instruction) {
        match instruction {
            Instruction::Clear => self.clear(),
            Instruction::ReturnSubroutine => self.ret(),
            Instruction::Jump(addr) => self.jmp(addr),
            Instruction::CallSubroutine(addr) => self.call_subroutine(addr),
            Instruction::SkipEqToConst { register, value } => self.skeq_vr_xx(register, value),
            Instruction::SkipNeToConst { register, value } => self.skne_vr_xx(register, value),
            Instruction::SkipEqToReg { x, y } => self.skeq_vr_vx(x, y),
            Instruction::MovConstToReg { dest, value } => self.mov_vr_xx(dest, value),
            Instruction::AddConstToReg { dest, value } => self.add_vr_xx(dest, value),
            Instruction::MovRegToReg { dest, src } => self.mov_vr_vx(dest, src),
            Instruction::Or { dest, other } => self.or_vr_vx(dest, other),
            Instruction::And { dest, other } => self.and_vr_vx(dest, other),
            Instruction::Xor { dest, other } => self.xor_vr_vx(dest, other),
            Instruction::AddRegToReg { dest, other } => self.add_vr_vx(dest, other),
            Instruction::SubRegFromReg { dest, other } => self.sub_vr_vx(dest, other),
            Instruction::ShiftRight { dest, src } => self.shr_vr(dest, src),
            Instruction::SubnRegFromReg { dest, other } => self.rsb_vr_vx(dest, other),
            Instruction::ShiftLeft { dest, src } => self.shl_vr(dest, src),
            Instruction::SkipNeToReg { x, y } => self.skne_vr_vx(x, y),
            Instruction::MovConstToI(addr) => self.mvi(addr),
            Instruction::JumpI(addr) => self.jmi(addr),
            #[cfg(feature = "bxnn")]
            Instruction::SuperJumpI { addr, x } => self.jmi_superchip(addr, x),
            Instruction::Rand { dest, mask } => self.rand(dest, mask),
            Instruction::Sprite { x, y, height } => self.sprite(x, y, height),
            Instruction::SkipIfPressed(key) => self.skpr(key),
            Instruction::SkipIfReleased(key) => self.skup(key),
            Instruction::GetDelay(dest) => self.gdelay_vr(dest),
            Instruction::WaitKey(dest) => self.key_vr(dest),
            Instruction::SetDelay(delay) => self.sdelay_vr(delay),
            Instruction::SetSoundDelay(delay) => self.ssound_vr(delay),
            Instruction::AddToI(register) => self.adi(register),
            Instruction::LoadFont(character) => self.font(character),
            Instruction::StoreBcd(src) => self.bcd_vr(src),
            Instruction::Store(to) => self.str_v0_vr(to),
            Instruction::Load(to) => self.ldr_v0_vr(to),
        }
    }

    /// Clears the display.
    ///
    /// Sets the [`Chip8::should_draw`] flag.
    fn clear(&mut self) {
        self.vram = [0; DISPLAY_SIZE];
        self.should_draw = true;
    }

    /// Return from the subroutine in the stack.
    ///
    /// Returns quietly if the [stack](`Chip8::stack`) is empty.
    fn ret(&mut self) {
        if let Some(pc) = self.stack.pop() {
            self.pc = pc;
        }
    }

    /// Jump to the given address.
    ///
    /// Does not add the current address to the [stack](`Chip8::stack`).
    ///
    /// # Arguments
    ///
    /// * `addr` - The address to jump the [program counter](`Chip8::pc`) to.
    fn jmp(&mut self, addr: usize) {
        self.pc = addr;
    }

    /// Start a subroutine at the given address.
    ///
    /// Jumps to the given address and adds the current [program
    /// counter](`Chip8::pc`) to the [stack](`Chip8::stack`).
    ///
    /// # Arguments
    ///
    /// * `addr` - The address to jump the [program counter](`Chip8::pc`) to.
    fn call_subroutine(&mut self, addr: usize) {
        self.stack.push(self.pc);
        self.jmp(addr);
    }

    /// Skip the next line if the register is equal to constant.
    ///
    /// # Arguments
    ///
    /// * `register` - The register to compare with the constant.
    /// * `value` - The constant to compare with the register.
    fn skeq_vr_xx(&mut self, register: usize, value: u8) {
        if self.registers[register] == value {
            self.next();
        }
    }

    /// Skip the next line if the register is not equal to constant.
    ///
    /// # Arguments
    ///
    /// * `register` - The register to compare with the constant.
    /// * `value` - The constant to compare with the register.
    fn skne_vr_xx(&mut self, register: usize, value: u8) {
        if self.registers[register] != value {
            self.next();
        }
    }

    /// Skip the next line if the value in register x is equal to register y.
    ///
    /// # Arguments
    ///
    /// * `rx` - The x register.
    /// * `ry` - The y register.
    fn skeq_vr_vx(&mut self, rx: usize, ry: usize) {
        if self.registers[rx] == self.registers[ry] {
            self.next();
        }
    }

    /// Set the register to the given constant.
    ///
    /// # Arguments
    ///
    /// * `dest` - The register to set.
    /// * `value` - The constant to set the register to.
    fn mov_vr_xx(&mut self, dest: usize, value: u8) {
        self.registers[dest] = value;
    }

    /// Add constant to register.
    ///
    /// Does not set the carry flag if the addition overflows.
    ///
    /// # Arguments
    ///
    /// * `dest` - The register to add the constant to.
    /// * `value` - The constant to add to the register.
    fn add_vr_xx(&mut self, dest: usize, value: u8) {
        let result = self.registers[dest] as u16 + value as u16;

        // Discard any overflow
        self.registers[dest] = result as u8;
    }

    /// Set the destination register to the value of the source register.
    ///
    /// # Arguments
    ///
    /// * `dest` - The register to set.
    /// * `src` - The register get the value from.
    fn mov_vr_vx(&mut self, dest: usize, src: usize) {
        self.registers[dest] = self.registers[src];
    }

    /// Bitwise-or two registers together.
    ///
    /// # Arguments
    ///
    /// * `dest` - The register to store the result in.
    /// * `other` - The register to or with the destination register.
    fn or_vr_vx(&mut self, dest: usize, other: usize) {
        self.registers[dest] |= self.registers[other];
    }

    /// Bitwise-and two registers together.
    ///
    /// # Arguments
    ///
    /// * `dest` - The register to store the result in.
    /// * `other` - The register to and with the destination register.
    fn and_vr_vx(&mut self, dest: usize, other: usize) {
        self.registers[dest] &= self.registers[other];
    }

    /// Bitwise-xor two registers together.
    ///
    /// # Arguments
    ///
    /// * `dest` - The register to store the result in.
    /// * `other` - The register to xor with the destination register.
    fn xor_vr_vx(&mut self, dest: usize, other: usize) {
        self.registers[dest] ^= self.registers[other];
    }

    /// Add two registers together.
    ///
    /// Does set the carry flag if the addition overflows.
    ///
    /// # Arguments
    ///
    /// * `dest` - The register to store the result in.
    /// * `other` - The register to add with the destination register.
    fn add_vr_vx(&mut self, dest: usize, other: usize) {
        let x = self.registers[dest];
        let y = self.registers[other];

        let (res, carry) = x.overflowing_add(y);

        self.registers[dest] = res;
        self.registers[FLAG_REGISTER] = carry as u8;
    }

    /// Subtract two registers from each other.
    ///
    /// Does set the carry flag if the subtraction underflows.
    ///
    /// # Arguments
    ///
    /// * `dest` - The register to store the result in.
    /// * `other` - The register to subtract from the destination register.
    fn sub_vr_vx(&mut self, dest: usize, other: usize) {
        let x = self.registers[dest];
        let y = self.registers[other];

        self.registers[dest] = x.wrapping_sub(y);
        self.registers[FLAG_REGISTER] = (x >= y) as u8;
    }

    /// Bitshift-right the destination register.
    ///
    /// Shifts the bits of the destination register to the right once.
    ///
    /// The least signifigant bit will be stored in the flag register.
    ///
    /// If the `superchip-bitshift` feature is enabled, the value of the
    /// destination register will first be set to the value of the source
    /// register before performing the bitshift.
    #[allow(unused_variables)] // src is not used with feature superchip-bitshift
    fn shr_vr(&mut self, dest: usize, src: usize) {
        // The original Chip8 moved the source register into the destination register
        // before performing the bitshift, but this feature was removed in the
        // superchip. Here this is supported with a feature to switch between the two
        // behaviours.
        #[cfg(not(feature = "superchip-bitshift"))]
        {
            self.registers[dest] = self.registers[src];
        }

        self.registers[FLAG_REGISTER] = self.registers[dest] & 0b0000_0001; // Store least signifigant bit in the flag
        self.registers[dest] >>= 1;
    }

    /// Subtract two registers from each other.
    ///
    /// As opposed to the normal subtraction instruction, this instruction
    /// subtracts the value of the destination register from the other
    /// register, before storing the result in the destination register.
    ///
    /// Does set the carry flag if the subtraction underflows.
    ///
    /// # Arguments
    ///
    /// * `dest` - The register to store the result in.
    /// * `other` - The register to be subtracted from by the destination
    ///   register.
    fn rsb_vr_vx(&mut self, dest: usize, other: usize) {
        let x = self.registers[dest];
        let y = self.registers[other];

        self.registers[FLAG_REGISTER] = (y >= x) as u8;
        self.registers[dest] = y.wrapping_sub(x);
    }

    /// Bitshift-left the destination register.
    ///
    /// Shifts the bits of the destination register to the left once.
    ///
    /// The most signifigant bit will be stored in the flag register.
    ///
    /// If the `superchip-bitshift` feature is enabled, the value of the
    /// destination register will first be set to the value of the source
    /// register before performing the bitshift.
    #[allow(unused_variables)] // src is not used with feature superchip-bitshift
    fn shl_vr(&mut self, dest: usize, src: usize) {
        // See the shr_vr function over.
        #[cfg(not(feature = "superchip-bitshift"))]
        {
            self.registers[dest] = self.registers[src];
        }

        self.registers[FLAG_REGISTER] = (self.registers[dest] & 0b1000_0000) >> 7; // Store most signifigant bit in the flag
        self.registers[dest] <<= 1;
    }

    /// Skip the next line if the value in register x is not equal to register
    /// y.
    ///
    /// # Arguments
    ///
    /// * `rx` - The x register.
    /// * `ry` - The y register.
    fn skne_vr_vx(&mut self, rx: usize, ry: usize) {
        if self.registers[rx] != self.registers[ry] {
            self.next();
        }
    }

    /// Set the index pointer to the given address.
    ///
    /// # Arguments
    ///
    /// * `address` - The memory address to set the [index
    ///   pointer](`Chip8::index`) to.
    fn mvi(&mut self, address: usize) {
        self.index = address;
    }

    /// Jump to the given address + the content of the first register.
    ///
    /// Does not add the current address to the [stack](`Chip8::stack`).
    ///
    /// # Arguments
    ///
    /// * `address` - The address to jump the [program counter](`Chip8::pc`) to.
    #[cfg_attr(feature = "bxnn", allow(dead_code))]
    fn jmi(&mut self, address: usize) {
        self.jmp(address + self.registers[0] as usize);
    }

    /// Jump to the given address + the content of the x register.
    ///
    /// Does not add the current address to the [stack](`Chip8::stack`).
    ///
    /// # Arguments
    ///
    /// * `address` - The address to jump the [program counter](`Chip8::pc`) to.
    /// * `rx` - The register to add to the given address.
    #[cfg(feature = "bxnn")]
    fn jmi_superchip(&mut self, address: usize, rx: usize) {
        self.jmp(address + self.registers[rx] as usize);
    }

    /// Generate a random value.
    ///
    /// # Arguments
    ///
    /// * `register` - The register to store the random value in.
    /// * `mask` - The mask to bitwise-and the random value with before storing
    ///   it in the given register.
    fn rand(&mut self, register: usize, mask: u8) {
        self.registers[register] = rand::random::<u8>() & mask;
    }

    /// Draw a sprite to the internal display.
    ///
    /// If the sprite overwrites an existing sprite, the collision-flag will be
    /// set.
    ///
    /// The sprite will be drawn from memory from where the [index
    /// pointer](`Chip8::index`) is, and increment up to the given height.
    ///
    /// # Arguments
    ///
    /// * `rx` - The x coordinate of the top-left x position to place the sprite
    ///   at.
    /// * `ry` - The y coordinate of the top-left x position to place the sprite
    ///   at.
    /// * `h` - The height of the sprite.
    fn sprite(&mut self, rx: usize, ry: usize, h: usize) {
        let x = self.registers[rx];
        let y = self.registers[ry];

        self.registers[FLAG_REGISTER] = 0;
        for y_line in 0..h {
            let y_coord = (y as usize + y_line) % DISPLAY_HEIGHT;
            let pixel = self.ram[self.index + y_line];

            for x_line in 0..8 {
                if (0b1000_0000 >> x_line) & pixel != 0 {
                    let x_coord = (x as usize + x_line) % DISPLAY_WIDTH;
                    let display_coord = x_coord + y_coord * DISPLAY_WIDTH;

                    // Check if this pixel will be erased, and if so, set the flag
                    if self.vram[display_coord] == 0xFF {
                        self.registers[FLAG_REGISTER] |= 1;
                    }

                    self.vram[display_coord] ^= 0xFF;
                }
            }
        }

        // The display has been updated and should be drawn to
        self.should_draw = true;
    }

    /// Skip if the given key is pressed.
    ///
    /// # Arguments
    ///
    /// * `r` - The register with the key to check.
    fn skpr(&mut self, r: usize) {
        let key = self.registers[r] as usize;
        if self.keys[key] {
            self.next();
        }
    }

    /// Skip if the given key is not pressed.
    ///
    /// # Arguments
    ///
    /// * `r` - The register with the key to check.
    fn skup(&mut self, r: usize) {
        let key = self.registers[r] as usize;
        if !self.keys[key] {
            self.pc += 2;
        }
    }

    /// Get the current delay of the [program timer](`Chip8::program_timer`).
    ///
    /// # Arguments
    ///
    /// * `r` - The register to store the timer value in.
    fn gdelay_vr(&mut self, r: usize) {
        self.registers[r] = self.program_timer.get();
    }

    /// Wait for a key to be pressed.
    ///
    /// # Arguments
    ///
    /// * `r` - The register to store the keycode of the pressed key in.
    fn key_vr(&mut self, r: usize) {
        self.waiting_for_input = Some(r);
    }

    /// Set the delay of the [program timer](`Chip8::program_timer`).
    ///
    /// # Arguments
    ///
    /// * `r` - The register to set the program timer to.
    fn sdelay_vr(&mut self, r: usize) {
        self.program_timer.set(self.registers[r]);
    }

    /// Set the delay of the [sound timer](`Chip8::sound_timer`).
    ///
    /// # Arguments
    ///
    /// * `r` - The register to set the sound timer to.
    fn ssound_vr(&mut self, r: usize) {
        warn!("Sound timer set; No sound emulation.");
        self.sound_timer.set(self.registers[r]);
    }

    /// Add the given register to the [index pointer](`Chip8::index`).
    ///
    /// # Arguments
    ///
    /// * `r` - The register to add to the [index pointer](`Chip8::index`)
    fn adi(&mut self, r: usize) {
        self.index += self.registers[r] as usize;
    }

    /// Point the index pointer to the given font character.
    ///
    /// # Arguments
    ///
    /// * `r` - The register to find the font character for.
    fn font(&mut self, r: usize) {
        self.index = RAM_FONT_SPACE_START + self.registers[r] as usize * 5;
    }

    /// Store the BCD representation of the given register in memory.
    ///
    /// Stores the hundreds-digit of the register value at the current index
    /// pointer location. Tens at one past the current location of the index
    /// pointer, and ones at two past the current index pointer.
    ///
    /// # Arguments
    ///
    /// * `r` - The register to store the BCD of.
    fn bcd_vr(&mut self, r: usize) {
        self.ram[self.index + 0] = self.registers[r] / 100;
        self.ram[self.index + 1] = (self.registers[r] / 10) % 10;
        self.ram[self.index + 2] = (self.registers[r] % 100) % 10;
    }

    /// Store the registers up to the given register in memory.
    ///
    /// The first register will be stored at the location of the [index
    /// pointer](`Chip8::index`), and the following registers at the
    /// following memory addresses.
    ///
    /// # Arguments
    ///
    /// * `r` - The last register to store in memory.
    fn str_v0_vr(&mut self, r: usize) {
        for i in 0..=r {
            self.ram[(self.index) + i] = self.registers[i];
        }

        // On the original chip8, the index pointer was incremented while storing the
        // register values, however, not on the superchip or the Chip48. This
        // behaviour can be switched between with the store-load-modify-index
        // feature.
        #[cfg(feature = "store-load-modify-index")]
        {
            self.index = self.index + r + 1;
        }
    }

    /// Load the registers up to the given register from memory.
    ///
    /// The first register will be loaded from the location of the [index
    /// pointer](`Chip8::index`), and the following registers from the
    /// following memory addresses.
    ///
    /// # Arguments
    ///
    /// * `r` - The last register to load from memory.
    fn ldr_v0_vr(&mut self, r: usize) {
        for i in 0..=r {
            self.registers[i] = self.ram[self.index + i];
        }

        // See the str_v0_vr instruction above.
        #[cfg(feature = "store-load-modify-index")]
        {
            self.index = self.index + r + 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_load_program() {
        let program = vec![0x0, 0x20, 0xAF, 0x0B0];

        let mut chip = Chip8::new();
        chip.load(&program);

        assert_eq!(
            chip.ram[RAM_PROGRAM_SPACE_START..RAM_PROGRAM_SPACE_START + program.len()],
            program
        );
    }

    #[test]
    fn test_load_rand_programs() {
        for _ in 0..100 {
            let mut program: Vec<u8> = Vec::new();
            for _ in 0..100 {
                program.push(rand::random());
            }

            let mut chip = Chip8::new();
            chip.load(&program);

            assert_eq!(
                chip.ram[RAM_PROGRAM_SPACE_START..RAM_PROGRAM_SPACE_START + program.len()],
                program
            );
        }
    }

    #[test]
    fn test_subroutine() {
        let mut chip = Chip8::new();

        chip.jmp(0x300);
        chip.call_subroutine(0x500);
        assert_eq!(chip.pc, 0x500);
        assert_eq!(*chip.stack.last().unwrap(), 0x300);

        chip.call_subroutine(0x150);
        assert_eq!(chip.pc, 0x150);
        assert_eq!(*chip.stack.last().unwrap(), 0x500);

        chip.ret();
        assert_eq!(chip.pc, 0x500);
        assert_eq!(*chip.stack.last().unwrap(), 0x300);

        chip.ret();
        assert_eq!(chip.pc, 0x300);
        assert!(chip.stack.last().is_none());

        chip.ret();
        assert_eq!(chip.pc, 0x300);
        assert!(chip.stack.last().is_none());
    }

    #[test]
    fn test_jmp() {
        let mut chip = Chip8::new();

        chip.jmp(0xFFFF);
        assert_eq!(chip.pc, 0xFFFF);

        chip.jmp(0xEAEA);
        assert_eq!(chip.pc, 0xEAEA);

        chip.jmp(0x200);
        assert_eq!(chip.pc, 0x200);
    }

    #[test]
    fn test_skeq_vr_xx() {
        let mut chip = Chip8::new();

        let org_pc = chip.pc;
        chip.skeq_vr_xx(0, 10);
        assert_eq!(chip.pc, org_pc);

        let org_pc = chip.pc;
        chip.skeq_vr_xx(0, 0);
        assert_eq!(chip.pc, org_pc + 2);

        let org_pc = chip.pc;
        chip.mov_vr_xx(0, 10);
        chip.skeq_vr_xx(0, 10);
        assert_eq!(chip.pc, org_pc + 2);
    }

    #[test]
    fn test_skne_vr_xx() {
        let mut chip = Chip8::new();

        let org_pc = chip.pc;
        chip.skne_vr_xx(0, 0);
        assert_eq!(chip.pc, org_pc);

        let org_pc = chip.pc;
        chip.skne_vr_xx(0, 10);
        assert_eq!(chip.pc, org_pc + 2);

        let org_pc = chip.pc;
        chip.mov_vr_xx(0, 10);
        chip.skne_vr_xx(0, 10);
        assert_eq!(chip.pc, org_pc);
    }

    #[test]
    fn test_skeq_vr_vx() {
        let mut chip = Chip8::new();

        let org_pc = chip.pc;
        chip.skeq_vr_vx(0, 1);
        assert_eq!(chip.pc, org_pc + 2);

        let org_pc = chip.pc;
        chip.mov_vr_xx(0, 10);
        chip.skeq_vr_vx(0, 1);
        assert_eq!(chip.pc, org_pc);

        let org_pc = chip.pc;
        chip.mov_vr_xx(1, 10);
        chip.skeq_vr_vx(0, 1);
        assert_eq!(chip.pc, org_pc + 2);
    }

    #[test]
    fn test_mov_vr_xx() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 1);
        assert_eq!(chip.registers[0], 1);

        chip.mov_vr_xx(5, 10);
        assert_eq!(chip.registers[5], 10);

        chip.mov_vr_xx(8, 5);
        assert_eq!(chip.registers[8], 5);

        for r in 0..16 {
            let val: u8 = rand::random();
            chip.mov_vr_xx(r, val);
            assert_eq!(chip.registers[r as usize], val);
        }
    }

    #[test]
    fn test_add_vr_xx() {
        let mut chip = Chip8::new();

        assert_eq!(chip.registers[0], 0);

        chip.add_vr_xx(0, 10);
        assert_eq!(chip.registers[0], 10);

        chip.add_vr_xx(0, 10);
        assert_eq!(chip.registers[0], 20);

        assert_eq!(chip.registers[1], 0);

        chip.add_vr_xx(1, 10);
        assert_eq!(chip.registers[1], 10);

        chip.add_vr_xx(1, 10);
        assert_eq!(chip.registers[1], 20);
    }

    #[test]
    fn test_mov_vr_vx() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(5, 10);
        assert_eq!(chip.registers[5], 10);

        chip.mov_vr_vx(0, 5);
        assert_eq!(chip.registers[0], 10);

        chip.mov_vr_vx(1, 0);
        assert_eq!(chip.registers[1], 10);

        chip.mov_vr_xx(10, 0xFF);
        assert_eq!(chip.registers[10], 0xFF);

        chip.mov_vr_vx(7, 10);
        assert_eq!(chip.registers[7], 0xFF);
    }

    #[test]
    fn test_or_vr_vx() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 0xFF);
        chip.mov_vr_xx(1, 0x0F);
        chip.or_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 0xFF);

        chip.mov_vr_xx(2, 0b1010_0000);
        chip.mov_vr_xx(3, 0b0000_1010);
        chip.or_vr_vx(2, 3);
        assert_eq!(chip.registers[2], 0b1010_1010);
    }

    #[test]
    fn test_and_vr_vx() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 0xF0);
        chip.mov_vr_xx(1, 0x0F);
        chip.and_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 0x00);

        chip.mov_vr_xx(2, 0xF0);
        chip.mov_vr_xx(3, 0xFF);
        chip.and_vr_vx(2, 3);
        assert_eq!(chip.registers[2], 0xF0);
    }

    #[test]
    fn test_xor_vr_vx() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 0xF0);
        chip.mov_vr_xx(1, 0xFF);
        chip.xor_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 0x0F);

        chip.mov_vr_xx(2, 0xF0);
        chip.mov_vr_xx(3, 0x0F);
        chip.xor_vr_vx(2, 3);
        assert_eq!(chip.registers[2], 0xFF);

        chip.mov_vr_xx(4, 0x0F);
        chip.mov_vr_xx(5, 0x00);
        chip.xor_vr_vx(4, 5);
        assert_eq!(chip.registers[4], 0x0F);
    }

    #[test]
    fn test_add_vr_vx() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 10);
        chip.mov_vr_xx(1, 15);
        chip.add_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 25);

        chip.mov_vr_xx(2, 0);
        chip.mov_vr_xx(3, 15);
        chip.add_vr_vx(2, 3);
        assert_eq!(chip.registers[2], 15);
    }

    #[test]
    fn test_sub_vr_vx() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 10);
        chip.mov_vr_xx(1, 10);
        chip.sub_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 0);
        assert_eq!(chip.registers[FLAG_REGISTER], 1);

        chip.mov_vr_xx(2, 15);
        chip.mov_vr_xx(3, 10);
        chip.sub_vr_vx(2, 3);
        assert_eq!(chip.registers[2], 5);
        assert_eq!(chip.registers[FLAG_REGISTER], 1);

        chip.mov_vr_xx(3, 10);
        chip.sub_vr_vx(2, 3);
        assert_eq!(chip.registers[2], 5u8.wrapping_sub(10));
        assert_eq!(chip.registers[FLAG_REGISTER], 0);

        chip.mov_vr_xx(4, 30);
        chip.mov_vr_xx(5, 20);
        chip.sub_vr_vx(4, 5);
        assert_eq!(chip.registers[4], 10);
        assert_eq!(chip.registers[FLAG_REGISTER], 1);
    }

    #[test]
    #[cfg(feature = "superchip-bitshift")]
    fn test_shr_vr() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 0b0000_1010);
        chip.shr_vr(0, 0);
        assert_eq!(chip.registers[0], 0b0000_0101);
        assert_eq!(chip.registers[FLAG_REGISTER], 0);

        chip.shr_vr(0, 0);
        assert_eq!(chip.registers[0], 0b0000_0010);
        assert_eq!(chip.registers[FLAG_REGISTER], 1);
    }

    #[test]
    #[cfg(not(feature = "superchip-bitshift"))]
    fn test_shr_vr() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(1, 0b0000_1010);
        chip.shr_vr(0, 1);
        assert_eq!(chip.registers[0], 0b0000_0101);
        assert_eq!(chip.registers[FLAG_REGISTER], 0);

        chip.shr_vr(0, 0);
        assert_eq!(chip.registers[0], 0b0000_0010);
        assert_eq!(chip.registers[FLAG_REGISTER], 1);
    }

    #[test]
    fn test_rsb_vr_vx() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 10);
        chip.mov_vr_xx(1, 15);
        chip.rsb_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 5);
        assert_eq!(chip.registers[FLAG_REGISTER], 1);

        chip.mov_vr_xx(1, 6);
        chip.rsb_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 1);
        assert_eq!(chip.registers[FLAG_REGISTER], 1);

        chip.mov_vr_xx(0, 15);
        chip.mov_vr_xx(1, 10);
        chip.rsb_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 10u8.wrapping_sub(15));
        assert_eq!(chip.registers[FLAG_REGISTER], 0);

        chip.mov_vr_xx(0, 10);
        chip.mov_vr_xx(1, 15);
        chip.rsb_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 5);
        assert_eq!(chip.registers[FLAG_REGISTER], 1);
    }

    #[test]
    #[cfg(feature = "superchip-bitshift")]
    fn test_shl_vr() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 0b0101_0000);
        chip.shl_vr(0, 0);
        assert_eq!(chip.registers[0], 0b1010_0000);
        assert_eq!(chip.registers[FLAG_REGISTER], 0);

        chip.shl_vr(0, 0);
        assert_eq!(chip.registers[0], 0b0100_0000);
        assert_eq!(chip.registers[FLAG_REGISTER], 1);
    }

    #[test]
    #[cfg(not(feature = "superchip-bitshift"))]
    fn test_shl_vr() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(1, 0b0101_0000);
        chip.shl_vr(0, 1);
        assert_eq!(chip.registers[0], 0b1010_0000);
        assert_eq!(chip.registers[FLAG_REGISTER], 0);

        chip.shl_vr(0, 0);
        assert_eq!(chip.registers[0], 0b0100_0000);
        assert_eq!(chip.registers[FLAG_REGISTER], 1);
    }

    #[test]
    fn test_skne_vr_vx() {
        let mut chip = Chip8::new();

        let org_pc = chip.pc;
        chip.mov_vr_xx(0, 0);
        chip.mov_vr_xx(1, 0);
        chip.skne_vr_vx(0, 1);
        assert_eq!(chip.pc, org_pc);

        let org_pc = chip.pc;
        chip.mov_vr_xx(2, 0);
        chip.mov_vr_xx(3, 1);
        chip.skne_vr_vx(2, 3);
        assert_eq!(chip.pc, org_pc + 2);
    }

    #[test]
    fn test_mvi() {
        let mut chip = Chip8::new();

        chip.mvi(0xFF);
        assert_eq!(chip.index, 0xFF);

        chip.mvi(0x0F);
        assert_eq!(chip.index, 0x0F);

        chip.mvi(0x8f);
        assert_eq!(chip.index, 0x8f);
    }

    #[test]
    #[cfg(not(feature = "bxnn"))]
    fn test_jmi() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 0);
        chip.jmi(20);
        assert_eq!(chip.pc, 20);

        chip.mov_vr_xx(0, 20);
        chip.jmi(0);
        assert_eq!(chip.pc, 20);

        chip.mov_vr_xx(0, 20);
        chip.jmi(20);
        assert_eq!(chip.pc, 40);
    }

    #[test]
    #[cfg(feature = "bxnn")]
    fn test_jmi_superchip() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 10);
        chip.mov_vr_xx(2, 20);
        chip.jmi_superchip(220, 2);
        assert_eq!(chip.pc, 240);

        chip.mov_vr_xx(0, 0);
        chip.jmi_superchip(240, 0);
        assert_eq!(chip.pc, 240);

        chip.mov_vr_xx(0, 10);
        chip.jmi_superchip(0, 0);
        assert_eq!(chip.pc, 10);
    }

    #[test]
    fn test_rand() {
        // Testing randomness is hard, so just check if
        // there is a lot of variance in the values

        let mut chip = Chip8::new();

        let mut last = chip.registers[0];
        let mut same_count = 0;
        for _ in 0..100 {
            chip.rand(0, 0xFF);

            if last == chip.registers[0] {
                same_count += 1;
            }
            last = chip.registers[0];

            println!("{}", last);
        }

        assert!(same_count < 3);
    }

    #[test]
    fn test_delay() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 10);
        chip.sdelay_vr(0);
        chip.ssound_vr(0);
        assert_eq!(chip.program_timer.get(), 10);
        assert_eq!(chip.sound_timer.get(), 10);

        chip.mov_vr_xx(0, 0);
        chip.sdelay_vr(0);
        assert_eq!(chip.program_timer.get(), 0);
    }

    #[test]
    fn test_adi() {
        let mut chip = Chip8::new();

        chip.mvi(10);
        chip.mov_vr_xx(0, 5);
        chip.adi(0);
        assert_eq!(chip.index, 15);

        chip.mov_vr_xx(5, 5);
        chip.adi(5);
        assert_eq!(chip.index, 20);
    }

    #[test]
    fn test_font_atlas() {
        let mut chip = Chip8::new();

        for i in 0..=0xF {
            chip.mov_vr_xx(0, i as u8);
            chip.font(0);

            for y in 0..5 {
                assert_eq!(chip.ram[chip.index + y], FONT_ATLAS[i * 5 + y]);
            }
        }
    }

    #[test]
    fn test_bcd() {
        let mut chip = Chip8::new();

        chip.mvi(0x300);
        chip.mov_vr_xx(0, 123);
        chip.bcd_vr(0);

        assert_eq!(chip.ram[0x300 + 0], 1);
        assert_eq!(chip.ram[0x300 + 1], 2);
        assert_eq!(chip.ram[0x300 + 2], 3);

        chip.mvi(0x400);
        chip.mov_vr_xx(1, 254);
        chip.bcd_vr(1);

        assert_eq!(chip.ram[0x400 + 0], 2);
        assert_eq!(chip.ram[0x400 + 1], 5);
        assert_eq!(chip.ram[0x400 + 2], 4);
    }

    #[test]
    fn test_str_v0_vr() {
        let mut chip = Chip8::new();

        chip.mvi(0x300);
        chip.mov_vr_xx(0, 10);
        chip.mov_vr_xx(1, 20);
        chip.mov_vr_xx(5, 60);
        chip.str_v0_vr(5);

        assert_eq!(chip.ram[0x300 + 0], 10);
        assert_eq!(chip.ram[0x300 + 1], 20);
        assert_eq!(chip.ram[0x300 + 5], 60);

        #[cfg(feature = "store-load-modify-index")]
        {
            assert_eq!(chip.index, 0x306);
        }

        #[cfg(not(feature = "store-load-modify-index"))]
        {
            assert_eq!(chip.index, 0x300);
        }
    }

    #[test]
    fn test_ldr_v0_vr() {
        let mut chip = Chip8::new();

        chip.mvi(0x300);
        chip.mov_vr_xx(0, 10);
        chip.mov_vr_xx(1, 15);
        chip.mov_vr_xx(2, 20);
        chip.str_v0_vr(2);

        chip.mov_vr_xx(0, 0);
        chip.mov_vr_xx(1, 0);
        chip.mov_vr_xx(2, 0);

        chip.mvi(0x300);
        chip.ldr_v0_vr(2);
        assert_eq!(chip.ram[0x300 + 0], 10);
        assert_eq!(chip.ram[0x300 + 1], 15);
        assert_eq!(chip.ram[0x300 + 2], 20);

        #[cfg(feature = "store-load-modify-index")]
        {
            assert_eq!(chip.index, 0x303);
        }

        #[cfg(not(feature = "store-load-modify-index"))]
        {
            assert_eq!(chip.index, 0x300);
        }
    }
}
