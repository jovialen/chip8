use rand::Rng;

pub const RAM_PROGRAM_SPACE_START: usize = 0x200;
pub const DISPLAY_WIDTH: usize = 64;
pub const DISPLAY_HEIGHT: usize = 32;

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

pub struct Chip8 {
    ram: [u8; 0xFFF],
    vram: [u8; DISPLAY_WIDTH * DISPLAY_HEIGHT],
    registers: [u8; 16],
    index: usize,
    pc: u16,
    stack: Vec<u16>,
    program_timer: u8,
    sound_timer: u8,
    keys: [bool; 16],
    should_draw: bool,
    wait_for_input: Option<u8>,
    rand: rand::rngs::ThreadRng,
}

impl Chip8 {
    pub fn new() -> Self {
        let mut ram = [0; 0xFFF];

        // Copy font atlas into ram
        ram[0..80].copy_from_slice(&FONT_ATLAS);

        Self {
            ram,
            vram: [0; DISPLAY_WIDTH * DISPLAY_HEIGHT],
            registers: [0; 16],
            index: 0,
            pc: RAM_PROGRAM_SPACE_START as u16,
            stack: Vec::with_capacity(16),
            program_timer: 0,
            sound_timer: 0,
            keys: [false; 16],
            should_draw: false,
            wait_for_input: None,
            rand: rand::thread_rng(),
        }
    }

    pub fn load(&mut self, program: &Vec<u8>) {
        for (i, v) in program.iter().enumerate() {
            self.ram[RAM_PROGRAM_SPACE_START + i] = *v;
        }
    }

    pub fn cycle(&mut self) {
        if self.wait_for_input.is_none() {
            let opcode = self.fetch_opcode();
            self.pc += 2;
            self.interpret(opcode);
            self.timer_tick();
        }
    }

    pub fn should_draw(&self) -> bool {
        self.should_draw
    }

    pub fn draw(&mut self, target: &mut [u8]) {
        for (i, pix) in target.chunks_exact_mut(4).enumerate() {
            let pixel = self.vram[i];
            pix.copy_from_slice(&[pixel, pixel, pixel, 0xFF]);
        }
        self.should_draw = false;
    }

    pub fn set_key(&mut self, key: usize, pressed: bool) {
        if pressed && self.wait_for_input.is_some() {
            self.registers[self.wait_for_input.unwrap() as usize] = key as u8;
            self.wait_for_input = None;
        }

        self.keys[key] = pressed;
    }

    fn fetch_opcode(&self) -> u16 {
        let bytes = [self.ram[self.pc as usize], self.ram[self.pc as usize + 1]];

        u16::from_be_bytes(bytes)
    }

    fn interpret(&mut self, instruction: u16) {
        match instruction & 0xF000 {
            0x0000 => match instruction {
                0x0000 => self.pc -= 2, // temp: stop execution
                0x00E0 => self.clear(),
                0x00EE => self.ret(),
                _ => {
                    // 0xxx is in some c8 programs a jump instruction
                    let address = Self::fetch_address(instruction);
                    self.jmp(address);
                }
            },
            0x1000 => {
                let address = Self::fetch_address(instruction);
                self.jmp(address);
            }
            0x2000 => {
                let address = Self::fetch_address(instruction);
                self.call_subroutine(address);
            }
            0x3000 => {
                let (r, v) = Self::fetch_register_and_value(instruction);
                self.skeq_vr_xx(r, v);
            }
            0x4000 => {
                let (r, v) = Self::fetch_register_and_value(instruction);
                self.skne_vr_xx(r, v);
            }
            0x5000 => {
                let (r1, r2, _) = Self::fetch_register_x_y_n(instruction);
                self.skeq_vr_vx(r1, r2);
            }
            0x6000 => {
                let (r, v) = Self::fetch_register_and_value(instruction);
                self.mov_vr_xx(r, v);
            }
            0x7000 => {
                let (r, v) = Self::fetch_register_and_value(instruction);
                self.add_vr_xx(r, v);
            }
            0x8000 => {
                let (r1, r2, _) = Self::fetch_register_x_y_n(instruction);
                match instruction & 0x000F {
                    0x0000 => self.mov_vr_vx(r1, r2),
                    0x0001 => self.or_vr_vx(r1, r2),
                    0x0002 => self.and_vr_vx(r1, r2),
                    0x0003 => self.xor_vr_vx(r1, r2),
                    0x0004 => self.add_vr_vx(r1, r2),
                    0x0005 => self.sub_vr_vx(r1, r2),
                    0x0006 => self.shr_vr(r1),
                    0x0007 => self.rsb_vr_vx(r1, r2),
                    0x000E => self.shl_vr(r1),
                    _ => panic!("Invalid 0x8000 instruction {:#06x}", instruction),
                }
            }
            0x9000 => {
                let (r1, r2, _) = Self::fetch_register_x_y_n(instruction);
                self.skne_vr_vx(r1, r2);
            }
            0xA000 => {
                let address = Self::fetch_address(instruction);
                self.mvi(address);
            }
            0xB000 => {
                let address = Self::fetch_address(instruction);
                self.jmi(address);
            }
            0xC000 => {
                let (r, v) = Self::fetch_register_and_value(instruction);
                self.rand(r, v);
            }
            0xD000 => {
                let (r1, r2, n) = Self::fetch_register_x_y_n(instruction);
                self.sprite(r1, r2, n);
            }
            0xE000 => {
                let k = (instruction & 0x0F00) >> 8;
                match instruction & 0x00FF {
                    0x009E => self.skpr(k as u8),
                    0x00A1 => self.skup(k as u8),
                    _ => panic!("Invalid 0xE000 instruction {:#06x}", instruction),
                }
            }
            0xF000 => {
                let (r, _, _) = Self::fetch_register_x_y_n(instruction);
                match instruction & 0x00FF {
                    0x0007 => self.gdelay_vr(r),
                    0x000A => self.key_vr(r),
                    0x0015 => self.sdelay_vr(r),
                    0x0018 => self.ssound_vr(r),
                    0x001E => self.adi(r),
                    0x0029 => self.font(r),
                    0x0033 => self.bcd_vr(r),
                    0x0055 => self.str_v0_vr(r),
                    0x0065 => self.ldr_v0_vr(r),
                    _ => panic!("Invalid 0xF000 instruction {:#06x}", instruction),
                }
            }
            _ => panic!("Unimplemented instruction {:#06x}", instruction),
        }
    }

    fn fetch_register_and_value(opcode: u16) -> (u8, u8) {
        let register = (opcode & 0x0F00) >> 8;
        let value = opcode & 0x00FF;
        (register as u8, value as u8)
    }

    fn fetch_register_x_y_n(opcode: u16) -> (u8, u8, u8) {
        let r1 = (opcode & 0x0F00) >> 8;
        let r2 = (opcode & 0x00F0) >> 4;
        let n = opcode & 0x000F;
        (r1 as u8, r2 as u8, n as u8)
    }

    fn fetch_address(opcode: u16) -> u16 {
        opcode & 0x0FFF
    }

    fn timer_tick(&mut self) {
        if self.sound_timer != 0 {
            self.sound_timer -= 1;
        }
        if self.program_timer != 0 {
            self.program_timer -= 1;
        }
    }

    fn clear(&mut self) {
        self.vram = [0; DISPLAY_WIDTH * DISPLAY_HEIGHT];
        self.should_draw = true;
    }

    fn ret(&mut self) {
        if let Some(pc) = self.stack.pop() {
            self.pc = pc;
        }
    }

    fn jmp(&mut self, addr: u16) {
        self.pc = addr;
    }

    fn call_subroutine(&mut self, addr: u16) {
        self.stack.push(self.pc);
        self.jmp(addr);
    }

    fn skeq_vr_xx(&mut self, register: u8, value: u8) {
        if self.registers[register as usize] == value {
            self.pc += 2;
        }
    }

    fn skne_vr_xx(&mut self, register: u8, value: u8) {
        if self.registers[register as usize] != value {
            self.pc += 2;
        }
    }

    fn skeq_vr_vx(&mut self, r1: u8, r2: u8) {
        if self.registers[r1 as usize] == self.registers[r2 as usize] {
            self.pc += 2;
        }
    }

    fn mov_vr_xx(&mut self, r: u8, xx: u8) {
        self.registers[r as usize] = xx;
    }

    fn add_vr_xx(&mut self, register: u8, value: u8) {
        let result = self.registers[register as usize] as u16 + value as u16;

        // Discard any overflow
        self.registers[register as usize] = result as u8;
    }

    fn mov_vr_vx(&mut self, r1: u8, r2: u8) {
        self.registers[r1 as usize] = self.registers[r2 as usize];
    }

    fn or_vr_vx(&mut self, r1: u8, r2: u8) {
        self.registers[r1 as usize] = self.registers[r1 as usize] | self.registers[r2 as usize];
    }

    fn and_vr_vx(&mut self, r1: u8, r2: u8) {
        self.registers[r1 as usize] = self.registers[r1 as usize] & self.registers[r2 as usize];
    }

    fn xor_vr_vx(&mut self, r1: u8, r2: u8) {
        self.registers[r1 as usize] = self.registers[r1 as usize] ^ self.registers[r2 as usize];
    }

    fn add_vr_vx(&mut self, r1: u8, r2: u8) {
        let x = self.registers[r1 as usize];
        let y = self.registers[r2 as usize];

        let (res, carry) = x.overflowing_add(y);

        self.registers[r1 as usize] = res;
        self.registers[15] = carry as u8;
    }

    fn sub_vr_vx(&mut self, r1: u8, r2: u8) {
        let x = self.registers[r1 as usize];
        let y = self.registers[r2 as usize];

        self.registers[r1 as usize] = x.wrapping_sub(y);
        self.registers[15] = (x >= y) as u8;
    }

    fn shr_vr(&mut self, r: u8) {
        let src = self.registers[r as usize];
        self.registers[15] = src & 0b0000_0001; // Store least signifigant bit in the flag
        self.registers[r as usize] = src >> 1;
    }

    fn rsb_vr_vx(&mut self, r1: u8, r2: u8) {
        let x = self.registers[r1 as usize];
        let y = self.registers[r2 as usize];

        self.registers[15] = (y >= x) as u8;
        self.registers[r1 as usize] = y.wrapping_sub(x);
    }

    fn shl_vr(&mut self, r: u8) {
        let src = self.registers[r as usize];
        self.registers[15] = (src & 0b1000_0000) >> 7; // Store most signifigant bit in the flag
        self.registers[r as usize] = src << 1;
    }

    fn skne_vr_vx(&mut self, r1: u8, r2: u8) {
        if self.registers[r1 as usize] != self.registers[r2 as usize] {
            self.pc += 2;
        }
    }

    fn mvi(&mut self, address: u16) {
        self.index = address as usize;
    }

    fn jmi(&mut self, address: u16) {
        self.jmp(address + self.registers[0] as u16);
    }

    fn rand(&mut self, register: u8, max: u8) {
        self.registers[register as usize] = self.rand.gen::<u8>() & max;
    }

    fn sprite(&mut self, r1: u8, r2: u8, h: u8) {
        let x = self.registers[r1 as usize];
        let y = self.registers[r2 as usize];

        self.registers[15] = 0;
        for y_line in 0..(h as usize) {
            let y_coord = (y as usize + y_line) % DISPLAY_HEIGHT;
            let pixel = self.ram[self.index + y_line];

            for x_line in 0..8 {
                if (0b1000_0000 >> x_line) & pixel != 0 {
                    let x_coord = (x as usize + x_line) % DISPLAY_WIDTH;
                    let display_coord = x_coord + y_coord * DISPLAY_WIDTH;

                    // Check if this pixel will be erased, and if so, set the flag
                    if self.vram[display_coord] == 0xFF {
                        self.registers[15] |= 1;
                    }

                    self.vram[display_coord] ^= 0xFF;
                }
            }
        }

        // The display has been updated and should be drawn to
        self.should_draw = true;
    }

    fn skpr(&mut self, r: u8) {
        let key = self.registers[r as usize] as usize;
        if self.keys[key] {
            self.pc += 2;
        }
    }

    fn skup(&mut self, r: u8) {
        let key = self.registers[r as usize] as usize;
        if !self.keys[key] {
            self.pc += 2;
        }
    }

    fn gdelay_vr(&mut self, r: u8) {
        self.registers[r as usize] = self.program_timer;
    }

    fn key_vr(&mut self, r: u8) {
        self.wait_for_input = Some(r);
    }

    fn sdelay_vr(&mut self, r: u8) {
        self.program_timer = self.registers[r as usize];
    }

    fn ssound_vr(&mut self, r: u8) {
        self.sound_timer = self.registers[r as usize];
    }

    fn adi(&mut self, r: u8) {
        self.index += self.registers[r as usize] as usize;
    }

    fn font(&mut self, r: u8) {
        self.index = self.registers[r as usize] as usize * 5;
    }

    fn bcd_vr(&mut self, r: u8) {
        self.ram[self.index + 0] = self.registers[r as usize] / 100;
        self.ram[self.index + 1] = (self.registers[r as usize] / 10) % 10;
        self.ram[self.index + 2] = (self.registers[r as usize] % 100) % 10;
    }

    fn str_v0_vr(&mut self, r: u8) {
        for i in 0..=(r as usize) {
            self.ram[(self.index) + i] = self.registers[i];
        }
    }

    fn ldr_v0_vr(&mut self, r: u8) {
        for i in 0..=(r as usize) {
            self.registers[i] = self.ram[self.index + i];
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
        assert_eq!(chip.registers[15], 1);

        chip.mov_vr_xx(2, 15);
        chip.mov_vr_xx(3, 10);
        chip.sub_vr_vx(2, 3);
        assert_eq!(chip.registers[2], 5);
        assert_eq!(chip.registers[15], 1);

        chip.mov_vr_xx(3, 10);
        chip.sub_vr_vx(2, 3);
        assert_eq!(chip.registers[2], 5u8.wrapping_sub(10));
        assert_eq!(chip.registers[15], 0);

        chip.mov_vr_xx(4, 30);
        chip.mov_vr_xx(5, 20);
        chip.sub_vr_vx(4, 5);
        assert_eq!(chip.registers[4], 10);
        assert_eq!(chip.registers[15], 1);
    }

    #[test]
    fn test_shr_vr() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 0b0000_1010);
        chip.shr_vr(0);
        assert_eq!(chip.registers[0], 0b0000_0101);
        assert_eq!(chip.registers[15], 0);

        chip.shr_vr(0);
        assert_eq!(chip.registers[0], 0b0000_0010);
        assert_eq!(chip.registers[15], 1);
    }

    #[test]
    fn test_rsb_vr_vx() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 10);
        chip.mov_vr_xx(1, 15);
        chip.rsb_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 5);
        assert_eq!(chip.registers[15], 1);

        chip.mov_vr_xx(1, 6);
        chip.rsb_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 1);
        assert_eq!(chip.registers[15], 1);

        chip.mov_vr_xx(0, 15);
        chip.mov_vr_xx(1, 10);
        chip.rsb_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 10u8.wrapping_sub(15));
        assert_eq!(chip.registers[15], 0);

        chip.mov_vr_xx(0, 10);
        chip.mov_vr_xx(1, 15);
        chip.rsb_vr_vx(0, 1);
        assert_eq!(chip.registers[0], 5);
        assert_eq!(chip.registers[15], 1);
    }

    #[test]
    fn test_shl_vr() {
        let mut chip = Chip8::new();

        chip.mov_vr_xx(0, 0b0101_0000);
        chip.shl_vr(0);
        assert_eq!(chip.registers[0], 0b1010_0000);
        assert_eq!(chip.registers[15], 0);

        chip.shl_vr(0);
        assert_eq!(chip.registers[0], 0b0100_0000);
        assert_eq!(chip.registers[15], 1);
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
        assert_eq!(chip.program_timer, 10);
        assert_eq!(chip.sound_timer, 10);

        chip.timer_tick();
        chip.timer_tick();
        chip.timer_tick();
        assert_eq!(chip.program_timer, 7);
        assert_eq!(chip.sound_timer, 7);

        chip.mov_vr_xx(0, 0);
        chip.sdelay_vr(0);
        assert_eq!(chip.program_timer, 0);
        assert_eq!(chip.sound_timer, 7);

        chip.timer_tick();
        assert_eq!(chip.program_timer, 0);
        assert_eq!(chip.sound_timer, 6);
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

        for i in 0..0xF {
            chip.font(i as u8);

            for y in 0..5 {
                chip.ram[chip.index + y] = FONT_ATLAS[i * 5 + y];
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

        chip.ldr_v0_vr(2);
        assert_eq!(chip.ram[0x300 + 0], 10);
        assert_eq!(chip.ram[0x300 + 1], 15);
        assert_eq!(chip.ram[0x300 + 2], 20);
    }
}
