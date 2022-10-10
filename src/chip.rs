const RAM_PROGRAM_SPACE_START: usize = 0x200;

pub struct Chip8 {
    memory: [u8; 0xFFF],
}

impl Chip8 {
    pub fn new() -> Self {
        Self { memory: [0; 0xFFF] }
    }

    pub fn load(&mut self, program: &Vec<u8>) {
        for (i, v) in program.iter().enumerate() {
            self.memory[RAM_PROGRAM_SPACE_START + i] = *v;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn load_program() {
        let program = vec![0x0, 0x20, 0xAF, 0x0B0];

        let mut chip = Chip8::new();
        chip.load(&program);

        assert_eq!(
            chip.memory[RAM_PROGRAM_SPACE_START..RAM_PROGRAM_SPACE_START + program.len()],
            program
        );
    }

    #[test]
    fn load_rand_programs() {
        for _ in 0..100 {
            let mut program: Vec<u8> = Vec::new();
            for _ in 0..100 {
                program.push(rand::random());
            }

            let mut chip = Chip8::new();
            chip.load(&program);

            assert_eq!(
                chip.memory[RAM_PROGRAM_SPACE_START..RAM_PROGRAM_SPACE_START + program.len()],
                program
            );
        }
    }
}
