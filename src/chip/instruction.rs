/// Available Chip8 instructions.
#[derive(Debug, PartialEq, Eq)]
#[rustfmt::skip]
pub enum Instruction {
    /// Clear the screen.
    Clear,
    /// Return from subroutine.
    ReturnSubroutine,
    /// Jump to address.
    Jump(usize),
    /// Call subroutine.
    CallSubroutine(usize),
    /// Skip if register value is equal to constant.
    SkipEqToConst { register: usize, value: u8 },
    /// Skip if register value is not equal to constant.
    SkipNeToConst { register: usize, value: u8 },
    /// Skip if register x is equal to register y.
    SkipEqToReg { x: usize, y: usize },
    /// Move constant value into destination register.
    MovConstToReg { dest: usize, value: u8 },
    /// Add constant value to destination register.
    AddConstToReg { dest: usize, value: u8 },
    /// Set value of dest to value of src.
    MovRegToReg { dest: usize, src: usize },
    /// Or value of other into dest.
    Or { dest: usize, other: usize },
    /// And value of other into dest.
    And { dest: usize, other: usize },
    /// Xor value of other into dest.
    Xor { dest: usize, other: usize },
    /// Add value of other into dest.
    AddRegToReg { dest: usize, other: usize },
    /// Subtract value of other from dest.
    SubRegFromReg { dest: usize, other: usize },
    /// Bitshift register to the right once.
    ShiftRight { dest: usize, src: usize },
    /// Subtract value of dest from other, and store the result in dest.
    SubnRegFromReg { dest: usize, other: usize },
    /// Bitshift register to the left once.
    ShiftLeft { dest: usize, src: usize },
    /// Skip if value of register x is not equal to value of register y.
    SkipNeToReg { x: usize, y: usize },
    /// Set the value of the index pointer.
    MovConstToI(usize),
    /// Jump to the address + the value of register 0.
    #[cfg(not(feature = "bxnn"))]
    JumpI(usize),
    /// Jump to the address + the value of the x register.
    /// 
    /// This instruction was added by the superchip, but
    /// is used in many Chip8 programs.
    #[cfg(feature = "bxnn")]
    SuperJumpI { addr: usize, x: usize },
    /// Store a random u8 in dest and bitwise-& with the mask.
    Rand { dest: usize, mask: u8 },
    /// Draw a sprite with the given height to the x and y on the screen.
    Sprite { x: usize, y: usize, height: usize },
    /// Skip if the given key is pressed.
    SkipIfPressed(usize),
    /// Skip if the given key is released.
    SkipIfReleased(usize),
    /// Get the current delay in the program timer.
    GetDelay(usize),
    /// Wait for a keypress and store in the given register.
    WaitKey(usize),
    /// Set the program delay.
    SetDelay(usize),
    /// Set the sound delay.
    SetSoundDelay(usize),
    /// Add the given register to the index pointer.
    AddToI(usize),
    /// Set I to the location of the sprite for the given character.
    LoadFont(usize),
    /// Store the bcd representation of the given register to memory at the index pointer.
    StoreBcd(usize),
    /// Store the values in registers 0 to x to memory at the index pointer.
    Store(usize),
    /// Load the values in registers 0 to x from memory at the index pointer.
    Load(usize),
}

impl Instruction {
    pub fn from_be_bytes(bytes: [u8; 2]) -> Self {
        Self::from(u16::from_be_bytes(bytes))
    }
}

impl From<u16> for Instruction {
    fn from(opcode: u16) -> Self {
        let x = ((opcode & 0x0F00) >> 8) as usize;
        let y = ((opcode & 0x00F0) >> 4) as usize;
        let n = (opcode & 0x000F) as usize;
        let nn = (opcode & 0x00FF) as u8;
        let nnn = (opcode & 0x0FFF) as usize;

        match opcode & 0xF000 {
            0x0000 => match opcode {
                0x00E0 => Self::Clear,
                0x00EE => Self::ReturnSubroutine,
                _ => Self::Jump(nnn), /* 0x0nnn is in some programs used as a jump
                                       * instruction */
            },
            0x1000 => Self::Jump(nnn),
            0x2000 => Self::CallSubroutine(nnn),
            0x3000 => Self::SkipEqToConst {
                register: x,
                value: nn,
            },
            0x4000 => Self::SkipNeToConst {
                register: x,
                value: nn,
            },
            0x5000 => Self::SkipEqToReg { x, y },
            0x6000 => Self::MovConstToReg { dest: x, value: nn },
            0x7000 => Self::AddConstToReg { dest: x, value: nn },
            0x8000 => match opcode & 0x000F {
                0x0000 => Self::MovRegToReg { dest: x, src: y },
                0x0001 => Self::Or { dest: x, other: y },
                0x0002 => Self::And { dest: x, other: y },
                0x0003 => Self::Xor { dest: x, other: y },
                0x0004 => Self::AddRegToReg { dest: x, other: y },
                0x0005 => Self::SubRegFromReg { dest: x, other: y },
                0x0006 => Self::ShiftRight { dest: x, src: y },
                0x0007 => Self::SubnRegFromReg { dest: x, other: y },
                0x000E => Self::ShiftLeft { dest: x, src: y },
                _ => panic!("Invalid 0x8000 opcode {:#06x}", opcode),
            },
            0x9000 => Self::SkipNeToReg { x, y },
            0xA000 => Self::MovConstToI(nnn),
            #[cfg(not(feature = "bxnn"))]
            0xB000 => Self::JumpI(nnn),
            #[cfg(feature = "bxnn")]
            0xB000 => Self::SuperJumpI { addr: nnn, x },
            0xC000 => Self::Rand { dest: x, mask: nn },
            0xD000 => Self::Sprite { x, y, height: n },
            0xE000 => match opcode & 0x00FF {
                0x009E => Self::SkipIfPressed(x),
                0x00A1 => Self::SkipIfReleased(x),
                _ => panic!("Invalid 0xE000 opcode {:#06x}", opcode),
            },
            0xF000 => match opcode & 0x00FF {
                0x0007 => Self::GetDelay(x),
                0x000A => Self::WaitKey(x),
                0x0015 => Self::SetDelay(x),
                0x0018 => Self::SetSoundDelay(x),
                0x001E => Self::AddToI(x),
                0x0029 => Self::LoadFont(x),
                0x0033 => Self::StoreBcd(x),
                0x0055 => Self::Store(x),
                0x0065 => Self::Load(x),
                _ => panic!("Invalid 0xF000 opcode {:#06x}", opcode),
            },
            _ => panic!("Unimplemented opcode {:#06x}", opcode),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clear_opcode() {
        assert_eq!(Instruction::from(0x00E0), Instruction::Clear);
    }

    #[test]
    fn test_return_opcode() {
        assert_eq!(Instruction::from(0x00EE), Instruction::ReturnSubroutine);
    }

    #[test]
    fn test_jmp_opcode() {
        assert_eq!(Instruction::from(0x1000), Instruction::Jump(0x000));
        assert_eq!(Instruction::from(0x1100), Instruction::Jump(0x100));
        assert_eq!(Instruction::from(0x1123), Instruction::Jump(0x123));
    }

    #[test]
    fn test_call_subroutine_opcode() {
        assert_eq!(
            Instruction::from(0x2000),
            Instruction::CallSubroutine(0x000)
        );
        assert_eq!(
            Instruction::from(0x2100),
            Instruction::CallSubroutine(0x100)
        );
        assert_eq!(
            Instruction::from(0x2123),
            Instruction::CallSubroutine(0x123)
        );
    }

    #[test]
    fn test_skeq_vr_xx_opcode() {
        assert_eq!(
            Instruction::from(0x3000),
            Instruction::SkipEqToConst {
                register: 0,
                value: 0
            }
        );
        assert_eq!(
            Instruction::from(0x3500),
            Instruction::SkipEqToConst {
                register: 5,
                value: 0
            }
        );
        assert_eq!(
            Instruction::from(0x3010),
            Instruction::SkipEqToConst {
                register: 0,
                value: 0x10
            }
        );
    }

    #[test]
    fn test_skne_vr_xx_opcode() {
        assert_eq!(
            Instruction::from(0x4000),
            Instruction::SkipNeToConst {
                register: 0,
                value: 0
            }
        );
        assert_eq!(
            Instruction::from(0x4500),
            Instruction::SkipNeToConst {
                register: 5,
                value: 0
            }
        );
        assert_eq!(
            Instruction::from(0x4010),
            Instruction::SkipNeToConst {
                register: 0,
                value: 0x10
            }
        );
    }

    #[test]
    fn test_mov_vr_xx_opcode() {
        assert_eq!(
            Instruction::from(0x6000),
            Instruction::MovConstToReg { dest: 0, value: 0 }
        );
        assert_eq!(
            Instruction::from(0x6500),
            Instruction::MovConstToReg { dest: 5, value: 0 }
        );
        assert_eq!(
            Instruction::from(0x6010),
            Instruction::MovConstToReg {
                dest: 0,
                value: 0x10
            }
        );
    }

    #[test]
    fn test_add_vr_xx_opcode() {
        assert_eq!(
            Instruction::from(0x7000),
            Instruction::AddConstToReg { dest: 0, value: 0 }
        );
        assert_eq!(
            Instruction::from(0x7500),
            Instruction::AddConstToReg { dest: 5, value: 0 }
        );
        assert_eq!(
            Instruction::from(0x7010),
            Instruction::AddConstToReg {
                dest: 0,
                value: 0x10
            }
        );
    }

    #[test]
    fn test_mov_vr_vx_opcode() {
        assert_eq!(
            Instruction::from(0x8000),
            Instruction::MovRegToReg { dest: 0, src: 0 }
        );
        assert_eq!(
            Instruction::from(0x8120),
            Instruction::MovRegToReg { dest: 1, src: 2 }
        );
        assert_eq!(
            Instruction::from(0x80E0),
            Instruction::MovRegToReg { dest: 0, src: 0xE }
        );
    }

    #[test]
    fn test_or_opcode() {
        assert_eq!(
            Instruction::from(0x8001),
            Instruction::Or { dest: 0, other: 0 }
        );
        assert_eq!(
            Instruction::from(0x8141),
            Instruction::Or { dest: 1, other: 4 }
        );
    }

    #[test]
    fn test_and_opcode() {
        assert_eq!(
            Instruction::from(0x8002),
            Instruction::And { dest: 0, other: 0 }
        );
        assert_eq!(
            Instruction::from(0x8142),
            Instruction::And { dest: 1, other: 4 }
        );
    }

    #[test]
    fn test_xor_opcode() {
        assert_eq!(
            Instruction::from(0x8003),
            Instruction::Xor { dest: 0, other: 0 }
        );
        assert_eq!(
            Instruction::from(0x8143),
            Instruction::Xor { dest: 1, other: 4 }
        );
    }

    #[test]
    fn test_add_vr_vx_opcode() {
        assert_eq!(
            Instruction::from(0x8004),
            Instruction::AddRegToReg { dest: 0, other: 0 }
        );
        assert_eq!(
            Instruction::from(0x8144),
            Instruction::AddRegToReg { dest: 1, other: 4 }
        );
    }

    #[test]
    fn test_sub_vr_vx_opcode() {
        assert_eq!(
            Instruction::from(0x8005),
            Instruction::SubRegFromReg { dest: 0, other: 0 }
        );
        assert_eq!(
            Instruction::from(0x8145),
            Instruction::SubRegFromReg { dest: 1, other: 4 }
        );
    }

    #[test]
    fn test_shr_opcode() {
        assert_eq!(
            Instruction::from(0x8006),
            Instruction::ShiftRight { dest: 0, src: 0 }
        );
        assert_eq!(
            Instruction::from(0x8106),
            Instruction::ShiftRight { dest: 1, src: 0 }
        );
        assert_eq!(
            Instruction::from(0x8516),
            Instruction::ShiftRight { dest: 5, src: 1 }
        );
    }

    #[test]
    fn test_rsb_opcode() {
        assert_eq!(
            Instruction::from(0x8007),
            Instruction::SubnRegFromReg { dest: 0, other: 0 }
        );
        assert_eq!(
            Instruction::from(0x8147),
            Instruction::SubnRegFromReg { dest: 1, other: 4 }
        );
    }

    #[test]
    fn test_shl_opcode() {
        assert_eq!(
            Instruction::from(0x800E),
            Instruction::ShiftLeft { dest: 0, src: 0 }
        );
        assert_eq!(
            Instruction::from(0x810E),
            Instruction::ShiftLeft { dest: 1, src: 0 }
        );
        assert_eq!(
            Instruction::from(0x851E),
            Instruction::ShiftLeft { dest: 5, src: 1 }
        );
    }

    #[test]
    fn test_skne_vr_vx_opcode() {
        assert_eq!(
            Instruction::from(0x9000),
            Instruction::SkipNeToReg { x: 0, y: 0 }
        );
        assert_eq!(
            Instruction::from(0x9140),
            Instruction::SkipNeToReg { x: 1, y: 4 }
        );
        assert_eq!(
            Instruction::from(0x9001),
            Instruction::SkipNeToReg { x: 0, y: 0 }
        );
        assert_eq!(
            Instruction::from(0x9141),
            Instruction::SkipNeToReg { x: 1, y: 4 }
        );
    }

    #[test]
    fn test_mvi_opcode() {
        assert_eq!(Instruction::from(0xA000), Instruction::MovConstToI(0));
        assert_eq!(Instruction::from(0xA123), Instruction::MovConstToI(0x123));
        assert_eq!(Instruction::from(0xAFFF), Instruction::MovConstToI(0xFFF));
    }

    #[test]
    #[cfg(not(feature = "bxnn"))]
    fn test_jmi_opcode() {
        assert_eq!(Instruction::from(0xB000), Instruction::JumpI(0));
        assert_eq!(Instruction::from(0xB123), Instruction::JumpI(0x123));
        assert_eq!(Instruction::from(0xBFFF), Instruction::JumpI(0xFFF));
    }

    #[test]
    #[cfg(feature = "bxnn")]
    fn test_super_jmi_opcode() {
        assert_eq!(
            Instruction::from(0xB000),
            Instruction::SuperJumpI { addr: 0, x: 0 }
        );
        assert_eq!(
            Instruction::from(0xB123),
            Instruction::SuperJumpI {
                addr: 0x123,
                x: 0x1
            }
        );
        assert_eq!(
            Instruction::from(0xBFFF),
            Instruction::SuperJumpI {
                addr: 0xFFF,
                x: 0xF
            }
        );
    }

    #[test]
    fn test_rand_opcode() {
        assert_eq!(
            Instruction::from(0xC000),
            Instruction::Rand {
                dest: 0,
                mask: 0x00
            }
        );
        assert_eq!(
            Instruction::from(0xC10F),
            Instruction::Rand {
                dest: 1,
                mask: 0x0F
            }
        );
        assert_eq!(
            Instruction::from(0xC5FF),
            Instruction::Rand {
                dest: 5,
                mask: 0xFF
            }
        );
    }

    #[test]
    fn test_sprite_opcode() {
        assert_eq!(
            Instruction::from(0xD000),
            Instruction::Sprite {
                x: 0,
                y: 0,
                height: 0
            }
        );
        assert_eq!(
            Instruction::from(0xD100),
            Instruction::Sprite {
                x: 1,
                y: 0,
                height: 0
            }
        );
        assert_eq!(
            Instruction::from(0xD010),
            Instruction::Sprite {
                x: 0,
                y: 1,
                height: 0
            }
        );
        assert_eq!(
            Instruction::from(0xD001),
            Instruction::Sprite {
                x: 0,
                y: 0,
                height: 1
            }
        );
        assert_eq!(
            Instruction::from(0xDEAF),
            Instruction::Sprite {
                x: 0xE,
                y: 0xA,
                height: 0xF
            }
        );
    }

    #[test]
    fn test_skpr_opcode() {
        assert_eq!(Instruction::from(0xE09E), Instruction::SkipIfPressed(0));
        assert_eq!(Instruction::from(0xE19E), Instruction::SkipIfPressed(1));
        assert_eq!(Instruction::from(0xE29E), Instruction::SkipIfPressed(2));
        assert_eq!(Instruction::from(0xEF9E), Instruction::SkipIfPressed(0xF));
    }

    #[test]
    fn test_skup_opcode() {
        assert_eq!(Instruction::from(0xE0A1), Instruction::SkipIfReleased(0));
        assert_eq!(Instruction::from(0xE1A1), Instruction::SkipIfReleased(1));
        assert_eq!(Instruction::from(0xE2A1), Instruction::SkipIfReleased(2));
        assert_eq!(Instruction::from(0xEFA1), Instruction::SkipIfReleased(0xF));
    }

    #[test]
    fn test_gdelay_opcode() {
        assert_eq!(Instruction::from(0xF007), Instruction::GetDelay(0));
        assert_eq!(Instruction::from(0xF107), Instruction::GetDelay(1));
        assert_eq!(Instruction::from(0xFF07), Instruction::GetDelay(0xF));
    }

    #[test]
    fn test_key_opcode() {
        assert_eq!(Instruction::from(0xF00A), Instruction::WaitKey(0));
        assert_eq!(Instruction::from(0xF10A), Instruction::WaitKey(1));
        assert_eq!(Instruction::from(0xFF0A), Instruction::WaitKey(0xF));
    }

    #[test]
    fn test_sdelay_opcode() {
        assert_eq!(Instruction::from(0xF015), Instruction::SetDelay(0));
        assert_eq!(Instruction::from(0xF115), Instruction::SetDelay(1));
        assert_eq!(Instruction::from(0xFE15), Instruction::SetDelay(0xE));
    }

    #[test]
    fn test_ssound_opcode() {
        assert_eq!(Instruction::from(0xF018), Instruction::SetSoundDelay(0));
        assert_eq!(Instruction::from(0xF118), Instruction::SetSoundDelay(1));
        assert_eq!(Instruction::from(0xFE18), Instruction::SetSoundDelay(0xE));
    }

    #[test]
    fn test_adi_opcode() {
        assert_eq!(Instruction::from(0xF01E), Instruction::AddToI(0));
        assert_eq!(Instruction::from(0xF11E), Instruction::AddToI(1));
        assert_eq!(Instruction::from(0xFF1E), Instruction::AddToI(0xF));
    }

    #[test]
    fn test_font_opcode() {
        assert_eq!(Instruction::from(0xF029), Instruction::LoadFont(0));
        assert_eq!(Instruction::from(0xF129), Instruction::LoadFont(1));
        assert_eq!(Instruction::from(0xFF29), Instruction::LoadFont(0xF));
    }

    #[test]
    fn test_bcd_opcode() {
        assert_eq!(Instruction::from(0xF033), Instruction::StoreBcd(0));
        assert_eq!(Instruction::from(0xF133), Instruction::StoreBcd(1));
        assert_eq!(Instruction::from(0xFF33), Instruction::StoreBcd(0xF));
    }

    #[test]
    fn test_str_opcode() {
        assert_eq!(Instruction::from(0xF055), Instruction::Store(0));
        assert_eq!(Instruction::from(0xF155), Instruction::Store(1));
        assert_eq!(Instruction::from(0xFF55), Instruction::Store(0xF));
    }

    #[test]
    fn test_ldr_opcode() {
        assert_eq!(Instruction::from(0xF065), Instruction::Load(0));
        assert_eq!(Instruction::from(0xF165), Instruction::Load(1));
        assert_eq!(Instruction::from(0xFF65), Instruction::Load(0xF));
    }
}
