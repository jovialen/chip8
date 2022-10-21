pub struct Timer {
    start: std::time::Instant,
    ticks: u8,
}

impl Timer {
    pub fn new() -> Self {
        Self {
            start: std::time::Instant::now(),
            ticks: 0,
        }
    }

    pub fn set(&mut self, ticks: u8) {
        self.start = std::time::Instant::now();
        self.ticks = ticks;
    }

    pub fn get(&self) -> u8 {
        let elapsed_ticks = (self.start.elapsed().as_secs_f64() * 60.0).floor() as u8;
        self.ticks.checked_sub(elapsed_ticks).unwrap_or(0)
    }
}
