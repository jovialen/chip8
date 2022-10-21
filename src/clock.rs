use std::time::{Duration, Instant};

pub struct Clock {
    last_tick: Instant,
    hz: u32,
}

impl Clock {
    /// Create a new clock.
    ///
    /// # Arguments
    ///
    /// * `hz` - The speed of the clock in hertz.
    pub fn new(hz: u32) -> Self {
        Self {
            last_tick: Instant::now(),
            hz,
        }
    }

    /// Manually trigger the clock.
    ///
    /// * `callback` - The callback to trigger when ticking the clock.
    pub fn trigger<F>(&mut self, mut callback: F)
    where
        F: FnMut(),
    {
        self.last_tick = Instant::now();
        callback();
    }

    /// Trigger a tick if the appropriate delay has passed since the last tick.
    ///
    /// Will return true if a tick was triggered.
    ///
    /// # Arguments
    ///
    /// * `callback` - The function to call if the clock is triggered.
    pub fn tick<F>(&mut self, callback: F) -> bool
    where
        F: FnMut(),
    {
        let threshold = Duration::from_secs(1).as_secs_f64() / self.hz as f64;
        let should_trigger = self.last_tick.elapsed().as_secs_f64() > threshold;

        if should_trigger {
            self.trigger(callback);
        }

        should_trigger
    }
}
