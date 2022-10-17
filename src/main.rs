mod chip;
mod cli;
mod instruction;

use std::time::Instant;

use chip::{Chip8, DISPLAY_HEIGHT, DISPLAY_WIDTH};
use clap::Parser;
use pixels::{Pixels, SurfaceTexture};
use winit::{
    dpi::LogicalSize,
    event::{ElementState, Event, VirtualKeyCode, WindowEvent},
    event_loop::{ControlFlow, EventLoop},
    window::{Window, WindowBuilder},
};

fn create_window(args: &cli::Args) -> (EventLoop<()>, Window, Pixels) {
    let event_loop = EventLoop::new();

    let min_size = LogicalSize::new(DISPLAY_WIDTH as f64, DISPLAY_HEIGHT as f64);
    let window = WindowBuilder::new()
        .with_title(format!(
            "Chip8 Emulator - {:?}",
            args.rom.file_name().unwrap()
        ))
        .with_min_inner_size(min_size)
        .build(&event_loop)
        .expect("Failed to create window");

    let size = window.inner_size();
    let surface = SurfaceTexture::new(size.width, size.height, &window);
    let pixels = Pixels::new(
        chip::DISPLAY_WIDTH as u32,
        chip::DISPLAY_HEIGHT as u32,
        surface,
    )
    .expect("Failed to create the pixel frame buffer");

    (event_loop, window, pixels)
}

fn main() {
    // Start logger
    env_logger::init();

    // Read command line arguments
    let args = cli::Args::parse();

    // Create window
    let (event_loop, window, mut pixels) = create_window(&args);

    // Create chip
    let mut chip = Chip8::new();

    // Load ROM into chip
    let rom = std::fs::read(args.rom).expect("Failed to read ROM file");
    chip.load(&rom);

    // Prepare timer
    let mut last_time = Instant::now();

    // Start the main loop
    event_loop.run(move |event, _, control_flow| match event {
        Event::WindowEvent { window_id, event } if window_id == window.id() => match event {
            WindowEvent::CloseRequested => *control_flow = ControlFlow::Exit,
            WindowEvent::KeyboardInput { input, .. } => {
                let pressed = input.state == ElementState::Pressed;

                let key = match input.virtual_keycode {
                    Some(VirtualKeyCode::Key1) => 0x1,
                    Some(VirtualKeyCode::Key2) => 0x2,
                    Some(VirtualKeyCode::Key3) => 0x3,
                    Some(VirtualKeyCode::Key4) => 0xC,
                    Some(VirtualKeyCode::Q) => 0x4,
                    Some(VirtualKeyCode::W) => 0x5,
                    Some(VirtualKeyCode::E) => 0x6,
                    Some(VirtualKeyCode::R) => 0xD,
                    Some(VirtualKeyCode::A) => 0x7,
                    Some(VirtualKeyCode::S) => 0x8,
                    Some(VirtualKeyCode::D) => 0x9,
                    Some(VirtualKeyCode::F) => 0xE,
                    Some(VirtualKeyCode::Z) => 0xA,
                    Some(VirtualKeyCode::X) => 0x0,
                    Some(VirtualKeyCode::C) => 0xB,
                    Some(VirtualKeyCode::V) => 0xF,
                    _ => return,
                };

                chip.set_key(key, pressed);
            }
            WindowEvent::Resized(physical_size) => {
                pixels.resize_surface(physical_size.width, physical_size.height);
                window.request_redraw();
            }
            WindowEvent::ScaleFactorChanged { new_inner_size, .. } => {
                pixels.resize_surface(new_inner_size.width, new_inner_size.height);
                window.request_redraw();
            }
            _ => (),
        },
        Event::RedrawRequested(window_id) if window_id == window.id() => {
            chip.draw(pixels.get_frame());

            if pixels
                .render()
                .map_err(|_| eprintln!("Render failed"))
                .is_err()
            {
                *control_flow = ControlFlow::Exit;
            }
        }
        Event::MainEventsCleared => {
            // Trigger 60 clock cycles per second
            if last_time.elapsed().as_secs_f64() > (1.0 / args.hz as f64) {
                last_time = Instant::now();
                chip.cycle();

                // Redraw the window if the chip display has changed
                if chip.should_draw() {
                    window.request_redraw();
                }
            }
        }
        _ => (),
    });
}
