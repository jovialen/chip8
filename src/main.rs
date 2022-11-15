// Enable the windows subsystem on release for windows
#![cfg_attr(all(windows, not(debug_assertions)), windows_subsystem = "windows")]

mod chip;
mod cli;
mod clock;

use chip::{Chip8, DISPLAY_HEIGHT, DISPLAY_WIDTH};
use clap::Parser;
use clock::Clock;
use native_dialog::FileDialog;
use pixels::{Pixels, SurfaceTexture};
use winit::{
    dpi::LogicalSize,
    event::{ElementState, Event, VirtualKeyCode, WindowEvent},
    event_loop::{ControlFlow, EventLoop},
    window::{Window, WindowBuilder},
};

const WINDOW_TITLE: &str = "Chip 8 Emulator";

fn create_window() -> (EventLoop<()>, Window) {
    let event_loop = EventLoop::new();

    let min_size = LogicalSize::new(DISPLAY_WIDTH as f64, DISPLAY_HEIGHT as f64);
    let window = WindowBuilder::new()
        .with_title(WINDOW_TITLE)
        .with_min_inner_size(min_size)
        .build(&event_loop)
        .expect("Failed to create window");

    (event_loop, window)
}

fn create_pixels_framebuffer(window: &Window) -> Pixels {
    let size = window.inner_size();
    let surface = SurfaceTexture::new(size.width, size.height, &window);
    Pixels::new(DISPLAY_WIDTH as u32, DISPLAY_HEIGHT as u32, surface)
        .expect("Failed to create the pixel framebuffer.")
}

fn main() {
    // Start logger
    env_logger::init();

    // Read command line arguments
    let args = cli::Args::parse();

    // Create window and framebuffer
    let (event_loop, window) = create_window();
    let mut pixels = create_pixels_framebuffer(&window);

    // Get the ROM file
    let rom_path = if let Some(rom) = args.rom {
        rom
    } else {
        FileDialog::new()
            .set_owner(&window)
            .set_location("~")
            .add_filter("Chip 8 Rom", &["c8", "ch8", "rom"])
            .show_open_single_file()
            .expect("File dialog failed.")
            .expect("No rom file chosen.")
    };

    // Create chip
    let mut chip = Chip8::new();

    // Load ROM into chip
    let rom = std::fs::read(&rom_path).expect("Failed to read ROM file");
    chip.load(&rom);

    window.set_title(
        format!(
            "{} - {:?}",
            WINDOW_TITLE,
            rom_path.file_name().unwrap_or_default(),
        )
        .as_str(),
    );

    // Prepare clock
    let mut clock = Clock::new(args.hz);

    // Start the main loop
    event_loop.run(move |event, _, control_flow| match event {
        Event::WindowEvent { window_id, event } if window_id == window.id() => match event {
            WindowEvent::CloseRequested => *control_flow = ControlFlow::Exit,
            WindowEvent::KeyboardInput {
                is_synthetic: true, ..
            } => (),
            WindowEvent::DroppedFile(path) => {
                let rom = std::fs::read(&path).expect("Failed to read provided file.");
                chip.load(&rom);
            }
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

                // Trigger a new cycle immediatly if the chip is waiting for input
                if chip.waiting_for_input() && pressed {
                    chip.set_key(key, pressed);
                    clock.trigger(|| chip.cycle());
                } else {
                    chip.set_key(key, pressed);
                }
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
            chip.draw(
                pixels.get_frame_mut(),
                args.foreground_color,
                args.background_color,
            );

            if pixels
                .render()
                .map_err(|_| eprintln!("Render failed"))
                .is_err()
            {
                *control_flow = ControlFlow::Exit;
            }
        }
        Event::MainEventsCleared => {
            // Redraw the window if the chip display has been updated.
            if clock.tick(|| chip.cycle()) && chip.should_draw() {
                window.request_redraw();
            }
        }
        _ => (),
    });
}
