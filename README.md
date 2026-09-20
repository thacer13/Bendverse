# Bendverse

Bendverse is a machine-checked reference engine for scalable falling-sand
cellular simulation; every scaling property is stated in `LAWS.bend` and checked
by `PROOF.bend`.

## Build

    mkdir -p bin
    bend runners/view3d.bend -o bin/view3d

Build the native binary. The JS interpreter is too slow for the tick loop.

## Run

    ./bin/view3d

Opens a 1920×1080 window.

## Controls

| Input | Action |
|---|---|
| `W` / `S` | fly forward / backward |
| `A` / `D` | strafe left / right |
| `Q` / `E`, `←` / `→` | turn left / right |
| `↑` / `↓` | pitch up / down |
| `R` / `F` | rise / sink |
| mouse drag | look |
| `space` | pause / resume |
| `-` / `=`, `[` / `]` | simulation speed down / up |
| `,` / `.` | render depth down / up |
| close window | quit |

Render depth is the quality/speed dial, range 5–8. Lower is faster and chunkier.

## 2D sandbox

    bend runners/window.bend -o bin/window
    ./bin/window

| Input | Action |
|---|---|
| left mouse | paint sand at cursor |
| right mouse | paint rock at cursor |
| `E` | erase at cursor |
| `space` | pause / resume |
| close window | quit |
