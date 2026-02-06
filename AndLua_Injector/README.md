# AndLua+ Samurai Injector (Non-Root Debuggable)

This project is an injector for AndLua+ designed to search and modify memory of other Android applications in a non-root environment using the `debuggable` feature.

## Features
- **Auto Start Game**: Automatically launches the target package using Android Intents.
- **Floating Mod Menu**: A draggable floating icon that provides on-the-fly cheats while in-game.
- **Plot Armor**: Automated group search and edit for invincibility (searches for pattern `8;2;0;65536;1:17` and edits `65536` to `-1`).
- **Java Heap Search**: Specifically targets Java Heap (dalvik-main) regions.
- **GG-Style UI**: Familiar Game Guardian-like interface.

## Requirements
1. **AndLua+ IDE**: Must be installed.
2. **Overlay Permission**: Required for the Floating Mod Menu.
3. **Debuggable Target**: The target application must have `android:debuggable="true"`.

## Project Structure
- `main.lua`: Entry point, handles permissions and starts game/service.
- `float.lua`: Floating mod menu service.
- `layout.aly`: Main UI layout.
- `layout_float.aly`: Floating menu UI layout.
- `MemoryTools.lua`: Core memory manipulation library with Group Search support.

## How to Use
1. Enter the package name in the main app.
2. Click **START GAME**.
3. Accept the **Overlay Permission** prompt if it appears.
4. Once the game starts, a red "S" icon will appear on the left.
5. Drag the "S" icon to move it.
6. Click the "S" icon to open the Mod Menu.
7. Toggle **Plot Armor** to activate the cheat.

## Group Search Logic
The `MemoryTools:groupSearch` function implements proximity-based searching. It scans memory chunks, finds anchor values, and validates that the remaining group values exist within the specified byte range (`proximity`).

---
*Created by Jules for HAISE39*
