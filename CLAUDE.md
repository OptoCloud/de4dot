# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

de4dot is a .NET deobfuscator and unpacker (GPLv3). It detects which obfuscator was used, then applies obfuscator-specific and generic deobfuscation passes (string decryption, control flow restoration, proxy method removal, symbol renaming, etc.). It uses [dnlib](https://github.com/0xd4d/dnlib/) for reading and writing .NET assemblies.

## Build Commands

Two solution files exist — one per target framework:

```bash
# .NET 8 (primary development target)
dotnet build -c Release de4dot.netcore.sln

# .NET Framework 4.8
dotnet build -c Release -f net48 de4dot.netframework.sln

# Full release build (both targets, via build.ps1)
pwsh build.ps1

# Run IL-based inlining tests (requires ilasm/ildasm on PATH)
pwsh test.ps1
```

There is no unit test project (xUnit/NUnit/MSTest). The only automated tests are IL-based integration tests in `tests/samples/inlining/` that assemble IL, run de4dot on it, then disassemble the output.

## Architecture

### Project dependency graph

```
de4dot (exe) → de4dot.cui → de4dot.code → de4dot.blocks
                                         → de4dot.mdecrypt
                                         → AssemblyData
de4dot.mcp (MCP server) → de4dot.cui
```

### Key projects

- **de4dot.blocks** — IL basic block representation (`Block`, `Blocks`, `MethodBlocks`) and control-flow deobfuscation (`cflow/`). Foundation layer; has no project references, only depends on dnlib.
- **de4dot.code** — Core deobfuscation logic: the `ObfuscatedFile` pipeline, all obfuscator-specific deobfuscators under `deobfuscators/`, the symbol `renamer/`, string inlining, and assembly client infrastructure for dynamic decryption.
- **de4dot.cui** — CLI entry point. `FilesDeobfuscator` orchestrates the full pipeline: detect → deobfuscate → rename → save. `Program.cs` registers all `IDeobfuscatorInfo` implementations.
- **de4dot.mdecrypt** — Method decryption helpers.
- **AssemblyData** — Runs in a separate process to dynamically invoke string decrypter methods in the target assembly (delegate-based or emulated). Communicates via remoting/.NET hosting.
- **de4dot.mcp** — Model Context Protocol (MCP) server exposing deobfuscation as tools/resources for AI agents.

### Deobfuscation pipeline

1. **Detection** — Each `IDeobfuscatorInfo` creates an `IDeobfuscator` that is `Initialize`d with the module and calls `Detect()` returning a confidence score. Highest score wins.
2. **Module decryption** — `GetDecryptedModule()` handles packed/encrypted assemblies; if it returns data, the module is reloaded via `ModuleReloaded()`.
3. **Deobfuscation passes** — `DeobfuscateBegin()` → per-method `DeobfuscateMethodBegin/Strings/End` (operating on `Blocks`) → `DeobfuscateEnd()`.
4. **String decryption** — Static (`StaticStringInliner`) or dynamic (`DynamicStringInliner` via `AssemblyData` subprocess). The `StringInlinerBase` replaces call instructions with `ldstr`.
5. **Symbol renaming** — `Renamer` in `de4dot.code/renamer/` renames types/methods/fields/etc. across all assemblies being processed together.
6. **Save** — Module written back via dnlib's `ModuleWriter`/`NativeModuleWriter`.

### Adding a new deobfuscator

Each obfuscator lives in `de4dot.code/deobfuscators/<Name>/` and needs:
1. `DeobfuscatorInfo` class implementing `IDeobfuscatorInfo` (factory + options)
2. `Deobfuscator` class extending `DeobfuscatorBase` (detection + deobfuscation logic)
3. Registration in `de4dot.cui/Program.cs` → `CreateDeobfuscatorInfos()`

Deobfuscators can also be loaded as plugins from a `bin/` directory adjacent to the executable via reflection (any DLL exporting `IDeobfuscatorInfo`).

### Shared build configuration

`De4DotCommon.props` sets target framework, language version, signing, and output path for all projects. `Directory.Packages.props` manages centralized NuGet package versions (dnlib 3.6.0).

## Key dnlib types used throughout

- `ModuleDefMD` — the loaded .NET module
- `TypeDef`, `MethodDef`, `FieldDef` — metadata definitions
- `Instruction` / `OpCodes` — IL instructions
- `IPEImage` — PE file access for native unpacking
