# Verification

Install [elan](https://github.com/leanprover/elan) and work from the repository root:

```bash
lake exe cache get
lake build
bash scripts/check.sh
```

`scripts/check.sh` runs the three Lean entry points in `checks/`. It exits on the first command failure. The commands can also be run individually:

```bash
lake env lean checks/MainCheck.lean
lake env lean checks/SharpCheck.lean
lake env lean checks/AxiomsCheck.lean
```

The main theorem should report only `propext`, `Classical.choice`, and `Quot.sound`. Each declaration in the full audit should use a subset of these standard axioms. `#print axioms` displays the dependency information; it does not itself enforce an allowlist.

## Environment

| Component | Pinned version |
| --- | --- |
| Lean | `leanprover/lean4:v4.29.1` |
| Mathlib | `v4.29.1`, commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6` |
| Boolean development | commit `6488afd9f5f94f40766c6915c6e4e4f8de15ada7` |

The checked-in `lake-manifest.json` records the complete dependency revisions. Keep it with the source when reproducing the build. Local Lake downloads and compiled artifacts are excluded by `.gitignore`.

## GitHub checks

[lean.yml](../.github/workflows/lean.yml) uses the standard [Lean action](https://github.com/leanprover/lean-action) to restore dependencies and build the project. It then runs the three check files on each push, pull request, or manual dispatch. The workflow uses the repository's pinned toolchain and manifest.

## Retained records

[verification/2026-10-17](../verification/2026-10-17/) contains the original build, main-theorem, band-estimate, and axiom-audit outputs. These records describe the supplied proof snapshot, before the documentation and directory cleanup. They are not a new run of this GitHub layout.

The cleanup preserves every Lean declaration and proof, all proof-module import paths, and the dependency configuration. The three check files have moved into `checks/`, and historical commentary has been updated. The source archive's old checksum file was omitted because it describes the previous file layout.

The recorded container build used a `readlink` compatibility shim, retained in [environment/proc_self.c](../verification/2026-10-17/environment/proc_self.c). Ordinary Lean installations do not require it; the GitHub workflow does not enable it.
