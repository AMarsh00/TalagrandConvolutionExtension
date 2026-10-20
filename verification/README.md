# Verification records

The [20 October 2026 snapshot](2026-10-20/) records checks of the cleaned source.

| File | Contents |
| --- | --- |
| `build.log` | Full project build with warnings treated as errors. |
| `main.log` | Main theorem, underlying definitions, and axiom dependencies. |
| `sharp.log` | Explicit band-estimate statements, constants, and axioms. |
| `axioms.log` | Axiom dependencies for all 473 theorem/lemma declarations. |
| `toolchain.txt` | Lean version used for these checks. |
| `summary.json` | Commands, source counts, and verification results. |
| `source-sha256.txt` | SHA-256 hashes of the distributed source and configuration. |
| `environment/proc_self.c` | Executable-path compatibility shim used in this container. |

Follow the [verification guide](../docs/VERIFICATION.md) to reproduce the checks.
The records are from a local run, but we have also had GitHub complete the lean build. This can be found in the Actions tab.
