# Verification records

The [17 October 2026 snapshot](2026-10-17/) retains the original verification outputs unchanged:

| File | Contents |
| --- | --- |
| `verification-build.log` | Project build output. |
| `verification-main.log` | Main theorem, underlying definitions, and axiom footprint. |
| `verification-sharp.log` | Explicit band-estimate statements, constants, and axioms. |
| `verification-axioms.log` | Axiom dependencies for 477 lemma/theorem declarations. |
| `verification-summary.json` | Toolchain and verification summary. |
| `environment/proc_self.c` | Compatibility shim used only in the original container. |

These are historical records from the supplied source archive. For a fresh run of the current layout, follow [the verification guide](../docs/VERIFICATION.md).
