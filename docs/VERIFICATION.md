# Verification

Install [elan](https://github.com/leanprover/elan), Git, and Python 3. From the
repository root, run:

```bash
python scripts/prepare_dependencies.py
lake exe cache get
lake build --wfail
bash scripts/check.sh
```

`--wfail` makes compiler warnings fail the build. The source does not disable
linters. The dependency preparation script fetches the pinned Boolean source
and applies the checked-in source fixes; it is safe to rerun.

On Windows, or to run the checks individually, replace the final command with:

```bash
lake env lean checks/MainCheck.lean
lake env lean checks/SharpCheck.lean
lake env lean checks/AxiomsCheck.lean
```

The main theorem should report only `propext`, `Classical.choice`, and
`Quot.sound`. The full audit covers all 473 theorem/lemma declarations in
`TailBound/`; each should use a subset of those standard axioms. `#print axioms`
displays dependencies but does not itself enforce an allowlist.

## Environment

| Component | Pinned version |
| --- | --- |
| Lean | `leanprover/lean4:v4.29.1` |
| Mathlib | `v4.29.1`, commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6` |
| Boolean development | commit `6488afd9f5f94f40766c6915c6e4e4f8de15ada7`, with the patch in `patches/` |

`lake-manifest.json` records Lake's dependencies. The Boolean revision is pinned
by `scripts/prepare_dependencies.py` and registered as a local dependency so the
intentional patch does not produce a dirty-checkout warning. See
[patches/README.md](../patches/README.md).

The [GitHub workflow](../.github/workflows/lean.yml) prepares these dependencies,
uses the standard Lean action and Mathlib cache, builds with `--wfail`, and runs
the three check files. It sets `LEAN_NUM_THREADS=1` to limit memory use on the
runner. It does not restore an entire `.lake` cache over the prepared sources.

## Recorded checks

The [verification records](../verification/README.md) contain build output,
theorem statements, axiom dependencies, and source hashes. Generated build
artifacts and downloaded packages are excluded from the source archive.

The local container required a small `readlink` compatibility shim, retained
with the verification record. It resolves the current executable path and does
not modify Lean or its kernel. Ordinary installations and GitHub CI do not use it.
