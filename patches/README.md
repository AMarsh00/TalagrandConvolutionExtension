# Dependency warning fixes

`boolean-lean-4.29.1.patch` contains source-level linter and deprecation fixes
for the Boolean development at commit
`6488afd9f5f94f40766c6915c6e4e4f8de15ada7`.

It updates deprecated tactics, removes unused parameters and simp arguments,
makes tactic sequencing explicit, and replaces broad Mathlib imports with focused
imports. It preserves the mathematical conclusions
and does not disable warnings.

Before downloading the Mathlib cache, run:

```bash
python scripts/prepare_dependencies.py
```

The script fetches the exact revision, checks it, and applies the patch. It
recognizes an already-applied patch and refuses conflicting local edits.
The patched source is registered as a local Lake dependency, avoiding an
intentional dirty-checkout warning. CI prepares the same source before building.
