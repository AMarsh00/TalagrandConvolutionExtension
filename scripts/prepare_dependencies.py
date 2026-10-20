#!/usr/bin/env python3
"""Fetch the pinned Boolean development and apply its warning fixes."""

from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
DEPENDENCY = ROOT / ".lake/packages/TalagrandConvConjecture"
REVISION = "6488afd9f5f94f40766c6915c6e4e4f8de15ada7"
UPSTREAM = "https://github.com/junwei-lu/TalagrandConvolutionConjecture.git"
PATCH = ROOT / "patches/boolean-lean-4.29.1.patch"


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess:
    result = subprocess.run(
        ["git", "-C", str(DEPENDENCY), *args],
        capture_output=True, text=True,
    )
    if check and result.returncode:
        raise SystemExit(result.stderr.strip() or result.stdout.strip())
    return result


def main() -> None:
    if not DEPENDENCY.is_dir():
        DEPENDENCY.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "init", "--initial-branch=main", str(DEPENDENCY)], check=True)
        git("remote", "add", "origin", UPSTREAM)
        git("config", "core.autocrlf", "false")
    if not (DEPENDENCY / "lakefile.lean").is_file():
        git("fetch", "--depth", "1", "origin", REVISION)
        git("checkout", "--detach", "FETCH_HEAD")
    if git("rev-parse", "HEAD").stdout.strip() != REVISION:
        raise SystemExit("Unexpected Boolean dependency revision; no files changed.")
    if git("apply", "--reverse", "--check", str(PATCH), check=False).returncode == 0:
        print("Boolean dependency warning fixes are already applied.")
        return
    result = git("apply", "--check", str(PATCH), check=False)
    if result.returncode:
        raise SystemExit("Cannot apply dependency patch; no files changed.\n" + result.stderr)
    git("apply", str(PATCH))
    print("Applied Boolean dependency warning fixes.")


if __name__ == "__main__":
    main()
