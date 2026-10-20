#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

for check in MainCheck SharpCheck AxiomsCheck; do
  lake env lean "checks/${check}.lean"
done
