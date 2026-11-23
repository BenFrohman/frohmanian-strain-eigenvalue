#!/usr/bin/env bash
# Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
# Author: Benjamin Stanley Frohman
# Report #print axioms for the main theorems, and report (not fail on)
# sorry tokens while this file is a skeleton. If the Lean sources contain
# no sorry, enforce a zero-sorry check. admit / native_decide / new axioms
# still fail the job.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== sorry / forbidden-token report =="
# Every tracked .lean file; no exclusion list. The same check as certificates/tools/sorry_scan.py.
python3 certificates/tools/sorry_scan.py

if git ls-files '*.lean' | xargs grep -nE '\b(admit|native_decide|implemented_by)\b|^\s*(axiom|unsafe|opaque)\b'; then
  echo "FAIL: admit/native_decide/axiom/unsafe/opaque/implemented_by found"
  exit 1
fi
echo "OK: no admit/native_decide/new axiom/unsafe/opaque/implemented_by"

echo "== #print axioms =="
out="$(lake env lean scripts/PrintAxioms.lean 2>&1)"
echo "$out"
expected="$(grep -c '^#print axioms' scripts/PrintAxioms.lean)"
got="$(printf '%s\n' "$out" | grep -cE "depends on axioms|does not depend on any axioms" || true)"
if [ "$got" -ne "$expected" ]; then
  echo "FAIL: expected ${expected} axiom reports, got ${got}"
  exit 1
fi
# Fail on Lean errors, but not on sorryAx (expected in a skeleton with sorry).
if printf '%s\n' "$out" | grep -v sorryAx | grep -qiE 'error:'; then
  echo "FAIL: errors in axiom audit"
  exit 1
fi
echo "OK: axiom reports printed for all listed declarations."
