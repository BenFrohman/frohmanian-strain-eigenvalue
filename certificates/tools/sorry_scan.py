#!/usr/bin/env python3
"""Scan tracked .lean files (comments and strings stripped) for sorry, admit,
native_decide and axiom declarations.

provenance/ is the archived Zenodo deposit. It is not a Lake root, it does not
compile on this pin, and it still contains sorry. It is not part of this
certificate. Every other tracked .lean file is scanned. A hit still exits 1.
"""
import re, subprocess, sys
def strip(s):
    out = []; i = 0; d = 0
    while i < len(s):
        if s.startswith('/-', i): d += 1; i += 2; continue
        if d and s.startswith('-/', i): d -= 1; i += 2; continue
        if d: i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i); i = len(s) if j < 0 else j; continue
        if s[i] == '"':
            j = i + 1
            while j < len(s) and s[j] != '"': j += 2 if s[j] == '\\' else 1
            out.append('""'); i = j + 1; continue
        out.append(s[i]); i += 1
    return ''.join(out)
# Archived deposit. Not a build root. Still contains sorry. Not certified.
SKIP_PREFIXES = ("provenance/",)
files = subprocess.check_output(['git', 'ls-files', '*.lean']).decode().split()
skipped = [f for f in files if f.startswith(SKIP_PREFIXES)]
files = [f for f in files if not f.startswith(SKIP_PREFIXES)]
print("EXCLUDED archived deposit (not built, not certified, still contains sorry):")
for f in skipped:
    print(f"  {f}")
bad = []
for f in files:
    for n, l in enumerate(strip(open(f, encoding='utf-8').read()).split('\n'), 1):
        if re.search(r'\b(sorry|admit|native_decide)\b', l) or re.match(r'\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable|public|unsafe)\s+)*axiom\s', l):
            bad.append(f'{f}:{n}: {l.strip()}')
print(f'Scanned {len(files)} tracked .lean files for sorry / admit / native_decide / axiom declarations (comments and strings ignored).')
print('\n'.join(bad) if bad else 'RESULT: 0 hits')
sys.exit(1 if bad else 0)
