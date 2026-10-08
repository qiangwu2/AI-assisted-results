#!/usr/bin/env python3
"""Check every source in dependency order, with independent branches in parallel."""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import hashlib
import os
import re
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
os.chdir(root)
stage = root / '.lake' / 'verification-stage'
stage.mkdir(parents=True, exist_ok=True)
build = root / '.lake' / 'build' / 'lib' / 'lean'
(build / 'SpinGlass').mkdir(parents=True, exist_ok=True)
sources = {f'SpinGlass.{p.stem}': p for p in (root / 'SpinGlass').glob('*.lean')}
def imports(path):
    return [item for line in path.read_text().splitlines()
            if re.match(r'^import\s+', line) for item in line.split()[1:]]
listed = [m for m in imports(root / 'SpinGlass.lean') if m.startswith('SpinGlass.')]
if len(listed) != len(set(listed)) or set(listed) != set(sources):
    sys.exit('ERROR: aggregate imports must include every project module exactly once')
deps = {name: {m for m in imports(path) if m.startswith('SpinGlass.')} for name, path in sources.items()}
seen = set()
for name in listed:
    if not deps[name] <= seen:
        sys.exit(f'ERROR: missing or out-of-order imports for {name}: {deps[name] - seen}')
    seen.add(name)
tracked = list(sources.values()) + [root / p for p in ('SpinGlass.lean', 'SemanticChecks.lean', 'Audit.lean',
    'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'scripts/check_sources.py', 'scripts/check_sources.sh')]
def fingerprints():
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in tracked}
before = fingerprints()
subprocess.run(['lean', '--version'], check=True)

def compile_module(name):
    stem = name.removeprefix('SpinGlass.')
    out = stage / stem
    result = subprocess.run(['lean', '-o', str(out.with_suffix('.olean')),
        '-i', str(out.with_suffix('.ilean')), str(sources[name].relative_to(root))],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode == 0:
        for suffix in ('.olean', '.ilean'):
            out.with_suffix(suffix).replace(build / 'SpinGlass' / (stem + suffix))
    return result

pending = set(listed)
finished = set()
workers = max(1, min(4, int(os.environ.get('LEAN_VERIFY_JOBS', '3'))))
print(f'Checking {len(sources)} modules from source; at most {workers} independent jobs.', flush=True)
with ThreadPoolExecutor(max_workers=workers) as pool:
    running = {}
    while pending or running:
        for name in listed:
            if len(running) >= workers:
                break
            if name in pending and deps[name] <= finished:
                pending.remove(name)
                running[pool.submit(compile_module, name)] = name
        if not running:
            sys.exit('ERROR: cyclic or missing project dependency')
        done, _ = wait(running, return_when=FIRST_COMPLETED)
        for future in done:
            name = running.pop(future)
            result = future.result()
            print(f'Checking {name}: {"PASS" if result.returncode == 0 else "FAIL"}', flush=True)
            if result.stdout:
                print(result.stdout, end='' if result.stdout.endswith('\n') else '\n', flush=True)
            if result.returncode:
                sys.exit(result.returncode)
            finished.add(name)

subprocess.run(['lean', '-o', str(stage / 'SpinGlass.olean'), '-i', str(stage / 'SpinGlass.ilean'), 'SpinGlass.lean'], check=True)
for suffix in ('.olean', '.ilean'):
    (stage / ('SpinGlass' + suffix)).replace(build / ('SpinGlass' + suffix))
subprocess.run(['lean', 'SemanticChecks.lean'], check=True)
subprocess.run(['lean', 'Audit.lean'], check=True)
if before != fingerprints() or set(sources.values()) != set((root / 'SpinGlass').glob('*.lean')):
    sys.exit('ERROR: sources changed during verification; a stable rebuild is required')
print('SOURCE VERIFICATION PASSED: all modules rebuilt; source snapshot unchanged.', flush=True)
