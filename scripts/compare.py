#!/usr/bin/env python3
"""Head-to-head timings: the verified Lean CLI against YAFU and CADO-NFS.

Every timed run is an end-to-end process invocation on an input from
data/cases.json, with the same thread budget for every tool. Runs are
serialized through an exclusive flock on a lock file shared with the other
benchmark jobs on this machine; the lock is acquired before the clock starts.
Repeats are interleaved (A B A B ...) to spread drift over all tools. Each
output is checked against the reference factorization; a wrong or missing
answer is recorded as such, never as a time.

Records are appended to a JSONL file as they complete (resumable). Use
`--report` to aggregate a JSONL file into per-tier tables.
"""
import argparse, fcntl, hashlib, json, os, pathlib, platform, re, shutil, statistics
import subprocess, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parents[1]
BASE = ROOT / 'baselines'
PREFIX = BASE / 'prefix/usr'
YAFU = BASE / 'src/yafu/yafu'
CADO = BASE / 'build/cado-nfs/cado-nfs.py'
LEAN = ROOT / '.lake/build/bin/factor'
TIMEOUTS = {'core': 60, 'medium': 120, 'large': 600, 'huge': 7200, 'challenge': 86400}
TIERS = ['core', 'medium', 'large', 'huge', 'challenge']


def env_for(tool):
    env = dict(os.environ)
    env['LD_LIBRARY_PATH'] = str(PREFIX / 'lib/x86_64-linux-gnu')
    env['PYTHONPATH'] = str(PREFIX / 'lib/python3/dist-packages')
    return env


def parse_yafu(out):
    """Factors printed by YAFU after '***factors found***' (None for n = 0)."""
    if '***factors found***' not in out:
        return 'missing'
    tail = out.split('***factors found***', 1)[1]
    factors = []
    for line in tail.splitlines():
        m = re.match(r'^(P|PRP|C|Q)(\d+) = (\d+)\s*$', line.strip())
        if m:
            if m.group(1) == 'C':
                if m.group(3) == '0':
                    return None
                return 'composite'
            factors.append(int(m.group(3)))
        elif line.startswith('ans =') or line.startswith('eof'):
            break
    return sorted(factors)


def run_tool(tool, n, threads, timeout, lean=LEAN):
    """Run one tool on n; returns (wall_ns, factors | None | error string, raw tail)."""
    work = tempfile.mkdtemp(prefix=f'cmp-{tool}-')
    try:
        if tool.startswith('lean-'):
            alg = tool[len('lean-'):]
            cmd, stdin = [str(lean), '--threads', str(threads), alg, n], None
        elif tool in ('yafu', 'yafu-siqs'):
            fn = 'factor' if tool == 'yafu' else 'siqs'
            cmd, stdin = [str(YAFU), '-threads', str(threads)], f'{fn}({n})\n'
        elif tool == 'cado':
            cmd = [sys.executable, str(CADO), n, '-t', str(threads), '--workdir', work + '/w']
            stdin = None
        else:
            raise ValueError(tool)
        start = time.perf_counter_ns()
        proc = subprocess.run(cmd, input=stdin, text=True, capture_output=True, cwd=work,
                              env=env_for(tool), timeout=timeout)
        wall = time.perf_counter_ns() - start
        out = proc.stdout
        if proc.returncode != 0 and tool != 'yafu' and tool != 'yafu-siqs':
            return wall, f'exit {proc.returncode}', (out + proc.stderr)[-2000:]
        if tool.startswith('lean-'):
            data = json.loads(out)
            fs = data.get('factors')
            return wall, (None if fs is None else sorted(map(int, fs))), ''
        if tool in ('yafu', 'yafu-siqs'):
            return wall, parse_yafu(out), out[-2000:]
        # cado: the last line lists the factors
        lines = [l for l in out.strip().splitlines() if l.strip()]
        if not lines:
            return wall, 'missing', (out + proc.stderr)[-2000:]
        return wall, sorted(int(x) for x in lines[-1].split()), ''
    except subprocess.TimeoutExpired:
        return None, 'timeout', ''
    finally:
        shutil.rmtree(work, ignore_errors=True)


def expected_for(case, tool):
    """Reference answer; CADO-NFS splits into the factors NFS finds, which for the
    semiprime inputs it is used on is the complete factorization."""
    if case['factors'] is None:
        return None
    return sorted(map(int, case['factors']))


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--tools', nargs='+', default=['lean-auto', 'yafu'])
    p.add_argument('--tiers', nargs='+', default=TIERS)
    p.add_argument('--cases', nargs='*', help='restrict to these case ids')
    p.add_argument('--categories', nargs='*', help='restrict to these categories')
    p.add_argument('--min-digits', type=int, default=0)
    p.add_argument('--max-digits', type=int, default=10 ** 9)
    p.add_argument('--repeats', type=int, default=3)
    p.add_argument('--threads', type=int, default=16)
    p.add_argument('--timeout', type=float, help='override per-tier timeouts (seconds)')
    p.add_argument('--lock', default='/tmp/vas-timed-benchmarks.lock')
    p.add_argument('--jsonl', type=pathlib.Path, required=True)
    p.add_argument('--lean', type=pathlib.Path, default=LEAN,
                   help='the factor binary (copy it first if you keep building)')
    a = p.parse_args()
    raw = (ROOT / 'data/cases.json').read_bytes()
    cases = [c for c in json.loads(raw) if c['tier'] in a.tiers
             and a.min_digits <= c['digits'] <= a.max_digits]
    if a.cases:
        cases = [c for c in cases if c['id'] in set(a.cases)]
    if a.categories:
        cases = [c for c in cases if c['category'] in set(a.categories)]
    done = {}
    if a.jsonl.exists():
        for line in a.jsonl.read_text().splitlines():
            r = json.loads(line)
            done[(r['tool'], r['case'], r['repeat'])] = r
    a.jsonl.parent.mkdir(parents=True, exist_ok=True)
    meta = dict(dataset_sha256=hashlib.sha256(raw).hexdigest(), threads=a.threads,
                platform=platform.platform(), host=platform.node(),
                lean_binary_sha256=hashlib.sha256(a.lean.read_bytes()).hexdigest()[:16])
    lockf = open(a.lock, 'a')
    with a.jsonl.open('a') as out:
        for case in cases:
            timeout = a.timeout or TIMEOUTS[case['tier']]
            for rep in range(a.repeats):
                for tool in a.tools:
                    if (tool, case['id'], rep) in done:
                        continue
                    fcntl.flock(lockf, fcntl.LOCK_EX)
                    try:
                        wall, result, tail = run_tool(tool, case['n'], a.threads, timeout, a.lean)
                    finally:
                        fcntl.flock(lockf, fcntl.LOCK_UN)
                    exp = expected_for(case, tool)
                    if isinstance(result, str):
                        status = result if result in ('timeout',) else 'error'
                    else:
                        status = 'pass' if result == exp else 'wrong'
                    rec = dict(tool=tool, case=case['id'], tier=case['tier'],
                               category=case['category'], digits=case['digits'],
                               repeat=rep, status=status, wall_ns=wall,
                               time=time.strftime('%Y-%m-%dT%H:%M:%S'), **meta)
                    if status != 'pass':
                        rec['detail'] = (result if isinstance(result, str) else
                                         [str(x) for x in result] if result else result)
                        rec['tail'] = tail[-1500:]
                    out.write(json.dumps(rec) + '\n')
                    out.flush()
                    w = f'{wall / 1e9:.3f}s' if wall else '-'
                    print(f"{case['id']:<36} {tool:<12} rep {rep} {status:<7} {w}", flush=True)


if __name__ == '__main__':
    main()
