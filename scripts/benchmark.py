#!/usr/bin/env python3
"""Run compiled Lean algorithms; all successful rows must match the oracle.

Timeouts are recorded as failures to finish, never counted as correct results.
Timing includes process startup; wall clock and in-program nanoseconds are kept
separate. Runs use the same explicit cases for every requested algorithm.
"""
import argparse, hashlib, json, os, pathlib, platform, statistics, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parents[1]
def run():
 p=argparse.ArgumentParser()
 p.add_argument('--algorithms',nargs='+',default=['trial','fermat','rho','brent','pminusone','ecm','qs','auto'])
 p.add_argument('--tier',choices=['core','stress','all'],default='core')
 p.add_argument('--timeout',type=float,default=10)
 p.add_argument('--repeat',type=int,default=1)
 p.add_argument('--limit',type=int)
 p.add_argument('--output',type=pathlib.Path,default=ROOT/'results/benchmark.json')
 p.add_argument('--binary',type=pathlib.Path,default=ROOT/'.lake/build/bin/factor')
 a=p.parse_args()
 raw=(ROOT/'data/cases.json').read_bytes(); cases=json.loads(raw)
 cases=[c for c in cases if a.tier=='all' or c['tier']==a.tier]
 if a.limit is not None: cases=cases[:a.limit]
 records=[]
 for alg in a.algorithms:
  for c in cases:
   for rep in range(a.repeat):
    t=time.perf_counter_ns()
    r=dict(algorithm=alg,case=c['id'],n=c['n'],repeat=rep)
    try:
     proc=subprocess.run([str(a.binary),alg,c['n']],text=True,capture_output=True,timeout=a.timeout)
     r['wall_ns']=time.perf_counter_ns()-t
     if proc.returncode != 0:
      r.update(status='error',exit_code=proc.returncode,stderr=proc.stderr[-1000:])
     else:
      out=json.loads(proc.stdout)
      actual=out.get('factors')
      actual=None if actual is None else sorted(map(int,actual))
      expected=None if c['factors'] is None else list(map(int,c['factors']))
      r.update(status='pass' if actual==expected else 'wrong',output=out)
    except subprocess.TimeoutExpired:
     r.update(status='timeout',wall_ns=time.perf_counter_ns()-t)
    except Exception as e:
     r.update(status='error',error=str(e))
    records.append(r)
  group=[r for r in records if r['algorithm']==alg]
  counts={s:sum(r['status']==s for r in group) for s in ['pass','wrong','timeout','error']}
  print(json.dumps(dict(algorithm=alg,**counts)),flush=True)
 report=dict(dataset_sha256=hashlib.sha256(raw).hexdigest(),tier=a.tier,timeout_seconds=a.timeout,repeats=a.repeat,platform=platform.platform(),processor=platform.processor(),python=platform.python_version(),timing_note='Wall time includes process startup. elapsedNs measures Lean algorithm only. Each factor output must equal the independently produced dataset oracle.',records=records)
 report['summary']={alg:dict(passed=sum(r['status']=='pass' for r in records if r['algorithm']==alg),total=sum(r['algorithm']==alg for r in records),median_wall_ns=statistics.median([r['wall_ns'] for r in records if r['algorithm']==alg and r['status']=='pass']) if any(r['algorithm']==alg and r['status']=='pass' for r in records) else None) for alg in a.algorithms}
 a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_text(json.dumps(report,indent=2)+'\n')
 if any(r['status']=='wrong' for r in records): raise SystemExit(1)
 if any(r['status'] in ('error','timeout') for r in records): raise SystemExit(2)
if __name__=='__main__':run()
