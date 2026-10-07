#!/usr/bin/env python3
"""Measure raw searches so a total factorizer's fallback cannot mask misses."""
import argparse,hashlib,json,pathlib,platform,subprocess,time
ROOT=pathlib.Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(); p.add_argument('--algorithms',nargs='+',default=['fermat','rho','brent','pminusone','ecm','qs','auto']); p.add_argument('--tier',choices=['core','stress','all'],default='all'); p.add_argument('--timeout',type=float,default=3);p.add_argument('--output',type=pathlib.Path,default=ROOT/'results/raw-splitters.json');a=p.parse_args()
 raw=(ROOT/'data/cases.json').read_bytes();cases=[c for c in json.loads(raw) if c['factors'] is not None and len(c['factors'])>1 and (a.tier=='all' or c['tier']==a.tier)]
 records=[]
 for alg in a.algorithms:
  for c in cases:
   n=int(c['n']); t=time.perf_counter_ns();r=dict(algorithm=alg,case=c['id'],n=c['n'])
   try:
    proc=subprocess.run([str(ROOT/'.lake/build/bin/factor'),'--split',alg,str(n)],text=True,capture_output=True,timeout=a.timeout)
    r['wall_ns']=time.perf_counter_ns()-t
    if proc.returncode!=0:r.update(status='error',stderr=proc.stderr[-1000:])
    else:
     out=json.loads(proc.stdout);d=out['divisor'];r['output']=out
     if d is None:r['status']='miss'
     else:
      d=int(d);r['status']='split' if 1<d<n and n%d==0 else 'wrong'
   except subprocess.TimeoutExpired:r.update(status='timeout',wall_ns=time.perf_counter_ns()-t)
   records.append(r)
  print(json.dumps(dict(algorithm=alg,**{s:sum(r['algorithm']==alg and r['status']==s for r in records) for s in ['split','miss','wrong','timeout','error']})),flush=True)
 report=dict(dataset_sha256=hashlib.sha256(raw).hexdigest(),tier=a.tier,timeout_seconds=a.timeout,platform=platform.platform(),note='Composite cases only. split means the raw algorithm found a checked proper divisor without prime certificates or trial fallback. miss is an honest bounded search failure. No expected factor was supplied to any search.',records=records)
 report['summary']={alg:{s:sum(r['algorithm']==alg and r['status']==s for r in records) for s in ['split','miss','wrong','timeout','error']} for alg in a.algorithms}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
 if any(r['status'] in ['wrong','error'] for r in records):raise SystemExit(1)
if __name__=='__main__':main()
