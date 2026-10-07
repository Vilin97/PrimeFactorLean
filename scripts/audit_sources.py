#!/usr/bin/env python3
"""Source hygiene complements the kernel axiom-closure audit in Tests.Audit."""
import pathlib,re
ROOT=pathlib.Path(__file__).resolve().parents[1]
def uncomment(s):
 out=[];i=0;depth=0;quoted=False
 while i<len(s):
  if depth:
   if s[i:i+2]=='/-':depth+=1;i+=2
   elif s[i:i+2]=='-/':depth-=1;i+=2
   else:i+=1
  elif quoted:
   if s[i]=='\\':i+=2
   elif s[i]=='"':quoted=False;i+=1
   else:i+=1
  elif s[i:i+2]=='/-':depth=1;i+=2
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j==-1 else j
  elif s[i]=='"':quoted=True;i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
for folder in ['PrimeFactorLean','Tests']:
 for p in (ROOT/folder).glob('*.lean'):
  bad=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|partial|implemented_by)\b',uncomment(p.read_text()))
  if bad:raise SystemExit(f'{p}: prohibited escape hatches: {bad}')
print('PASS source hygiene: no proof escape hatches in project modules/tests.')
