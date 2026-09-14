#!/usr/bin/env python3
"""Exact *Python* audit of the generated Lean data and finite arithmetic.
This is an independent consistency check, NOT a substitute for compiling Lean.
"""
from __future__ import annotations
import csv
import hashlib
import json
import re
from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
A, B = F(1158423, 10**6), F(1158424, 10**6)
MINPOLY = (-1,-6,-11,-1,10,3)


def lower(p):
    return sum((c * (A if c >= 0 else B)**i for i,c in enumerate(p)), F(0))


def times_t(p):
    return (p[4]/3, p[0]+2*p[4], p[1]+11*p[4]/3,
            p[2]+p[4]/3, p[3]-10*p[4]/3)


def remainder(p):
    p=list(map(F,p))
    while len(p)>5:
        coefficient=p.pop()/3
        shift=len(p)-5
        for j in range(5):
            p[shift+j]-=coefficient*MINPOLY[j]
    return tuple(p+[F(0)]*(5-len(p)))


def main():
    text=(ROOT/'ThreeStep/Data.lean').read_text(encoding='utf-8')
    poly_text, index_text=text.split('def weightIndex',1)
    matches=re.findall(r'!\[([\d,\s-]+)\],?\s*-- w(\d+)',poly_text)
    if len(matches)!=139 or [int(n) for _,n in matches]!=list(range(1,140)):
        raise ValueError('Incorrect polynomial dictionary')
    polys=[tuple(F(c.strip()) for c in entry.split(',')) for entry,_ in matches]
    grids=re.findall(r'!\[([\d,\s]+)\]',index_text)
    if len(grids)!=48:
        raise ValueError('Incorrect lookup grids')
    indices=[int(x) for row in grids for x in row.split(',')]
    if len(indices)!=384 or not all(0<=i<139 for i in indices):
        raise ValueError('Incorrect state-to-polynomial mapping')
    weights=[polys[i] for i in indices]
    with (ROOT/'data/three_step_weights.csv').open(newline='') as f:
        rows=list(csv.DictReader(f))
    canonical=[tuple(F(r[f'c{i}']) for i in range(5)) for r in rows]
    if weights!=canonical:
        raise ValueError('Lean weights differ from the canonical appendix CSV')
    # Independent check of the reduction formula on a basis of Q[T]_{<=4}.
    for i in range(5):
        p=tuple(F(int(i==j)) for j in range(5))
        if times_t(p)!=remainder((0,)+p):
            raise ValueError('Multiplication-by-t formula is incorrect')
    if not all(lower(p)>0 for p in weights):
        raise ValueError('A state weight has no positive lower bound')

    stats=Counter()
    reduced_slacks=[]
    records=[]
    for h,U,L in product(range(6),range(8),range(8)):
        i=64*h+8*U+L
        # h ordering is exactly the six histories in the paper.
        old_blue=int(h>=2); old_red=h%2
        blue_head=U//4; red_head=L//4
        allowed=(h<4 or red_head==0)
        pb=0 if blue_head==0 else (2 if old_blue==0 else 1)
        pr=0 if red_head==0 else (2 if old_red==0 else 1)
        for nb,nr in product(range(2),repeat=2):
            j=64*(4*blue_head+old_red)+8*((2*U+nb)%8)+L
            k=64*(2*old_blue+red_head)+8*U+((2*L+nr)%8)
            # Simulate the short reduced operations used in the Lean file.
            w=weights[i]
            p=[v+u for v,u in zip(w,times_t(w))]
            for target,power in ((j,pb),(k,pr)) if allowed else ((j,pb),):
                charge=weights[target]
                for _ in range(power):
                    charge=times_t(charge)
                p=[a-b for a,b in zip(p,charge)]
            p=tuple(p)
            # Independently assemble degree-six raw slack and divide by m.
            raw=[F(0)]*7
            for degree,c in enumerate(w):
                raw[degree]+=c; raw[degree+1]+=c
            for target,power in ((j,pb),(k,pr)) if allowed else ((j,pb),):
                for degree,c in enumerate(weights[target]):
                    raw[degree+power]-=c
            if remainder(raw)!=p:
                raise ValueError(f'Reduction mismatch at {i,nb,nr}')
            bound=lower(p)
            if bound<0 or (any(p) and bound<=0):
                raise ValueError(f'Uncertified slack at {i,nb,nr}')
            stats['zero' if not any(p) else 'positive']+=1
            reduced_slacks.append(p)
            records.append({'state_id':f'q{i+1:03d}',
                            'new_blue':('Bo','B')[nb], 'new_red':('Ro','R')[nr],
                            'blue_target':f'q{j+1:03d}',
                            'red_target':f'q{k+1:03d}' if allowed else '',
                            **{f'c{degree}':str(c) for degree,c in enumerate(p)}})
    expected=ROOT/'checks/python-verification/all_1536_inequalities.csv'
    if expected.exists():
        with expected.open(newline='') as f:
            previous=list(csv.DictReader(f))
        if len(previous)!=len(records):
            raise ValueError('Reference case count mismatch')
        for new,old in zip(records,previous):
            if any(new[key]!=old[key] for key in new):
                raise ValueError(f'Reference mismatch at {new["state_id"]}')
    if stats!=Counter(zero=514,positive=1022):
        raise ValueError(f'Unexpected totals {stats}')
    report={'audit':'PASS: exact Python arithmetic and data consistency',
            'lean_compilation':'NOT RUN; this report does not certify Lean elaboration',
            'states':384, 'inequalities':len(records), **stats,
            'distinct_weights':len(set(weights)),
            'distinct_slacks':len(set(reduced_slacks)),
            'canonical_csv_sha256':hashlib.sha256((ROOT/'data/three_step_weights.csv').read_bytes()).hexdigest()}
    (ROOT/'checks/python_arithmetic_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
