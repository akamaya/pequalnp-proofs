"""Projection-based generalization of exact abstract OR-budget cuts."""
from pnp_or_budget_v1 import feasible, impossible_core


def projected_core(roots,budget,max_nodes=2000,projection_nodes=100):
    """Return (original core roots, projection mask, status).

    Intersecting every wire support in a union DAG with P preserves
    union. Empty/singleton/duplicate projected supports require no new
    OR gates. Hence infeasibility after projection is a necessary
    condition for every completion of those projected root masks.
    Never infer infeasibility from an exhausted search budget.
    """
    core,status=impossible_core(roots,budget,max_nodes)
    if core is None:return None,0,status
    P=0
    for s in core:P|=s
    # Project to the union of the roots (all other bits are irrelevant).
    # Then greedily try deleting further atoms. Retain only proven cuts.
    for i in range(P.bit_length()):
        if not P&(1<<i):continue
        trial=P^(1<<i)
        if feasible([s&trial for s in core],budget,projection_nodes) is False:
            P=trial
    # Drop duplicate/singleton projected requirements.
    unique={}
    for s in core:
        if (s&P).bit_count()>1:unique.setdefault(s&P,s)
    return tuple(unique.values()),P,False


def self_test():
    import itertools
    # Three disjoint pairs need three ORs, even if an arbitrary fourth
    # (unconstrained) atom is added to any of them.
    core,P,status=projected_core([3,12,48],2)
    assert status is False and core is not None
    assert feasible([s&P for s in core],2) is False
    # Independent complete enumeration on 4 atoms.
    atoms=frozenset(1<<i for i in range(4))
    levels=[{frozenset()}]
    for _ in range(4):
        nxt=set()
        for state in levels[-1]:
            for a,b in itertools.combinations(atoms|state,2):
                s=a|b
                if s not in atoms|state:nxt.add(state|{s})
        levels.append(nxt)
    composites=sorted(x for x in range(1,16) if x.bit_count()>1)
    checks=0
    for count in range(1,4):
        for roots in itertools.combinations(composites,count):
            for b in range(4):
                core,P,status=projected_core(roots,b)
                if core is None:continue
                assert status is False
                # Enumerate all possible completions of every projected
                # root independently using 4 atoms.
                choices=[[s for s in range(1,16) if s&P==r&P] for r in core]
                possible=[state|atoms for level in levels[:b+1] for state in level]
                for rr in itertools.product(*choices):
                    assert not any(set(rr)<=state for state in possible),(roots,b,P,rr)
                    checks+=1
    print("OR PROJECTION SELF TEST OK",checks,flush=True)


if __name__=="__main__":self_test()
