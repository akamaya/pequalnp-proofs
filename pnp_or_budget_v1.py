"""Bounded exact abstract OR-union DAG feasibility. None means unknown."""
from functools import lru_cache


@lru_cache(maxsize=256)
def decompositions(s):
    """Sets of composite children of all two-way proper unions of s."""
    out=set()
    a=(s-1)&s
    while a:
        missing=s^a
        t=(a-1)&a
        while True:
            b=missing|t
            if a<b:
                out.add(tuple(sorted(x for x in (a,b) if x.bit_count()>1)))
            if not t:break
            t=(t-1)&a
        a=(a-1)&s
    return tuple(sorted(out,key=lambda x:(len(x),x)))


def feasible(roots,budget,max_nodes=2000,max_bits=6):
    """True: an abstract union DAG exists. False: proven impossible.
    Ignore actual graph/junk dependencies, Lambda and timing constraints.
    Singleton atoms are free; each distinct composite mask costs one OR.
    """
    roots=frozenset(x for x in roots if x.bit_count()>1)
    if len(roots)>budget or any(x.bit_count()>budget+1 for x in roots):
        return False
    if any(x.bit_count()>max_bits for x in roots):return None
    seen={}
    nodes=0
    def search(state):
        nonlocal nodes
        if state in seen:return seen[state]
        if nodes>=max_nodes:return None
        nodes+=1
        room=budget-len(state)
        best=None
        for s in sorted(state):
            options=[]
            already=False
            for pair in decompositions(s):
                add=frozenset(pair)-state
                if not add:
                    already=True
                    break
                if len(add)<=room:options.append(add)
            if already:continue
            if not options:
                seen[state]=False
                return False
            options=sorted(set(options),key=lambda x:(len(x),tuple(sorted(x))))
            if best is None or len(options)<len(best):best=options
        if best is None:
            seen[state]=True
            return True
        unknown=False
        for add in best:
            result=search(state|add)
            if result is True:
                seen[state]=True
                return True
            if result is None:unknown=True
        result=None if unknown else False
        seen[state]=result
        return result
    return search(roots)


def impossible_core(roots,budget,max_nodes=2000):
    """A subset proven infeasible, or None (including skipped/feasible)."""
    roots=tuple(sorted(set(x for x in roots if x.bit_count()>1)))
    result=feasible(roots,budget,max_nodes)
    if result is not False:return None,result
    core=list(roots)
    # Removing requirements can only make the OR problem easier.
    for x in roots:
        trial=[y for y in core if y!=x]
        if feasible(trial,budget,min(max_nodes,200)) is False:core=trial
    return tuple(core),False


def self_test():
    import itertools
    # Three triples with pairwise overlap, but no pair common to all.
    assert feasible([7,11,13],4) is False
    assert feasible([7,11,13],5) is True
    core,status=impossible_core([7,11,13,3],4)
    assert status is False and feasible(core,4) is False
    assert feasible([7],2,max_nodes=0) is None
    # Independent full enumeration of abstract union networks on four atoms.
    atoms=frozenset(1<<i for i in range(4))
    levels=[{frozenset()}]
    for _ in range(5):
        nxt=set()
        for state in levels[-1]:
            for a,b in itertools.combinations(atoms|state,2):
                s=a|b
                if s not in atoms|state:nxt.add(state|{s})
        levels.append(nxt)
    composites=[x for x in range(1,16) if x.bit_count()>1]
    for count in range(4):
        for rr in itertools.combinations(composites,count):
            for b in range(5):
                want=any(set(rr)<=s for level in levels[:b+1] for s in level)
                assert feasible(rr,b,max_nodes=100000) is want,(rr,b,want)
    print('OR BUDGET SELF TEST OK')


if __name__=='__main__':self_test()
