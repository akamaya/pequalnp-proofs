# L2260: graph partition / first-merge bound

Status: independent finite enumeration tested, mathematical reduction argued below, not formalized in Lean. This is not a submission or a verified certificate. It assumes the same minimum-circuit normalization as v9: binary AND/OR, two used junk ANDs J0,J1, J0 strictly in the cone of J1, k terminal clean ANDs, r retained ORs, and the output OR of those tops. The retained ORs are union operations over n original atoms and the two junk atoms. Each AND operand has nonempty symbolic OR support. Every gate reaches the output.

## 1. Components

Take the 13 atoms as vertices of an auxiliary undirected multigraph. For each retained OR, connect one representative atom from each operand support by one edge. In symbolic OR-DAG order every support lies in one connected component: the two operand supports are each already connected, and the new edge connects them. Loops and redundant edges do not invalidate the count.

Call a junk AND singleton-bearing if it is true on some singleton original-input assignment. For each such junk in order J0,J1, add one auxiliary edge connecting its output atom to one original vertex on which it is true. All original vertices on which that junk is true belong to the same component: its two operand supports each lie in one component and their effective singleton-truth sets intersect. For J1 this uses the preceding J0 link if J0 is singleton-bearing. Thus the effective singleton-truth set of any AND operand lies entirely in its symbolic support's final component (or is empty).

Let t be the number of singleton-bearing junk gates, b the number of components containing original vertices, z the number containing only junk atoms. Then z <= 2-t, and the auxiliary graph has 13 vertices and at most r+t edges. Hence b+z >= 13-r-t and b >= 11-r.

If b=11-r, all inequalities are equalities, z=2-t, the auxiliary graph has no redundant edge, and every singleton-free junk atom is an isolated component. Such an atom cannot enter any retained OR: any OR support containing it would be exactly that singleton, requiring a redundant union. In particular a used isolated singleton-free J1 must be read directly by at least one terminal AND.

## 2. First merge of an edge

For a graph edge {u,v}, f({u,v}) is true while f({u}) and f({v}) are false. At least one retained AND is true on {u,v} but false on both singleton inputs. Choose the first such gate in actual topological order. It cannot first occur at an OR: a true OR must have a true operand, and if it is false on both singleton inputs its true operand is also false on both. At the first such AND, each operand is true on one of the singleton endpoints, otherwise an earlier pair-only value would be necessary; they are true on opposite endpoints, otherwise the AND itself is true on one singleton.

Consequently every first-merge edge of a fixed AND is in one unordered pair of original-vertex blocks (including a block paired with itself). A clean AND's effective singleton sets A and B are disjoint, and all cross pairs in A x B are graph edges, because its output implies f. L2260 has no 4-cycle, so at least one of A,B has size at most one. Thus its first-merge edges lie in one star.

Partition the 16 graph edges into subgraphs E_ab according to their unordered endpoint block pair. Write T_ab = minimum vertex cover size of E_ab and S = sum T_ab. If a subgraph has no junk first-merge gate, at least T_ab clean ANDs are needed to cover its first-merge edges by stars. Clean ANDs cannot serve two different block pairs. At most two distinct subgraphs may receive a junk first merge. Discarding those subgraphs altogether is a relaxation. Therefore k >= S minus the two largest T_ab values (missing entries count as zero). This holds even if two junk gates serve the same subgraph or one serves none.

## 3. Tight component count

When b=11-r, strengthen the discounts:

* If J0 is singleton-free, it is isolated. The strict-cone link forces a direct J0 operand in J1, since no OR contains J0. Thus J1 is singleton-free and cannot first-merge any edge: every pair on which J1 is true already makes J0 true, and J0 is false on singletons. J1 is isolated and must have a direct terminal AND reader. That reader has an operand false on every singleton and cannot first-merge any edge. At most k-1 clean ANDs are available for the star count; only J0 can discount a subgraph. Thus k >= 1+S-max_ab T_ab.
* If J0 is singleton-bearing but J1 is singleton-free, J0 can first-merge only within one block a (both its operand effective singleton sets share a vertex). The J0 atom lies in that block, and one J1 operand contains it by the strict-cone link. Any first-merge edge of J1 must therefore belong to an incident block pair {a,b}; if it has an empty singleton operand it merges no edge. Again an isolated J1 requires one direct terminal reader that cannot first-merge. Therefore k >= 1+S-max_a(T_aa + max_{b != a} T_ab). This allows discarding a whole loop and a whole incident cross group, even if the gates do not actually cover them.
* If both are singleton-bearing, the strict-cone link forces their input components to be the same original block a: J0's output atom belongs to a, a J1 operand contains it, and J1's operand singleton sets intersect. Both junk first merges are confined to E_aa, so k >= S-max_a T_aa.

The minimum of these three lower bounds is necessary at equality. For n=11 and r=4, b>=7. Enumeration shows that b>=8 requires k>=9 even under the generic two-discount relaxation. At b=7 the minimum generic bound is 7, but the minimum tight bound is 8. Therefore k=7,r=4 is impossible under the stated normalization.

## 4. Finite enumeration

pnp_graph_partition_v1.cpp enumerates all 678570 set partitions of 11 vertices as restricted-growth strings, each once. It computes vertex cover size for all 65536 edge subgraphs in two independent ways: enumerate all 2048 vertex sets then propagate minimum costs down the edge-mask subset lattice; and recursively branch on the two endpoints of an uncovered edge. It checks equality on all masks and checks the absence of a 4-cycle. The entire program was compiled and run in the development container, without SAT.

```
blocks partitions two_any one_any two_loops one_loop loop_incident tight_bound
1 1 0 0 0 0 0 0
2 1023 0 1 1 1 0 1
3 28501 1 2 2 2 1 2
4 145750 2 3 3 3 2 3
5 246730 3 4 4 4 3 4
6 179487 5 6 6 6 5 6
7 63987 7 8 8 8 7 8
8 11880 9 10 10 10 9 10
9 1155 11 12 12 12 11 12
10 55 13 14 14 14 13 14
11 1 14 15 16 16 15 16
total=678570 cover_crosscheck=65536 tau=7
k r generic_partitions refined_partitions
7 4 82 0
7 5 11517 1272
7 6 111389 31692
6 5 1417 69
6 6 34179 6482
6 7 118793 60423
6 8 147131 139723
5 6 6349 878
5 7 44358 15188
5 8 69713 57080
5 9 70736 70736
5 10 70737 70737
L2260 PARTITION CHECK OK; (7,4) excluded by graph argument, not yet Lean-certified
```

The remaining partition counts are only necessary-condition survivors, not circuit witnesses and not estimates of computational completion. We do not write the result into any SAT checkpoint. The next proof work is to formalize the component and first-merge lemmas, or strengthen the tight-case analysis for the 69 partitions at k=6,r=5. Existing SAT UNSAT results and the new graph exclusion are not Lean proofs.
