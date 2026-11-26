# L2260 graph partition v2: (k,r)=(6,5)

This is a finite combinatorial exclusion under the normalization and first-merge lemmas in graph_partition_v1.md. Not a Lean proof. No SAT solver is used.

## Tight components

For k=6,r=5, v1 establishes b>=6 and excludes b>=7 (the generic lower bound at b=7 is 7). At b=6 the tight bound leaves exactly 69 partitions. The auxiliary component graph is a forest with exactly r+t edges, where t counts singleton-bearing junk gates. A block containing s original vertices and t_B singleton-bearing junk atoms has s+t_B vertices and s+t_B-1 edges. Exactly t_B of those edges are junk-to-original links. Hence exactly s-1 retained OR edges belong to the block. Every operand support in that block is nonempty and has at most s atoms: an OR cone with q distinct atom leaves requires at least q-1 binary OR gates, all within the same block. Singleton-free junk atoms are isolated and have no OR reader, by the equality argument of v1.

## Junk semantics

Enumerate J0 as AND of two nonempty subsets of original vertices, each contained in one block. In a minimum circuit the two symbolic supports are incomparable by inclusion, since otherwise absorption would permit eliminating the AND. Evaluate the AND on 16 edge inputs, 24 maximal independent sets, and all 11 singleton inputs (the singleton set is stored separately). A junk gate is true on at least one maximal independent set. If its singleton set is nonempty, its atom is in the block containing that set; otherwise it is isolated. Enumerate J1 similarly, using the expanded allowed atom supports and requiring J0 in at least one operand (strict-cone dependence via ORs). Impose the per-block size cap. We do not require the simultaneous support family to have a realizable OR network. This is a relaxation.

For an AND with effective singleton sets A,B, its first-merge edges lie in the cross pairs between A\\B and B\\A. This follows from the first-merge argument of v1: the first pair-only true gate must have operands true at opposite singleton endpoints, and neither endpoint can make the AND true. Remove the union of both junk gates' possible first-merge edge masks from each block-pair subgraph. The sum of minimum vertex cover sizes of the residual subgraphs is a lower bound on the number of clean first-merge ANDs. If J1 is singleton-free, at least one clean AND directly reads it and cannot first-merge any edge, so add 1. The J0-only mask is fully determined by its edge truth mask and singleton set, because J0 reads only raw-input OR supports. Thus deduplicating J0 by (block, truth, singleton set) preserves this necessary-condition search. Deduplicate J1 by the analogous semantic triple only after the first-merge bound; top-cover feasibility depends only on both semantic triples and the partition, not on the original pair of supports.

## Relaxed clean top cover

Given the two junk semantics, enumerate all allowed supports A. For each possible component B, take the union of all its individual atoms whose truth tables never overlap A on a maximal independent set. Any clean AND with A as one operand and a support in B as the other is contained in this enlarged truth table: every atom of its other operand is compatible. The enlarged AND remains false on the maximal independent sets and covers a superset of the original AND's positive edges. Thus the resulting set of edge masks is an overapproximation of all legal clean top ANDs. In particular, we intentionally ignore B's size bound, OR sharing/cost, minimality and mandatory junk use for this step. Any actual circuit gives a cover of all 16 edges by at most k of these masks. Discard empty and dominated masks and use the exact finite recurrence D(R)=1+min_{T containing e} D(R\\T), with e any remaining edge and D(empty)=0. If D(E)>k, the original circuit is impossible.

## Results

A development-container C++ prototype was compiled and run. With the looser top cover (no mandatory J1 reader and no requirement that a junk gate be true on a positive edge), the result was:

```
before 69 after 0 pairs 205347379 merge 226281 cover 0 types 0 0 0
```

The pair counter includes repeat support combinations after J0 semantic dedup; 226281 distinct semantic pairs passing the structural bound were tested by the relaxed top cover. None admitted a cover by 6 tops. Thus all 69 partitions are excluded. The repository version is a readability/diagnostic refactor of that tested algorithm, with result assertions; run it on WSL to confirm. No solver checkpoint is modified.

Run v1 first to verify the b>=7 exclusion and the vertex cover table, then v2.

```bash
g++ -O3 -std=c++17 -Wall -Wextra -pedantic pnp_graph_partition_v1.cpp -o /tmp/pnp_graph_partition_v1 && /tmp/pnp_graph_partition_v1 && g++ -O3 -std=c++17 -Wall -Wextra -pedantic pnp_graph_partition_v2.cpp -o /tmp/pnp_graph_partition_v2 && /tmp/pnp_graph_partition_v2
```

Next target: (5,6) or (7,5). Their survivor lists include partitions with b>11-r, so the tight support cap and isolated-junk rule cannot be used unconditionally. Analyze excess component rank explicitly. Do not count this as an additional formally proved Lean case.
