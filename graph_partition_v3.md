# Graph partition v3: L2260 (k,r)=(5,6)

No SAT solver. This is a necessary-condition screening experiment under the same minimum-circuit normalization, component and first-merge lemmas as v1/v2. It is NOT a complete exclusion or Lean proof.

## Extra OR rank

Let b be the number of components containing original vertices, d=r-(11-b). The v1 lower bound requires b>=5; for k=5, b>=7 is impossible. There are 809 tight b=5 partitions and 69 b=6 partitions with d=1 that pass v1's screening.

For each final original-containing block with s original vertices and j junk atoms, of which t are singleton-bearing, the auxiliary graph needs at least s+j-1 edges. Of these, t are the added singleton links, leaving at least s-1+(j-t) OR edges. Two junk atoms sharing an original-free component also require an OR edge. Consequently the number of singleton-free junk atoms attached to original blocks plus the indicator for a shared junk-only component cannot exceed d. For an original block the OR budget is at most s-1+d (other original blocks each need their minimum s'-1). Each symbolic support has at most s+d atoms, since its OR cone uses at least support size minus one binary ORs. We deliberately permit all original blocks to use the same d independently: this is an overapproximation, not an actual allocation.

Enumerate each nonbearing junk's component (original blocks or original-free blocks); bearing junk must be in the block of its singleton truth set. As in v2, enumerate allowable raw supports for J0 and then supports containing J0 for one operand of J1. When J1 is in an original-free component, at least one terminal AND reads a support in that component and hence has a singleton-false operand. It cannot first-merge any edge. First-merge residual vertex-cover bounds apply unchanged. All actual gates are used. Thus at least one top has J1 in an operand's symbolic support; require one such gate in the relaxed edge cover. In a minimum circuit each top is true on at least one edge, since otherwise that top could be removed from the output OR.

## Additional h6 lower bound

Write b_star=|starEdges|, c=|centreless|, lambda=|lam|. With base 17, 16 graph edges and total size 2k+1+r, h6 simplifies to c+b_star+(r-lambda)<=k+r.

For any edge not covered by a raw-input star, a clean top true on that edge has a junk atom true in one of its operands. Choose that atom and one true atom in the other operand. Their AND is a subfunction of the clean top, so is false on every maximal independent set. Enumerate these clean pairs of individual atoms (at least one junk) and union their positive edge masks R. Then b_star>=16-|R|. This holds regardless of whether the corresponding pair can actually appear in a minimum circuit.

An OR belonging to lambda has a raw-input vertex in the opposite side of its terminal top, so its value AND that vertex must be clean. Thus a composite support for which no raw vertex is compatible on all negative rows forces an OR outside lambda. A support with no raw input also cannot be lambda. At d=0 the auxiliary graph is a forest; an OR with intersecting operand supports would add a redundant edge, so a lambda OR's two nonempty raw operand supports require at least two distinct raw atoms. A composite support with only one raw atom therefore forces nonlambda at d=0.

Count distinct forced-nonlambda roots among J0's two raw supports and the J0-containing supports of J1. The two types cannot coincide. Because J0 support representations with equal boundary and singleton semantics are deduplicated, preserve the MINIMUM forced-nonlambda count over all eligible representations. The first-merge edge mask of J0 is determined by its edge/singleton truth. Other nonlambda roots, centreless count, actual sharing, and allocation of slack are ignored. If the resulting lower bound on b_star+(r-lambda) exceeds k+r=11, reject the candidate. Otherwise run the relaxed top cover.

## Results and reproducibility

A preliminary development-container run without the h6 addition or mandatory-J1 top check completed 391 of 878 partition checks before the execution limit, excluding 390 and finding 1 relaxation survivor (ID 139, restricted growth string 01020300004). The stronger local version with h6 and mandatory-J1 was compiled and tested on ID 139 and IDs 870..878. The last nine all failed; 139 still had a relaxation survivor. The printed raw masks A=528, B=768, X=2688, Y=576 and boundary truths are only a relaxed candidate, not a circuit. The final GitHub version has equivalent logic and clearer formatting; its complete run is not yet verified.

Run the previous v1 verifier first if not already done. Compile and run 4 independent shards:

```bash
g++ -O3 -std=c++17 -Wall -Wextra -pedantic pnp_graph_partition_v3.cpp -o /tmp/pnp_graph_partition_v3 && mkdir -p sat-results && seq 0 3 | xargs -P 4 -I{} bash -c 'set -o pipefail; /tmp/pnp_graph_partition_v3 "$1" 4 | tee "sat-results/l2260-graph-v3-$1.log"' _ {}
```

Each shard enumerates the same stable partition IDs and checks only IDs with (ID-1)%shard_count==shard_index. Each completed partition prints a line immediately. An optional first_id last_id range allows restart after the last finished ID, or targeted analysis:

```bash
/tmp/pnp_graph_partition_v3 0 1 139 139
```

For a full run sum the four examined counts; they must total 878. Sum after counts for survivors. A nonzero survivor count means only the relaxation was satisfied. Interruption is not a proof. Do not import these results as SAT UNSAT. Current provisional total remains 90/100 (88 SAT, 2 graph). No Lean certification.
