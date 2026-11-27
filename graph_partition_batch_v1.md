# L2260: batched incremental component search

Status: implementation and mathematical design, not an end-to-end benchmark or a Lean proof. The six-hour constraint motivates measuring a fixed ten-minute budget before running larger searches.

## Persistent formulas and range cubes

pnp_graph_partition_incremental_v1.py adds symbolic original-component labels (one-hot). A partition is an assumption on each original vertex's label. Each active OR and each junk atom has one component label; a bearing junk is linked to its effective singleton truth vertices. Inactive ORs have no label. For each label, the necessary rank inequality is

    original vertices + nonbearing junk atoms <= active ORs + 1.

It follows by subtracting the singleton-bearing attachment links from the component's vertex-minus-one edge lower bound. For an unused label the inequality is harmless. The construction permits two junk-only labels. Connectivity is not required by the CNF, which only relaxes the necessary condition.

The maximum-OR v19 formula supports an inactive prefix. A unit clause requires at least r_min active ORs; h6 in v9 cancels the active count and uses only the true Lambda count. For any actual r in [r_min,r_max], its component partition has b>=11-r>=11-r_max and satisfies the generic graph bound. If b=11-r_max, necessarily r=r_max, so the tight graph bound at the maximum is also valid. Thus it is enough to enumerate the max-r candidate set and use the range formula. No claim that an exact max-r UNSAT alone implies smaller-r UNSAT.

Explicit first-merge clauses use singleton truth sets of *effective* AND operands (including junk values). On any edge, the first pair-only wire cannot be an input or an OR. It is an AND whose two operands are true on opposite singleton endpoints, and false on the other endpoints. Every graph edge must be represented by at least one such AND. For clean ANDs, disjoint singleton sets and nonedge exclusions follow from cleanness. These conditions are additional necessary clauses. Exhaustively tested the two local Boolean implications on all 64 possible operand truth triples and the component-count arithmetic on 2376 small integer cases, independently of the SAT code.

One worker holds its solver while processing the same component count. A returned UNSAT assumption core can be negated and added to that solver, because the base formula entails that clause. The old v2 exact-r database is imported read-only after verifying its original fingerprint and assignments. Existing results are not used as SAT clauses.

## MDD compression and adaptive search

pnp_graph_partition_batch_v1.py constructs a reduced multi-valued decision diagram of all candidate partitions for each component count. Nodes at the same depth with identical labeled children are shared. With root true and the vertex labels one-hot, every true node must enable its child for the selected label, or reject a missing branch. The accepting terminal needs no variable. This admits exactly the full candidate list. An independent Python enumeration of all accepting paths compared equal to the original candidate lists for (7,6), (6,8), and (5,10): 31692, 139723, 70737 paths respectively.

Start with groups of partitions sharing the first eight vertex labels (and the block count). The exact common prefix of each group is used as assumptions. If UNSAT, all pending leaves in that group are UNSAT. If TIMEOUT, divide by the next differing label. A single leaf has its entire assignment fixed. The solver still sees the full original MDD, including already-solved candidates; the inherited results are not inserted into the formula. The group result is safe even if its prefix also includes earlier solved leaves. Checkpoint rows record prefix, assumption core positions, and partition assignment. The parent commits only completed exclusions, and terminates workers on overall wall limit; interrupted tasks are still pending.

Measured initial group counts at depth 8 (not predicted solve counts):
* k=7,r=6: 1380 pending from user log, 437 groups (48 b=5 and 1332 b=6).
* k=6,r=7..8: 139723 candidate leaves, 7660 groups.
* k=5,r=8..10: 70737 candidate leaves, 5782 groups.

Total 13879 initial groups vs 400079 separate outstanding v2 cases, if all group cubes succeeded without splitting. TIMEOUT splitting can increase the number; MDD and larger range formulas can also make each solve harder. No measured speedup yet. Real PySAT and Lean are unavailable in the development container; the new repository versions are not run end-to-end. The included self-tests compare small exact/range SAT results with the previous encoding, and MDD language/prefix queries with explicit enumeration.

## Bounded benchmark

Stop an old long-running sweep before this benchmark. Existing checkpoints are preserved. Use the batch script (it imports the incremental script).

```bash
git -C "$HOME/dev/pequalnp-tools" pull --ff-only && cd "$HOME/dev/pequalnp-tools" && .venv-sat/bin/python -u pnp_graph_partition_batch_v1.py --self-test
```

```bash
cd "$HOME/dev/pequalnp-tools" && nice -n 10 .venv-sat/bin/python -u pnp_graph_partition_batch_v1.py --top-count 7 --or-min 6 --or-max 6 --seed-v2 sat-results/l2260-graph-sweep-v2-k7-r6-compact.sqlite3 --jobs 8 --prefix-depth 8 --seconds 2 --leaf-seconds 15 --wall-seconds 600 --solver cadical195
```

Use new_unsat, calls, splits, remaining_count and wall_seconds to measure actual performance. No old DB mutation. Other ranges can be benchmarked with the same wall limit, no seed-v2, e.g. --top-count 6 --or-min 7 --or-max 8 or --top-count 5 --or-min 8 --or-max 10. Do not extrapolate until actual results.

## Formalization

formalization/FirstMerge.lean is a standalone draft without sorry/axiom declarations: Boolean local lemmas, a valid evaluation trace with earlier source values, and existence of an opposite-singleton AND if any trace wire is pair-only true. Also includes the arithmetic portion of the component count. Compile with the project Mathlib environment:

```bash
cd "$HOME/dev/pequalnp-proofs/lean" && lake env lean "$HOME/dev/pequalnp-tools/formalization/FirstMerge.lean"
```

This is not a Lean proof of L_meta_2260. Remaining work:
1. Connect IsLeastAO/TopForm and gateVal/OrReaches to the normalized OR supports, the trace and component construction. Prove no unused gates, output clean-OR count, effective singleton semantics and forest/tight cases.
2. Formalize per-block graph star/vertex-cover bound and verify partition enumeration coverage.
3. Prove the custom v19, rank, first-merge and MDD CNF soundness with actual Boolean assignments. For a range formula, verify inactive OR padding and all h4/h5/h6 conditions. The project's enc2 checker does not automatically certify a custom CNF.
4. Export and independently verify UNSAT certificates (including existing solved cases); connect the checked UNSAT formulas to the theorem in Lean. Prior SQLite/JSON statuses are empirical, not proof certificates.

The 94/100 provisional count is unchanged. The six-hour target has not been achieved or demonstrated.
