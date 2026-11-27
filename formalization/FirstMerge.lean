import Mathlib
import PEqualNP.Defs.TopForm

/-!
First-merge lemmas for the graph-circuit reduction.
The abstract lemmas passed the WSL Lean check. The new official
Circuit.wires/IsLeastAO bridge below requires a separate compile check.
-/

namespace L2260FirstMerge

structure Sample where
  u : Bool
  v : Bool
  uv : Bool
  deriving DecidableEq

def PairOnly (x : Sample) : Prop :=
  x.uv = true ∧ x.u = false ∧ x.v = false

def Opposite (a b : Sample) : Prop :=
  (a.u = true ∧ a.v = false ∧ b.u = false ∧ b.v = true) ∨
  (a.u = false ∧ a.v = true ∧ b.u = true ∧ b.v = false)

def andSample (a b : Sample) : Sample :=
  ⟨a.u && b.u, a.v && b.v, a.uv && b.uv⟩

def orSample (a b : Sample) : Sample :=
  ⟨a.u || b.u, a.v || b.v, a.uv || b.uv⟩

/-- An OR cannot be the first pair-only wire. -/
theorem or_pair (a b : Sample) :
    PairOnly (orSample a b) → PairOnly a ∨ PairOnly b := by
  rcases a with ⟨au, av, ap⟩
  rcases b with ⟨bu, bv, bp⟩
  cases au <;> cases av <;> cases ap <;>
    cases bu <;> cases bv <;> cases bp <;>
    simp [PairOnly, orSample]

/-- The first pair-only AND has opposite singleton inputs. -/
theorem and_first (a b : Sample) :
    ¬ PairOnly a → ¬ PairOnly b →
    PairOnly (andSample a b) → Opposite a b := by
  rcases a with ⟨au, av, ap⟩
  rcases b with ⟨bu, bv, bp⟩
  cases au <;> cases av <;> cases ap <;>
    cases bu <;> cases bv <;> cases bp <;>
    simp [PairOnly, Opposite, andSample]

inductive Step where
  | input (x : Sample)
  | andGate (a b : Sample)
  | orGate (a b : Sample)

def Step.value : Step → Sample
  | .input x => x
  | .andGate a b => andSample a b
  | .orGate a b => orSample a b

def Step.ok (s : Step) (prior : List Sample) : Prop :=
  match s with
  | .input x => ¬ PairOnly x
  | .andGate a b => a ∈ prior ∧ b ∈ prior
  | .orGate a b => a ∈ prior ∧ b ∈ prior

def Step.cross : Step → Prop
  | .andGate a b => Opposite a b
  | _ => False

def Valid (prior : List Sample) : List Step → Prop
  | [] => True
  | s :: tail => s.ok prior ∧ Valid (s.value :: prior) tail

theorem safe_step (s : Step) (prior : List Sample)
    (hok : s.ok prior)
    (hprior : ∀ x ∈ prior, ¬ PairOnly x)
    (hcross : ¬ s.cross) : ¬ PairOnly s.value := by
  cases s with
  | input x => exact hok
  | andGate a b =>
      change a ∈ prior ∧ b ∈ prior at hok
      change ¬ Opposite a b at hcross
      change ¬ PairOnly (andSample a b)
      intro hm
      exact hcross (and_first a b (hprior a hok.1) (hprior b hok.2) hm)
  | orGate a b =>
      change a ∈ prior ∧ b ∈ prior at hok
      change ¬ PairOnly (orSample a b)
      intro hm
      rcases or_pair a b hm with ha | hb
      · exact hprior a hok.1 ha
      · exact hprior b hok.2 hb

theorem no_merge_of_no_cross (steps : List Step) (prior : List Sample)
    (hvalid : Valid prior steps)
    (hprior : ∀ x ∈ prior, ¬ PairOnly x)
    (hnocross : ∀ s ∈ steps, ¬ s.cross) :
    ∀ s ∈ steps, ¬ PairOnly s.value := by
  induction steps generalizing prior with
  | nil => simp
  | cons s tail ih =>
      change s.ok prior ∧ Valid (s.value :: prior) tail at hvalid
      have hs : ¬ PairOnly s.value :=
        safe_step s prior hvalid.1 hprior (hnocross s (List.mem_cons.mpr (Or.inl rfl)))
      have hp : ∀ x ∈ s.value :: prior, ¬ PairOnly x := by
        intro x hx
        rcases List.mem_cons.mp hx with h | h
        · subst x
          exact hs
        · exact hprior x h
      have ht : ∀ z ∈ tail, ¬ PairOnly z.value :=
        ih (s.value :: prior) hvalid.2 hp
          (fun z hz => hnocross z (List.mem_cons.mpr (Or.inr hz)))
      intro z hz
      rcases List.mem_cons.mp hz with h | h
      · subst z
        exact hs
      · exact ht z h

/-- If any step is pair-only true, some actual AND step has opposite
singleton operands. The source relation only refers to earlier values. -/
theorem first_merge_exists (steps : List Step) (prior : List Sample)
    (hvalid : Valid prior steps)
    (hprior : ∀ x ∈ prior, ¬ PairOnly x)
    (htarget : ∃ s ∈ steps, PairOnly s.value) :
    ∃ s ∈ steps, s.cross := by
  classical
  by_contra hn
  have hnone : ∀ s ∈ steps, ¬ s.cross := by
    intro s hs hc
    exact hn ⟨s, hs, hc⟩
  obtain ⟨s, hs, hm⟩ := htarget
  exact no_merge_of_no_cross steps prior hvalid hprior hnone s hs hm

/-- Arithmetic part of the auxiliary-component bound. The graph-rank
inequality and the junk-only component bound are hypotheses. -/
theorem original_components (n r t b z : ℕ)
    (hrank : n + 2 ≤ b + z + r + t)
    (hfree : z + t ≤ 2) : n ≤ b + r := by
  omega

theorem tight_components (n r t b z : ℕ)
    (hrank : n + 2 ≤ b + z + r + t)
    (hfree : z + t ≤ 2)
    (htight : n = b + r) : z + t = 2 := by
  omega

end L2260FirstMerge

/-! ## Bridge to the official circuit evaluator

This section uses the actual Circuit.wires fold, not an assumed trace.
The witness records the precise gate prefix at which its operands are
evaluated. Even missing wires are handled, with the official false default.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

def wireSample (wu wv wp : List Bool) (i : Nat) : Sample :=
  ⟨wu.getD i false, wv.getD i false, wp.getD i false⟩

def WireSafe (wu wv wp : List Bool) : Prop :=
  ∀ i, ¬ PairOnly (wireSample wu wv wp i)

/-- The exact step used by the official Circuit.wires evaluator. -/
def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def CrossAt (g : Gate) (wu wv wp : List Bool) : Prop :=
  g.op = GateOp.and ∧
    ∃ a b, g.inputs = [a,b] ∧
      Opposite (wireSample wu wv wp a) (wireSample wu wv wp b)

/-- A concrete gate with its actual preceding gate list. -/
def CircuitCross (gs : List Gate) (wu wv wp : List Bool) : Prop :=
  ∃ pre g post, gs = pre ++ g :: post ∧
    CrossAt g (pre.foldl gateStep wu) (pre.foldl gateStep wv)
      (pre.foldl gateStep wp)

private theorem getD_snoc (xs : List Bool) (x : Bool) (i : Nat) :
    (xs ++ [x]).getD i false =
      if i = xs.length then x else xs.getD i false := by
  induction xs generalizing i with
  | nil =>
      cases i <;> simp
  | cons a xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          simpa only [List.cons_append, List.getD_cons_succ,
            List.length_cons, Nat.succ.injEq] using ih i

private theorem append_safe (wu wv wp : List Bool) (x : Sample)
    (hv : wu.length = wv.length) (hp : wu.length = wp.length)
    (hs : WireSafe wu wv wp) (hx : ¬ PairOnly x) :
    WireSafe (wu ++ [x.u]) (wv ++ [x.v]) (wp ++ [x.uv]) := by
  intro i
  change ¬ PairOnly ⟨(wu ++ [x.u]).getD i false,
    (wv ++ [x.v]).getD i false, (wp ++ [x.uv]).getD i false⟩
  rw [getD_snoc wu x.u i, getD_snoc wv x.v i, getD_snoc wp x.uv i, ← hv, ← hp]
  by_cases hi : i = wu.length
  · simp only [if_pos hi]
    cases x
    exact hx
  · simp only [if_neg hi]
    exact hs i

private theorem two_inputs (l : List Nat) (h : l.length = 2) :
    ∃ a b, l = [a,b] := by
  cases l with
  | nil => simp at h
  | cons a l =>
      cases l with
      | nil => simp at h
      | cons b l =>
          cases l with
          | nil => exact ⟨a,b,rfl⟩
          | cons c l => simp at h

private theorem gate_safe (g : Gate) (wu wv wp : List Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2)
    (hv : wu.length = wv.length) (hp : wu.length = wp.length)
    (hs : WireSafe wu wv wp) (hc : ¬ CrossAt g wu wv wp) :
    WireSafe (gateStep wu g) (gateStep wv g) (gateStep wp g) := by
  rcases g with ⟨op, ins⟩
  change ins.length = 2 at hlen
  obtain ⟨a,b,rfl⟩ := two_inputs ins hlen
  change op = GateOp.and ∨ op = GateOp.or at hop
  rcases hop with rfl | rfl
  · have hx : ¬ PairOnly (andSample (wireSample wu wv wp a) (wireSample wu wv wp b)) := by
      intro hm
      exact hc ⟨rfl, a, b, rfl, and_first _ _ (hs a) (hs b) hm⟩
    simpa [gateStep, GateOp.eval, wireSample, andSample] using
      append_safe wu wv wp _ hv hp hs hx
  · have hx : ¬ PairOnly (orSample (wireSample wu wv wp a) (wireSample wu wv wp b)) := by
      intro hm
      rcases or_pair _ _ hm with ha | hb
      · exact hs a ha
      · exact hs b hb
    simpa [gateStep, GateOp.eval, wireSample, orSample] using
      append_safe wu wv wp _ hv hp hs hx

/-- Induction on the official gate list: either all final wires remain
safe, or a concrete earlier AND has opposite singleton operands. -/
theorem fold_safe_or_cross (gs : List Gate) (wu wv wp : List Bool)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hv : wu.length = wv.length) (hp : wu.length = wp.length)
    (hs : WireSafe wu wv wp) :
    WireSafe (gs.foldl gateStep wu) (gs.foldl gateStep wv) (gs.foldl gateStep wp) ∨
      CircuitCross gs wu wv wp := by
  classical
  induction gs generalizing wu wv wp with
  | nil => exact Or.inl hs
  | cons g gs ih =>
      by_cases hc : CrossAt g wu wv wp
      · exact Or.inr ⟨[],g,gs,rfl,hc⟩
      · have hg := hm g (by simp)
        have hs' := gate_safe g wu wv wp hg.1 hg.2 hv hp hs hc
        have hv' : (gateStep wu g).length = (gateStep wv g).length := by
          simp [gateStep, hv]
        have hp' : (gateStep wu g).length = (gateStep wp g).length := by
          simp [gateStep, hp]
        have hm' : ∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length = 2 :=
          fun h hh => hm h (List.mem_cons.mpr (Or.inr hh))
        rcases ih (gateStep wu g) (gateStep wv g) (gateStep wp g) hm' hv' hp' hs' with hf | hc'
        · exact Or.inl hf
        · obtain ⟨pre,h,post,he,hcross⟩ := hc'
          refine Or.inr ⟨g :: pre,h,post,?_,?_⟩
          · simp [he]
          · exact hcross

/-- Actual Circuit.eval bridge. No normalization hypothesis is needed,
only the binary AND/OR model and the three input evaluations. -/
theorem circuit_first_merge (C : Circuit) (xu xv xp : List Bool)
    (hm : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hv : xu.length = xv.length) (hp : xu.length = xp.length)
    (hs : WireSafe xu xv xp)
    (ht : PairOnly ⟨C.eval xu, C.eval xv, C.eval xp⟩) :
    CircuitCross C.gates xu xv xp := by
  rcases fold_safe_or_cross C.gates xu xv xp hm hv hp hs with hf | hc
  · exact False.elim (hf C.output ht)
  · exact hc

private theorem pair_inputs_safe {n : Nat} (u v : Fin n) :
    WireSafe (List.ofFn (pairInput u u)) (List.ofFn (pairInput v v))
      (List.ofFn (pairInput u v)) := by
  intro i
  by_cases hi : i < n
  · simp [wireSample, PairOnly, List.getD_eq_getElem?_getD,
      hi, pairInput] <;> aesop
  · simp [wireSample, PairOnly, List.getD_eq_getElem?_getD,
      hi]

private theorem graph_singleton_false {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u : Fin n) :
    graphFun G ∅ (pairInput u u) = false := by
  have hn : ¬ ∃ a b, G.Adj a b ∧ pairInput u u a = true ∧ pairInput u u b = true := by
    rintro ⟨a,b,hab,ha,hb⟩
    have ha' : a = u := by simpa [pairInput] using ha
    have hb' : b = u := by simpa [pairInput] using hb
    subst a
    subst b
    exact (G.ne_of_adj hab) rfl
  simp [graphFun, hn]

private theorem graph_pair_true {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u v : Fin n) (he : G.Adj u v) :
    graphFun G ∅ (pairInput u v) = true := by
  have h : ∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true :=
    ⟨u,v,he,by simp [pairInput],by simp [pairInput]⟩
  simp [graphFun, h]

/-- Direct connection to the official IsLeastAO hypothesis and edge
function. The existential witness is an actual gate of C, not an
arbitrary Boolean function or an abstract trace step. -/
theorem graph_edge_first_merge {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (u v : Fin n) (he : G.Adj u v) :
    CircuitCross C.gates (List.ofFn (pairInput u u)) (List.ofFn (pairInput v v))
      (List.ofFn (pairInput u v)) := by
  have hm : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hmin.1.1 g hg, hmin.1.2.2 g hg⟩
  have hf (x : Fin n → Bool) : C.eval (List.ofFn x) = graphFun G ∅ x :=
    congrFun hmin.2.1 x
  apply circuit_first_merge C _ _ _ hm (by simp) (by simp) (pair_inputs_safe u v)
  change C.eval (List.ofFn (pairInput u v)) = true ∧
    C.eval (List.ofFn (pairInput u u)) = false ∧ C.eval (List.ofFn (pairInput v v)) = false
  exact ⟨(hf _).trans (graph_pair_true G u v he),
    (hf _).trans (graph_singleton_false G u),
    (hf _).trans (graph_singleton_false G v)⟩

end L2260FirstMerge

/-! ## Indexed witnesses and stable wire values -/

namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl gateStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      change (gs.foldl gateStep (gateStep w g)).length = w.length + (g :: gs).length
      rw [ih]
      simp only [gateStep, List.length_append, List.length_cons, List.length_nil]
      omega

/-- Appending further gates cannot change an already existing wire. -/
theorem fold_preserves_getD (gs : List Gate) (w : List Bool) (i : Nat)
    (hi : i < w.length) :
    (gs.foldl gateStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      change (gs.foldl gateStep (gateStep w g)).getD i false = w.getD i false
      have hi' : i < (gateStep w g).length := by
        simp only [gateStep, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (gateStep w g) hi']
      unfold gateStep
      rw [getD_snoc]
      simp [Nat.ne_of_lt hi]

private theorem split_getD {α : Type} (pre post : List α) (g d : α) :
    (pre ++ g :: post).getD pre.length d = g := by
  induction pre with
  | nil => simp
  | cons h pre ih =>
      simpa only [List.cons_append, List.length_cons, List.getD_cons_succ] using ih

/-- Use the final official wire list rather than the evaluation prefix. -/
def finalSample {n : Nat} (C : Circuit) (u v : Fin n) (i : Nat) : Sample :=
  wireSample (C.wires (List.ofFn (pairInput u u)))
    (C.wires (List.ofFn (pairInput v v))) (C.wires (List.ofFn (pairInput u v))) i

private theorem prefix_wire {n : Nat} (C : Circuit) (pre tail : List Gate)
    (h : C.gates = pre ++ tail) (x : Fin n → Bool) (i : Nat)
    (hi : i < n + pre.length) :
    (C.wires (List.ofFn x)).getD i false =
      (pre.foldl gateStep (List.ofFn x)).getD i false := by
  change (C.gates.foldl gateStep (List.ofFn x)).getD i false = _
  rw [h, List.foldl_append]
  apply fold_preserves_getD
  rw [fold_length]
  simpa using hi

theorem finalSample_gate {n : Nat} (C : Circuit) (u v : Fin n) (j : Nat) :
    finalSample C u v (n+j) =
      ⟨gateVal n C j (pairInput u u), gateVal n C j (pairInput v v),
        gateVal n C j (pairInput u v)⟩ := rfl

/-- The opposite-singleton witness is now a gate index of the actual
circuit, with its actual two operand wire indices and their final values. -/
theorem graph_edge_first_merge_indexed {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (u v : Fin n) (he : G.Adj u v) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      ∃ a b, (gateAt C j).inputs = [a,b] ∧
        Opposite (finalSample C u v a) (finalSample C u v b) := by
  obtain ⟨pre,g,post,hg,hcross⟩ := graph_edge_first_merge G C hmin u v he
  obtain ⟨hop,a,b,hin,hopp⟩ := hcross
  have hj : pre.length < C.gates.length := by
    rw [hg]
    simp only [List.length_append, List.length_cons]
    omega
  have hat : gateAt C pre.length = g := by
    unfold gateAt
    rw [hg]
    exact split_getD pre post g _
  have ha : a < n + pre.length := by
    apply hmin.1.2.1 pre.length hj a
    rw [hat, hin]
    simp
  have hb : b < n + pre.length := by
    apply hmin.1.2.1 pre.length hj b
    rw [hat, hin]
    simp
  have eqsample (i : Nat) (hi : i < n + pre.length) :
      finalSample C u v i =
        wireSample (pre.foldl gateStep (List.ofFn (pairInput u u)))
          (pre.foldl gateStep (List.ofFn (pairInput v v)))
          (pre.foldl gateStep (List.ofFn (pairInput u v))) i := by
    unfold finalSample wireSample
    rw [prefix_wire C pre (g :: post) hg (pairInput u u) i hi,
      prefix_wire C pre (g :: post) hg (pairInput v v) i hi,
      prefix_wire C pre (g :: post) hg (pairInput u v) i hi]
  refine ⟨pre.length,hj,?_,a,b,?_,?_⟩
  · rw [hat]
    exact hop
  · rw [hat]
    exact hin
  · rw [eqsample a ha, eqsample b hb]
    exact hopp

end L2260FirstMerge

/-! ## Clean cross-products in a graph with no four-cycle

These lemmas formalize the graph-theoretic part of the incompatible-edge
cuts. The hypotheses that the effective singleton sets of a clean AND
form an adjacent cross-product and each lie in one component still need
to be derived from the circuit.
-/
namespace L2260FirstMerge

def CrossPair {α : Type} (A B : Finset α) (u v : α) : Prop :=
  (u ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ u ∈ B)

/-- The two sides of a complete bipartite subgraph cannot both have
two vertices in a graph with no four-cycle. -/
theorem cross_card_le_one {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : PEqualNP.TopForm.NoFourCycle G)
    (A B : Finset (Fin n))
    (hadj : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  classical
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  · have hA' : 1 < A.card := by omega
    obtain ⟨a,ha,a',ha',hne⟩ := Finset.one_lt_card.mp hA'
    have hsub : B ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj a' w) := by
      intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ b,hadj a ha b hb,hadj a' ha' b hb⟩
    exact Or.inr ((Finset.card_le_card hsub).trans (h4 a a' hne))

/-- When both sides are nonempty, every crossing edge has a common
centre. This is a property of the effective singleton sets, not
necessarily the raw OR-support sets. -/
theorem cross_pairs_common_center {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : PEqualNP.TopForm.NoFourCycle G)
    (A B : Finset (Fin n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (hadj : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    ∃ c : Fin n, ∀ u v, CrossPair A B u v → u = c ∨ v = c := by
  obtain ⟨a,ha⟩ := hA
  obtain ⟨b,hb⟩ := hB
  rcases cross_card_le_one G h4 A B hadj with h | h
  · refine ⟨a,?_⟩
    intro u v huv
    rcases huv with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact Or.inl (Finset.card_le_one.mp h u hu a ha)
    · exact Or.inr (Finset.card_le_one.mp h v hv a ha)
  · refine ⟨b,?_⟩
    intro u v huv
    rcases huv with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact Or.inr (Finset.card_le_one.mp h v hv b hb)
    · exact Or.inl (Finset.card_le_one.mp h u hu b hb)

/-- Two disjoint graph edges cannot both be in one clean crossing
star. This justifies the disjoint-endpoint part of the SAT clique cut. -/
theorem cross_pairs_share_endpoint {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : PEqualNP.TopForm.NoFourCycle G)
    (A B : Finset (Fin n)) (hadj : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (u v x y : Fin n) (he : CrossPair A B u v) (hf : CrossPair A B x y) :
    u = x ∨ u = y ∨ v = x ∨ v = y := by
  have hA : A.Nonempty := by
    rcases he with h | h
    · exact ⟨u,h.1⟩
    · exact ⟨v,h.1⟩
  have hB : B.Nonempty := by
    rcases he with h | h
    · exact ⟨v,h.2⟩
    · exact ⟨u,h.2⟩
  obtain ⟨c,hc⟩ := cross_pairs_common_center G h4 A B hA hB hadj
  rcases hc u v he with hu | hv
  · rcases hc x y hf with hx | hy
    · exact Or.inl (hu.trans hx.symm)
    · exact Or.inr (Or.inl (hu.trans hy.symm))
  · rcases hc x y hf with hx | hy
    · exact Or.inr (Or.inr (Or.inl (hv.trans hx.symm)))
    · exact Or.inr (Or.inr (Or.inr (hv.trans hy.symm)))

/-- If both operand singleton sets are component-local, all their
crossing edges have the same unordered component pair. -/
theorem cross_pairs_same_blocks {α β : Type} (A B : Finset α)
    (label : α → β) (a b : β)
    (hA : ∀ x ∈ A, label x = a) (hB : ∀ x ∈ B, label x = b)
    (u v : α) (he : CrossPair A B u v) :
    (label u = a ∧ label v = b) ∨
      (label u = b ∧ label v = a) := by
  rcases he with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · exact Or.inl ⟨hA u hu,hB v hv⟩
  · exact Or.inr ⟨hB u hu,hA v hv⟩

end L2260FirstMerge

/-! ## Actual singleton supports of clean AND gates -/

namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

def WireLe (w z : List Bool) : Prop :=
  ∀ i, w.getD i false = true → z.getD i false = true

private theorem append_le (w z : List Bool) (a b : Bool)
    (hlen : w.length = z.length) (h : WireLe w z)
    (hab : a = true → b = true) : WireLe (w ++ [a]) (z ++ [b]) := by
  intro i hi
  rw [getD_snoc] at hi
  rw [getD_snoc, ← hlen]
  by_cases he : i = w.length
  · simp only [if_pos he] at hi ⊢
    exact hab hi
  · simp only [if_neg he] at hi ⊢
    exact h i hi

private theorem gateStep_le (w z : List Bool) (g : Gate)
    (hlen : w.length = z.length) (h : WireLe w z)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : g.inputs.length = 2) : WireLe (gateStep w g) (gateStep z g) := by
  obtain ⟨a,b,hab⟩ := two_inputs g.inputs hin
  unfold gateStep
  apply append_le w z _ _ hlen h
  rcases hop with ho | ho
  · rw [ho, hab]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, Bool.and_eq_true_iff]
    intro hh
    exact ⟨h a hh.1,h b hh.2⟩
  · rw [ho, hab]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      id_eq, Bool.or_false, Bool.or_eq_true_iff]
    intro hh
    rcases hh with ha | hb
    · exact Or.inl (h a ha)
    · exact Or.inr (h b hb)

theorem fold_le (gs : List Gate) (w z : List Bool)
    (hlen : w.length = z.length) (h : WireLe w z)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    WireLe (gs.foldl gateStep w) (gs.foldl gateStep z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
      have hg := hm g (by simp)
      apply ih (gateStep w g) (gateStep z g)
      · simp [gateStep, hlen]
      · exact gateStep_le w z g hlen h hg.1 hg.2
      · intro g' hg'
        exact hm g' (List.mem_cons.mpr (Or.inr hg'))

/-- Monotonicity of every wire of a binary AND/OR circuit. -/
theorem wire_monotone {n : Nat} (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ v, x v = true → y v = true) :
    WireLe (C.wires (List.ofFn x)) (C.wires (List.ofFn y)) := by
  apply fold_le C.gates (List.ofFn x) (List.ofFn y) (by simp)
  · intro i hi
    by_cases h : i < n
    · have hx : x ⟨i,h⟩ = true := by
        simpa [List.getD_eq_getElem?_getD, h] using hi
      simpa [List.getD_eq_getElem?_getD, h] using hxy ⟨i,h⟩ hx
    · simp [List.getD_eq_getElem?_getD, h] at hi
  · intro g hg
    exact ⟨hAO.1 g hg,hAO.2.2 g hg⟩

private theorem split_at_index {α : Type} (l : List α) (j : Nat)
    (hj : j < l.length) :
    ∃ pre g post, l = pre ++ g :: post ∧ pre.length = j := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
      cases j with
      | zero => exact ⟨[],a,l,rfl,rfl⟩
      | succ j =>
          have hj' : j < l.length := by
            simp only [List.length_cons] at hj
            omega
          obtain ⟨pre,g,post,he,hpre⟩ := ih j hj'
          refine ⟨a :: pre,g,post,?_,?_⟩
          · simp [he]
          · simp [hpre]

/-- The actual gate value is the Boolean AND of its two final operand
wire values. ReadsBack ensures that the final values equal the values
seen at the time of evaluation. -/
theorem gateVal_and_eq {n : Nat} (C : Circuit)
    (hr : ReadsBack n C) (j a b : Nat) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [a,b]) (x : Fin n → Bool) :
    gateVal n C j x =
      ((C.wires (List.ofFn x)).getD a false &&
       (C.wires (List.ofFn x)).getD b false) := by
  obtain ⟨pre,g,post,hg,hpre⟩ := split_at_index C.gates j hj
  have hat : gateAt C j = g := by
    unfold gateAt
    rw [hg, ← hpre]
    exact split_getD pre post g _
  have ha : a < n + pre.length := by
    rw [hpre]
    apply hr j hj a
    rw [hin]
    simp
  have hb : b < n + pre.length := by
    rw [hpre]
    apply hr j hj b
    rw [hin]
    simp
  have hop' : g.op = GateOp.and := hat ▸ hop
  have hin' : g.inputs = [a,b] := hat ▸ hin
  rw [prefix_wire C pre (g :: post) hg x a ha,
    prefix_wire C pre (g :: post) hg x b hb]
  let w := pre.foldl gateStep (List.ofFn x)
  have hw : w.length = n+j := by
    dsimp [w]
    rw [fold_length, hpre]
    simp
  change (C.gates.foldl gateStep (List.ofFn x)).getD (n+j) false =
    (w.getD a false && w.getD b false)
  rw [hg, List.foldl_append]
  change (post.foldl gateStep (gateStep w g)).getD (n+j) false = _
  have hi : n+j < (gateStep w g).length := by
    simp [gateStep, hw]
  rw [fold_preserves_getD post (gateStep w g) (n+j) hi]
  unfold gateStep
  rw [getD_snoc, hw]
  simp [hop', hin', GateOp.eval]

/-- Effective singleton support: includes input truth conveyed through
ANDs, unlike the raw OR-only support in TopForm.side. -/
def effectiveSingletons {n : Nat} (C : Circuit) (w : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun u => (C.wires (List.ofFn (pairInput u u))).getD w false = true

private theorem graph_pair_adj_of_true {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u v : Fin n) (h : graphFun G ∅ (pairInput u v) = true) :
    G.Adj u v := by
  have hex : ∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true := by
    simpa [graphFun] using h
  obtain ⟨a,b,hab,ha,hb⟩ := hex
  have ha' : a = u ∨ a = v := by simpa [pairInput] using ha
  have hb' : b = u ∨ b = v := by simpa [pairInput] using hb
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact False.elim ((G.ne_of_adj hab) rfl)
  · exact hab
  · exact hab.symm
  · exact False.elim ((G.ne_of_adj hab) rfl)

/-- Every crossing pair of effective singleton supports of a clean
AND is an edge of G, including the exclusion of loops. -/
theorem clean_effective_adj {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (j a b : Nat) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hin : (gateAt C j).inputs = [a,b])
    (hc : PEqualNP.TopForm.BelowF G C j)
    (u v : Fin n) (hu : u ∈ effectiveSingletons C a) (hv : v ∈ effectiveSingletons C b) :
    G.Adj u v := by
  have hu' : (C.wires (List.ofFn (pairInput u u))).getD a false = true :=
    (Finset.mem_filter.mp hu).2
  have hv' : (C.wires (List.ofFn (pairInput v v))).getD b false = true :=
    (Finset.mem_filter.mp hv).2
  have hleft := wire_monotone C hAO (pairInput u u) (pairInput u v) (by
    intro w h
    simp [pairInput] at h ⊢
    exact Or.inl h)
  have hright := wire_monotone C hAO (pairInput v v) (pairInput u v) (by
    intro w h
    simp [pairInput] at h ⊢
    exact Or.inr h)
  have ht : gateVal n C j (pairInput u v) = true := by
    rw [gateVal_and_eq C hAO.2.1 j a b hj hop hin]
    exact Bool.and_eq_true_iff.mpr ⟨hleft a hu', hright b hv'⟩
  exact graph_pair_adj_of_true G u v (hc _ ht)

/-- The effective singleton supports of an actual clean AND form a
star in a no-four-cycle graph. -/
theorem clean_effective_star {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (h4 : PEqualNP.TopForm.NoFourCycle G)
    (j a b : Nat) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hin : (gateAt C j).inputs = [a,b])
    (hc : PEqualNP.TopForm.BelowF G C j) :
    (effectiveSingletons (n := n) C a).card ≤ 1 ∨
      (effectiveSingletons (n := n) C b).card ≤ 1 := by
  apply cross_card_le_one G h4
  intro u hu v hv
  exact clean_effective_adj G C hAO j a b hj hop hin hc u v hu hv

end L2260FirstMerge

/-! ## Effective supports and component merging

This construction counts only merges of original-vertex labels.
It does not yet construct the full auxiliary graph with two junk atoms.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

/-- OR analogue of gateVal_and_eq. -/
theorem gateVal_or_eq {n : Nat} (C : Circuit)
    (hr : ReadsBack n C) (j a b : Nat) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [a,b]) (x : Fin n → Bool) :
    gateVal n C j x =
      ((C.wires (List.ofFn x)).getD a false ||
       (C.wires (List.ofFn x)).getD b false) := by
  obtain ⟨pre,g,post,hg,hpre⟩ := split_at_index C.gates j hj
  have hat : gateAt C j = g := by
    unfold gateAt
    rw [hg, ← hpre]
    exact split_getD pre post g _
  have ha : a < n + pre.length := by
    rw [hpre]
    apply hr j hj a
    rw [hin]
    simp
  have hb : b < n + pre.length := by
    rw [hpre]
    apply hr j hj b
    rw [hin]
    simp
  have hop' : g.op = GateOp.or := hat ▸ hop
  have hin' : g.inputs = [a,b] := hat ▸ hin
  rw [prefix_wire C pre (g :: post) hg x a ha,
    prefix_wire C pre (g :: post) hg x b hb]
  let w := pre.foldl gateStep (List.ofFn x)
  have hw : w.length = n+j := by
    dsimp [w]
    rw [fold_length, hpre]
    simp
  change (C.gates.foldl gateStep (List.ofFn x)).getD (n+j) false =
    (w.getD a false || w.getD b false)
  rw [hg, List.foldl_append]
  change (post.foldl gateStep (gateStep w g)).getD (n+j) false = _
  have hi : n+j < (gateStep w g).length := by
    simp [gateStep, hw]
  rw [fold_preserves_getD post (gateStep w g) (n+j) hi]
  unfold gateStep
  rw [getD_snoc, hw]
  simp [hop', hin', GateOp.eval]


/-- An original input wire is true on precisely its own singleton. -/
theorem effective_input {n : Nat} (C : Circuit) (u : Fin n) :
    effectiveSingletons C (u : Nat) = {u} := by
  ext v
  have hw : (C.wires (List.ofFn (pairInput v v))).getD (u : Nat) false =
      (List.ofFn (pairInput v v)).getD (u : Nat) false := by
    change (C.gates.foldl gateStep (List.ofFn (pairInput v v))).getD (u : Nat) false = _
    apply fold_preserves_getD
    simpa using u.isLt
  have hx : (List.ofFn (pairInput v v)).getD (u : Nat) false = pairInput v v u := by
    simp [List.getD_eq_getElem?_getD, u.isLt]
  simp only [effectiveSingletons, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hw, hx]
  simp [pairInput, eq_comm]

theorem effective_and {n : Nat} (C : Circuit) (hr : ReadsBack n C)
    (j a b : Nat) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hin : (gateAt C j).inputs = [a,b]) :
    effectiveSingletons (n := n) C (n+j) =
      effectiveSingletons C a ∩ effectiveSingletons C b := by
  ext v
  simp only [effectiveSingletons, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter]
  change gateVal n C j (pairInput v v) = true ↔ _
  rw [gateVal_and_eq C hr j a b hj hop hin]
  exact Bool.and_eq_true_iff

theorem effective_or {n : Nat} (C : Circuit) (hr : ReadsBack n C)
    (j a b : Nat) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hin : (gateAt C j).inputs = [a,b]) :
    effectiveSingletons (n := n) C (n+j) =
      effectiveSingletons C a ∪ effectiveSingletons C b := by
  ext v
  simp only [effectiveSingletons, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  change gateVal n C j (pairInput v v) = true ↔ _
  rw [gateVal_or_eq C hr j a b hj hop hin]
  exact Bool.or_eq_true_iff

/-- A clean wire at a gate index has no effective singleton inputs. -/
theorem effective_clean_empty {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : Nat)
    (hc : PEqualNP.TopForm.BelowF G C j) :
    effectiveSingletons (n := n) C (n+j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have ht : gateVal n C j (pairInput v v) = true :=
    (Finset.mem_filter.mp hv).2
  have hf := hc _ ht
  rw [graph_singleton_false G v] at hf
  contradiction

/-- All members of a set occupy one label class (empty sets allowed). -/
def SupportLocal {α β : Type} (label : α → β) (S : Finset α) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, label u = label v

theorem local_subset {α β : Type} (label : α → β) (A B : Finset α)
    (h : SupportLocal label B) (hs : A ⊆ B) : SupportLocal label A :=
  fun u hu v hv => h u (hs hu) v (hs hv)

theorem local_inter {α β : Type} [DecidableEq α] (label : α → β)
    (A B : Finset α) (h : SupportLocal label A) :
    SupportLocal label (A ∩ B) :=
  local_subset label _ _ h (fun _ hx => (Finset.mem_inter.mp hx).1)

theorem local_empty {α β : Type} (label : α → β) : SupportLocal label ∅ := by
  intro u hu
  simp at hu

theorem local_singleton {α β : Type} [DecidableEq α] (label : α → β)
    (a : α) : SupportLocal label {a} := by
  intro u hu v hv
  rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp hv]

/-- Number of nonempty classes of original vertices. -/
def labelCount {α β : Type} [Fintype α] [DecidableEq β] (label : α → β) : Nat :=
  (Finset.univ.image label).card

def mergeLabel {α β : Type} [DecidableEq β] (label : α → β)
    (p q : β) (x : α) : β :=
  if label x = q then p else label x

theorem merge_preserves_local {α β : Type} [DecidableEq β]
    (label : α → β) (p q : β) (S : Finset α)
    (h : SupportLocal label S) : SupportLocal (mergeLabel label p q) S := by
  intro u hu v hv
  unfold mergeLabel
  rw [h u hu v hv]

/-- Relabeling one entire class cannot destroy more than one class. -/
theorem merge_count {α β : Type} [Fintype α] [DecidableEq β]
    (label : α → β) (p q : β) :
    labelCount label ≤ labelCount (mergeLabel label p q) + 1 := by
  classical
  unfold labelCount
  have hs : Finset.univ.image label ⊆
      insert q (Finset.univ.image (mergeLabel label p q)) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    by_cases h : label x = q
    · rw [h]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨x,hx,by simp [mergeLabel,h]⟩
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

/-- One OR can make the union local with at most one class merge.
Every previously local support stays local. -/
theorem merge_union_local {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (label : α → β) (A B : Finset α)
    (hA : SupportLocal label A) (hB : SupportLocal label B) :
    ∃ label' : α → β,
      (∀ S : Finset α, SupportLocal label S → SupportLocal label' S) ∧
      SupportLocal label' (A ∪ B) ∧ labelCount label ≤ labelCount label' + 1 := by
  classical
  by_cases hAe : A = ∅
  · subst A
    exact ⟨label,fun _ h => h,by simpa using hB,by omega⟩
  by_cases hBe : B = ∅
  · subst B
    exact ⟨label,fun _ h => h,by simpa using hA,by omega⟩
  obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hAe
  obtain ⟨b,hb⟩ := Finset.nonempty_iff_ne_empty.mpr hBe
  let label' := mergeLabel label (label a) (label b)
  have hval : ∀ x ∈ A ∪ B, label' x = label a := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · dsimp [label',mergeLabel]
      rw [hA x hx a ha]
      split <;> rfl
    · dsimp [label',mergeLabel]
      rw [hB x hx b hb]
      simp
  refine ⟨label',fun S h => merge_preserves_local label _ _ S h,?_,?_⟩
  · intro u hu v hv
    exact (hval u hu).trans (hval v hv).symm
  · exact merge_count label _ _

end L2260FirstMerge

/-! ## Component labels for a whole official circuit

This proves the original-vertex component lower bound without invoking
normalization or constructing the two auxiliary junk atoms. The labels
are built by induction on the actual gate index.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

def dirtyOrPrefix {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : Nat) : Nat :=
  ((Finset.range j).filter fun i =>
    (gateAt C i).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C i).card

private theorem dirtyOrPrefix_succ {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : Nat) :
    dirtyOrPrefix G C (j+1) =
      dirtyOrPrefix G C j +
        (if (gateAt C j).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C j
          then 1 else 0) := by
  classical
  by_cases h : (gateAt C j).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C j
  · have he : ((insert j (Finset.range j)).filter fun i =>
          (gateAt C i).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C i) =
        insert j ((Finset.range j).filter fun i =>
          (gateAt C i).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi, hp⟩
        rcases hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr ⟨hi,hp⟩
      · rintro (hi | ⟨hi,hp⟩)
        · subst i
          exact ⟨Or.inl rfl,h⟩
        · exact ⟨Or.inr hi,hp⟩
    unfold dirtyOrPrefix
    rw [Finset.range_add_one, he, Finset.card_insert_of_notMem]
    · simp only [if_pos h]
    · intro hm
      exact Finset.notMem_range_self ((Finset.mem_filter.mp hm).1)
  · have he : ((insert j (Finset.range j)).filter fun i =>
          (gateAt C i).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C i) =
        ((Finset.range j).filter fun i =>
          (gateAt C i).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi,hp⟩
        rcases hi with hi | hi
        · subst i
          exact False.elim (h hp)
        · exact ⟨hi,hp⟩
      · rintro ⟨hi,hp⟩
        exact ⟨Or.inr hi,hp⟩
    unfold dirtyOrPrefix
    rw [Finset.range_add_one, he]
    simp only [if_neg h, Nat.add_zero]

/-- At every gate prefix, all effective singleton supports can be
made local, using at most one class merge per dirty OR. -/
theorem prefix_component_labels {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (j : Nat) (hj : j ≤ C.gates.length) :
    ∃ label : Fin n → Fin n,
      (∀ w < n+j, SupportLocal label (effectiveSingletons C w)) ∧
      n ≤ labelCount label + dirtyOrPrefix G C j := by
  classical
  induction j with
  | zero =>
      refine ⟨id,?_,?_⟩
      · intro w hw
        have hw' : w < n := by omega
        have he : effectiveSingletons (n := n) C w = {⟨w,hw'⟩} :=
          effective_input C (⟨w,hw'⟩ : Fin n)
        rw [he]
        exact local_singleton id (⟨w,hw'⟩ : Fin n)
      · simp [labelCount, dirtyOrPrefix]
  | succ j ih =>
      have hj' : j < C.gates.length := by omega
      obtain ⟨label,hlocal,hcount⟩ := ih (by omega)
      have hmem : gateAt C j ∈ C.gates := by
        obtain ⟨pre,g,post,hg,hpre⟩ := split_at_index C.gates j hj'
        have hat : gateAt C j = g := by
          unfold gateAt
          rw [hg, ← hpre]
          exact split_getD pre post g _
        rw [hat,hg]
        simp
      obtain ⟨a,b,hin⟩ := two_inputs (gateAt C j).inputs (hAO.2.2 _ hmem)
      have ha : a < n+j := by
        apply hAO.2.1 j hj' a
        rw [hin]
        simp
      have hb : b < n+j := by
        apply hAO.2.1 j hj' b
        rw [hin]
        simp
      -- If no relabeling is needed, extend the old locality invariant.
      have extend (hnew : SupportLocal label (effectiveSingletons C (n+j))) :
          ∀ w < n+(j+1), SupportLocal label (effectiveSingletons C w) := by
        intro w hw
        by_cases h : w < n+j
        · exact hlocal w h
        · have he : w = n+j := by omega
          rw [he]
          exact hnew
      rcases hAO.1 _ hmem with hop | hop
      · have hnew : SupportLocal label (effectiveSingletons C (n+j)) := by
          rw [effective_and C hAO.2.1 j a b hj' hop hin]
          exact local_inter label _ _ (hlocal a ha)
        refine ⟨label,extend hnew,?_⟩
        rw [dirtyOrPrefix_succ]
        split <;> omega
      · by_cases hc : PEqualNP.TopForm.BelowF G C j
        · have hnew : SupportLocal label (effectiveSingletons C (n+j)) := by
            rw [effective_clean_empty G C j hc]
            exact local_empty label
          refine ⟨label,extend hnew,?_⟩
          rw [dirtyOrPrefix_succ]
          split <;> omega
        · obtain ⟨label',hpres,hunion,hmerge⟩ :=
            merge_union_local label (effectiveSingletons C a)
              (effectiveSingletons C b) (hlocal a ha) (hlocal b hb)
          refine ⟨label',?_,?_⟩
          · intro w hw
            by_cases h : w < n+j
            · exact hpres _ (hlocal w h)
            · have he : w = n+j := by omega
              rw [he,effective_or C hAO.2.1 j a b hj' hop hin]
              exact hunion
          · rw [dirtyOrPrefix_succ]
            have hd : (gateAt C j).op = GateOp.or ∧
                ¬ PEqualNP.TopForm.BelowF G C j := ⟨hop,hc⟩
            rw [if_pos hd]
            omega

/-- The actual circuit admits a partition of its original inputs with
at least n - |orN| blocks. Every real wire's effective singleton
support is local in this partition. -/
theorem circuit_component_labels {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) :
    ∃ label : Fin n → Fin n,
      (∀ w < n+C.gates.length, SupportLocal label (effectiveSingletons C w)) ∧
      n ≤ labelCount label + (PEqualNP.TopForm.orN G C).card := by
  have h := prefix_component_labels G C hAO C.gates.length (Nat.le_refl _)
  simpa only [dirtyOrPrefix, PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere] using h

end L2260FirstMerge

/-! ## Incompatible edge cuts for the actual circuit

The component partition here only needs locality of the effective
singleton sets. The complete auxiliary-atom partition used in the
strong SAT encoding is a separate, stronger construction.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

def GateCross {n : Nat} (C : Circuit) (j : Nat) (u v : Fin n) : Prop :=
  Opposite (finalSample C u v (PEqualNP.TopForm.opnd C j 0))
    (finalSample C u v (PEqualNP.TopForm.opnd C j 1))

theorem edge_has_gate_cross {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (u v : Fin n) (he : G.Adj u v) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ GateCross C j u v := by
  obtain ⟨j,hj,hop,a,b,hin,hcross⟩ := graph_edge_first_merge_indexed G C hmin u v he
  refine ⟨j,hj,hop,?_⟩
  simpa [GateCross, PEqualNP.TopForm.opnd, hin] using hcross

theorem gate_cross_pair {n : Nat} (C : Circuit) (j : Nat) (u v : Fin n)
    (h : GateCross C j u v) :
    CrossPair (effectiveSingletons C (PEqualNP.TopForm.opnd C j 0))
      (effectiveSingletons C (PEqualNP.TopForm.opnd C j 1)) u v := by
  unfold GateCross Opposite at h
  simp only [CrossPair, effectiveSingletons, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases h with h | h
  · exact Or.inl ⟨h.1,h.2.2.2⟩
  · exact Or.inr ⟨h.2.1,h.2.2.1⟩

def SameBlockPair {α β : Type} (label : α → β) (u v x y : α) : Prop :=
  (label u = label x ∧ label v = label y) ∨
    (label u = label y ∧ label v = label x)

theorem local_cross_same_pair {α β : Type} (label : α → β)
    (A B : Finset α) (hA : SupportLocal label A) (hB : SupportLocal label B)
    (u v x y : α) (he : CrossPair A B u v) (hf : CrossPair A B x y) :
    SameBlockPair label u v x y := by
  rcases he with ⟨hu,hv⟩ | ⟨hv,hu⟩ <;>
    rcases hf with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · exact Or.inl ⟨hA u hu x hx,hB v hv y hy⟩
  · exact Or.inr ⟨hA u hu y hy,hB v hv x hx⟩
  · exact Or.inr ⟨hB u hu y hy,hA v hv x hx⟩
  · exact Or.inl ⟨hB u hu x hx,hA v hv y hy⟩

/-- Two edges crossing the same clean AND share an endpoint AND
have the same unordered pair of component labels. -/
theorem clean_cross_compatible {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (label : Fin n → Fin n)
    (hl : ∀ w < n+C.gates.length, SupportLocal label (effectiveSingletons C w))
    (j : Nat) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hc : PEqualNP.TopForm.BelowF G C j)
    (u v x y : Fin n) (he : GateCross C j u v) (hf : GateCross C j x y) :
    (u = x ∨ u = y ∨ v = x ∨ v = y) ∧ SameBlockPair label u v x y := by
  have hmem : gateAt C j ∈ C.gates := by
    obtain ⟨pre,g,post,hg,hpre⟩ := split_at_index C.gates j hj
    have hat : gateAt C j = g := by
      unfold gateAt
      rw [hg, ← hpre]
      exact split_getD pre post g _
    rw [hat,hg]
    simp
  obtain ⟨a,b,hin⟩ := two_inputs (gateAt C j).inputs (hAO.2.2 _ hmem)
  have ha : a < n+j := by
    apply hAO.2.1 j hj a
    rw [hin]
    simp
  have hb : b < n+j := by
    apply hAO.2.1 j hj b
    rw [hin]
    simp
  let A := effectiveSingletons (n := n) C a
  let B := effectiveSingletons (n := n) C b
  have he' : CrossPair A B u v := by
    simpa [A,B,PEqualNP.TopForm.opnd,hin] using gate_cross_pair C j u v he
  have hf' : CrossPair A B x y := by
    simpa [A,B,PEqualNP.TopForm.opnd,hin] using gate_cross_pair C j x y hf
  have hadj : ∀ s ∈ A, ∀ t ∈ B, G.Adj s t := by
    intro s hs t ht
    exact clean_effective_adj G C hAO j a b hj hop hin hc s t hs ht
  exact ⟨cross_pairs_share_endpoint G h4 A B hadj u v x y he' hf',
    local_cross_same_pair label A B (hl a (by omega)) (hl b (by omega)) u v x y he' hf'⟩

/-- A clique of mutually incompatible edges, none of which can be
crossed by a dirty AND, needs at least that many distinct clean ANDs.
The edges are stored as ordered vertex pairs; the incompatibility
hypothesis prohibits counting both orientations of one edge. -/
theorem incompatible_edges_bound {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C) (h4 : PEqualNP.TopForm.NoFourCycle G)
    (label : Fin n → Fin n)
    (hl : ∀ w < n+C.gates.length, SupportLocal label (effectiveSingletons C w))
    (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, G.Adj e.1 e.2)
    (hn : ∀ e ∈ E, ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        GateCross C j e.1 e.2 → PEqualNP.TopForm.BelowF G C j)
    (hi : ∀ e ∈ E, ∀ f ∈ E, e ≠ f →
      ¬ ((e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2) ∧
        SameBlockPair label e.1 e.2 f.1 f.2)) :
    E.card ≤ (PEqualNP.TopForm.tops G C).card := by
  classical
  have hex : ∀ e : E, ∃ j ∈ PEqualNP.TopForm.tops G C, GateCross C j e.val.1 e.val.2 := by
    intro e
    obtain ⟨j,hj,hop,hcross⟩ := edge_has_gate_cross G C hmin e.val.1 e.val.2 (hE e.val e.property)
    have hc := hn e.val e.property j hj hop hcross
    refine ⟨j,?_,hcross⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hop,hc⟩
  let chooseGate : E → PEqualNP.TopForm.tops G C := fun e =>
    ⟨Classical.choose (hex e),(Classical.choose_spec (hex e)).1⟩
  have hg (e : E) : GateCross C (chooseGate e).val e.val.1 e.val.2 :=
    (Classical.choose_spec (hex e)).2
  apply Finset.card_le_card_of_injective (f := chooseGate)
  intro e f h
  apply Subtype.ext
  by_contra hne
  have hval : (chooseGate e).val = (chooseGate f).val := congrArg Subtype.val h
  have htop : (chooseGate e).val ∈ PEqualNP.TopForm.tops G C := (chooseGate e).property
  have ht : (chooseGate e).val < C.gates.length ∧
      (gateAt C (chooseGate e).val).op = GateOp.and ∧
      PEqualNP.TopForm.BelowF G C (chooseGate e).val := by
    obtain ⟨hr,hop,hc⟩ := Finset.mem_filter.mp htop
    exact ⟨Finset.mem_range.mp hr,hop,hc⟩
  have hf : GateCross C (chooseGate e).val f.val.1 f.val.2 := hval.symm ▸ hg f
  exact hi e.val e.property f.val f.property hne
    (clean_cross_compatible G C hmin.1 h4 label hl _ ht.1 ht.2.1 ht.2.2
      e.val.1 e.val.2 f.val.1 f.val.2 (hg e) hf)

end L2260FirstMerge

/-! ## Auxiliary atom labels

The original inputs and the two junk gates are separate symbolic atoms.
A bearing junk atom has a nonempty effective singleton set and is
attached to an original vertex in that set. OR operations merge the
classes of their symbolic operands. These are reusable lemmas for the
auxiliary-atom construction, not yet its circuit-level instantiation.
-/
namespace L2260FirstMerge

/-- Effective singleton support obtained by evaluating symbolic atoms. -/
def atomEffective {α γ : Type} [DecidableEq γ]
    (truth : α → Finset γ) (S : Finset α) : Finset γ :=
  S.biUnion truth

/-- Every singleton carried by an atom belongs to that atom's class. -/
def AtomLinked {α β γ : Type} (label : α → β) (raw : γ → α)
    (truth : α → Finset γ) : Prop :=
  ∀ a u, u ∈ truth a → label (raw u) = label a

theorem atom_effective_local {α β γ : Type} [DecidableEq γ]
    (label : α → β) (raw : γ → α) (truth : α → Finset γ)
    (S : Finset α) (hl : AtomLinked label raw truth)
    (hs : SupportLocal label S) :
    SupportLocal (fun u => label (raw u)) (atomEffective truth S) := by
  intro u hu v hv
  obtain ⟨a,ha,hua⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨b,hb,hvb⟩ := Finset.mem_biUnion.mp hv
  exact (hl a u hua).trans ((hs a ha b hb).trans (hl b v hvb).symm)

theorem atom_effective_union {α γ : Type} [DecidableEq α] [DecidableEq γ]
    (truth : α → Finset γ) (A B : Finset α) :
    atomEffective truth (A ∪ B) = atomEffective truth A ∪ atomEffective truth B := by
  ext u
  simp only [atomEffective, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨a,ha,hu⟩
    rcases ha with ha | ha
    · exact Or.inl ⟨a,ha,hu⟩
    · exact Or.inr ⟨a,ha,hu⟩
  · rintro (⟨a,ha,hu⟩ | ⟨a,ha,hu⟩)
    · exact ⟨a,Or.inl ha,hu⟩
    · exact ⟨a,Or.inr ha,hu⟩

theorem merge_preserves_equal {α β : Type} [DecidableEq β]
    (label : α → β) (p q : β) (a b : α) (h : label a = label b) :
    mergeLabel label p q a = mergeLabel label p q b := by
  unfold mergeLabel
  rw [h]

theorem merge_preserves_linked {α β γ : Type} [DecidableEq β]
    (label : α → β) (raw : γ → α) (truth : α → Finset γ)
    (p q : β) (h : AtomLinked label raw truth) :
    AtomLinked (mergeLabel label p q) raw truth := by
  intro a u hu
  exact merge_preserves_equal label p q _ _ (h a u hu)

/-- A new junk atom with a nonempty, local singleton set can be linked
to all those original vertices by at most one class merge. Empty
singleton sets require no merge at all. All old equalities survive. -/
theorem attach_junk {α β γ : Type} [Fintype α] [DecidableEq β]
    (label : α → β) (raw : γ → α) (j : α) (U : Finset γ)
    (hU : SupportLocal (fun u => label (raw u)) U) :
    ∃ label' : α → β,
      (∀ a b, label a = label b → label' a = label' b) ∧
      (∀ u ∈ U, label' (raw u) = label' j) ∧
      labelCount label ≤ labelCount label' + (if U.Nonempty then 1 else 0) := by
  classical
  by_cases he : U.Nonempty
  · obtain ⟨u,hu⟩ := he
    let label' := mergeLabel label (label (raw u)) (label j)
    refine ⟨label',fun a b h => merge_preserves_equal label _ _ a b h,?_,?_⟩
    · intro v hv
      have hvu : label (raw v) = label (raw u) := hU v hv u hu
      change mergeLabel label (label (raw u)) (label j) (raw v) =
        mergeLabel label (label (raw u)) (label j) j
      unfold mergeLabel
      rw [hvu,if_pos rfl]
      split <;> rfl
    · have hm := merge_count label (label (raw u)) (label j)
      have hne : U.Nonempty := ⟨u,hu⟩
      simpa only [if_pos hne] using hm
  · refine ⟨label,fun _ _ h => h,?_,?_⟩
    · intro u hu
      exact False.elim (he ⟨u,hu⟩)
    · simp only [if_neg he,Nat.add_zero,Nat.le_refl]

/-- A sequence of class merges loses at most one class per operation. -/
def mergeSequence {α β : Type} [DecidableEq β]
    (label : α → β) (ops : List (β × β)) : α → β :=
  ops.foldl (fun l p => mergeLabel l p.1 p.2) label

theorem merge_sequence_count {α β : Type} [Fintype α] [DecidableEq β]
    (label : α → β) (ops : List (β × β)) :
    labelCount label ≤ labelCount (mergeSequence label ops) + ops.length := by
  induction ops generalizing label with
  | nil => simp [mergeSequence]
  | cons p ops ih =>
      have h1 := merge_count label p.1 p.2
      have h2 := ih (mergeLabel label p.1 p.2)
      change labelCount label ≤
        labelCount (mergeSequence (mergeLabel label p.1 p.2) ops) + (p :: ops).length
      simp only [List.length_cons]
      omega

/-- Inserting a junk label costs no additional class if that label is
already represented by an original vertex. -/
theorem two_junk_labels_count {β : Type} [DecidableEq β]
    (R : Finset β) (a b : β) (t0 t1 : Bool)
    (h0 : t0 = true → a ∈ R) (h1 : t1 = true → b ∈ R) :
    (insert a (insert b R)).card + t0.toNat + t1.toNat ≤ R.card + 2 := by
  cases t0 <;> cases t1
  · have ha := Finset.card_insert_le a (insert b R)
    have hb := Finset.card_insert_le b R
    simp only [Bool.toNat_false] at ⊢
    omega
  · have hb : b ∈ R := h1 rfl
    rw [Finset.insert_eq_of_mem hb]
    have ha := Finset.card_insert_le a R
    simp only [Bool.toNat_false,Bool.toNat_true] at ⊢
    omega
  · have ha : a ∈ R := h0 rfl
    have ha' : a ∈ insert b R := Finset.mem_insert_of_mem ha
    rw [Finset.insert_eq_of_mem ha']
    have hb := Finset.card_insert_le b R
    simp only [Bool.toNat_false,Bool.toNat_true] at ⊢
    omega
  · rw [Finset.insert_eq_of_mem (h1 rfl),Finset.insert_eq_of_mem (h0 rfl)]
    simp only [Bool.toNat_true]
    omega

/-- Combining the two-junk class bound with the rank lower bound gives
the original-vertex class bound. At equality, both bounds are tight. -/
theorem auxiliary_rank_tight (n r t b total : Nat)
    (hrank : n+2 ≤ total+r+t) (hclasses : total+t ≤ b+2)
    (heq : n = b+r) :
    total+t = b+2 ∧ n+2 = total+r+t := by
  omega

end L2260FirstMerge

/-! ## Symbolic OR supports of the actual circuit

An atom is the wire of an original input or an AND gate. OR gates are
expanded recursively, stopping at atoms. Clean AND atoms are not yet
excluded from dirty OR cones; that needs the top-form argument.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

def Expandable (n : Nat) (C : Circuit) (w : Nat) : Prop :=
  n ≤ w ∧ w < n+C.gates.length ∧
    (gateAt C (w-n)).op = GateOp.or ∧
    PEqualNP.TopForm.opnd C (w-n) 0 < w ∧
    PEqualNP.TopForm.opnd C (w-n) 1 < w

instance (n : Nat) (C : Circuit) (w : Nat) : Decidable (Expandable n C w) := by
  unfold Expandable
  infer_instance

/-- Recursion is on the actual wire index. The guard makes it total
even for malformed circuits. Under IsAO2 every real OR is expandable. -/
def symbolicSupport (n : Nat) (C : Circuit) (w : Nat) : Finset Nat :=
  if h : Expandable n C w then
    symbolicSupport n C (PEqualNP.TopForm.opnd C (w-n) 0) ∪
      symbolicSupport n C (PEqualNP.TopForm.opnd C (w-n) 1)
  else {w}
termination_by w
decreasing_by
  · exact h.2.2.2.1
  · exact h.2.2.2.2

theorem symbolic_expand (n : Nat) (C : Circuit) (w : Nat)
    (h : Expandable n C w) :
    symbolicSupport n C w =
      symbolicSupport n C (PEqualNP.TopForm.opnd C (w-n) 0) ∪
      symbolicSupport n C (PEqualNP.TopForm.opnd C (w-n) 1) := by
  rw [symbolicSupport] <;> simp [h]

theorem symbolic_atom (n : Nat) (C : Circuit) (w : Nat)
    (h : ¬ Expandable n C w) : symbolicSupport n C w = {w} := by
  rw [symbolicSupport] <;> simp [h]

private theorem actual_gate_mem (C : Circuit) (j : Nat) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  obtain ⟨pre,g,post,hg,hpre⟩ := split_at_index C.gates j hj
  have hat : gateAt C j = g := by
    unfold gateAt
    rw [hg, ← hpre]
    exact split_getD pre post g _
  rw [hat,hg]
  simp

/-- Both official operands are present, in order, and read backwards. -/
theorem actual_opnds {n : Nat} (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (j : Nat) (hj : j < C.gates.length) :
    (gateAt C j).inputs = [PEqualNP.TopForm.opnd C j 0, PEqualNP.TopForm.opnd C j 1] ∧
    PEqualNP.TopForm.opnd C j 0 < n+j ∧ PEqualNP.TopForm.opnd C j 1 < n+j := by
  obtain ⟨a,b,hin⟩ := two_inputs (gateAt C j).inputs
    (hAO.2.2 _ (actual_gate_mem C j hj))
  have ha : a < n+j := by
    apply hAO.2.1 j hj a
    rw [hin]
    simp
  have hb : b < n+j := by
    apply hAO.2.1 j hj b
    rw [hin]
    simp
  simp [PEqualNP.TopForm.opnd, hin, ha, hb]

theorem real_or_expandable {n : Nat} (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (j : Nat) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) : Expandable n C (n+j) := by
  obtain ⟨_,ha,hb⟩ := actual_opnds C hAO j hj
  have he : n+j-n = j := by omega
  unfold Expandable
  rw [he]
  exact ⟨by omega,by omega,hop,ha,hb⟩

/-- The symbolic OR support evaluates to exactly the effective
singleton set of the original wire, using actual atom truth values. -/
theorem symbolic_effective {n : Nat} (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (w : Nat) :
    atomEffective (effectiveSingletons (n := n) C) (symbolicSupport n C w) =
      effectiveSingletons C w := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
      by_cases h : Expandable n C w
      · obtain ⟨hn,hw,hop,ha,hb⟩ := h
        have hj : w-n < C.gates.length := by omega
        have he : n+(w-n) = w := by omega
        rw [symbolic_expand n C w ⟨hn,hw,hop,ha,hb⟩, atom_effective_union,
          ih _ ha, ih _ hb]
        have hs := effective_or C hAO.2.1 (w-n) _ _ hj hop
          (actual_opnds C hAO (w-n) hj).1
        rw [he] at hs
        exact hs.symm
      · rw [symbolic_atom n C w h]
        ext u
        simp [atomEffective]

/-- Every leaf of a symbolic support is at or before the root wire. -/
theorem symbolic_leaf_le (n : Nat) (C : Circuit) (w a : Nat)
    (ha : a ∈ symbolicSupport n C w) : a ≤ w := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
      by_cases h : Expandable n C w
      · rw [symbolic_expand n C w h] at ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact (ih _ h.2.2.2.1 ha).trans (Nat.le_of_lt h.2.2.2.1)
        · exact (ih _ h.2.2.2.2 ha).trans (Nat.le_of_lt h.2.2.2.2)
      · rw [symbolic_atom n C w h] at ha
        exact (Finset.mem_singleton.mp ha).le

/-- For a real root in a well-formed circuit every leaf is an original
input or a real AND wire, never an OR wire. -/
theorem symbolic_leaf_kind {n : Nat} (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (w : Nat) (hw : w < n+C.gates.length)
    (a : Nat) (ha : a ∈ symbolicSupport n C w) :
    a < n ∨ ∃ j < C.gates.length, a = n+j ∧ (gateAt C j).op = GateOp.and := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
      by_cases h : Expandable n C w
      · rw [symbolic_expand n C w h] at ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact ih _ h.2.2.2.1 (Nat.lt_trans h.2.2.2.1 hw) ha
        · exact ih _ h.2.2.2.2 (Nat.lt_trans h.2.2.2.2 hw) ha
      · rw [symbolic_atom n C w h] at ha
        have he : a = w := Finset.mem_singleton.mp ha
        subst a
        by_cases hn : w < n
        · exact Or.inl hn
        · have hj : w-n < C.gates.length := by omega
          have heq : n+(w-n) = w := by omega
          rcases hAO.1 _ (actual_gate_mem C (w-n) hj) with hop | hop
          · exact Or.inr ⟨w-n,hj,heq.symm,hop⟩
          · have hx := real_or_expandable C hAO (w-n) hj hop
            rw [heq] at hx
            exact False.elim (h hx)

end L2260FirstMerge

/-! ## Connecting symbolic leaves to the official strict cone

TopForm forbids a clean AND inside any AND's strict cone. In this
section we prove that an AND leaf of an operand's symbolic support is
in that cone. Dirty ORs not yet known to feed an AND require a further
minimality/output argument.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

private theorem generic_getD_snoc {α : Type} (xs : List α) (x d : α) (i : Nat) :
    (xs ++ [x]).getD i d = if i = xs.length then x else xs.getD i d := by
  induction xs generalizing i with
  | nil => cases i <;> simp
  | cons a xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          simpa only [List.cons_append, List.getD_cons_succ,
            List.length_cons, Nat.succ.injEq] using ih i

private theorem cone_fold_length (n : Nat) (gs : List Gate) (cs : List (List Nat)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
      change (gs.foldl (coneStep n) (coneStep n cs g)).length = _
      rw [ih]
      simp [coneStep] <;> omega

private theorem cone_fold_preserves (n : Nat) (gs : List Gate) (cs : List (List Nat))
    (i : Nat) (hi : i < cs.length) :
    (gs.foldl (coneStep n) cs).getD i [] = cs.getD i [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
      change (gs.foldl (coneStep n) (coneStep n cs g)).getD i [] = _
      have hi' : i < (coneStep n cs g).length := by
        simp [coneStep] <;> omega
      rw [ih _ hi']
      unfold coneStep
      rw [generic_getD_snoc]
      simp [Nat.ne_of_lt hi]

/-- Every earlier gate read by a gate belongs to its strict cone,
as do all gates in the earlier gate's cone. -/
theorem cone_of_read {n : Nat} (C : Circuit) (j k i : Nat)
    (hj : j < C.gates.length) (hk : k < j)
    (hread : n+k ∈ (gateAt C j).inputs)
    (hi : i = k ∨ InCone n C i k) : InCone n C i j := by
  obtain ⟨pre,g,post,hg,hpre⟩ := split_at_index C.gates j hj
  have hat : gateAt C j = g := by
    unfold gateAt
    rw [hg, ← hpre]
    exact split_getD pre post g _
  let cs := pre.foldl (coneStep n) []
  have hlen : cs.length = j := by
    dsimp [cs]
    rw [cone_fold_length, hpre]
    simp
  have hkcs : k < cs.length := by omega
  have hjcs : j < (coneStep n cs g).length := by
    simp [coneStep, hlen]
  have hpast : (cones n C).getD k [] = cs.getD k [] := by
    unfold cones
    rw [hg, List.foldl_append]
    change ((g :: post).foldl (coneStep n) cs).getD k [] = _
    exact cone_fold_preserves n (g :: post) cs k hkcs
  unfold InCone cones
  rw [hg, List.foldl_append]
  change i ∈ (post.foldl (coneStep n) (coneStep n cs g)).getD j []
  rw [cone_fold_preserves n post _ j hjcs]
  unfold coneStep
  rw [generic_getD_snoc, hlen, if_pos rfl]
  apply List.mem_flatMap.mpr
  refine ⟨n+k,?_,?_⟩
  · apply List.mem_filter.mpr
    refine ⟨hat ▸ hread,?_⟩
    simp only [decide_eq_true_eq]
    omega
  · have he : n+k-n = k := by omega
    rw [he]
    rcases hi with hi | hi
    · exact List.mem_cons.mpr (Or.inl hi)
    · apply List.mem_cons.mpr
      right
      change i ∈ (cones n C).getD k [] at hi
      rw [hpast] at hi
      exact hi

/-- A symbolic AND leaf is either the root gate itself or lies in
its strict cone. This is a structural statement, independent of
singleton truth. -/
theorem symbolic_leaf_cone {n : Nat} (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (w : Nat)
    (hw : w < n+C.gates.length) (i : Nat)
    (hi : n+i ∈ symbolicSupport n C w) :
    w = n+i ∨ ∃ j < C.gates.length, w = n+j ∧ InCone n C i j := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
      by_cases h : Expandable n C w
      · obtain ⟨hn,_,hop,ha,hb⟩ := h
        have hj : w-n < C.gates.length := by omega
        have he : w = n+(w-n) := by omega
        have hinput := (actual_opnds C hAO (w-n) hj).1
        have extend (z : Nat) (hz : z < w) (hr : z ∈ (gateAt C (w-n)).inputs)
            (hm : n+i ∈ symbolicSupport n C z) :
            w = n+i ∨ ∃ j < C.gates.length, w = n+j ∧ InCone n C i j := by
          refine Or.inr ⟨w-n,hj,he,?_⟩
          rcases ih z hz (Nat.lt_trans hz hw) hm with hs | ⟨k,hk,hz',hc⟩
          · have hik : i < w-n := by omega
            exact cone_of_read C (w-n) i i hj hik (hs ▸ hr) (Or.inl rfl)
          · have hkj : k < w-n := by omega
            exact cone_of_read C (w-n) k i hj hkj (hz' ▸ hr) (Or.inr hc)
        rw [symbolic_expand n C w ⟨hn,hw,hop,ha,hb⟩] at hi
        rcases Finset.mem_union.mp hi with hi | hi
        · apply extend _ ha _ hi
          rw [hinput]
          simp
        · apply extend _ hb _ hi
          rw [hinput]
          simp
      · rw [symbolic_atom n C w h] at hi
        exact Or.inl (Finset.mem_singleton.mp hi).symm

/-- All AND atoms in an AND operand's OR support are dirty under
the official TopForm assumption. -/
theorem and_operand_atoms_junk {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) (j : Nat)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (w : Nat) (hr : w ∈ (gateAt C j).inputs)
    (i : Nat) (hi : n+i ∈ symbolicSupport n C w)
    (hiop : (gateAt C i).op = GateOp.and) :
    i ∈ PEqualNP.TopForm.junk G C := by
  have hw := hAO.2.1 j hj w hr
  have hreal : w < n+C.gates.length := by omega
  have hle := symbolic_leaf_le n C w (n+i) hi
  have hil : i < C.gates.length := by omega
  have hc : InCone n C i j := by
    rcases symbolic_leaf_cone C hAO w hreal i hi with he | ⟨k,hk,he,hc⟩
    · have hij : i < j := by omega
      exact cone_of_read C j i i hj hij (he ▸ hr) (Or.inl rfl)
    · have hkj : k < j := by omega
      exact cone_of_read C j k i hj hkj (he ▸ hr) (Or.inr hc)
  have hd : ¬ PEqualNP.TopForm.BelowF G C i := by
    intro hclean
    exact htop i hil j hj hiop hclean hop hc
  have hex : ∃ x : Fin n → Bool, gateVal n C i x = true ∧ graphFun G ∅ x = false := by
    classical
    unfold PEqualNP.TopForm.BelowF at hd
    push_neg at hd
    obtain ⟨x,hx,hf⟩ := hd
    exact ⟨x,hx,by cases h : graphFun G ∅ x <;> simp_all⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hil,hiop,hil,hex⟩

end L2260FirstMerge

/-! ## Full symbolic evaluation and the raw/junk atom universe

For the auxiliary partition it suffices initially to consider supports
contained in the raw/junk universe. Every AND operand has such a
support by TopForm. Any OR with such a support is dirty, so these
ORs can be charged to orN without first deleting unused gates.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

theorem symbolic_nonempty (n : Nat) (C : Circuit) (w : Nat) :
    (symbolicSupport n C w).Nonempty := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
      by_cases h : Expandable n C w
      · rw [symbolic_expand n C w h]
        obtain ⟨a,ha⟩ := ih _ h.2.2.2.1
        exact ⟨a,Finset.mem_union.mpr (Or.inl ha)⟩
      · rw [symbolic_atom n C w h]
        exact ⟨w,Finset.mem_singleton.mpr rfl⟩

/-- OR expansion agrees with the actual evaluation on every input,
not just singleton inputs. -/
theorem symbolic_eval {n : Nat} (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool) (w : Nat) :
    wireVal n C w x = true ↔
      ∃ a ∈ symbolicSupport n C w, wireVal n C a x = true := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
      by_cases h : Expandable n C w
      · obtain ⟨hn,hw,hop,ha,hb⟩ := h
        have hj : w-n < C.gates.length := by omega
        have he : n+(w-n) = w := by omega
        have hv := gateVal_or_eq C hAO.2.1 (w-n) _ _ hj hop
          (actual_opnds C hAO (w-n) hj).1 x
        change wireVal n C (n+(w-n)) x =
          (wireVal n C (PEqualNP.TopForm.opnd C (w-n) 0) x ||
            wireVal n C (PEqualNP.TopForm.opnd C (w-n) 1) x) at hv
        rw [he] at hv
        rw [hv, Bool.or_eq_true_iff, ih _ ha, ih _ hb,
          symbolic_expand n C w ⟨hn,hw,hop,ha,hb⟩]
        constructor
        · rintro (⟨a,hm,ht⟩ | ⟨a,hm,ht⟩)
          · exact ⟨a,Finset.mem_union.mpr (Or.inl hm),ht⟩
          · exact ⟨a,Finset.mem_union.mpr (Or.inr hm),ht⟩
        · rintro ⟨a,hm,ht⟩
          rcases Finset.mem_union.mp hm with hm | hm
          · exact Or.inl ⟨a,hm,ht⟩
          · exact Or.inr ⟨a,hm,ht⟩
      · rw [symbolic_atom n C w h]
        simp

/-- The universe used for internal ORs and AND operands: raw inputs
and dirty AND wire indices, with no clean AND atoms. -/
def atomUniverse {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) : Finset Nat :=
  Finset.range n ∪ (PEqualNP.TopForm.junk G C).image (fun j => n+j)

theorem atom_universe_card {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) :
    (atomUniverse G C).card = n + (PEqualNP.TopForm.junk G C).card := by
  have hd : Disjoint (Finset.range n)
      ((PEqualNP.TopForm.junk G C).image (fun j => n+j)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp hb
    have hlt := Finset.mem_range.mp ha
    omega
  have hinj : Function.Injective (fun j : Nat => n+j) := by
    intro a b h
    change n+a = n+b at h
    omega
  unfold atomUniverse
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hinj,
    Finset.card_range]

theorem and_operand_support_subset {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) (j : Nat)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (w : Nat) (hr : w ∈ (gateAt C j).inputs) :
    symbolicSupport n C w ⊆ atomUniverse G C := by
  have hw := hAO.2.1 j hj w hr
  have hw' : w < n+C.gates.length := by omega
  intro a ha
  rcases symbolic_leaf_kind C hAO w hw' a ha with hraw | ⟨i,hi,he,hiop⟩
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hraw))
  · have hmem : n+i ∈ symbolicSupport n C w := he ▸ ha
    have hjunk := and_operand_atoms_junk G C hAO htop j hj hop w hr i hmem hiop
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i,hjunk,he.symm⟩))

theorem and_operand_atom_bound {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) (j : Nat)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (w : Nat) (hr : w ∈ (gateAt C j).inputs)
    (h2 : (PEqualNP.TopForm.junk G C).card = 2) :
    (symbolicSupport n C w).card ≤ n+2 := by
  have hc := Finset.card_le_card (and_operand_support_subset G C hAO htop j hj hop w hr)
  rw [atom_universe_card, h2] at hc
  exact hc

/-- Every raw/junk atom has some input on which it is true while the
graph function is false. -/
theorem atom_dirty_witness {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (a : Nat) (ha : a ∈ atomUniverse G C) :
    ∃ x : Fin n → Bool, wireVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_union.mp ha with hr | hj
  · have hlt := Finset.mem_range.mp hr
    let u : Fin n := ⟨a,hlt⟩
    have hm : u ∈ effectiveSingletons C a := by
      have he : effectiveSingletons C a = ({u} : Finset (Fin n)) :=
        effective_input C u
      rw [he]
      exact Finset.mem_singleton.mpr rfl
    exact ⟨pairInput u u,(Finset.mem_filter.mp hm).2,graph_singleton_false G u⟩
  · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hj
    have hd : IsDirtyAnd n G C j := (Finset.mem_filter.mp hj).2
    obtain ⟨_,_,x,hx,hf⟩ := hd
    refine ⟨x,?_,hf⟩
    rw [← he]
    exact hx

/-- Every real OR over a raw/junk-only support belongs to orN.
This covers the relevant ORs inside AND operands without assuming
that every gate of the circuit has a path to the output. -/
theorem raw_junk_or_dirty {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (j : Nat) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hs : symbolicSupport n C (n+j) ⊆ atomUniverse G C) :
    j ∈ PEqualNP.TopForm.orN G C := by
  obtain ⟨a,ha⟩ := symbolic_nonempty n C (n+j)
  obtain ⟨x,hx,hf⟩ := atom_dirty_witness G C a (hs ha)
  have ht : gateVal n C j x = true :=
    (symbolic_eval C hAO x (n+j)).mpr ⟨a,ha,hx⟩
  have hd : ¬ PEqualNP.TopForm.BelowF G C j := by
    intro hc
    have hh := hc x ht
    rw [hf] at hh
    contradiction
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hop,hd⟩

end L2260FirstMerge

/-! ## Actual auxiliary partition: finite atom rank

Labels are natural numbers, but the rank counts only labels represented
in atomUniverse. This permits induction over the actual circuit without
counting clean ANDs or OR wires as extra atoms.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

def atomRank (U : Finset Nat) (label : Nat → Nat) : Nat :=
  (U.image label).card

theorem atom_rank_merge (U : Finset Nat) (label : Nat → Nat) (p q : Nat) :
    atomRank U label ≤ atomRank U (mergeLabel label p q) + 1 := by
  unfold atomRank
  have hs : U.image label ⊆ insert q (U.image (mergeLabel label p q)) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    by_cases h : label x = q
    · rw [h]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x,hx,by simp [mergeLabel,h]⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

def PreservesLabels (l l' : Nat → Nat) : Prop :=
  ∀ a b, l a = l b → l' a = l' b

theorem preserves_local (l l' : Nat → Nat) (hp : PreservesLabels l l')
    (S : Finset Nat) (hs : SupportLocal l S) : SupportLocal l' S := by
  intro a ha b hb
  exact hp a b (hs a ha b hb)

theorem atom_rank_union (U : Finset Nat) (l : Nat → Nat) (A B : Finset Nat)
    (hA : SupportLocal l A) (hB : SupportLocal l B) :
    ∃ l' : Nat → Nat, PreservesLabels l l' ∧ SupportLocal l' (A ∪ B) ∧
      atomRank U l ≤ atomRank U l' + 1 := by
  classical
  by_cases hAe : A = ∅
  · subst A
    exact ⟨l,fun _ _ h => h,by simpa using hB,by omega⟩
  by_cases hBe : B = ∅
  · subst B
    exact ⟨l,fun _ _ h => h,by simpa using hA,by omega⟩
  obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hAe
  obtain ⟨b,hb⟩ := Finset.nonempty_iff_ne_empty.mpr hBe
  let l' := mergeLabel l (l a) (l b)
  have hv : ∀ x ∈ A ∪ B, l' x = l a := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · dsimp [l',mergeLabel]
      rw [hA x hx a ha]
      split <;> rfl
    · dsimp [l',mergeLabel]
      rw [hB x hx b hb]
      simp
  exact ⟨l',fun a b h => merge_preserves_equal l _ _ a b h,
    fun a ha b hb => (hv a ha).trans (hv b hb).symm,atom_rank_merge U l _ _⟩

theorem atom_rank_attach {n : Nat} (U : Finset Nat) (l : Nat → Nat)
    (a : Nat) (S : Finset (Fin n))
    (hs : SupportLocal (fun u : Fin n => l u.val) S) :
    ∃ l' : Nat → Nat, PreservesLabels l l' ∧
      (∀ u ∈ S, l' u.val = l' a) ∧
      atomRank U l ≤ atomRank U l' + (if S.Nonempty then 1 else 0) := by
  classical
  by_cases he : S.Nonempty
  · obtain ⟨u,hu⟩ := he
    let l' := mergeLabel l (l u.val) (l a)
    refine ⟨l',fun a b h => merge_preserves_equal l _ _ a b h,?_,?_⟩
    · intro v hv
      have hvu : l v.val = l u.val := hs v hv u hu
      change mergeLabel l (l u.val) (l a) v.val = mergeLabel l (l u.val) (l a) a
      unfold mergeLabel
      rw [hvu,if_pos rfl]
      split <;> rfl
    · have hne : S.Nonempty := ⟨u,hu⟩
      simpa only [if_pos hne] using atom_rank_merge U l (l u.val) (l a)
  · refine ⟨l,fun _ _ h => h,?_,?_⟩
    · intro u hu
      exact False.elim (he ⟨u,hu⟩)
    · simp [he]

/-- Count only ORs outside F, and bearing junk ANDs. -/
def AuxCharge {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : Nat) : Prop :=
  ((gateAt C j).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C j) ∨
    (j ∈ PEqualNP.TopForm.junk G C ∧ (effectiveSingletons (n := n) C (n+j)).Nonempty)

instance {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : Nat) : Decidable (AuxCharge G C j) := by
  unfold AuxCharge
  infer_instance

def auxCost {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : Nat) : Nat :=
  ((Finset.range j).filter (AuxCharge G C)).card

private theorem aux_cost_succ {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : Nat) :
    auxCost G C (j+1) = auxCost G C j + (if AuxCharge G C j then 1 else 0) := by
  classical
  by_cases h : AuxCharge G C j
  · have he : ((insert j (Finset.range j)).filter (AuxCharge G C)) =
        insert j ((Finset.range j).filter (AuxCharge G C)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi,hp⟩
        rcases hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr ⟨hi,hp⟩
      · rintro (hi | ⟨hi,hp⟩)
        · subst i
          exact ⟨Or.inl rfl,h⟩
        · exact ⟨Or.inr hi,hp⟩
    unfold auxCost
    rw [Finset.range_add_one, he, Finset.card_insert_of_notMem]
    · simp only [if_pos h]
    · intro hm
      exact Finset.notMem_range_self ((Finset.mem_filter.mp hm).1)
  · have he : ((insert j (Finset.range j)).filter (AuxCharge G C)) =
        ((Finset.range j).filter (AuxCharge G C)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi,hp⟩
        rcases hi with hi | hi
        · subst i
          exact False.elim (h hp)
        · exact ⟨hi,hp⟩
      · rintro ⟨hi,hp⟩
        exact ⟨Or.inr hi,hp⟩
    unfold auxCost
    rw [Finset.range_add_one,he]
    simp only [if_neg h,Nat.add_zero]

/-- Prefix invariant: raw/junk-only supports are local and each
already processed atom is linked to all its true singleton inputs. -/
def AuxInvariant {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : Nat) (l : Nat → Nat) : Prop :=
  (∀ w < n+j, symbolicSupport n C w ⊆ atomUniverse G C →
    SupportLocal l (symbolicSupport n C w)) ∧
  (∀ a < n+j, a ∈ atomUniverse G C → ∀ u ∈ effectiveSingletons (n := n) C a,
    l u.val = l a)

theorem aux_effective_local {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (j : Nat) (l : Nat → Nat) (hi : AuxInvariant G C j l)
    (w : Nat) (hw : w < n+j) (hs : symbolicSupport n C w ⊆ atomUniverse G C) :
    SupportLocal (fun u : Fin n => l u.val) (effectiveSingletons C w) := by
  intro u hu v hv
  rw [← symbolic_effective C hAO w] at hu hv
  obtain ⟨a,ha,hua⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨b,hb,hvb⟩ := Finset.mem_biUnion.mp hv
  have hal := symbolic_leaf_le n C w a ha
  have hbl := symbolic_leaf_le n C w b hb
  exact (hi.2 a (by omega) (hs ha) u hua).trans
    ((hi.1 w hw hs a ha b hb).trans (hi.2 b (by omega) (hs hb) v hvb).symm)

/-- Extension of the prefix invariant under any equality-preserving
relabeling. Only the newly processed wire needs separate checks. -/
theorem aux_extend {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : Nat) (l l' : Nat → Nat) (hi : AuxInvariant G C j l)
    (hp : PreservesLabels l l')
    (hs : symbolicSupport n C (n+j) ⊆ atomUniverse G C →
      SupportLocal l' (symbolicSupport n C (n+j)))
    (ha : n+j ∈ atomUniverse G C → ∀ u ∈ effectiveSingletons (n := n) C (n+j),
      l' u.val = l' (n+j)) : AuxInvariant G C (j+1) l' := by
  constructor
  · intro w hw hsub
    by_cases h : w < n+j
    · exact preserves_local l l' hp _ (hi.1 w h hsub)
    · have he : w = n+j := by omega
      subst w
      exact hs hsub
  · intro a ha' hm u hu
    by_cases h : a < n+j
    · exact hp _ _ (hi.2 a h hm u hu)
    · have he : a = n+j := by omega
      subst a
      exact ha hm u hu

/-- Actual auxiliary-atom partition, with a rank loss of at most
one per dirty OR and one per bearing junk AND. No unused-gate
assumption is needed for this prefix construction. -/
theorem auxiliary_prefix_labels {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) (j : Nat) (hj : j ≤ C.gates.length) :
    ∃ l : Nat → Nat, AuxInvariant G C j l ∧
      (atomUniverse G C).card ≤ atomRank (atomUniverse G C) l + auxCost G C j := by
  classical
  induction j with
  | zero =>
      refine ⟨id,⟨?_,?_⟩,?_⟩
      · intro w hw _
        rw [symbolic_atom n C w (by intro h; have hh := h.1; omega)]
        exact local_singleton id w
      · intro a ha _ u hu
        have halt : a < n := by omega
        let v : Fin n := ⟨a,halt⟩
        have he : effectiveSingletons (n := n) C a = {v} := effective_input C v
        rw [he] at hu
        have huv := Finset.mem_singleton.mp hu
        subst u
        rfl
      · simp [atomRank,auxCost]
  | succ j ih =>
      have hj' : j < C.gates.length := by omega
      obtain ⟨l,hi,hcount⟩ := ih (by omega)
      obtain ⟨hin,ha,hb⟩ := actual_opnds C hAO j hj'
      let a := PEqualNP.TopForm.opnd C j 0
      let b := PEqualNP.TopForm.opnd C j 1
      have ha' : a < n+j := ha
      have hb' : b < n+j := hb
      have hin' : (gateAt C j).inputs = [a,b] := hin
      have hrA : a ∈ (gateAt C j).inputs := by rw [hin']; simp
      have hrB : b ∈ (gateAt C j).inputs := by rw [hin']; simp
      have hcost : auxCost G C j ≤ auxCost G C (j+1) := by
        rw [aux_cost_succ]
        omega
      rcases hAO.1 _ (actual_gate_mem C j hj') with hop | hop
      · have hs : symbolicSupport n C (n+j) = {n+j} := by
          apply symbolic_atom
          intro he
          have h := he.2.2.1
          have hjsub : n+j-n = j := by omega
          rw [hjsub,hop] at h
          contradiction
        have hA := and_operand_support_subset G C hAO htop j hj' hop a hrA
        have hB := and_operand_support_subset G C hAO htop j hj' hop b hrB
        have hloc : SupportLocal (fun u : Fin n => l u.val) (effectiveSingletons C (n+j)) := by
          rw [effective_and C hAO.2.1 j a b hj' hop hin']
          exact local_inter _ _ _ (aux_effective_local G C hAO j l hi a ha' hA)
        by_cases hm : n+j ∈ atomUniverse G C
        · have hjunk : j ∈ PEqualNP.TopForm.junk G C := by
            rcases Finset.mem_union.mp hm with hraw | hjunk
            · have h := Finset.mem_range.mp hraw
              omega
            · obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hjunk
              change n+k = n+j at he
              have he' : k = j := by omega
              simpa [he'] using hk
          obtain ⟨l',hp,hlink,hmerge⟩ :=
            atom_rank_attach (atomUniverse G C) l (n+j) (effectiveSingletons C (n+j)) hloc
          refine ⟨l',aux_extend G C j l l' hi hp ?_ (fun _ => hlink),?_⟩
          · intro _
            rw [hs]
            exact local_singleton l' _
          · rw [aux_cost_succ]
            by_cases hne : (effectiveSingletons (n := n) C (n+j)).Nonempty
            · have hc : AuxCharge G C j := Or.inr ⟨hjunk,hne⟩
              rw [if_pos hc]
              rw [if_pos hne] at hmerge
              omega
            · rw [if_neg hne] at hmerge
              omega
        · refine ⟨l,aux_extend G C j l l hi (fun _ _ h => h) ?_ ?_,?_⟩
          · intro _
            rw [hs]
            exact local_singleton l _
          · intro h
            exact False.elim (hm h)
          · omega
      · have hnot : n+j ∉ atomUniverse G C := by
          intro hm
          rcases Finset.mem_union.mp hm with hraw | hjunk
          · have h := Finset.mem_range.mp hraw
            omega
          · obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hjunk
            change n+k = n+j at he
            have he' : k = j := by omega
            subst k
            have hdirty : IsDirtyAnd n G C j := (Finset.mem_filter.mp hk).2
            have ho := hdirty.1
            rw [hop] at ho
            contradiction
        by_cases hs : symbolicSupport n C (n+j) ⊆ atomUniverse G C
        · have hu : symbolicSupport n C (n+j) = symbolicSupport n C a ∪ symbolicSupport n C b := by
            have he := symbolic_expand n C (n+j) (real_or_expandable C hAO j hj' hop)
            simpa [a,b] using he
          have hA : symbolicSupport n C a ⊆ atomUniverse G C := by
            intro x hx
            apply hs
            rw [hu]
            exact Finset.mem_union.mpr (Or.inl hx)
          have hB : symbolicSupport n C b ⊆ atomUniverse G C := by
            intro x hx
            apply hs
            rw [hu]
            exact Finset.mem_union.mpr (Or.inr hx)
          obtain ⟨l',hp,hl,hmerge⟩ := atom_rank_union (atomUniverse G C) l
            (symbolicSupport n C a) (symbolicSupport n C b)
            (hi.1 a ha' hA) (hi.1 b hb' hB)
          refine ⟨l',aux_extend G C j l l' hi hp ?_ ?_,?_⟩
          · intro _
            rw [hu]
            exact hl
          · intro h
            exact False.elim (hnot h)
          · have hd := raw_junk_or_dirty G C hAO j hj' hop hs
            have hc : AuxCharge G C j := Or.inl (Finset.mem_filter.mp hd).2
            rw [aux_cost_succ,if_pos hc]
            omega
        · refine ⟨l,aux_extend G C j l l hi (fun _ _ h => h) ?_ ?_,?_⟩
          · intro h
            exact False.elim (hs h)
          · intro h
            exact False.elim (hnot h)
          · omega

end L2260FirstMerge

/-! ## Local component budgets

A class-closed subset contains every atom sharing a label with any of
its members. When two classes merge, a subset closed under the new
labels was also closed under the old labels. The merge costs one
unit inside that subset only if the merged class belongs to it.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

def ClassClosed (U V : Finset Nat) (l : Nat → Nat) : Prop :=
  ∀ x ∈ V, ∀ y ∈ U, l x = l y → y ∈ V

theorem closed_before (U V : Finset Nat) (l l' : Nat → Nat)
    (hp : PreservesLabels l l') (hc : ClassClosed U V l') :
    ClassClosed U V l := by
  intro x hx y hy he
  exact hc x hx y hy (hp x y he)

theorem local_rank_merge (U V : Finset Nat) (l : Nat → Nat) (a b : Nat)
    (ha : a ∈ U) (hc : ClassClosed U V (mergeLabel l (l a) (l b))) :
    atomRank V l ≤ atomRank V (mergeLabel l (l a) (l b)) +
      (if a ∈ V then 1 else 0) := by
  by_cases h : a ∈ V
  · rw [if_pos h]
    exact atom_rank_merge V l (l a) (l b)
  · rw [if_neg h,Nat.add_zero]
    have he : ∀ x ∈ V, mergeLabel l (l a) (l b) x = l x := by
      intro x hx
      have hn : l x ≠ l b := by
        intro hb
        have heq : mergeLabel l (l a) (l b) x =
            mergeLabel l (l a) (l b) a := by
          unfold mergeLabel
          rw [hb,if_pos rfl]
          split <;> rfl
        exact h (hc x hx a ha heq)
      simp [mergeLabel,hn]
    have hi : V.image (mergeLabel l (l a) (l b)) = V.image l := by
      ext z
      constructor
      · intro hz
        obtain ⟨x,hx,hz⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨x,hx,(he x hx).symm.trans hz⟩
      · intro hz
        obtain ⟨x,hx,hz⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨x,hx,(he x hx).trans hz⟩
    unfold atomRank
    rw [hi]

/-- The local cost charges an OR only to subsets containing its whole
symbolic support, and a bearing junk only to subsets containing it. -/
def LocalAuxCharge {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (V : Finset Nat) (j : Nat) : Prop :=
  ((gateAt C j).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C j ∧
    symbolicSupport n C (n+j) ⊆ V) ∨
  (j ∈ PEqualNP.TopForm.junk G C ∧
    (effectiveSingletons (n := n) C (n+j)).Nonempty ∧ n+j ∈ V)

instance {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (V : Finset Nat) (j : Nat) : Decidable (LocalAuxCharge G C V j) := by
  unfold LocalAuxCharge
  infer_instance

def localAuxCost {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (V : Finset Nat) (j : Nat) : Nat :=
  ((Finset.range j).filter (LocalAuxCharge G C V)).card

private theorem local_cost_succ {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) (j : Nat) :
    localAuxCost G C V (j+1) =
      localAuxCost G C V j + (if LocalAuxCharge G C V j then 1 else 0) := by
  classical
  by_cases h : LocalAuxCharge G C V j
  · have he : ((insert j (Finset.range j)).filter (LocalAuxCharge G C V)) =
        insert j ((Finset.range j).filter (LocalAuxCharge G C V)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi,hp⟩
        rcases hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr ⟨hi,hp⟩
      · rintro (hi | ⟨hi,hp⟩)
        · subst i
          exact ⟨Or.inl rfl,h⟩
        · exact ⟨Or.inr hi,hp⟩
    unfold localAuxCost
    rw [Finset.range_add_one,he,Finset.card_insert_of_notMem]
    · simp only [if_pos h]
    · intro hm
      exact Finset.notMem_range_self ((Finset.mem_filter.mp hm).1)
  · have he : ((insert j (Finset.range j)).filter (LocalAuxCharge G C V)) =
        ((Finset.range j).filter (LocalAuxCharge G C V)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hp⟩
        rcases hi with hi | hi
        · subst i
          exact False.elim (h hp)
        · exact ⟨hi,hp⟩
      · rintro ⟨hi,hp⟩
        exact ⟨Or.inr hi,hp⟩
    unfold localAuxCost
    rw [Finset.range_add_one,he]
    simp only [if_neg h,Nat.add_zero]

def LocalBudget {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : Nat) (l : Nat → Nat) : Prop :=
  ∀ V : Finset Nat, V ⊆ atomUniverse G C → ClassClosed (atomUniverse G C) V l →
    V.card ≤ atomRank V l + localAuxCost G C V j

theorem budget_skip {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : Nat) (l : Nat → Nat) (hb : LocalBudget G C j l) :
    LocalBudget G C (j+1) l := by
  intro V hV hc
  have h := hb V hV hc
  rw [local_cost_succ]
  omega

theorem budget_merge {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : Nat) (l : Nat → Nat) (a b : Nat)
    (ha : a ∈ atomUniverse G C) (hb : LocalBudget G C j l)
    (hcharge : ∀ V : Finset Nat, V ⊆ atomUniverse G C →
      ClassClosed (atomUniverse G C) V (mergeLabel l (l a) (l b)) →
      a ∈ V → LocalAuxCharge G C V j) :
    LocalBudget G C (j+1) (mergeLabel l (l a) (l b)) := by
  intro V hV hc
  have hp : PreservesLabels l (mergeLabel l (l a) (l b)) :=
    fun x y h => merge_preserves_equal l _ _ x y h
  have hprev := hb V hV (closed_before _ _ _ _ hp hc)
  have hr := local_rank_merge (atomUniverse G C) V l a b ha hc
  rw [local_cost_succ]
  by_cases h : a ∈ V
  · rw [if_pos h] at hr
    rw [if_pos (hcharge V hV hc h)]
    omega
  · rw [if_neg h] at hr
    omega

theorem merge_union_explicit (l : Nat → Nat) (A B : Finset Nat)
    (a b : Nat) (ha : a ∈ A) (hb : b ∈ B)
    (hA : SupportLocal l A) (hB : SupportLocal l B) :
    ∀ x ∈ A ∪ B, mergeLabel l (l a) (l b) x = l a := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · unfold mergeLabel
    rw [hA x hx a ha]
    split <;> rfl
  · unfold mergeLabel
    rw [hB x hx b hb]
    simp

/-- The actual prefix construction simultaneously satisfies all
closed-subset budgets. This is stronger than a global class count. -/
theorem auxiliary_local_budget {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) (j : Nat) (hj : j ≤ C.gates.length) :
    ∃ l : Nat → Nat, AuxInvariant G C j l ∧ LocalBudget G C j l := by
  classical
  induction j with
  | zero =>
      refine ⟨id,⟨?_,?_⟩,?_⟩
      · intro w hw _
        rw [symbolic_atom n C w (by intro h; have hh := h.1; omega)]
        exact local_singleton id w
      · intro a ha _ u hu
        have halt : a < n := by omega
        let v : Fin n := ⟨a,halt⟩
        have he : effectiveSingletons (n := n) C a = {v} := effective_input C v
        rw [he] at hu
        have huv := Finset.mem_singleton.mp hu
        subst u
        rfl
      · intro V _ _
        simp [atomRank,localAuxCost]
  | succ j ih =>
      have hj' : j < C.gates.length := by omega
      obtain ⟨l,hi,hbudget⟩ := ih (by omega)
      obtain ⟨hin,ha,hb⟩ := actual_opnds C hAO j hj'
      let a := PEqualNP.TopForm.opnd C j 0
      let b := PEqualNP.TopForm.opnd C j 1
      have ha' : a < n+j := ha
      have hb' : b < n+j := hb
      have hin' : (gateAt C j).inputs = [a,b] := hin
      have hrA : a ∈ (gateAt C j).inputs := by rw [hin']; simp
      have hrB : b ∈ (gateAt C j).inputs := by rw [hin']; simp
      rcases hAO.1 _ (actual_gate_mem C j hj') with hop | hop
      · have hs : symbolicSupport n C (n+j) = {n+j} := by
          apply symbolic_atom
          intro he
          have h := he.2.2.1
          have hjsub : n+j-n = j := by omega
          rw [hjsub,hop] at h
          contradiction
        have hA := and_operand_support_subset G C hAO htop j hj' hop a hrA
        have hloc : SupportLocal (fun u : Fin n => l u.val) (effectiveSingletons C (n+j)) := by
          rw [effective_and C hAO.2.1 j a b hj' hop hin']
          exact local_inter _ _ _ (aux_effective_local G C hAO j l hi a ha' hA)
        by_cases hm : n+j ∈ atomUniverse G C
        · have hjunk : j ∈ PEqualNP.TopForm.junk G C := by
            rcases Finset.mem_union.mp hm with hraw | hjunk
            · have h := Finset.mem_range.mp hraw
              omega
            · obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hjunk
              change n+k = n+j at he
              have he' : k = j := by omega
              simpa [he'] using hk
          by_cases hne : (effectiveSingletons (n := n) C (n+j)).Nonempty
          · obtain ⟨u,hu⟩ := hne
            let l' := mergeLabel l (l (n+j)) (l u.val)
            have hp : PreservesLabels l l' := fun x y h => merge_preserves_equal l _ _ x y h
            have hlink : ∀ v ∈ effectiveSingletons (n := n) C (n+j), l' v.val = l' (n+j) := by
              intro v hv
              have he : l v.val = l u.val := hloc v hv u hu
              dsimp [l',mergeLabel]
              rw [he,if_pos rfl]
              split <;> rfl
            refine ⟨l',aux_extend G C j l l' hi hp ?_ (fun _ => hlink),?_⟩
            · intro _
              rw [hs]
              exact local_singleton l' _
            · apply budget_merge G C j l (n+j) u.val hm hbudget
              intro V _ _ hV
              exact Or.inr ⟨hjunk,⟨u,hu⟩,hV⟩
          · refine ⟨l,aux_extend G C j l l hi (fun _ _ h => h) ?_ ?_,
                budget_skip G C j l hbudget⟩
            · intro _
              rw [hs]
              exact local_singleton l _
            · intro _ u hu
              exact False.elim (hne ⟨u,hu⟩)
        · refine ⟨l,aux_extend G C j l l hi (fun _ _ h => h) ?_ ?_,
              budget_skip G C j l hbudget⟩
          · intro _
            rw [hs]
            exact local_singleton l _
          · intro h
            exact False.elim (hm h)
      · have hnot : n+j ∉ atomUniverse G C := by
          intro hm
          rcases Finset.mem_union.mp hm with hraw | hjunk
          · have h := Finset.mem_range.mp hraw
            omega
          · obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hjunk
            change n+k = n+j at he
            have he' : k = j := by omega
            subst k
            have ho := ((Finset.mem_filter.mp hk).2 :
              PEqualNP.CleanedNonEdge.IsDirtyAnd n G C j).1
            rw [hop] at ho
            contradiction
        by_cases hs : symbolicSupport n C (n+j) ⊆ atomUniverse G C
        · have hu : symbolicSupport n C (n+j) = symbolicSupport n C a ∪ symbolicSupport n C b := by
            have he := symbolic_expand n C (n+j) (real_or_expandable C hAO j hj' hop)
            simpa [a,b] using he
          have hA : symbolicSupport n C a ⊆ atomUniverse G C := by
            intro x hx
            apply hs
            rw [hu]
            exact Finset.mem_union.mpr (Or.inl hx)
          have hB : symbolicSupport n C b ⊆ atomUniverse G C := by
            intro x hx
            apply hs
            rw [hu]
            exact Finset.mem_union.mpr (Or.inr hx)
          obtain ⟨x,hx⟩ := symbolic_nonempty n C a
          obtain ⟨y,hy⟩ := symbolic_nonempty n C b
          let l' := mergeLabel l (l x) (l y)
          have hp : PreservesLabels l l' := fun p q h => merge_preserves_equal l _ _ p q h
          have hv : ∀ z ∈ symbolicSupport n C (n+j), l' z = l x := by
            rw [hu]
            exact merge_union_explicit l _ _ x y hx hy (hi.1 a ha' hA) (hi.1 b hb' hB)
          have hxroot : x ∈ symbolicSupport n C (n+j) := by
            rw [hu]
            exact Finset.mem_union.mpr (Or.inl hx)
          refine ⟨l',aux_extend G C j l l' hi hp ?_ ?_,?_⟩
          · intro _ p hp' q hq'
            exact (hv p hp').trans (hv q hq').symm
          · intro h
            exact False.elim (hnot h)
          · apply budget_merge G C j l x y (hA hx) hbudget
            intro V _ hc hxV
            have hd := raw_junk_or_dirty G C hAO j hj' hop hs
            have hdirty := (Finset.mem_filter.mp hd).2.2
            refine Or.inl ⟨hop,hdirty,?_⟩
            intro z hz
            exact hc x hxV z (hs hz) ((hv x hxroot).trans (hv z hz).symm)
        · refine ⟨l,aux_extend G C j l l hi (fun _ _ h => h) ?_ ?_,
              budget_skip G C j l hbudget⟩
          · intro h
            exact False.elim (hs h)
          · intro h
            exact False.elim (hnot h)

end L2260FirstMerge

/-! ## Extract the budget of an individual component -/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

def atomClass (U : Finset Nat) (l : Nat → Nat) (c : Nat) : Finset Nat :=
  U.filter fun a => l a = c

theorem atom_class_closed (U : Finset Nat) (l : Nat → Nat) (c : Nat) :
    ClassClosed U (atomClass U l c) l := by
  intro x hx y hy he
  have hx' : l x = c := (Finset.mem_filter.mp hx).2
  exact Finset.mem_filter.mpr ⟨hy,he.symm.trans hx'⟩

theorem atom_class_rank_le_one (U : Finset Nat) (l : Nat → Nat) (c : Nat) :
    atomRank (atomClass U l c) l ≤ 1 := by
  have hs : (atomClass U l c).image l ⊆ ({c} : Finset Nat) := by
    intro z hz
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hz
    exact Finset.mem_singleton.mpr (he.symm.trans (Finset.mem_filter.mp hx).2)
  exact (Finset.card_le_card hs).trans (by simp)

theorem component_local_cost_bound {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : Nat) (l : Nat → Nat)
    (hb : LocalBudget G C j l) (c : Nat) :
    (atomClass (atomUniverse G C) l c).card ≤
      1 + localAuxCost G C (atomClass (atomUniverse G C) l c) j := by
  have h := hb (atomClass (atomUniverse G C) l c)
    (Finset.filter_subset _ _) (atom_class_closed _ _ _)
  have hr := atom_class_rank_le_one (atomUniverse G C) l c
  omega

/-- One common labeling satisfies all actual wire support constraints
and all individual component budgets. -/
theorem circuit_component_budgets {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) :
    ∃ l : Nat → Nat, AuxInvariant G C C.gates.length l ∧
      ∀ c : Nat, (atomClass (atomUniverse G C) l c).card ≤
        1 + localAuxCost G C (atomClass (atomUniverse G C) l c) C.gates.length := by
  obtain ⟨l,hi,hb⟩ := auxiliary_local_budget G C hAO htop C.gates.length (Nat.le_refl _)
  exact ⟨l,hi,fun c => component_local_cost_bound G C _ l hb c⟩

end L2260FirstMerge


/-! ## Cancel bearing-junk charges from the local budget

Keep the same labeling for every closed subset and every AND operand.
Bearing junk atoms may consume their own attachment charge, but raw
inputs and nonbearing junk must be paid for by dirty ORs. This is
a necessary condition only; it does not yet justify the normalized CNF.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

def localDirtyOrGates {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) : Finset Nat :=
  (Finset.range C.gates.length).filter fun i =>
    (gateAt C i).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C i ∧
      symbolicSupport n C (n+i) ⊆ V

def localBearingGates {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) : Finset Nat :=
  (Finset.range C.gates.length).filter fun i =>
    i ∈ PEqualNP.TopForm.junk G C ∧
      (effectiveSingletons (n := n) C (n+i)).Nonempty ∧ n+i ∈ V

def localBearingAtoms {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) : Finset Nat :=
  (localBearingGates G C V).image (fun i => n+i)

def localFreeAtoms {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) : Finset Nat :=
  V \ localBearingAtoms G C V

theorem local_bearing_atoms_subset {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) :
    localBearingAtoms G C V ⊆ V := by
  intro a ha
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp ha
  have h := (Finset.mem_filter.mp hi).2.2.2
  rw [← he]
  exact h

theorem local_bearing_atoms_card {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) :
    (localBearingAtoms G C V).card = (localBearingGates G C V).card := by
  unfold localBearingAtoms
  apply Finset.card_image_of_injective
  intro a b h
  change n+a = n+b at h
  omega

theorem local_aux_cost_split_le {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) :
    localAuxCost G C V C.gates.length ≤
      (localDirtyOrGates G C V).card + (localBearingGates G C V).card := by
  have he : ((Finset.range C.gates.length).filter (LocalAuxCharge G C V)) =
      localDirtyOrGates G C V ∪ localBearingGates G C V := by
    ext i
    simp only [localDirtyOrGates, localBearingGates, LocalAuxCharge,
      Finset.mem_filter, Finset.mem_union]
    tauto
  unfold localAuxCost
  rw [he]
  exact Finset.card_union_le _ _

theorem local_free_atoms_card_add {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) :
    (localFreeAtoms G C V).card + (localBearingGates G C V).card = V.card := by
  have hs := local_bearing_atoms_subset G C V
  have hd : Disjoint (localFreeAtoms G C V) (localBearingAtoms G C V) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 hb
  have hu : localFreeAtoms G C V ∪ localBearingAtoms G C V = V := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_union.mp ha with hf | hb
      · exact (Finset.mem_sdiff.mp hf).1
      · exact hs hb
    · intro ha
      by_cases hb : a ∈ localBearingAtoms G C V
      · exact Finset.mem_union.mpr (Or.inr hb)
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨ha,hb⟩))
  have h := Finset.card_union_of_disjoint hd
  rw [hu, local_bearing_atoms_card G C V] at h
  exact h.symm

/-- All raw inputs and all nonbearing junk atoms in V remain after
cancelling the attachment charges. -/
theorem mem_local_free_of_raw_or_empty {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) (a : Nat)
    (ha : a ∈ V)
    (hf : a < n ∨ ¬ (effectiveSingletons (n := n) C a).Nonempty) :
    a ∈ localFreeAtoms G C V := by
  apply Finset.mem_sdiff.mpr
  refine ⟨ha,?_⟩
  intro hb
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hb
  rcases hf with hraw | hempty
  · change n+i = a at he
    omega
  · apply hempty
    rw [← he]
    exact (Finset.mem_filter.mp hi).2.2.1

theorem local_dirty_or_subset {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) :
    localDirtyOrGates G C V ⊆ PEqualNP.TopForm.orN G C := by
  intro i hi
  have h := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨h.1,h.2.1,h.2.2.1⟩

/-- Stronger than a separate per-class bound: the cancellation is valid
simultaneously for every union of label classes. -/
theorem closed_subset_or_budget {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (l : Nat → Nat)
    (hb : LocalBudget G C C.gates.length l) (V : Finset Nat)
    (hV : V ⊆ atomUniverse G C) (hc : ClassClosed (atomUniverse G C) V l) :
    (localFreeAtoms G C V).card ≤ atomRank V l + (localDirtyOrGates G C V).card := by
  have h := hb V hV hc
  have hs := local_aux_cost_split_le G C V
  have he := local_free_atoms_card_add G C V
  omega

theorem component_or_budget {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (l : Nat → Nat)
    (hb : LocalBudget G C C.gates.length l) (c : Nat) :
    (localFreeAtoms G C (atomClass (atomUniverse G C) l c)).card ≤
      1 + (localDirtyOrGates G C (atomClass (atomUniverse G C) l c)).card := by
  have h := closed_subset_or_budget G C l hb (atomClass (atomUniverse G C) l c)
    (Finset.filter_subset _ _) (atom_class_closed _ _ _)
  have hr := atom_class_rank_le_one (atomUniverse G C) l c
  omega

/-- Restrict to the union of all classes containing an original input.
Its rank is at most the number of original-input labels. No new
labeling or assumption on exactly two junk gates is required. -/
theorem raw_rank_or_budget {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (l : Nat → Nat)
    (hb : LocalBudget G C C.gates.length l) :
    n ≤ ((Finset.range n).image l).card + (PEqualNP.TopForm.orN G C).card := by
  classical
  let R := (Finset.range n).image l
  let V := (atomUniverse G C).filter fun a => l a ∈ R
  have hV : V ⊆ atomUniverse G C := Finset.filter_subset _ _
  have hc : ClassClosed (atomUniverse G C) V l := by
    intro x hx y hy he
    have h := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨hy,he ▸ h⟩
  have hraw : Finset.range n ⊆ localFreeAtoms G C V := by
    intro a ha
    have hlt := Finset.mem_range.mp ha
    have hu : a ∈ atomUniverse G C := Finset.mem_union.mpr (Or.inl ha)
    have hR : l a ∈ R := Finset.mem_image.mpr ⟨a,ha,rfl⟩
    have hm : a ∈ V := Finset.mem_filter.mpr ⟨hu,hR⟩
    exact mem_local_free_of_raw_or_empty G C V a hm (Or.inl hlt)
  have hrank : atomRank V l ≤ R.card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hz
    rw [← he]
    exact (Finset.mem_filter.mp ha).2
  have hcard := Finset.card_le_card hraw
  rw [Finset.card_range] at hcard
  have hor := Finset.card_le_card (local_dirty_or_subset G C V)
  have h := closed_subset_or_budget G C l hb V hV hc
  change n ≤ R.card + (PEqualNP.TopForm.orN G C).card
  omega

/-- Keep all necessary conditions under one common existential label.
In particular, both symbolic supports and effective singleton supports
of every actual AND operand are local in this same partition. -/
theorem circuit_or_budgets {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) :
    ∃ l : Nat → Nat, AuxInvariant G C C.gates.length l ∧
      LocalBudget G C C.gates.length l ∧
      n ≤ ((Finset.range n).image l).card + (PEqualNP.TopForm.orN G C).card ∧
      (∀ c : Nat,
        (localFreeAtoms G C (atomClass (atomUniverse G C) l c)).card ≤
          1 + (localDirtyOrGates G C (atomClass (atomUniverse G C) l c)).card) ∧
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∀ w ∈ (gateAt C j).inputs,
          SupportLocal l (symbolicSupport n C w) ∧
          SupportLocal (fun u : Fin n => l u.val) (effectiveSingletons C w)) := by
  obtain ⟨l,hi,hb⟩ := auxiliary_local_budget G C hAO htop C.gates.length (Nat.le_refl _)
  refine ⟨l,hi,hb,raw_rank_or_budget G C l hb,fun c => component_or_budget G C l hb c,?_⟩
  intro j hj hop w hw
  have hs := and_operand_support_subset G C hAO htop j hj hop w hw
  have hlt := hAO.2.1 j hj w hw
  have hlt' : w < n+C.gates.length := by omega
  exact ⟨hi.1 w hlt' hs,aux_effective_local G C hAO C.gates.length l hi w hlt' hs⟩

end L2260FirstMerge


/-! ## OR-only support rank

A bearing junk attachment can merge auxiliary labels without an OR,
but it cannot enlarge the symbolic OR support of an actual wire.
Construct a second, independent labeling, used only to count the ORs
needed to assemble a support. The original auxiliary labels are kept
unchanged for all partition constraints.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

def localOrPrefix {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) (j : Nat) : Nat :=
  ((Finset.range j).filter fun i =>
    (gateAt C i).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C i ∧
      symbolicSupport n C (n+i) ⊆ V).card

private theorem local_or_prefix_succ {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) (j : Nat) :
    localOrPrefix G C V (j+1) = localOrPrefix G C V j +
      (if (gateAt C j).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C j ∧
          symbolicSupport n C (n+j) ⊆ V then 1 else 0) := by
  classical
  let P : Nat → Prop := fun i =>
    (gateAt C i).op = GateOp.or ∧ ¬ PEqualNP.TopForm.BelowF G C i ∧
      symbolicSupport n C (n+i) ⊆ V
  change ((Finset.range (j+1)).filter P).card =
    ((Finset.range j).filter P).card + (if P j then 1 else 0)
  rw [Finset.range_add_one]
  by_cases h : P j
  · have he : (insert j (Finset.range j)).filter P =
        insert j ((Finset.range j).filter P) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hp⟩
        rcases hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr ⟨hi,hp⟩
      · rintro (hi | ⟨hi,hp⟩)
        · subst i
          exact ⟨Or.inl rfl,h⟩
        · exact ⟨Or.inr hi,hp⟩
    rw [he,Finset.card_insert_of_notMem,if_pos h]
    intro hm
    exact Finset.notMem_range_self ((Finset.mem_filter.mp hm).1)
  · have he : (insert j (Finset.range j)).filter P =
        (Finset.range j).filter P := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hp⟩
        rcases hi with hi | hi
        · subst i
          exact False.elim (h hp)
        · exact ⟨hi,hp⟩
      · rintro ⟨hi,hp⟩
        exact ⟨Or.inr hi,hp⟩
    rw [he,if_neg h,Nat.add_zero]

theorem or_only_prefix_labels {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (V : Finset Nat) (hV : V ⊆ atomUniverse G C)
    (j : Nat) (hj : j ≤ C.gates.length) :
    ∃ l : Nat → Nat,
      (∀ w < n+j, symbolicSupport n C w ⊆ V →
        SupportLocal l (symbolicSupport n C w)) ∧
      V.card ≤ atomRank V l + localOrPrefix G C V j := by
  classical
  induction j with
  | zero =>
      refine ⟨id,?_,?_⟩
      · intro w hw _
        rw [symbolic_atom n C w (by intro h; have hh := h.1; omega)]
        exact local_singleton id w
      · simp [atomRank,localOrPrefix]
  | succ j ih =>
      have hj' : j < C.gates.length := by omega
      obtain ⟨l,hl,hbudget⟩ := ih (by omega)
      have hcost : localOrPrefix G C V j ≤ localOrPrefix G C V (j+1) := by
        rw [local_or_prefix_succ]
        omega
      by_cases he : Expandable n C (n+j)
      · by_cases hs : symbolicSupport n C (n+j) ⊆ V
        · let a := PEqualNP.TopForm.opnd C j 0
          let b := PEqualNP.TopForm.opnd C j 1
          have hidx : n+j-n = j := by omega
          have ha : a < n+j := by simpa [a,hidx] using he.2.2.2.1
          have hb : b < n+j := by simpa [b,hidx] using he.2.2.2.2
          have hu : symbolicSupport n C (n+j) =
              symbolicSupport n C a ∪ symbolicSupport n C b := by
            simpa [a,b,hidx] using symbolic_expand n C (n+j) he
          have hA : symbolicSupport n C a ⊆ V := by
            intro x hx
            apply hs
            rw [hu]
            exact Finset.mem_union.mpr (Or.inl hx)
          have hB : symbolicSupport n C b ⊆ V := by
            intro x hx
            apply hs
            rw [hu]
            exact Finset.mem_union.mpr (Or.inr hx)
          obtain ⟨l',hp,hu',hr⟩ :=
            atom_rank_union V l (symbolicSupport n C a) (symbolicSupport n C b)
              (hl a ha hA) (hl b hb hB)
          have hop : (gateAt C j).op = GateOp.or := by
            simpa [hidx] using he.2.2.1
          have hU : symbolicSupport n C (n+j) ⊆ atomUniverse G C :=
            fun _ hx => hV (hs hx)
          have hd := raw_junk_or_dirty G C hAO j hj' hop hU
          have hcharge : (gateAt C j).op = GateOp.or ∧
              ¬ PEqualNP.TopForm.BelowF G C j ∧
              symbolicSupport n C (n+j) ⊆ V :=
            ⟨hop,(Finset.mem_filter.mp hd).2.2,hs⟩
          refine ⟨l',?_,?_⟩
          · intro w hw hwV
            by_cases hw' : w < n+j
            · exact preserves_local l l' hp _ (hl w hw' hwV)
            · have hwe : w = n+j := by omega
              subst w
              rw [hu]
              exact hu'
          · rw [local_or_prefix_succ,if_pos hcharge]
            omega
        · refine ⟨l,?_,by omega⟩
          intro w hw hwV
          by_cases hw' : w < n+j
          · exact hl w hw' hwV
          · have hwe : w = n+j := by omega
            subst w
            exact False.elim (hs hwV)
      · refine ⟨l,?_,by omega⟩
        intro w hw hwV
        by_cases hw' : w < n+j
        · exact hl w hw' hwV
        · have hwe : w = n+j := by omega
          subst w
          rw [symbolic_atom n C (n+j) he]
          exact local_singleton l _

theorem local_dirty_or_mono {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (A B : Finset Nat) (h : A ⊆ B) :
    localDirtyOrGates G C A ⊆ localDirtyOrGates G C B := by
  intro i hi
  have h' := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨h'.1,h'.2.1,h'.2.2.1,
    fun _ hx => h (h'.2.2.2 hx)⟩

/-- An actual wire with raw/junk-only support S needs at least |S|-1
distinct OR gates with support inside S (even with arbitrary fanout). -/
theorem symbolic_support_or_bound {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (w : Nat) (hw : w < n+C.gates.length)
    (hs : symbolicSupport n C w ⊆ atomUniverse G C) :
    (symbolicSupport n C w).card ≤
      1 + (localDirtyOrGates G C (symbolicSupport n C w)).card := by
  classical
  let S := symbolicSupport n C w
  obtain ⟨l,hl,hb⟩ := or_only_prefix_labels G C hAO S hs C.gates.length (Nat.le_refl _)
  have hl' := hl w hw (show S ⊆ S from fun _ h => h)
  obtain ⟨a,ha⟩ := symbolic_nonempty n C w
  have him : S.image l ⊆ ({l a} : Finset Nat) := by
    intro z hz
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hz
    exact Finset.mem_singleton.mpr (he.symm.trans (hl' x hx a ha))
  have hr : atomRank S l ≤ 1 := by
    exact (Finset.card_le_card him).trans (by simp)
  change S.card ≤ atomRank S l + (localDirtyOrGates G C S).card at hb
  change S.card ≤ 1 + (localDirtyOrGates G C S).card
  omega

/-- No OR can be charged to two disjoint atom sets: its symbolic
support is nonempty. -/
theorem local_dirty_or_disjoint {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (A B : Finset Nat)
    (hd : Disjoint A B) :
    Disjoint (localDirtyOrGates G C A) (localDirtyOrGates G C B) := by
  apply Finset.disjoint_left.mpr
  intro i ha hb
  obtain ⟨x,hx⟩ := symbolic_nonempty n C (n+i)
  exact Finset.disjoint_left.mp hd
    ((Finset.mem_filter.mp ha).2.2.2 hx)
    ((Finset.mem_filter.mp hb).2.2.2 hx)

theorem local_dirty_or_sum_le {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (A B : Finset Nat)
    (hd : Disjoint A B) :
    (localDirtyOrGates G C A).card + (localDirtyOrGates G C B).card ≤
      (PEqualNP.TopForm.orN G C).card := by
  have hsub : localDirtyOrGates G C A ∪ localDirtyOrGates G C B ⊆
      PEqualNP.TopForm.orN G C := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact local_dirty_or_subset G C A hi
    · exact local_dirty_or_subset G C B hi
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (local_dirty_or_disjoint G C A B hd)] at h
  exact h

end L2260FirstMerge


/-! ## Reserve ORs for the other raw classes

The OR-only support count and the simultaneous closed-subset budget
are independent counting arguments, but the latter's original label
is used for every partition cut. The other raw classes reserve at
least (number of their raw atoms minus their number of classes) ORs.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

def rawClass (n : Nat) (l : Nat → Nat) (c : Nat) : Finset Nat :=
  (Finset.range n).filter fun a => l a = c

theorem other_raw_budget {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (l : Nat → Nat)
    (hb : LocalBudget G C C.gates.length l) (c : Nat)
    (hc : c ∈ (Finset.range n).image l) :
    (localDirtyOrGates G C (atomClass (atomUniverse G C) l c)).card + n + 1 ≤
      (rawClass n l c).card + ((Finset.range n).image l).card +
        (PEqualNP.TopForm.orN G C).card := by
  classical
  let R := (Finset.range n).image l
  let W := (atomUniverse G C).filter fun a => l a ∈ R.erase c
  let T := (Finset.range n).filter fun a => l a ≠ c
  let A := atomClass (atomUniverse G C) l c
  have hW : W ⊆ atomUniverse G C := Finset.filter_subset _ _
  have hclosed : ClassClosed (atomUniverse G C) W l := by
    intro x hx y hy he
    have hm := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨hy,he ▸ hm⟩
  have hT : T ⊆ localFreeAtoms G C W := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hU : a ∈ atomUniverse G C := Finset.mem_union.mpr (Or.inl ha'.1)
    have hR : l a ∈ R := Finset.mem_image.mpr ⟨a,ha'.1,rfl⟩
    have haW : a ∈ W := Finset.mem_filter.mpr
      ⟨hU,Finset.mem_erase.mpr ⟨ha'.2,hR⟩⟩
    exact mem_local_free_of_raw_or_empty G C W a haW
      (Or.inl (Finset.mem_range.mp ha'.1))
  have hrank : atomRank W l ≤ (R.erase c).card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hz
    rw [← he]
    exact (Finset.mem_filter.mp ha).2
  have hR : (R.erase c).card + 1 = R.card := by
    have hc' : c ∈ R := hc
    have he := Finset.card_insert_of_notMem (Finset.notMem_erase c R)
    rw [Finset.insert_erase hc'] at he
    exact he.symm
  have hTdis : Disjoint (rawClass n l c) T := by
    apply Finset.disjoint_left.mpr
    intro a ha ht
    exact (Finset.mem_filter.mp ht).2 (Finset.mem_filter.mp ha).2
  have hTunion : rawClass n l c ∪ T = Finset.range n := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (Finset.mem_filter.mp ha).1
      · exact (Finset.mem_filter.mp ha).1
    · intro ha
      by_cases h : l a = c
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨ha,h⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨ha,h⟩))
  have hTcard := Finset.card_union_of_disjoint hTdis
  rw [hTunion,Finset.card_range] at hTcard
  have hd : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro a ha hw
    have he := (Finset.mem_filter.mp ha).2
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp hw).2).1 he
  have hsum := local_dirty_or_sum_le G C A W hd
  have hbudget := closed_subset_or_budget G C l hb W hW hclosed
  have hTc := Finset.card_le_card hT
  change (localDirtyOrGates G C A).card + n + 1 ≤
    (rawClass n l c).card + R.card + (PEqualNP.TopForm.orN G C).card
  omega

/-- The support cap used by the fixed-partition SAT encoder.
When a support touches raw class c, it has at most the raw class size
plus the global slack r + b - n, including *all* junk atoms in it. -/
theorem symbolic_support_raw_cap {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (l : Nat → Nat) (hi : AuxInvariant G C C.gates.length l)
    (hb : LocalBudget G C C.gates.length l)
    (w : Nat) (hw : w < n+C.gates.length)
    (hs : symbolicSupport n C w ⊆ atomUniverse G C)
    (a : Nat) (ha : a ∈ symbolicSupport n C w) (haraw : a < n) :
    (symbolicSupport n C w).card + n ≤
      (rawClass n l (l a)).card + ((Finset.range n).image l).card +
        (PEqualNP.TopForm.orN G C).card := by
  let A := atomClass (atomUniverse G C) l (l a)
  have hsub : symbolicSupport n C w ⊆ A := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hs hx,hi.1 w hw hs x hx a ha⟩
  have hmem : l a ∈ (Finset.range n).image l :=
    Finset.mem_image.mpr ⟨a,Finset.mem_range.mpr haraw,rfl⟩
  have hreserve := other_raw_budget G C l hb (l a) hmem
  have hsupport := symbolic_support_or_bound G C hAO w hw hs
  have hmono := Finset.card_le_card (local_dirty_or_mono G C _ A hsub)
  change (localDirtyOrGates G C A).card + n + 1 ≤
    (rawClass n l (l a)).card + ((Finset.range n).image l).card +
      (PEqualNP.TopForm.orN G C).card at hreserve
  omega

theorem and_operand_raw_cap {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (l : Nat → Nat) (hi : AuxInvariant G C C.gates.length l)
    (hb : LocalBudget G C C.gates.length l)
    (j : Nat) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (w : Nat) (hr : w ∈ (gateAt C j).inputs)
    (a : Nat) (ha : a ∈ symbolicSupport n C w) (haraw : a < n) :
    (symbolicSupport n C w).card + n ≤
      (rawClass n l (l a)).card + ((Finset.range n).image l).card +
        (PEqualNP.TopForm.orN G C).card := by
  have hw := hAO.2.1 j hj w hr
  exact symbolic_support_raw_cap G C hAO l hi hb w (by omega)
    (and_operand_support_subset G C hAO htop j hj hop w hr) a ha haraw

end L2260FirstMerge


/-! ## Normalization: output and AND operands

The output is an OR of clean AND values; every AND operand is an
OR of original input values and strictly earlier junk AND values.
This gives the semantic skeleton before numbering the two junk
atoms, ordering the top gates, and encoding the physical OR DAG.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

theorem actual_output_bound {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (u v : Fin n) (he : G.Adj u v) :
    C.output < n+C.gates.length := by
  have ht : C.eval (List.ofFn (pairInput u v)) = true :=
    (congrFun hmin.2.1 (pairInput u v)).trans (graph_pair_true G u v he)
  have hlen : (C.wires (List.ofFn (pairInput u v))).length = n+C.gates.length := by
    change (C.gates.foldl gateStep (List.ofFn (pairInput u v))).length = _
    rw [fold_length]
    simp
  by_contra h
  have hn : ¬ C.output < (C.wires (List.ofFn (pairInput u v))).length := by
    rw [hlen]
    exact h
  simp [Circuit.eval,List.getD_eq_getElem?_getD,hn] at ht

theorem output_leaf_below {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (a : Nat) (ha : a ∈ symbolicSupport n C C.output) :
    ∀ x : Fin n → Bool, wireVal n C a x = true → graphFun G ∅ x = true := by
  intro x hx
  have ho := (symbolic_eval C hmin.1 x C.output).mpr ⟨a,ha,hx⟩
  change C.eval (List.ofFn x) = true at ho
  have he : C.eval (List.ofFn x) = graphFun G ∅ x := congrFun hmin.2.1 x
  rw [← he]
  exact ho

theorem output_support_tops {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (u v : Fin n) (he : G.Adj u v) :
    symbolicSupport n C C.output ⊆
      (PEqualNP.TopForm.tops G C).image (fun j => n+j) := by
  intro a ha
  have hc := output_leaf_below G C hmin a ha
  rcases symbolic_leaf_kind C hmin.1 C.output
      (actual_output_bound G C hmin u v he) a ha with hr | ⟨j,hj,haj,hop⟩
  · have hm : a ∈ atomUniverse G C :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hr))
    obtain ⟨x,hx,hf⟩ := atom_dirty_witness G C a hm
    have ht := hc x hx
    rw [hf] at ht
    contradiction
  · have hb : PEqualNP.TopForm.BelowF G C j := by
      intro x hx
      apply hc x
      rw [haj]
      exact hx
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hop,hb⟩,haj.symm⟩

/-- Taking the OR over *all* clean ANDs preserves the graph function,
even if an unused clean AND does not belong to the output closure. -/
theorem graph_eq_or_of_tops {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (u v : Fin n) (he : G.Adj u v) (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔
      ∃ j ∈ PEqualNP.TopForm.tops G C, gateVal n C j x = true := by
  constructor
  · intro hx
    have hf : C.eval (List.ofFn x) = graphFun G ∅ x := congrFun hmin.2.1 x
    have ho : wireVal n C C.output x = true := hf.trans hx
    obtain ⟨a,ha,ht⟩ := (symbolic_eval C hmin.1 x C.output).mp ho
    obtain ⟨j,hj,haj⟩ := Finset.mem_image.mp (output_support_tops G C hmin u v he ha)
    refine ⟨j,hj,?_⟩
    rw [← haj] at ht
    exact ht
  · rintro ⟨j,hj,ht⟩
    exact (Finset.mem_filter.mp hj).2.2 x ht

/-- The exact shape of an atom in an actual AND operand. In the junk
case its gate index precedes that of the consumer AND. -/
theorem and_operand_leaf_earlier_junk {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (j : Nat) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (w : Nat) (hw : w ∈ (gateAt C j).inputs)
    (a : Nat) (ha : a ∈ symbolicSupport n C w) :
    a < n ∨ ∃ i ∈ PEqualNP.TopForm.junk G C, i < j ∧ a = n+i := by
  have hm := and_operand_support_subset G C hAO htop j hj hop w hw ha
  have hlt := hAO.2.1 j hj w hw
  have hle := symbolic_leaf_le n C w a ha
  rcases Finset.mem_union.mp hm with hr | hh
  · exact Or.inl (Finset.mem_range.mp hr)
  · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hh
    change n+i = a at he
    exact Or.inr ⟨i,hi,by omega,he.symm⟩

/-- The two symbolic operand sets suffice to evaluate an AND on every
Boolean input. The preceding theorem justifies using only earlier
junk values, rather than values of other clean ANDs. -/
theorem normalized_and_eval {n : Nat} (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (j : Nat)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) :
    gateVal n C j x = true ↔
      (∃ a ∈ symbolicSupport n C (PEqualNP.TopForm.opnd C j 0),
        wireVal n C a x = true) ∧
      (∃ b ∈ symbolicSupport n C (PEqualNP.TopForm.opnd C j 1),
        wireVal n C b x = true) := by
  have hv := gateVal_and_eq C hAO.2.1 j _ _ hj hop (actual_opnds C hAO j hj).1 x
  change gateVal n C j x =
    (wireVal n C (PEqualNP.TopForm.opnd C j 0) x &&
     wireVal n C (PEqualNP.TopForm.opnd C j 1) x) at hv
  rw [hv,Bool.and_eq_true_iff,symbolic_eval C hAO x _,symbolic_eval C hAO x _]

end L2260FirstMerge


/-! ## Normalization: the shared internal OR DAG

Use actual wire indices as names for now. Each retained OR is counted
once, regardless of fanout or the number of AND operands using it.
Retaining every raw/junk-only OR (even an unused one) is safe for this
structural step. Dense numbering and minimum-circuit cuts are separate.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

def internalOrGates {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) : Finset Nat :=
  localDirtyOrGates G C (atomUniverse G C)

def internalOrWires {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) : Finset Nat :=
  (internalOrGates G C).image (fun i => n+i)

def internalSource {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) : Finset Nat :=
  atomUniverse G C ∪ internalOrWires G C

theorem internal_or_mem {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : Nat)
    (hj : j ∈ internalOrGates G C) :
    j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      symbolicSupport n C (n+j) ⊆ atomUniverse G C := by
  have h : j ∈ localDirtyOrGates G C (atomUniverse G C) := hj
  have hm := Finset.mem_filter.mp h
  exact ⟨Finset.mem_range.mp hm.1,hm.2.1,hm.2.2.2⟩

theorem internal_or_budget {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) :
    (internalOrGates G C).card ≤ (PEqualNP.TopForm.orN G C).card := by
  exact Finset.card_le_card (local_dirty_or_subset G C (atomUniverse G C))

theorem internal_or_wire_card {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) :
    (internalOrWires G C).card = (internalOrGates G C).card := by
  unfold internalOrWires
  apply Finset.card_image_of_injective
  intro a b h
  change n+a = n+b at h
  omega

theorem atom_internal_or_disjoint {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) :
    Disjoint (atomUniverse G C) (internalOrWires G C) := by
  apply Finset.disjoint_left.mpr
  intro w ha ho
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp ho
  have hop := (internal_or_mem G C j hj).2.1
  rcases Finset.mem_union.mp ha with hr | hd
  · have hlt := Finset.mem_range.mp hr
    change n+j = w at he
    omega
  · obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp hd
    change n+i = w at hei
    change n+j = w at he
    have hij : i = j := by omega
    subst i
    have hd' : IsDirtyAnd n G C j := (Finset.mem_filter.mp hi).2
    have ha' := hd'.1
    rw [hop] at ha'
    contradiction

theorem internal_source_card {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) :
    (internalSource G C).card =
      n + (PEqualNP.TopForm.junk G C).card + (internalOrGates G C).card := by
  unfold internalSource
  rw [Finset.card_union_of_disjoint (atom_internal_or_disjoint G C),
    atom_universe_card,internal_or_wire_card]

/-- A real wire with raw/junk-only support is either an atom or a
retained physical OR. In the atom case its support is a singleton. -/
theorem classify_internal_source {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (w : Nat) (hw : w < n+C.gates.length)
    (hs : symbolicSupport n C w ⊆ atomUniverse G C) :
    (w ∈ atomUniverse G C ∧ symbolicSupport n C w = {w}) ∨
      ∃ j ∈ internalOrGates G C, w = n+j := by
  by_cases he : Expandable n C w
  · have hj : w-n < C.gates.length := by
      have h := he.1
      omega
    have hidx : n+(w-n) = w := by
      have h := he.1
      omega
    have hop := he.2.2.1
    have hs' : symbolicSupport n C (n+(w-n)) ⊆ atomUniverse G C := by
      rw [hidx]
      exact hs
    have hd := raw_junk_or_dirty G C hAO (w-n) hj hop hs'
    have hm : w-n ∈ internalOrGates G C := by
      change w-n ∈ localDirtyOrGates G C (atomUniverse G C)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hop,
        (Finset.mem_filter.mp hd).2.2,hs'⟩
    exact Or.inr ⟨w-n,hm,hidx.symm⟩
  · have h := symbolic_atom n C w he
    have hm : w ∈ symbolicSupport n C w := by
      rw [h]
      exact Finset.mem_singleton.mpr rfl
    exact Or.inl ⟨hs hm,h⟩

theorem mem_internal_source {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (w : Nat) (hw : w < n+C.gates.length)
    (hs : symbolicSupport n C w ⊆ atomUniverse G C) :
    w ∈ internalSource G C := by
  rcases classify_internal_source G C hAO w hw hs with h | ⟨j,hj,he⟩
  · exact Finset.mem_union.mpr (Or.inl h.1)
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j,hj,he.symm⟩))

/-- Both children of a retained OR are valid internal sources with
strictly earlier physical indices. Their support union is exactly
the support recorded at this shared OR node. -/
theorem internal_or_children {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (j : Nat) (hj : j ∈ internalOrGates G C) :
    ∃ a b, (gateAt C j).inputs = [a,b] ∧ a < n+j ∧ b < n+j ∧
      a ∈ internalSource G C ∧ b ∈ internalSource G C ∧
      symbolicSupport n C (n+j) = symbolicSupport n C a ∪ symbolicSupport n C b := by
  obtain ⟨hlt,hop,hs⟩ := internal_or_mem G C j hj
  obtain ⟨hin,ha,hb⟩ := actual_opnds C hAO j hlt
  let a := PEqualNP.TopForm.opnd C j 0
  let b := PEqualNP.TopForm.opnd C j 1
  have hu : symbolicSupport n C (n+j) = symbolicSupport n C a ∪ symbolicSupport n C b := by
    have he := symbolic_expand n C (n+j) (real_or_expandable C hAO j hlt hop)
    have hidx : n+j-n = j := by omega
    simpa [a,b,hidx] using he
  have hA : symbolicSupport n C a ⊆ atomUniverse G C := by
    intro x hx
    apply hs
    rw [hu]
    exact Finset.mem_union.mpr (Or.inl hx)
  have hB : symbolicSupport n C b ⊆ atomUniverse G C := by
    intro x hx
    apply hs
    rw [hu]
    exact Finset.mem_union.mpr (Or.inr hx)
  have ha' : a < n+j := ha
  have hb' : b < n+j := hb
  exact ⟨a,b,hin,ha',hb',
    mem_internal_source G C hAO a (by omega) hA,
    mem_internal_source G C hAO b (by omega) hB,hu⟩

/-- Every AND reads two nodes of the same shared source network. -/
theorem internal_and_children {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (j : Nat) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    ∀ w ∈ (gateAt C j).inputs, w < n+j ∧ w ∈ internalSource G C := by
  intro w hw
  have hlt := hAO.2.1 j hj w hw
  exact ⟨hlt,mem_internal_source G C hAO w (by omega)
    (and_operand_support_subset G C hAO htop j hj hop w hw)⟩

/-- In a two-junk case the retained source pool has at most n+2+r
nodes, where r is the actual dirty OR count. The count is of physical
OR nodes, not separate expansions of each occurrence. -/
theorem two_junk_source_budget {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (h2 : (PEqualNP.TopForm.junk G C).card = 2) :
    (internalSource G C).card ≤ n+2+(PEqualNP.TopForm.orN G C).card := by
  rw [internal_source_card,h2]
  have h := internal_or_budget G C
  omega

end L2260FirstMerge


/-! ## Normalization: dense source numbering

Original inputs retain their indices. Junk ANDs are numbered by their
physical order, and internal ORs are numbered by their physical order
in a separate suffix. The latter order is sufficient for the OR-to-OR
dependencies even though a junk atom can depend on an earlier OR.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

def indexRank (S : Finset Nat) (i : Nat) : Nat :=
  (S.filter fun a => a < i).card

theorem index_rank_lt_card (S : Finset Nat) (i : Nat) (hi : i ∈ S) :
    indexRank S i < S.card := by
  let T := S.filter fun a => a < i
  have hn : i ∉ T := by simp [T]
  have hs : insert i T ⊆ S := by
    intro a ha
    rcases Finset.mem_insert.mp ha with he | ht
    · simpa [he] using hi
    · exact (Finset.mem_filter.mp ht).1
  have h := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hn] at h
  change T.card < S.card
  omega

theorem index_rank_strict (S : Finset Nat) (i j : Nat)
    (hi : i ∈ S) (hij : i < j) : indexRank S i < indexRank S j := by
  let T := S.filter fun a => a < i
  let U := S.filter fun a => a < j
  have hn : i ∉ T := by simp [T]
  have hs : insert i T ⊆ U := by
    intro a ha
    rcases Finset.mem_insert.mp ha with he | ht
    · subst a
      exact Finset.mem_filter.mpr ⟨hi,hij⟩
    · have hm := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨hm.1,hm.2.trans hij⟩
  have h := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hn] at h
  change T.card < U.card
  omega

theorem index_rank_injective (S : Finset Nat) (i j : Nat)
    (hi : i ∈ S) (hj : j ∈ S) (he : indexRank S i = indexRank S j) :
    i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have h' := index_rank_strict S i j hi h
    omega
  · exact h
  · have h' := index_rank_strict S j i hj h
    omega

def sourceCode {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (w : Nat) : Nat :=
  if w < n then w
  else if w-n ∈ PEqualNP.TopForm.junk G C then
    n + indexRank (PEqualNP.TopForm.junk G C) (w-n)
  else n + (PEqualNP.TopForm.junk G C).card +
    indexRank (internalOrGates G C) (w-n)

theorem source_code_raw {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (w : Nat) (hw : w < n) :
    sourceCode G C w = w := by
  simp [sourceCode,hw]

theorem source_code_junk {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : Nat)
    (hj : j ∈ PEqualNP.TopForm.junk G C) :
    sourceCode G C (n+j) = n + indexRank (PEqualNP.TopForm.junk G C) j := by
  have hn : ¬ n+j < n := by omega
  have he : n+j-n = j := by omega
  simp [sourceCode,hn,he,hj]

theorem internal_or_not_junk {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : Nat)
    (hj : j ∈ internalOrGates G C) :
    j ∉ PEqualNP.TopForm.junk G C := by
  intro h
  have hop := (internal_or_mem G C j hj).2.1
  have hd : IsDirtyAnd n G C j := (Finset.mem_filter.mp h).2
  have ha := hd.1
  rw [hop] at ha
  contradiction

theorem source_code_or {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : Nat)
    (hj : j ∈ internalOrGates G C) :
    sourceCode G C (n+j) = n + (PEqualNP.TopForm.junk G C).card +
      indexRank (internalOrGates G C) j := by
  have hn : ¬ n+j < n := by omega
  have he : n+j-n = j := by omega
  simp [sourceCode,hn,he,internal_or_not_junk G C j hj]

theorem source_cases {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (w : Nat)
    (hw : w ∈ internalSource G C) :
    w < n ∨ (∃ j ∈ PEqualNP.TopForm.junk G C, w = n+j) ∨
      ∃ j ∈ internalOrGates G C, w = n+j := by
  rcases Finset.mem_union.mp hw with ha | ho
  · rcases Finset.mem_union.mp ha with hr | hj
    · exact Or.inl (Finset.mem_range.mp hr)
    · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hj
      exact Or.inr (Or.inl ⟨j,hj,he.symm⟩)
  · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp ho
    exact Or.inr (Or.inr ⟨j,hj,he.symm⟩)

theorem source_code_bound {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (w : Nat)
    (hw : w ∈ internalSource G C) :
    sourceCode G C w < n + (PEqualNP.TopForm.junk G C).card +
      (internalOrGates G C).card := by
  rcases source_cases G C w hw with hr | ⟨j,hj,he⟩ | ⟨j,hj,he⟩
  · rw [source_code_raw G C w hr]
    omega
  · rw [he,source_code_junk G C j hj]
    have h := index_rank_lt_card _ j hj
    omega
  · rw [he,source_code_or G C j hj]
    have h := index_rank_lt_card _ j hj
    omega

/-- Distinct physical sources never acquire the same SAT source number. -/
theorem source_code_injective {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (a b : Nat)
    (ha : a ∈ internalSource G C) (hb : b ∈ internalSource G C)
    (he : sourceCode G C a = sourceCode G C b) : a = b := by
  rcases source_cases G C a ha with har | ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
  · rw [source_code_raw G C a har] at he
    rcases source_cases G C b hb with hbr | ⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩
    · rw [source_code_raw G C b hbr] at he
      exact he
    · rw [source_code_junk G C j hj] at he
      omega
    · rw [source_code_or G C j hj] at he
      omega
  · rw [source_code_junk G C i hi] at he
    have hir := index_rank_lt_card _ i hi
    rcases source_cases G C b hb with hbr | ⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩
    · rw [source_code_raw G C b hbr] at he
      omega
    · rw [source_code_junk G C j hj] at he
      have hr : indexRank (PEqualNP.TopForm.junk G C) i =
          indexRank (PEqualNP.TopForm.junk G C) j := by omega
      rw [index_rank_injective _ i j hi hj hr]
    · rw [source_code_or G C j hj] at he
      omega
  · rw [source_code_or G C i hi] at he
    rcases source_cases G C b hb with hbr | ⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩
    · rw [source_code_raw G C b hbr] at he
      omega
    · rw [source_code_junk G C j hj] at he
      have hjr := index_rank_lt_card _ j hj
      omega
    · rw [source_code_or G C j hj] at he
      have hr : indexRank (internalOrGates G C) i =
          indexRank (internalOrGates G C) j := by omega
      rw [index_rank_injective _ i j hi hj hr]

/-- All physical children of an internal OR have a smaller source
number in the SAT layout (raw and junk atoms precede the OR suffix). -/
theorem source_code_before_or {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (w j : Nat)
    (hw : w ∈ internalSource G C) (hj : j ∈ internalOrGates G C)
    (hlt : w < n+j) :
    sourceCode G C w < sourceCode G C (n+j) := by
  rw [source_code_or G C j hj]
  rcases source_cases G C w hw with hr | ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
  · rw [source_code_raw G C w hr]
    omega
  · rw [source_code_junk G C i hi]
    have h := index_rank_lt_card _ i hi
    omega
  · rw [source_code_or G C i hi]
    have hij : i < j := by omega
    have h := index_rank_strict _ i j hi hij
    omega

def numberedSupport {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (w : Nat) : Finset Nat :=
  (symbolicSupport n C w).image (sourceCode G C)

theorem numbered_support_card {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (w : Nat)
    (hs : symbolicSupport n C w ⊆ atomUniverse G C) :
    (numberedSupport G C w).card = (symbolicSupport n C w).card := by
  unfold numberedSupport
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  exact source_code_injective G C a b
    (Finset.mem_union.mpr (Or.inl (hs ha)))
    (Finset.mem_union.mpr (Or.inl (hs hb))) he

theorem numbered_support_union {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j a b : Nat)
    (hu : symbolicSupport n C (n+j) =
      symbolicSupport n C a ∪ symbolicSupport n C b) :
    numberedSupport G C (n+j) = numberedSupport G C a ∪ numberedSupport G C b := by
  unfold numberedSupport
  rw [hu,Finset.image_union]

/-- For a junk consumer its support bits can only refer to raw inputs
and strictly earlier junk ranks, exactly as in the SAT encoder. -/
theorem numbered_junk_operand_bound {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) (j : Nat)
    (hj : j ∈ PEqualNP.TopForm.junk G C)
    (w : Nat) (hw : w ∈ (gateAt C j).inputs)
    (z : Nat) (hz : z ∈ numberedSupport G C w) :
    z < n + indexRank (PEqualNP.TopForm.junk G C) j := by
  have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hd : IsDirtyAnd n G C j := (Finset.mem_filter.mp hj).2
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hz
  rcases and_operand_leaf_earlier_junk G C hAO htop j hlt hd.1 w hw a ha with
    hr | ⟨i,hi,hij,hai⟩
  · rw [← he,source_code_raw G C a hr]
    omega
  · rw [← he,hai,source_code_junk G C i hi]
    have h := index_rank_strict _ i j hi hij
    omega

end L2260FirstMerge


/-! ## Dense numbering: no missing indices

Injectivity and the exact source cardinality imply surjectivity.
For the unpadded source pool every selector index denotes a real node.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

theorem index_rank_image_range (S : Finset Nat) :
    S.image (indexRank S) = Finset.range S.card := by
  have hs : S.image (indexRank S) ⊆ Finset.range S.card := by
    intro z hz
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hz
    rw [← he]
    exact Finset.mem_range.mpr (index_rank_lt_card S i hi)
  have hcard : (S.image (indexRank S)).card = S.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    exact index_rank_injective S i j hi hj he
  apply Finset.eq_of_subset_of_card_le hs
  rw [Finset.card_range,hcard]

theorem index_rank_surjective (S : Finset Nat) (z : Nat)
    (hz : z < S.card) : ∃ i ∈ S, indexRank S i = z := by
  have hm : z ∈ Finset.range S.card := Finset.mem_range.mpr hz
  rw [← index_rank_image_range S] at hm
  exact Finset.mem_image.mp hm

theorem source_code_image_range {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) :
    (internalSource G C).image (sourceCode G C) =
      Finset.range (n+(PEqualNP.TopForm.junk G C).card+(internalOrGates G C).card) := by
  have hs : (internalSource G C).image (sourceCode G C) ⊆
      Finset.range (n+(PEqualNP.TopForm.junk G C).card+(internalOrGates G C).card) := by
    intro z hz
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hz
    rw [← he]
    exact Finset.mem_range.mpr (source_code_bound G C w hw)
  have hcard : ((internalSource G C).image (sourceCode G C)).card =
      (internalSource G C).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb he
    exact source_code_injective G C a b ha hb he
  apply Finset.eq_of_subset_of_card_le hs
  rw [Finset.card_range,hcard,internal_source_card]

theorem source_code_surjective {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (z : Nat)
    (hz : z < n+(PEqualNP.TopForm.junk G C).card+(internalOrGates G C).card) :
    ∃ w ∈ internalSource G C, sourceCode G C w = z := by
  have hm : z ∈ Finset.range
      (n+(PEqualNP.TopForm.junk G C).card+(internalOrGates G C).card) :=
    Finset.mem_range.mpr hz
  rw [← source_code_image_range G C] at hm
  exact Finset.mem_image.mp hm

/-! ## Minimum-circuit cuts: semantic redundancy

These are semantic equalities, not yet a minimality theorem. The
following redirection simulation is intended for the deletion proof.
-/

theorem support_subset_wire_imp {n : Nat} (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (a b : Nat)
    (hs : symbolicSupport n C a ⊆ symbolicSupport n C b)
    (x : Fin n → Bool) :
    wireVal n C a x = true → wireVal n C b x = true := by
  intro ha
  obtain ⟨w,hw,ht⟩ := (symbolic_eval C hAO x a).mp ha
  exact (symbolic_eval C hAO x b).mpr ⟨w,hs hw,ht⟩

theorem comparable_and_value {n : Nat} (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (j a b : Nat)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [a,b])
    (hs : symbolicSupport n C a ⊆ symbolicSupport n C b)
    (x : Fin n → Bool) :
    gateVal n C j x = wireVal n C a x := by
  have hi := support_subset_wire_imp C hAO a b hs x
  have hv := gateVal_and_eq C hAO.2.1 j a b hj hop hin x
  change gateVal n C j x = (wireVal n C a x && wireVal n C b x) at hv
  rw [hv]
  cases ha : wireVal n C a x with
  | false => rfl
  | true =>
      have hb := hi ha
      simp [hb]

theorem comparable_or_value {n : Nat} (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (j a b : Nat)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [a,b])
    (hs : symbolicSupport n C a ⊆ symbolicSupport n C b)
    (x : Fin n → Bool) :
    gateVal n C j x = wireVal n C b x := by
  have hi := support_subset_wire_imp C hAO a b hs x
  have hv := gateVal_or_eq C hAO.2.1 j a b hj hop hin x
  change gateVal n C j x = (wireVal n C a x || wireVal n C b x) at hv
  rw [hv]
  cases ha : wireVal n C a x with
  | false => rfl
  | true =>
      have hb := hi ha
      simp [hb]

/-- Remove wire cut, redirect all references to it to an earlier
wire rep, and shift every later physical index down by one. -/
def redirectIndex (cut rep i : Nat) : Nat :=
  if i = cut then rep else if cut < i then i-1 else i

def redirectGate (cut rep : Nat) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (redirectIndex cut rep)⟩

theorem redirect_index_before {cut rep i k : Nat}
    (hr : rep < cut) (hc : cut < k) (hi : i < k) :
    redirectIndex cut rep i < k-1 := by
  unfold redirectIndex
  split
  · omega
  · split <;> omega

theorem redirect_index_end_iff {cut rep i k : Nat}
    (hr : rep < cut) (hc : cut < k) :
    redirectIndex cut rep i = k-1 ↔ i = k := by
  unfold redirectIndex
  split
  · omega
  · split <;> omega

/-- A single suffix step preserves all old wire values under the
redirection, including the default false reads outside the list. -/
theorem redirect_step_simulation (cut rep : Nat) (w z : List Bool)
    (hr : rep < cut) (hc : cut < w.length)
    (hlen : w.length = z.length+1)
    (hrel : ∀ i, w.getD i false = z.getD (redirectIndex cut rep i) false)
    (g : Gate) :
    ∀ i, (gateStep w g).getD i false =
      (gateStep z (redirectGate cut rep g)).getD (redirectIndex cut rep i) false := by
  have hmap : g.inputs.map (fun i => w.getD i false) =
      (redirectGate cut rep g).inputs.map (fun i => z.getD i false) := by
    change g.inputs.map (fun i => w.getD i false) =
      (g.inputs.map (redirectIndex cut rep)).map (fun i => z.getD i false)
    rw [List.map_map]
    simp only [Function.comp_def]
    simp_rw [← hrel]
  intro i
  unfold gateStep
  rw [generic_getD_snoc, generic_getD_snoc]
  have he : redirectIndex cut rep i = z.length ↔ i = w.length := by
    have h := redirect_index_end_iff (i := i) hr hc
    have hlen' : w.length-1 = z.length := by omega
    rw [hlen'] at h
    exact h
  by_cases hi : i = w.length
  · have hi' := he.mpr hi
    simp only [if_pos hi,if_pos hi']
    change g.op.eval (g.inputs.map (fun i => w.getD i false)) =
      g.op.eval ((redirectGate cut rep g).inputs.map (fun i => z.getD i false))
    rw [hmap]
  · have hi' : redirectIndex cut rep i ≠ z.length := fun h => hi (he.mp h)
    simp only [if_neg hi,if_neg hi']
    exact hrel i

theorem redirect_fold_simulation (cut rep : Nat) (gs : List Gate)
    (w z : List Bool) (hr : rep < cut) (hc : cut < w.length)
    (hlen : w.length = z.length+1)
    (hrel : ∀ i, w.getD i false = z.getD (redirectIndex cut rep i) false) :
    ∀ i, (gs.foldl gateStep w).getD i false =
      ((gs.map (redirectGate cut rep)).foldl gateStep z).getD
        (redirectIndex cut rep i) false := by
  induction gs generalizing w z with
  | nil => exact hrel
  | cons g gs ih =>
      change ∀ i, (gs.foldl gateStep (gateStep w g)).getD i false =
        ((gs.map (redirectGate cut rep)).foldl gateStep
          (gateStep z (redirectGate cut rep g))).getD (redirectIndex cut rep i) false
      apply ih (gateStep w g) (gateStep z (redirectGate cut rep g))
      · simp only [gateStep,List.length_append,List.length_cons,List.length_nil]
        omega
      · simp only [gateStep,List.length_append,List.length_cons,List.length_nil]
        omega
      · exact redirect_step_simulation cut rep w z hr hc hlen hrel g

end L2260FirstMerge


/-! ## Minimum-circuit cuts: actual deletion

A gate that agrees with an earlier wire on every input can be removed
in the original AO2 model, including all physical index shifts.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

private theorem delete_getD_left {α : Type} (pre post : List α) (d : α)
    (i : Nat) (hi : i < pre.length) :
    (pre ++ post).getD i d = pre.getD i d := by
  induction pre generalizing i with
  | nil => simp at hi
  | cons a pre ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have h : i < pre.length := by simpa using hi
          simpa only [List.cons_append,List.getD_cons_succ] using ih i h

private theorem delete_getD_right {α : Type} (pre post : List α) (d : α)
    (i : Nat) : (pre ++ post).getD (pre.length+i) d = post.getD i d := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
      have he : (a::pre).length+i = (pre.length+i)+1 := by simp; omega
      rw [he]
      simpa only [List.cons_append,List.getD_cons_succ] using ih

private theorem delete_getD_map {α β : Type} (f : α → β) (l : List α)
    (d : α) (e : β) (i : Nat) (hi : i < l.length) :
    (l.map f).getD i e = f (l.getD i d) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have h : i < l.length := by simpa using hi
          simpa only [List.map_cons,List.getD_cons_succ] using ih i h

def deletedCircuit (n : Nat) (C : Circuit) (pre post : List Gate)
    (rep : Nat) : Circuit :=
  ⟨pre ++ post.map (redirectGate (n+pre.length) rep),
    redirectIndex (n+pre.length) rep C.output⟩

theorem deleted_circuit_ao {n : Nat} (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (pre post : List Gate) (g : Gate) (rep : Nat)
    (he : C.gates = pre ++ g :: post) (hr : rep < n+pre.length) :
    PEqualNP.TopForm.IsAO2 n (deletedCircuit n C pre post rep) := by
  have hp (a : Gate) (ha : a ∈ pre) : a ∈ C.gates := by
    rw [he]
    exact List.mem_append.mpr (Or.inl ha)
  have ht (a : Gate) (ha : a ∈ post) : a ∈ C.gates := by
    rw [he]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr ha)))
  refine ⟨?_,?_,?_⟩
  · intro a ha
    change a ∈ pre ++ post.map (redirectGate (n+pre.length) rep) at ha
    rcases List.mem_append.mp ha with h | h
    · exact hAO.1 a (hp a h)
    · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
      exact hAO.1 b (ht b hb)
  · intro i hi w hw
    change i < (pre ++ post.map (redirectGate (n+pre.length) rep)).length at hi
    simp only [List.length_append,List.length_map] at hi
    by_cases hip : i < pre.length
    · have hnew : gateAt (deletedCircuit n C pre post rep) i =
          pre.getD i ⟨GateOp.or,[]⟩ := by
        exact delete_getD_left _ _ _ i hip
      have hold : gateAt C i = pre.getD i ⟨GateOp.or,[]⟩ := by
        unfold gateAt
        rw [he]
        exact delete_getD_left _ _ _ i hip
      have hiold : i < C.gates.length := by
        rw [he]
        simp only [List.length_append,List.length_cons]
        omega
      apply hAO.2.1 i hiold w
      rw [hold,← hnew]
      exact hw
    · let k := i-pre.length
      have hk : k < post.length := by dsimp [k]; omega
      have hki : pre.length+k = i := by dsimp [k]; omega
      have hnew : gateAt (deletedCircuit n C pre post rep) i =
          redirectGate (n+pre.length) rep (post.getD k ⟨GateOp.or,[]⟩) := by
        change (pre ++ post.map (redirectGate (n+pre.length) rep)).getD i
          ⟨GateOp.or,[]⟩ = _
        rw [← hki,delete_getD_right]
        exact delete_getD_map _ _ _ _ k hk
      have hold : gateAt C (i+1) = post.getD k ⟨GateOp.or,[]⟩ := by
        unfold gateAt
        rw [he]
        have hidx : i+1 = pre.length+(k+1) := by omega
        rw [hidx,delete_getD_right]
        rfl
      rw [hnew] at hw
      change w ∈ (post.getD k ⟨GateOp.or,[]⟩).inputs.map
        (redirectIndex (n+pre.length) rep) at hw
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
      have hiold : i+1 < C.gates.length := by
        rw [he]
        simp only [List.length_append,List.length_cons]
        omega
      have ha' : a < n+(i+1) := by
        apply hAO.2.1 (i+1) hiold a
        rw [hold]
        exact ha
      have hh := redirect_index_before hr (show n+pre.length < n+(i+1) by omega) ha'
      omega
  · intro a ha
    change a ∈ pre ++ post.map (redirectGate (n+pre.length) rep) at ha
    rcases List.mem_append.mp ha with h | h
    · exact hAO.2.2 a (hp a h)
    · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
      change (b.inputs.map (redirectIndex (n+pre.length) rep)).length = 2
      rw [List.length_map]
      exact hAO.2.2 b (ht b hb)

theorem deleted_circuit_eval {n : Nat} (C : Circuit)
    (pre post : List Gate) (g : Gate) (rep : Nat)
    (he : C.gates = pre ++ g :: post) (hr : rep < n+pre.length)
    (hval : ∀ x : Fin n → Bool,
      gateVal n C pre.length x = wireVal n C rep x)
    (x : Fin n → Bool) :
    (deletedCircuit n C pre post rep).eval (List.ofFn x) =
      C.eval (List.ofFn x) := by
  let z := pre.foldl gateStep (List.ofFn x)
  let w := gateStep z g
  have hz : z.length = n+pre.length := by
    dsimp [z]
    rw [fold_length]
    simp
  have hw : w.length = z.length+1 := by simp [w,gateStep]
  have hval' : w.getD (n+pre.length) false = z.getD rep false := by
    have hv := hval x
    change (C.gates.foldl gateStep (List.ofFn x)).getD (n+pre.length) false =
      (C.gates.foldl gateStep (List.ofFn x)).getD rep false at hv
    rw [he,List.foldl_append] at hv
    change (post.foldl gateStep w).getD (n+pre.length) false =
      (post.foldl gateStep w).getD rep false at hv
    rw [fold_preserves_getD post w _ (by omega),
      fold_preserves_getD post w _ (by omega)] at hv
    have hh : w.getD rep false = z.getD rep false := by
      change (gateStep z g).getD rep false = _
      unfold gateStep
      rw [generic_getD_snoc]
      simp [show rep ≠ z.length by omega]
    exact hv.trans hh
  have hrel : ∀ i, w.getD i false =
      z.getD (redirectIndex (n+pre.length) rep i) false := by
    intro i
    by_cases hi : i = n+pre.length
    · subst i
      simpa [redirectIndex] using hval'
    · have hi' : i ≠ z.length := by omega
      change (gateStep z g).getD i false = _
      unfold gateStep
      rw [generic_getD_snoc]
      simp only [if_neg hi']
      by_cases hgt : n+pre.length < i
      · have h1 : ¬ i < z.length := by omega
        have h2 : ¬ i-1 < z.length := by omega
        simp [redirectIndex,hi,hgt,List.getD_eq_getElem?_getD,h1,h2]
      · simp [redirectIndex,hi,hgt]
  have hsim := redirect_fold_simulation (n+pre.length) rep post w z hr
      (by omega) hw hrel C.output
  change ((pre ++ post.map (redirectGate (n+pre.length) rep)).foldl
      gateStep (List.ofFn x)).getD (redirectIndex (n+pre.length) rep C.output) false =
    (C.gates.foldl gateStep (List.ofFn x)).getD C.output false
  rw [he,List.foldl_append,List.foldl_append]
  exact hsim.symm

/-- No gate of a least AO2 circuit is semantically equal to any
earlier wire: deletion would preserve its function and reduce size. -/
theorem least_no_earlier_equal {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (j rep : Nat) (hj : j < C.gates.length) (hr : rep < n+j) :
    ¬ (∀ x : Fin n → Bool, gateVal n C j x = wireVal n C rep x) := by
  intro hval
  obtain ⟨pre,g,post,he,hpre⟩ := split_at_index C.gates j hj
  have hr' : rep < n+pre.length := by omega
  have hv : ∀ x : Fin n → Bool,
      gateVal n C pre.length x = wireVal n C rep x := by
    rw [hpre]
    exact hval
  let D := deletedCircuit n C pre post rep
  have hAO : PEqualNP.TopForm.IsAO2 n D :=
    deleted_circuit_ao C hmin.1 pre post g rep he hr'
  have hf : PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ := by
    funext x
    change D.eval (List.ofFn x) = graphFun G ∅ x
    exact (deleted_circuit_eval C pre post g rep he hr' hv x).trans
      (congrFun hmin.2.1 x)
  have hs := hmin.2.2 D hAO hf
  change C.gates.length ≤ (pre ++ post.map (redirectGate (n+pre.length) rep)).length at hs
  rw [he] at hs
  simp only [List.length_append,List.length_cons,List.length_map] at hs
  omega

theorem least_and_not_subset {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (j a b : Nat) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [a,b]) :
    ¬ symbolicSupport n C a ⊆ symbolicSupport n C b := by
  intro hs
  have ha : a < n+j := hmin.1.2.1 j hj a (by rw [hin]; simp)
  exact least_no_earlier_equal G C hmin j a hj ha
    (fun x => comparable_and_value C hmin.1 j a b hj hop hin hs x)

theorem least_or_not_subset {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (j a b : Nat) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [a,b]) :
    ¬ symbolicSupport n C a ⊆ symbolicSupport n C b := by
  intro hs
  have hb : b < n+j := hmin.1.2.1 j hj b (by rw [hin]; simp)
  exact least_no_earlier_equal G C hmin j b hj hb
    (fun x => comparable_or_value C hmin.1 j a b hj hop hin hs x)

end L2260FirstMerge


/-! ## Minimum-circuit cuts: live gates

An unread non-output gate can be deleted without requiring equality
between that gate and the replacement wire. The simulation relation
therefore excludes precisely the deleted wire.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

theorem unread_redirect_step (cut rep : Nat) (w z : List Bool)
    (hr : rep < cut) (hc : cut < w.length)
    (hlen : w.length = z.length+1)
    (hrel : ∀ i, i ≠ cut → w.getD i false =
      z.getD (redirectIndex cut rep i) false)
    (g : Gate) (hg : cut ∉ g.inputs) :
    ∀ i, i ≠ cut → (gateStep w g).getD i false =
      (gateStep z (redirectGate cut rep g)).getD (redirectIndex cut rep i) false := by
  have hmap : g.inputs.map (fun i => w.getD i false) =
      (redirectGate cut rep g).inputs.map (fun i => z.getD i false) := by
    change g.inputs.map (fun i => w.getD i false) =
      (g.inputs.map (redirectIndex cut rep)).map (fun i => z.getD i false)
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact hrel i (fun he => hg (he ▸ hi))
  intro i hic
  unfold gateStep
  rw [generic_getD_snoc,generic_getD_snoc]
  have he : redirectIndex cut rep i = z.length ↔ i = w.length := by
    have h := redirect_index_end_iff (i := i) hr hc
    have hlen' : w.length-1 = z.length := by omega
    rw [hlen'] at h
    exact h
  by_cases hi : i = w.length
  · have hi' := he.mpr hi
    simp only [if_pos hi,if_pos hi']
    change g.op.eval (g.inputs.map (fun i => w.getD i false)) =
      g.op.eval ((redirectGate cut rep g).inputs.map (fun i => z.getD i false))
    rw [hmap]
  · have hi' : redirectIndex cut rep i ≠ z.length := fun h => hi (he.mp h)
    simp only [if_neg hi,if_neg hi']
    exact hrel i hic

theorem unread_redirect_fold (cut rep : Nat) (gs : List Gate)
    (w z : List Bool) (hr : rep < cut) (hc : cut < w.length)
    (hlen : w.length = z.length+1)
    (hrel : ∀ i, i ≠ cut → w.getD i false =
      z.getD (redirectIndex cut rep i) false)
    (hgs : ∀ g ∈ gs, cut ∉ g.inputs) :
    ∀ i, i ≠ cut → (gs.foldl gateStep w).getD i false =
      ((gs.map (redirectGate cut rep)).foldl gateStep z).getD
        (redirectIndex cut rep i) false := by
  induction gs generalizing w z with
  | nil => exact hrel
  | cons g gs ih =>
      change ∀ i, i ≠ cut → (gs.foldl gateStep (gateStep w g)).getD i false =
        ((gs.map (redirectGate cut rep)).foldl gateStep
          (gateStep z (redirectGate cut rep g))).getD (redirectIndex cut rep i) false
      apply ih (gateStep w g) (gateStep z (redirectGate cut rep g))
      · simp only [gateStep,List.length_append,List.length_cons,List.length_nil]
        omega
      · simp only [gateStep,List.length_append,List.length_cons,List.length_nil]
        omega
      · exact unread_redirect_step cut rep w z hr hc hlen hrel g (hgs g (by simp))
      · intro a ha
        exact hgs a (List.mem_cons.mpr (Or.inr ha))

theorem unread_deleted_eval {n : Nat} (C : Circuit)
    (pre post : List Gate) (g : Gate) (rep : Nat)
    (he : C.gates = pre ++ g :: post) (hr : rep < n+pre.length)
    (hout : C.output ≠ n+pre.length)
    (hpost : ∀ a ∈ post, n+pre.length ∉ a.inputs)
    (x : Fin n → Bool) :
    (deletedCircuit n C pre post rep).eval (List.ofFn x) =
      C.eval (List.ofFn x) := by
  let z := pre.foldl gateStep (List.ofFn x)
  let w := gateStep z g
  have hz : z.length = n+pre.length := by
    dsimp [z]
    rw [fold_length]
    simp
  have hw : w.length = z.length+1 := by simp [w,gateStep]
  have hrel : ∀ i, i ≠ n+pre.length → w.getD i false =
      z.getD (redirectIndex (n+pre.length) rep i) false := by
    intro i hi
    have hi' : i ≠ z.length := by omega
    change (gateStep z g).getD i false = _
    unfold gateStep
    rw [generic_getD_snoc]
    simp only [if_neg hi']
    by_cases hgt : n+pre.length < i
    · have h1 : ¬ i < z.length := by omega
      have h2 : ¬ i-1 < z.length := by omega
      simp [redirectIndex,hi,hgt,List.getD_eq_getElem?_getD,h1,h2]
    · simp [redirectIndex,hi,hgt]
  have hsim := unread_redirect_fold (n+pre.length) rep post w z hr
    (by omega) hw hrel hpost C.output hout
  change ((pre ++ post.map (redirectGate (n+pre.length) rep)).foldl
      gateStep (List.ofFn x)).getD (redirectIndex (n+pre.length) rep C.output) false =
    (C.gates.foldl gateStep (List.ofFn x)).getD C.output false
  rw [he,List.foldl_append,List.foldl_append]
  exact hsim.symm

private theorem mem_has_index {α : Type} (l : List α) (a d : α)
    (ha : a ∈ l) : ∃ i < l.length, l.getD i d = a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rcases List.mem_cons.mp ha with he | h
      · exact ⟨0,by simp,by simp [he]⟩
      · obtain ⟨i,hi,hv⟩ := ih h
        exact ⟨i+1,by simpa using Nat.succ_lt_succ hi,by simpa using hv⟩

/-- Every real gate in a least circuit is the output or has a direct
reader at a strictly later gate. -/
theorem least_gate_has_reader {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (j : Nat) (hj : j < C.gates.length) :
    C.output = n+j ∨ ∃ k < C.gates.length, j < k ∧
      n+j ∈ (gateAt C k).inputs := by
  classical
  by_contra h
  have hout : C.output ≠ n+j := fun he => h (Or.inl he)
  obtain ⟨pre,g,post,he,hpre⟩ := split_at_index C.gates j hj
  have hpost : ∀ a ∈ post, n+pre.length ∉ a.inputs := by
    intro a ha hm
    obtain ⟨i,hi,hv⟩ := mem_has_index post a ⟨GateOp.or,[]⟩ ha
    let k := pre.length+(i+1)
    have hk : k < C.gates.length := by
      rw [he]
      simp only [List.length_append,List.length_cons]
      dsimp [k]
      omega
    have hgate : gateAt C k = a := by
      unfold gateAt
      rw [he]
      change (pre ++ g :: post).getD (pre.length+(i+1)) ⟨GateOp.or,[]⟩ = a
      rw [delete_getD_right]
      exact hv
    apply h
    refine Or.inr ⟨k,hk,?_,?_⟩
    · dsimp [k]
      omega
    · rw [hgate,← hpre]
      exact hm
  let rep := PEqualNP.TopForm.opnd C j 0
  have hr : rep < n+pre.length := by
    rw [hpre]
    exact (actual_opnds C hmin.1 j hj).2.1
  let D := deletedCircuit n C pre post rep
  have hAO : PEqualNP.TopForm.IsAO2 n D :=
    deleted_circuit_ao C hmin.1 pre post g rep he hr
  have hf : PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ := by
    funext x
    change D.eval (List.ofFn x) = graphFun G ∅ x
    have hout' : C.output ≠ n+pre.length := by rwa [hpre]
    exact (unread_deleted_eval C pre post g rep he hr hout' hpost x).trans
      (congrFun hmin.2.1 x)
  have hs := hmin.2.2 D hAO hf
  change C.gates.length ≤ (pre ++ post.map (redirectGate (n+pre.length) rep)).length at hs
  rw [he] at hs
  simp only [List.length_append,List.length_cons,List.length_map] at hs
  omega

/-- In a least circuit a gate cannot read the same source twice. -/
theorem least_distinct_operands {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (j : Nat) (hj : j < C.gates.length) :
    PEqualNP.TopForm.opnd C j 0 ≠ PEqualNP.TopForm.opnd C j 1 := by
  intro he
  obtain ⟨hin,ha,hb⟩ := actual_opnds C hmin.1 j hj
  rcases hmin.1.1 _ (actual_gate_mem C j hj) with hop | hop
  · apply least_and_not_subset G C hmin j _ _ hj hop hin
    rw [he]
  · apply least_or_not_subset G C hmin j _ _ hj hop hin
    rw [he]

/-- Different real OR gates of a least circuit have distinct expanded
supports, since equal supports imply equality on all Boolean inputs. -/
theorem least_distinct_or_supports {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (i j : Nat) (hj : j < C.gates.length) (hij : i < j) :
    symbolicSupport n C (n+i) ≠ symbolicSupport n C (n+j) := by
  intro he
  apply least_no_earlier_equal G C hmin j (n+i) hj (by omega)
  intro x
  change wireVal n C (n+j) x = wireVal n C (n+i) x
  have h1 := support_subset_wire_imp C hmin.1 (n+i) (n+j) (by rw [he]) x
  have h2 := support_subset_wire_imp C hmin.1 (n+j) (n+i) (by rw [he]) x
  cases ha : wireVal n C (n+j) x <;> cases hb : wireVal n C (n+i) x <;> simp_all

end L2260FirstMerge


/-! ## Minimum-circuit cuts: closure of the internal network

A dirty wire cannot be the output. A direct OR reader of a dirty
wire is itself dirty. Following readers in a least top-form circuit
therefore proves that every dirty OR is in the raw/junk network.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

theorem or_reader_support_subset {n : Nat} (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (j w : Nat)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hw : w ∈ (gateAt C j).inputs) :
    symbolicSupport n C w ⊆ symbolicSupport n C (n+j) := by
  have hu := symbolic_expand n C (n+j) (real_or_expandable C hAO j hj hop)
  have he : n+j-n = j := by omega
  rw [he] at hu
  rw [(actual_opnds C hAO j hj).1] at hw
  rcases List.mem_cons.mp hw with h | h
  · subst w
    rw [hu]
    exact Finset.subset_union_left
  · have h' : w = PEqualNP.TopForm.opnd C j 1 := by simpa using h
    subst w
    rw [hu]
    exact Finset.subset_union_right

theorem dirty_not_output {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (j : Nat) (hd : ¬ PEqualNP.TopForm.BelowF G C j) :
    C.output ≠ n+j := by
  intro he
  apply hd
  intro x hx
  have hf := congrFun hmin.2.1 x
  change (C.wires (List.ofFn x)).getD C.output false = graphFun G ∅ x at hf
  rw [he] at hf
  change (C.wires (List.ofFn x)).getD (n+j) false = true at hx
  exact hf.symm.trans hx

theorem dirty_or_reader_dirty {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (i j : Nat) (hd : ¬ PEqualNP.TopForm.BelowF G C i)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hr : n+i ∈ (gateAt C j).inputs) :
    ¬ PEqualNP.TopForm.BelowF G C j := by
  intro hc
  apply hd
  intro x hx
  apply hc x
  change wireVal n C (n+j) x = true
  exact support_subset_wire_imp C hAO (n+i) (n+j)
    (or_reader_support_subset C hAO j (n+i) hj hop hr) x hx

/-- All dirty ORs are retained, not just those known a priori to
have raw/junk-only support. The descending induction is justified
by strict physical readback and the absence of unused gates. -/
theorem dirty_or_internal {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (j : Nat) (hj : j ∈ PEqualNP.TopForm.orN G C) :
    j ∈ internalOrGates G C := by
  have aux : ∀ d j : Nat, d = C.gates.length-j →
      j ∈ PEqualNP.TopForm.orN G C → j ∈ internalOrGates G C := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
        intro j hdist hj
        have hm := Finset.mem_filter.mp hj
        have hjlt := Finset.mem_range.mp hm.1
        have hop := hm.2.1
        have hd := hm.2.2
        have hs : symbolicSupport n C (n+j) ⊆ atomUniverse G C := by
          rcases least_gate_has_reader G C hmin j hjlt with hout | ⟨k,hk,hjk,hr⟩
          · exact False.elim (dirty_not_output G C hmin j hd hout)
          · rcases hmin.1.1 _ (actual_gate_mem C k hk) with ha | ho
            · exact and_operand_support_subset G C hmin.1 htop k hk ha (n+j) hr
            · have hd' := dirty_or_reader_dirty G C hmin.1 j k hd hk ho hr
              have hmem : k ∈ PEqualNP.TopForm.orN G C :=
                Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,ho,hd'⟩
              have hkl : C.gates.length-k < d := by omega
              have hki := ih (C.gates.length-k) hkl k rfl hmem
              exact (or_reader_support_subset C hmin.1 k (n+j) hk ho hr).trans
                (internal_or_mem G C k hki).2.2
        change j ∈ localDirtyOrGates G C (atomUniverse G C)
        exact Finset.mem_filter.mpr ⟨hm.1,hop,hd,hs⟩
  exact aux (C.gates.length-j) j rfl hj

theorem internal_or_eq_orN {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C) :
    internalOrGates G C = PEqualNP.TopForm.orN G C := by
  apply Finset.Subset.antisymm
  · exact local_dirty_or_subset G C (atomUniverse G C)
  · intro j hj
    exact dirty_or_internal G C hmin htop j hj

/-- Every dirty gate has a direct reader retained by the SAT model:
an AND (junk or clean) or a retained physical OR. -/
theorem dirty_gate_internal_reader {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (j : Nat) (hj : j < C.gates.length)
    (hd : ¬ PEqualNP.TopForm.BelowF G C j) :
    ∃ k < C.gates.length, j < k ∧ n+j ∈ (gateAt C k).inputs ∧
      ((gateAt C k).op = GateOp.and ∨ k ∈ internalOrGates G C) := by
  rcases least_gate_has_reader G C hmin j hj with hout | ⟨k,hk,hjk,hr⟩
  · exact False.elim (dirty_not_output G C hmin j hd hout)
  · refine ⟨k,hk,hjk,hr,?_⟩
    rcases hmin.1.1 _ (actual_gate_mem C k hk) with ha | ho
    · exact Or.inl ha
    · apply Or.inr
      apply dirty_or_internal G C hmin htop k
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,ho,
        dirty_or_reader_dirty G C hmin.1 j k hd hk ho hr⟩

theorem internal_or_has_reader {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (j : Nat) (hj : j ∈ internalOrGates G C) :
    ∃ k < C.gates.length, j < k ∧ n+j ∈ (gateAt C k).inputs ∧
      ((gateAt C k).op = GateOp.and ∨ k ∈ internalOrGates G C) := by
  have hm := Finset.mem_filter.mp (local_dirty_or_subset G C (atomUniverse G C) hj)
  exact dirty_gate_internal_reader G C hmin htop j (Finset.mem_range.mp hm.1) hm.2.2

theorem junk_has_internal_reader {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (j : Nat) (hj : j ∈ PEqualNP.TopForm.junk G C) :
    ∃ k < C.gates.length, j < k ∧ n+j ∈ (gateAt C k).inputs ∧
      ((gateAt C k).op = GateOp.and ∨ k ∈ internalOrGates G C) := by
  have hm := Finset.mem_filter.mp hj
  have hd : IsDirtyAnd n G C j := hm.2
  obtain ⟨_,_,x,hx,hf⟩ := hd
  have hn : ¬ PEqualNP.TopForm.BelowF G C j := by
    intro hc
    have ht := hc x hx
    rw [hf] at ht
    contradiction
  exact dirty_gate_internal_reader G C hmin htop j (Finset.mem_range.mp hm.1) hn

theorem least_two_junk_source_count {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (h2 : (PEqualNP.TopForm.junk G C).card = 2) :
    (internalSource G C).card = n+2+(PEqualNP.TopForm.orN G C).card := by
  rw [internal_source_card,h2,internal_or_eq_orN G C hmin htop]

end L2260FirstMerge


/-! ## Graph exposure (v19)

Changing just one input can change the output only if some first
reader changes. An OR whose raw support contains a true input is
already true and cannot change under this monotone input extension.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

theorem raw_wire_value {n : Nat} (C : Circuit) (x : Fin n → Bool)
    (u : Fin n) : wireVal n C u.val x = x u := by
  change (C.gates.foldl gateStep (List.ofFn x)).getD u.val false = x u
  rw [fold_preserves_getD C.gates _ _ (by simpa using u.isLt)]
  simp [List.getD_eq_getElem?_getD,u.isLt]

theorem raw_symbolic_singleton {n : Nat} (C : Circuit) (u : Fin n) :
    symbolicSupport n C u.val = {u.val} := by
  apply symbolic_atom
  intro h
  have h' := h.1
  exact (Nat.not_le_of_lt u.isLt) h'

theorem raw_reader_or_internal {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (u : Fin n) (j : Nat) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hr : u.val ∈ (gateAt C j).inputs) :
    j ∈ internalOrGates G C := by
  have hm : u.val ∈ symbolicSupport n C (n+j) := by
    apply or_reader_support_subset C hmin.1 j u.val hj hop hr
    rw [raw_symbolic_singleton C u]
    simp
  have hd : ¬ PEqualNP.TopForm.BelowF G C j := by
    intro hc
    have hx : wireVal n C u.val (pairInput u u) = true := by
      rw [raw_wire_value]
      simp [pairInput]
    have ht : gateVal n C j (pairInput u u) = true :=
      (symbolic_eval C hmin.1 (pairInput u u) (n+j)).mpr ⟨u.val,hm,hx⟩
    have hh := hc (pairInput u u) ht
    rw [graph_singleton_false G u] at hh
    contradiction
  exact dirty_or_internal G C hmin htop j
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hop,hd⟩)

theorem graph_exposure {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ u, u ≠ v → x u = y u)
    (hxv : x v = false) (hyv : y v = true)
    (hfx : graphFun G ∅ x = false) (hfy : graphFun G ∅ y = true) :
    (∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      v.val ∈ (gateAt C j).inputs) ∨
    (∃ j ∈ internalOrGates G C, v.val ∈ (gateAt C j).inputs ∧
      ∀ u : Fin n, x u = true → u.val ∉ symbolicSupport n C (n+j)) := by
  classical
  by_contra hn
  have hmono : ∀ u, x u = true → y u = true := by
    intro u hu
    by_cases he : u = v
    · subst u
      exact hyv
    · rw [← hxy u he]
      exact hu
  have hsame : ∀ w : Nat, w < n+C.gates.length → w ≠ v.val →
      wireVal n C w x = wireVal n C w y := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
        intro hw hv
        by_cases hraw : w < n
        · let u : Fin n := ⟨w,hraw⟩
          have hu : u ≠ v := by
            intro he
            apply hv
            exact congrArg Fin.val he
          change wireVal n C u.val x = wireVal n C u.val y
          rw [raw_wire_value,raw_wire_value]
          exact hxy u hu
        · let j := w-n
          have hidx : w = n+j := by dsimp [j]; omega
          have hj : j < C.gates.length := by omega
          obtain ⟨hin,ha,hb⟩ := actual_opnds C hmin.1 j hj
          let a := PEqualNP.TopForm.opnd C j 0
          let b := PEqualNP.TopForm.opnd C j 1
          have har : a ∈ (gateAt C j).inputs := by rw [hin]; simp [a]
          have hbr : b ∈ (gateAt C j).inputs := by rw [hin]; simp [b]
          by_cases hread : v.val ∈ (gateAt C j).inputs
          · have hop : (gateAt C j).op = GateOp.or := by
              rcases hmin.1.1 _ (actual_gate_mem C j hj) with hand | hor
              · exact False.elim (hn (Or.inl ⟨j,hj,hand,hread⟩))
              · exact hor
            have hjin := raw_reader_or_internal G C hmin htop v j hj hop hread
            have hex : ∃ u : Fin n, x u = true ∧
                u.val ∈ symbolicSupport n C (n+j) := by
              by_contra hh
              apply hn
              refine Or.inr ⟨j,hjin,hread,?_⟩
              intro u hu hm
              exact hh ⟨u,hu,hm⟩
            obtain ⟨u,hu,hm⟩ := hex
            have ht : wireVal n C (n+j) x = true :=
              (symbolic_eval C hmin.1 x (n+j)).mpr
                ⟨u.val,hm,(raw_wire_value C x u).trans hu⟩
            have ht' : wireVal n C (n+j) y = true :=
              wire_monotone C hmin.1 x y hmono (n+j) ht
            rw [hidx,ht,ht']
          · have han : a ≠ v.val := fun he => hread (he ▸ har)
            have hbn : b ≠ v.val := fun he => hread (he ▸ hbr)
            have hal : a < w := by rw [hidx]; exact ha
            have hbl : b < w := by rw [hidx]; exact hb
            have hA := ih a hal (hal.trans hw) han
            have hB := ih b hbl (hbl.trans hw) hbn
            rw [hidx]
            rcases hmin.1.1 _ (actual_gate_mem C j hj) with hand | hor
            · have h1 := gateVal_and_eq C hmin.1.2.1 j a b hj hand hin x
              have h2 := gateVal_and_eq C hmin.1.2.1 j a b hj hand hin y
              change wireVal n C (n+j) x = (wireVal n C a x && wireVal n C b x) at h1
              change wireVal n C (n+j) y = (wireVal n C a y && wireVal n C b y) at h2
              rw [h1,h2,hA,hB]
            · have h1 := gateVal_or_eq C hmin.1.2.1 j a b hj hor hin x
              have h2 := gateVal_or_eq C hmin.1.2.1 j a b hj hor hin y
              change wireVal n C (n+j) x = (wireVal n C a x || wireVal n C b x) at h1
              change wireVal n C (n+j) y = (wireVal n C a y || wireVal n C b y) at h2
              rw [h1,h2,hA,hB]
  have hpos : ∃ u w, G.Adj u w ∧ y u = true ∧ y w = true := by
    simpa [graphFun] using hfy
  obtain ⟨u,t,he,_,_⟩ := hpos
  have hout := actual_output_bound G C hmin u t he
  have houtne : C.output ≠ v.val := by
    intro heq
    have hf := congrFun hmin.2.1 (pairInput v v)
    change wireVal n C C.output (pairInput v v) =
      graphFun G ∅ (pairInput v v) at hf
    rw [heq,raw_wire_value,graph_singleton_false G v] at hf
    simp [pairInput] at hf
  have hs := hsame C.output hout houtne
  change C.eval (List.ofFn x) = C.eval (List.ofFn y) at hs
  have hf1 := congrFun hmin.2.1 x
  have hf2 := congrFun hmin.2.1 y
  change C.eval (List.ofFn x) = graphFun G ∅ x at hf1
  change C.eval (List.ofFn y) = graphFun G ∅ y at hf2
  rw [hf1,hf2,hfx,hfy] at hs
  contradiction

end L2260FirstMerge


/-! ## Output OR closure and edge-wise redundancy

Every clean AND occurs in the output OR closure of a least top-form
circuit. Edge coverage of a subset of the tops suffices for coverage
on all inputs. These results are prerequisites for the private-edge
minimality cut; they do not yet assert that the subset can be realized
with fewer gates.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

def topWires {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) : Finset Nat :=
  (PEqualNP.TopForm.tops G C).image (fun j => n+j)

theorem top_wire_not_atom {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (i : Nat)
    (hi : i ∈ PEqualNP.TopForm.tops G C) :
    n+i ∉ atomUniverse G C := by
  intro ha
  rcases Finset.mem_union.mp ha with hr | hj
  · have h := Finset.mem_range.mp hr
    omega
  · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hj
    change n+j = n+i at he
    have hji : j = i := by omega
    subst j
    have hd : IsDirtyAnd n G C i := (Finset.mem_filter.mp hj).2
    obtain ⟨_,_,x,hx,hf⟩ := hd
    have hc := (Finset.mem_filter.mp hi).2.2 x hx
    rw [hf] at hc
    contradiction

theorem and_wire_symbolic_singleton {n : Nat} (C : Circuit) (i : Nat)
    (hop : (gateAt C i).op = GateOp.and) :
    symbolicSupport n C (n+i) = {n+i} := by
  apply symbolic_atom
  intro h
  have he : n+i-n = i := by omega
  have ho := h.2.2.1
  rw [he,hop] at ho
  contradiction

/-- A top atom appearing at any real gate must appear in the output:
follow a reader and rule out AND readers using TopForm. -/
theorem top_leaf_reaches_output {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C) (i : Nat)
    (hi : i ∈ PEqualNP.TopForm.tops G C)
    (j : Nat) (hj : j < C.gates.length)
    (hleaf : n+i ∈ symbolicSupport n C (n+j)) :
    n+i ∈ symbolicSupport n C C.output := by
  have hn := top_wire_not_atom G C i hi
  have aux : ∀ d j : Nat, d = C.gates.length-j →
      j < C.gates.length → n+i ∈ symbolicSupport n C (n+j) →
      n+i ∈ symbolicSupport n C C.output := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
        intro j hdist hj hm
        rcases least_gate_has_reader G C hmin j hj with hout | ⟨k,hk,hjk,hr⟩
        · rw [hout]
          exact hm
        · rcases hmin.1.1 _ (actual_gate_mem C k hk) with ha | ho
          · exact False.elim (hn (and_operand_support_subset G C hmin.1 htop
              k hk ha (n+j) hr hm))
          · have hd : C.gates.length-k < d := by omega
            exact ih (C.gates.length-k) hd k rfl hk
              (or_reader_support_subset C hmin.1 k (n+j) hk ho hr hm)
  exact aux (C.gates.length-j) j rfl hj hleaf

theorem output_support_eq_top_wires {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C) (u v : Fin n) (he : G.Adj u v) :
    symbolicSupport n C C.output = topWires G C := by
  apply Finset.Subset.antisymm
  · exact output_support_tops G C hmin u v he
  · intro a ha
    obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp ha
    have hm := Finset.mem_filter.mp hi
    rw [← heq]
    apply top_leaf_reaches_output G C hmin htop i hi i (Finset.mem_range.mp hm.1)
    rw [and_wire_symbolic_singleton C i hm.2.1]
    simp

theorem top_wires_card {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) :
    (topWires G C).card = (PEqualNP.TopForm.tops G C).card := by
  unfold topWires
  apply Finset.card_image_of_injective
  intro a b h
  change n+a = n+b at h
  omega

theorem clean_support_subset_tops {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (j : Nat)
    (hj : j < C.gates.length) (hc : PEqualNP.TopForm.BelowF G C j) :
    symbolicSupport n C (n+j) ⊆ topWires G C := by
  intro a ha
  have himp : ∀ x : Fin n → Bool, wireVal n C a x = true →
      graphFun G ∅ x = true := by
    intro x hx
    exact hc x ((symbolic_eval C hAO x (n+j)).mpr ⟨a,ha,hx⟩)
  rcases symbolic_leaf_kind C hAO (n+j) (by omega) a ha with hr | ⟨i,hi,he,hop⟩
  · have ham : a ∈ atomUniverse G C :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hr))
    obtain ⟨x,hx,hf⟩ := atom_dirty_witness G C a ham
    have ht := himp x hx
    rw [hf] at ht
    contradiction
  · have hb : PEqualNP.TopForm.BelowF G C i := by
      intro x hx
      apply himp x
      rw [he]
      exact hx
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hi,hop,hb⟩,he.symm⟩

theorem support_tops_implies_clean {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (j : Nat) (hs : symbolicSupport n C (n+j) ⊆ topWires G C) :
    PEqualNP.TopForm.BelowF G C j := by
  intro x hx
  obtain ⟨a,ha,ht⟩ := (symbolic_eval C hAO x (n+j)).mp hx
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (hs ha)
  rw [← he] at ht
  exact (Finset.mem_filter.mp hi).2.2 x ht

/-- Positive edge rows are enough to establish the full graph function
for an OR of any subset of the clean AND gates. -/
theorem edge_cover_full_truth {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (T : Finset Nat)
    (hT : T ⊆ PEqualNP.TopForm.tops G C)
    (hcover : ∀ u v : Fin n, G.Adj u v →
      ∃ j ∈ T, gateVal n C j (pairInput u v) = true)
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ j ∈ T, gateVal n C j x = true := by
  constructor
  · intro hx
    have he : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hx
    obtain ⟨u,v,huv,hu,hv⟩ := he
    obtain ⟨j,hj,ht⟩ := hcover u v huv
    have hm : ∀ w, pairInput u v w = true → x w = true := by
      intro w hw
      have h : w = u ∨ w = v := by simpa [pairInput] using hw
      rcases h with rfl | rfl
      · exact hu
      · exact hv
    exact ⟨j,hj,wire_monotone C hAO (pairInput u v) x hm (n+j) ht⟩
  · rintro ⟨j,hj,ht⟩
    exact (Finset.mem_filter.mp (hT hj)).2.2 x ht

/-- If a top lacks an exclusive positive edge, it can be omitted
from the semantic OR without changing the function. Realizing
this reduced OR by a smaller AO2 circuit is a separate step. -/
theorem no_private_edge_cover {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (i : Nat) (hi : i ∈ PEqualNP.TopForm.tops G C)
    (hn : ¬ ∃ u v : Fin n, G.Adj u v ∧
      gateVal n C i (pairInput u v) = true ∧
      ∀ j ∈ PEqualNP.TopForm.tops G C, j ≠ i →
        gateVal n C j (pairInput u v) = false)
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔
      ∃ j ∈ (PEqualNP.TopForm.tops G C).erase i, gateVal n C j x = true := by
  classical
  apply edge_cover_full_truth G C hmin.1 _ (Finset.erase_subset _ _) _ x
  intro u v he
  obtain ⟨j,hj,ht⟩ := (graph_eq_or_of_tops G C hmin u v he (pairInput u v)).mp
    (graph_pair_true G u v he)
  by_cases hji : j = i
  · subst j
    by_contra hh
    apply hn
    refine ⟨u,v,he,ht,?_⟩
    intro k hk hki
    cases hv : gateVal n C k (pairInput u v) with
    | false => rfl
    | true => exact False.elim (hh ⟨k,Finset.mem_erase.mpr ⟨hki,hk⟩,hv⟩)
  · exact ⟨j,Finset.mem_erase.mpr ⟨hji,hj⟩,ht⟩

end L2260FirstMerge


/-! ## Counting the clean output OR network

An arbitrary shared clean OR DAG covering k terminal ANDs costs at
least k-1 physical ORs. The argument counts rank merges, not tree
occurrences, so it does not assume fanout one.
-/
namespace L2260FirstMerge

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

attribute [local instance] gateOpDecEq

def cleanOrPrefix {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) (j : Nat) : Nat :=
  ((Finset.range j).filter fun i =>
    (gateAt C i).op = GateOp.or ∧ PEqualNP.TopForm.BelowF G C i ∧
      symbolicSupport n C (n+i) ⊆ V).card

private theorem clean_or_prefix_succ {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (V : Finset Nat) (j : Nat) :
    cleanOrPrefix G C V (j+1) = cleanOrPrefix G C V j +
      (if (gateAt C j).op = GateOp.or ∧ PEqualNP.TopForm.BelowF G C j ∧
          symbolicSupport n C (n+j) ⊆ V then 1 else 0) := by
  classical
  let P : Nat → Prop := fun i =>
    (gateAt C i).op = GateOp.or ∧ PEqualNP.TopForm.BelowF G C i ∧
      symbolicSupport n C (n+i) ⊆ V
  change ((Finset.range (j+1)).filter P).card =
    ((Finset.range j).filter P).card + (if P j then 1 else 0)
  rw [Finset.range_add_one]
  by_cases h : P j
  · have he : (insert j (Finset.range j)).filter P =
        insert j ((Finset.range j).filter P) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hp⟩
        rcases hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr ⟨hi,hp⟩
      · rintro (hi | ⟨hi,hp⟩)
        · subst i
          exact ⟨Or.inl rfl,h⟩
        · exact ⟨Or.inr hi,hp⟩
    rw [he,Finset.card_insert_of_notMem,if_pos h]
    intro hm
    exact Finset.notMem_range_self ((Finset.mem_filter.mp hm).1)
  · have he : (insert j (Finset.range j)).filter P =
        (Finset.range j).filter P := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hp⟩
        rcases hi with hi | hi
        · subst i
          exact False.elim (h hp)
        · exact ⟨hi,hp⟩
      · rintro ⟨hi,hp⟩
        exact ⟨Or.inr hi,hp⟩
    rw [he,if_neg h,Nat.add_zero]

theorem clean_or_prefix_labels {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (V : Finset Nat) (hV : V ⊆ topWires G C)
    (j : Nat) (hj : j ≤ C.gates.length) :
    ∃ l : Nat → Nat,
      (∀ w < n+j, symbolicSupport n C w ⊆ V →
        SupportLocal l (symbolicSupport n C w)) ∧
      V.card ≤ atomRank V l + cleanOrPrefix G C V j := by
  classical
  induction j with
  | zero =>
      refine ⟨id,?_,?_⟩
      · intro w hw _
        rw [symbolic_atom n C w (by intro h; have hh := h.1; omega)]
        exact local_singleton id w
      · simp [atomRank,cleanOrPrefix]
  | succ j ih =>
      have hj' : j < C.gates.length := by omega
      obtain ⟨l,hl,hbudget⟩ := ih (by omega)
      have hcost : cleanOrPrefix G C V j ≤ cleanOrPrefix G C V (j+1) := by
        rw [clean_or_prefix_succ]
        omega
      by_cases he : Expandable n C (n+j)
      · by_cases hs : symbolicSupport n C (n+j) ⊆ V
        · let a := PEqualNP.TopForm.opnd C j 0
          let b := PEqualNP.TopForm.opnd C j 1
          have hidx : n+j-n = j := by omega
          have ha : a < n+j := by simpa [a,hidx] using he.2.2.2.1
          have hb : b < n+j := by simpa [b,hidx] using he.2.2.2.2
          have hu : symbolicSupport n C (n+j) =
              symbolicSupport n C a ∪ symbolicSupport n C b := by
            simpa [a,b,hidx] using symbolic_expand n C (n+j) he
          have hA : symbolicSupport n C a ⊆ V := by
            intro x hx
            apply hs
            rw [hu]
            exact Finset.mem_union.mpr (Or.inl hx)
          have hB : symbolicSupport n C b ⊆ V := by
            intro x hx
            apply hs
            rw [hu]
            exact Finset.mem_union.mpr (Or.inr hx)
          obtain ⟨l',hp,hu',hr⟩ :=
            atom_rank_union V l (symbolicSupport n C a) (symbolicSupport n C b)
              (hl a ha hA) (hl b hb hB)
          have hop : (gateAt C j).op = GateOp.or := by
            simpa [hidx] using he.2.2.1
          have hU : symbolicSupport n C (n+j) ⊆ topWires G C :=
            fun _ hx => hV (hs hx)
          have hd := support_tops_implies_clean G C hAO j hU
          have hcharge : (gateAt C j).op = GateOp.or ∧
              PEqualNP.TopForm.BelowF G C j ∧
              symbolicSupport n C (n+j) ⊆ V :=
            ⟨hop,hd,hs⟩
          refine ⟨l',?_,?_⟩
          · intro w hw hwV
            by_cases hw' : w < n+j
            · exact preserves_local l l' hp _ (hl w hw' hwV)
            · have hwe : w = n+j := by omega
              subst w
              rw [hu]
              exact hu'
          · rw [clean_or_prefix_succ,if_pos hcharge]
            omega
        · refine ⟨l,?_,by omega⟩
          intro w hw hwV
          by_cases hw' : w < n+j
          · exact hl w hw' hwV
          · have hwe : w = n+j := by omega
            subst w
            exact False.elim (hs hwV)
      · refine ⟨l,?_,by omega⟩
        intro w hw hwV
        by_cases hw' : w < n+j
        · exact hl w hw' hwV
        · have hwe : w = n+j := by omega
          subst w
          rw [symbolic_atom n C (n+j) he]
          exact local_singleton l _


theorem clean_output_or_budget {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C) (u v : Fin n) (he : G.Adj u v) :
    (PEqualNP.TopForm.tops G C).card ≤ 1 + (PEqualNP.TopForm.orT G C).card := by
  classical
  let V := topWires G C
  have hs : symbolicSupport n C C.output = V :=
    output_support_eq_top_wires G C hmin htop u v he
  obtain ⟨l,hl,hb⟩ := clean_or_prefix_labels G C hmin.1 V
    (fun _ h => h) C.gates.length (Nat.le_refl _)
  have hloc := hl C.output (actual_output_bound G C hmin u v he)
    (show symbolicSupport n C C.output ⊆ V from by rw [hs])
  rw [hs] at hloc
  obtain ⟨a,ha⟩ := symbolic_nonempty n C C.output
  rw [hs] at ha
  have him : V.image l ⊆ ({l a} : Finset Nat) := by
    intro z hz
    obtain ⟨x,hx,heq⟩ := Finset.mem_image.mp hz
    exact Finset.mem_singleton.mpr (heq.symm.trans (hloc x hx a ha))
  have hr : atomRank V l ≤ 1 :=
    (Finset.card_le_card him).trans (by simp)
  have hc : cleanOrPrefix G C V C.gates.length ≤
      (PEqualNP.TopForm.orT G C).card := by
    unfold cleanOrPrefix
    apply Finset.card_le_card
    intro i hi
    have hm := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hm.1,hm.2.1,hm.2.2.1⟩
  have hcard : V.card = (PEqualNP.TopForm.tops G C).card :=
    top_wires_card G C
  omega

theorem top_wires_disjoint_atoms {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) :
    Disjoint (topWires G C) (atomUniverse G C) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp ha
  rw [← he] at hb
  exact top_wire_not_atom G C i hi hb

/-- No clean gate is read by an AND or a dirty OR. This is the
separation needed to rebuild only the output network. -/
theorem clean_gate_reader_clean_or {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (i j : Nat) (hi : i < C.gates.length)
    (hc : PEqualNP.TopForm.BelowF G C i)
    (hj : j < C.gates.length) (hr : n+i ∈ (gateAt C j).inputs) :
    j ∈ PEqualNP.TopForm.orT G C := by
  have hs := clean_support_subset_tops G C hmin.1 i hi hc
  obtain ⟨a,ha⟩ := symbolic_nonempty n C (n+i)
  have hna : a ∉ atomUniverse G C := by
    intro ham
    exact (Finset.disjoint_left.mp (top_wires_disjoint_atoms G C)) (hs ha) ham
  rcases hmin.1.1 _ (actual_gate_mem C j hj) with hand | hor
  · exact False.elim (hna (and_operand_support_subset G C hmin.1 htop
      j hj hand (n+i) hr ha))
  · have hclean : PEqualNP.TopForm.BelowF G C j := by
      by_contra hd
      have hm : j ∈ PEqualNP.TopForm.orN G C :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hor,hd⟩
      have hjin := dirty_or_internal G C hmin htop j hm
      exact hna ((internal_or_mem G C j hjin).2.2
        (or_reader_support_subset C hmin.1 j (n+i) hj hor hr ha))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hor,hclean⟩

/-- Equivalently, every operand of a gate that is not a clean OR
is outside the clean OR suffix to be removed. -/
theorem nonclean_or_no_clean_or_input {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (htop : PEqualNP.TopForm.TopForm G C)
    (j : Nat) (hj : j < C.gates.length)
    (hn : j ∉ PEqualNP.TopForm.orT G C) :
    ∀ i ∈ PEqualNP.TopForm.orT G C, n+i ∉ (gateAt C j).inputs := by
  intro i hi hr
  have hm := Finset.mem_filter.mp hi
  exact hn (clean_gate_reader_clean_or G C hmin htop i j
    (Finset.mem_range.mp hm.1) hm.2.2 hj hr)

end L2260FirstMerge
