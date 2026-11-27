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
  · simp [dirtyOrPrefix, Finset.range_add_one, h]
  · simp [dirtyOrPrefix, Finset.range_add_one, h]

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
