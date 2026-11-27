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
