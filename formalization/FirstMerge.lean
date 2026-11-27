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
