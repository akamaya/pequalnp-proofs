import Mathlib

/-!
Standalone first-merge lemmas for the graph-circuit reduction.
This is a draft to compile in the project's Lean environment.
It does not yet connect the abstract trace to Circuit/gateVal.
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
