/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Bounded descent on a finite set of states

Let `V` be a finite set of states, `Q v w` a property of a state `v` and a weight `w` in a
well-founded order, and `P v s` a property of a state `v` and a size `s`. Suppose that whenever
`Q v w` holds, either `P v t` holds, or there are a state `v'` and a smaller weight `w'` with
`Q v' w'` from which sizes are transported back at the cost of a function `f`:
`P v' s → P v (f s)` for every `s`. Then every state with `Q v w` satisfies `P v (f^[k] t)` for
some `k < |V|` (`TauCeti.exists_lt_card_iterate_of_descent`). The bound comes from the fact that
a shortest chain of transport steps ending in a state with `P · t` visits each state at most
once.

This is the counting argument that turns a terminating rewriting procedure on a finite set of
configurations into a bound. For word equations solved by recompression, the states are the
equations of bounded size, `Q E w` says that `E` has a solution of weight `w`, `P E s` says that
`E` has a solution of length at most `s`, and `f` is the cost of transporting a solution back
through one compression step.

## References

* V. Diekert, A. Jez, W. Plandowski, *Finding all solutions of equations in free groups and
  monoids with involution*, Inform. and Comput. 251 (2016), §2.2: the finite graph whose nodes
  are the equations of bounded size and whose paths give all solutions. That paper states no
  bound on the length of the paths; the bound here is the length of a shortest one.
-/

public section

namespace TauCeti

-- `DescentChain P f t k v`: the state `v` reaches a state of size `t` in `k` transport steps.
private inductive DescentChain {V S : Type*} (P : V → S → Prop) (f : S → S) (t : S) : ℕ → V → Prop
  | base {v} : P v t → DescentChain P f t 0 v
  | step {v v' k} : (∀ s, P v' s → P v (f s)) → DescentChain P f t k v' →
      DescentChain P f t (k + 1) v

private theorem DescentChain.prop {V S : Type*} {P : V → S → Prop} {f : S → S} {t : S} {k : ℕ}
    {v : V} (h : DescentChain P f t k v) : P v (f^[k] t) := by
  induction h with
  | base h => simpa using h
  | step hT _ ih =>
    rw [Function.iterate_succ_apply']
    exact hT _ ih

-- Along a shortest chain of length `k`, the state `j` steps before the end, for each `j ≤ k`, is
-- reached by a chain of length `j` and by none shorter.
private theorem DescentChain.exists_min {V S : Type*} {P : V → S → Prop} {f : S → S} {t : S} {k : ℕ}
    {v : V} (h : DescentChain P f t k v) (hmin : ∀ j < k, ¬ DescentChain P f t j v) :
    ∀ j ≤ k, ∃ u, DescentChain P f t j u ∧ ∀ i < j, ¬ DescentChain P f t i u := by
  induction h with
  | base h =>
    intro j hj
    obtain rfl := Nat.le_zero.1 hj
    exact ⟨_, .base h, by simp⟩
  | @step v v' k hT hr ih =>
    intro j hj
    rcases hj.lt_or_eq with hj | rfl
    · exact ih (fun i hi hri ↦ hmin (i + 1) (by lia) (.step hT hri)) j (by lia)
    · exact ⟨v, .step hT hr, hmin⟩

/-- **Bounded descent.** On a finite set of states `V`, suppose that every state `v` with a
weight `w` (that is, `Q v w`) either satisfies `P v t` or leads to a state `v'` of smaller weight
with `P v' s → P v (f s)` for all `s`. Then every state `v` with a weight satisfies
`P v (f^[k] t)` for some `k < Nat.card V`.

Neither `P` nor `f` needs to be monotone, and `k` depends on `v`; to get one bound for all states,
compose with `s ≤ f s` and monotonicity of `P` in `s` where these hold. -/
theorem exists_lt_card_iterate_of_descent {V S W : Type*} [Finite V] [LT W] [WellFoundedLT W]
    {P : V → S → Prop} {Q : V → W → Prop} {f : S → S} {t : S}
    (hstep : ∀ v w, Q v w → P v t ∨ ∃ v' w', w' < w ∧ Q v' w' ∧ ∀ s, P v' s → P v (f s)) {v : V}
    {w : W} (hv : Q v w) : ∃ k < Nat.card V, P v (f^[k] t) := by
  classical
  -- Descent on the weight gives a chain of transport steps.
  have hex : ∃ k, DescentChain P f t k v := by
    induction w using WellFoundedLT.induction generalizing v with
    | _ w ih =>
      rcases hstep v w hv with h | ⟨v', w', hw', hv', hT⟩
      · exact ⟨0, .base h⟩
      · exact (ih w' hw' hv').elim fun k hk ↦ ⟨k + 1, .step hT hk⟩
  refine ⟨Nat.find hex, ?_, (Nat.find_spec hex).prop⟩
  -- The states `0, …, Nat.find hex` steps before the end of a shortest chain are distinct.
  choose g hg hg' using fun j : Fin (Nat.find hex + 1) ↦
    (Nat.find_spec hex).exists_min (fun _ ↦ Nat.find_min hex) j (Nat.lt_succ_iff.1 j.isLt)
  simpa using Nat.card_le_card_of_injective g
    (.of_lt_imp_ne fun i j hij hgij ↦ hg' j i hij (hgij ▸ hg i))

end TauCeti
