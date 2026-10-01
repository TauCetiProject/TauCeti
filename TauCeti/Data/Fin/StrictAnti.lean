/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.Preorder.Finite

/-!
# Strictly antitone sequences indexed by `Fin n`

A sequence `f : Fin n → α` is strictly antitone when it strictly decreases along the indices.  This
file records the three facts about such sequences that the Pieri rule for Schur polynomials needs.

Over `ℕ` a strictly antitone sequence drops by at least one at each step, so it drops by at least
the index gap: `TauCeti.add_sub_le_of_strictAnti`.  This is what makes a strictly decreasing
sequence of `n` natural numbers a sequence of beta-numbers of a Young diagram.  The increasing
analogue indexed by all of `ℕ` is `StrictMono.add_le_nat`.

Over any linear order, an *injective* sequence becomes strictly antitone after precomposition with a
suitable permutation of the indices (`TauCeti.exists_strictAnti_comp`), and that permutation is
unique (`TauCeti.eq_of_strictAnti_comp`): sorting into decreasing order is possible and
unambiguous.  Mathlib's `Tuple.sort` sorts into *increasing* order; composing with the reversal
`Fin.revPerm` turns it around.

## Main results

* `TauCeti.add_sub_le_of_strictAnti`: a strictly antitone sequence of naturals drops by at least
  the index gap.
* `TauCeti.exists_strictAnti_comp`: an injective sequence can be sorted into decreasing order.
* `TauCeti.eq_of_strictAnti_comp`: the sorting permutation is unique.
-/

public section

namespace TauCeti

open Equiv

/-- **A strictly antitone sequence of naturals drops by at least the index gap**: it loses at least
one unit at each step, hence at least `j - i` units between the indices `i ≤ j`. -/
theorem add_sub_le_of_strictAnti {n : ℕ} {η : Fin n → ℕ} (hη : StrictAnti η) {i j : Fin n}
    (hij : i ≤ j) : η j + ((j : ℕ) - (i : ℕ)) ≤ η i := by
  have key : ∀ k : ℕ, ∀ i j : Fin n, (i : ℕ) + k = (j : ℕ) → η j + k ≤ η i := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      have hij' : i = j := Fin.ext (by omega)
      subst hij'
      simp
    | succ k ih =>
      intro i j hij
      have hi : (i : ℕ) + 1 < n := by omega
      have hlt : η ⟨(i : ℕ) + 1, hi⟩ < η i := hη (by simp [Fin.lt_def])
      have := ih ⟨(i : ℕ) + 1, hi⟩ j (by simp; omega)
      omega
  exact key _ i j (by omega)

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- **Sorting into decreasing order.**  Precomposing an injective sequence indexed by `Fin n` with
a suitable permutation of the indices makes it strictly antitone. -/
theorem exists_strictAnti_comp {f : Fin n → α} (hf : Function.Injective f) :
    ∃ τ : Perm (Fin n), StrictAnti (f ∘ τ) := by
  have hmono : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  refine ⟨Fin.revPerm.trans (Tuple.sort f), fun i j hij => ?_⟩
  simpa using hmono (Fin.rev_lt_rev.mpr hij)

/-- **The sorting permutation is unique.**  Two permutations of the indices that both make a
sequence strictly antitone are equal. -/
theorem eq_of_strictAnti_comp {f : Fin n → α} {τ₁ τ₂ : Perm (Fin n)}
    (h₁ : StrictAnti (f ∘ τ₁)) (h₂ : StrictAnti (f ∘ τ₂)) : τ₁ = τ₂ := by
  have hf : Function.Injective f := by
    have hfact : (f : Fin n → α) = (f ∘ ⇑τ₁) ∘ ⇑τ₁.symm := funext fun i => by simp
    rw [hfact]
    exact h₁.injective.comp τ₁.symm.injective
  exact Equiv.ext fun i =>
    hf (congrFun (Tuple.unique_antitone h₁.antitone h₂.antitone) i)

end TauCeti
