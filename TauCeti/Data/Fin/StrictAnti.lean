/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Strictly antitone sequences indexed by `Fin n`

A sequence `f : Fin n → α` is strictly antitone when it strictly decreases along the indices.  This
file records facts about such sequences, used for beta-numbers of Young diagrams, the Pieri rule
for Schur polynomials and chains of critical values in Morse theory.

Over `ℕ` a strictly antitone sequence drops by at least one at each step, so it drops by at least
the index gap: `StrictAnti.add_sub_le_nat`.  This is what makes a strictly decreasing sequence of
`n` natural numbers a sequence of beta-numbers of a Young diagram.  The increasing analogue indexed
by all of `ℕ` is `StrictMono.add_le_nat`.

Over any linear order, an *injective* sequence becomes strictly antitone after precomposition with
Mathlib's decreasing sort `Tuple.sortDesc` (`Function.Injective.strictAnti_sortDesc`), and over any
partial order a permutation with this property is unique (`StrictAnti.perm_eq`): sorting into
decreasing order is possible and unambiguous.

For an antitone sequence `a`, the closed intervals `[a (i + 1), a i]` of consecutive steps overlap
only at their ends, so a point strictly inside one of them lies in no other
(`Antitone.eq_of_mem_Ioo_of_mem_Icc_fin`).

## Main results

* `StrictAnti.add_sub_le_nat`: a strictly antitone sequence of naturals drops by at least the index
  gap.
* `Function.Injective.strictAnti_sortDesc`: `Tuple.sortDesc` sorts an injective sequence into
  strictly decreasing order.
* `StrictAnti.perm_eq`: the sorting permutation is unique.
* `Antitone.eq_of_mem_Ioo_of_mem_Icc_fin`: for an antitone sequence, the open interval between two
  consecutive values meets the closed interval of no other step.
-/

public section

open Equiv

variable {n : ℕ} {α : Type*}

/-- **A strictly antitone sequence of naturals drops by at least the index gap**: it loses at least
one unit at each step, hence at least `j - i` units between the indices `i ≤ j`. -/
theorem StrictAnti.add_sub_le_nat {η : Fin n → ℕ} (hη : StrictAnti η) {i j : Fin n}
    (hij : i ≤ j) : η j + ((j : ℕ) - (i : ℕ)) ≤ η i := by
  obtain ⟨j, hj⟩ := j
  simp only [Fin.le_def] at hij
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ k hik ih => grind [hη (show (⟨k, by omega⟩ : Fin n) < ⟨k + 1, hj⟩ by simp)]

/-- **Sorting into decreasing order.**  Precomposing an injective sequence indexed by `Fin n` with
its decreasing sort `Tuple.sortDesc` makes it strictly antitone. -/
theorem Function.Injective.strictAnti_sortDesc [LinearOrder α] {f : Fin n → α}
    (hf : Function.Injective f) : StrictAnti (f ∘ Tuple.sortDesc f) :=
  (Tuple.antitone_sortDesc f).strictAnti_of_injective (hf.comp (Tuple.sortDesc f).injective)

/-- **The sorting permutation is unique.**  Two permutations of the indices that both make a
sequence strictly antitone are equal. -/
theorem StrictAnti.perm_eq [PartialOrder α] {f : Fin n → α} {τ₁ τ₂ : Perm (Fin n)}
    (h₁ : StrictAnti (f ∘ τ₁)) (h₂ : StrictAnti (f ∘ τ₂)) : τ₁ = τ₂ :=
  Equiv.ext <| congrFun <| ((τ₁.injective_comp f).mp h₁.injective).comp_left
    (Tuple.unique_antitone h₁.antitone h₂.antitone)

/-- **The steps of an antitone sequence overlap only at their ends.** If `a : Fin (n + 1) → α` is
antitone, a point strictly between `a (i + 1)` and `a i` lies between `a (j + 1)` and `a j` only
for `j = i`. -/
theorem Antitone.eq_of_mem_Ioo_of_mem_Icc_fin [Preorder α] {a : Fin (n + 1) → α}
    (ha : Antitone a) {i j : Fin n} {x : α} (hi : x ∈ Set.Ioo (a i.succ) (a i.castSucc))
    (hj : x ∈ Set.Icc (a j.succ) (a j.castSucc)) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd (hj.2.trans (ha (Fin.succ_le_castSucc_iff.2 hij))) (not_le_of_gt hi.1)
  · rfl
  · exact absurd ((ha (Fin.succ_le_castSucc_iff.2 hij)).trans hj.1) (not_le_of_gt hi.2)

