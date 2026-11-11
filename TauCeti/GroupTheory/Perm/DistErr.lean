/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.MovedNorm

/-!
# The distance with errors between permutations of different degrees

Chapman and Lubotzky compare permutations of possibly different degrees `n` and `m` by
`Equiv.Perm.distErr σ τ = 1 - #{j < min n m | σ j = τ j} / max n m`, the values `σ j` and
`τ j` being compared as natural numbers. This is the distance used to define their cross-degree
coboundary constant, where the gauge may live in a different symmetric group than the cochain.

Main results:

* `Equiv.Perm.distErr_eq_movedNorm_div`: in equal degree `n ≠ 0`, the distance with errors is the
  normalized Hamming distance `movedNorm (σ⁻¹ * τ) / n`;
* `Equiv.Perm.distErr_comm`: the distance with errors is symmetric;
* `Equiv.Perm.one_sub_min_div_max_le_distErr`: it is at least `1 - min n m / max n m`, with
  equality for the two identity permutations (`Equiv.Perm.distErr_one_one`).

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, equation (2.9).
-/

public section

open Finset

namespace Equiv.Perm

variable {n m : ℕ}

/-- The number of common indices `j < min n m` at which `σ` and `τ` take the same value, the
values compared as natural numbers. -/
def agreeCount (σ : Perm (Fin n)) (τ : Perm (Fin m)) : ℕ :=
  #{j : Fin (min n m) |
    (σ (j.castLE (min_le_left n m)) : ℕ) = τ (j.castLE (min_le_right n m))}

theorem agreeCount_def (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ τ = #{j : Fin (min n m) |
      (σ (j.castLE (min_le_left n m)) : ℕ) = τ (j.castLE (min_le_right n m))} := (rfl)

/-- The distance with errors between a permutation of degree `n` and one of degree `m`:
one minus the proportion, among the `max n m` points of the larger degree, of common indices
where the two permutations agree. -/
noncomputable def distErr (σ : Perm (Fin n)) (τ : Perm (Fin m)) : ℝ :=
  1 - (agreeCount σ τ : ℝ) / max n m

theorem distErr_def (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    distErr σ τ = 1 - (agreeCount σ τ : ℝ) / max n m := (rfl)

/-- Swapping the two permutations does not change the number of agreements. -/
theorem agreeCount_comm (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ τ = agreeCount τ σ := by
  refine card_equiv (finCongr (min_comm n m)) fun j => ?_
  have hj {k : ℕ} (h₁ : min m n ≤ k) (h₂ : min n m ≤ k) :
      (Fin.cast (min_comm n m) j).castLE h₁ = j.castLE h₂ := Fin.ext rfl
  simp [hj, eq_comm]

/-- The number of agreements is at most the smaller degree. -/
theorem agreeCount_le_min (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ τ ≤ min n m :=
  (card_filter_le _ _).trans (by simp)

/-- The identity permutations agree at every common index. -/
@[simp]
theorem agreeCount_one_one : agreeCount (1 : Perm (Fin n)) (1 : Perm (Fin m)) = min n m := by
  simp [agreeCount_def]

/-- In equal degree, the number of agreements is the number of points where the two permutations
take the same value. -/
theorem agreeCount_eq_card_eq (σ τ : Perm (Fin n)) :
    agreeCount σ τ = #{i : Fin n | σ i = τ i} := by
  refine card_equiv (finCongr (min_self n)) fun j => ?_
  have hj : j.castLE (min_le_left n n) = finCongr (min_self n) j := Fin.ext rfl
  simp [hj, Fin.val_inj]

/-- In equal degree, the agreements and the Hamming distance partition the points. -/
theorem agreeCount_add_hammingDist (σ τ : Perm (Fin n)) :
    agreeCount σ τ + hammingDist ⇑σ ⇑τ = n := by
  rw [agreeCount_eq_card_eq, hammingDist, card_filter_add_card_filter_not, card_univ,
    Fintype.card_fin]

/-- The distance with errors is symmetric. -/
theorem distErr_comm (σ : Perm (Fin n)) (τ : Perm (Fin m)) : distErr σ τ = distErr τ σ := by
  rw [distErr_def, distErr_def, agreeCount_comm, max_comm]

/-- The distance with errors is at least the proportion `1 - min n m / max n m` of points outside
the smaller degree. -/
theorem one_sub_min_div_max_le_distErr (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    1 - (min n m : ℝ) / max n m ≤ distErr σ τ := by
  rw [distErr_def]
  gcongr
  exact_mod_cast agreeCount_le_min σ τ

/-- The identity permutations of degrees `n` and `m` attain the lower bound
`one_sub_min_div_max_le_distErr`. -/
@[simp]
theorem distErr_one_one :
    distErr (1 : Perm (Fin n)) (1 : Perm (Fin m)) = 1 - (min n m : ℝ) / max n m := by
  simp [distErr_def]

/-- The distance with errors is nonnegative. -/
theorem distErr_nonneg (σ : Perm (Fin n)) (τ : Perm (Fin m)) : 0 ≤ distErr σ τ := by
  rw [distErr_def, sub_nonneg]
  refine div_le_one_of_le₀ ?_ (by positivity)
  exact_mod_cast (agreeCount_le_min σ τ).trans (min_le_max)

/-- The distance with errors is at most one. -/
theorem distErr_le_one (σ : Perm (Fin n)) (τ : Perm (Fin m)) : distErr σ τ ≤ 1 := by
  rw [distErr_def]
  linarith [show 0 ≤ (agreeCount σ τ : ℝ) / max n m by positivity]

/-- In equal degree `n ≠ 0`, the distance with errors is the normalized Hamming distance. Degree
`0` is excluded: there the two empty permutations have distance with errors `1`. -/
theorem distErr_eq_hammingDist_div [NeZero n] (σ τ : Perm (Fin n)) :
    distErr σ τ = (hammingDist ⇑σ ⇑τ : ℝ) / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h : (agreeCount σ τ : ℝ) + hammingDist ⇑σ ⇑τ = n := by
    exact_mod_cast agreeCount_add_hammingDist σ τ
  rw [distErr_def, max_self]
  field_simp
  linarith

/-- In equal degree `n ≠ 0`, the distance with errors is the moved-point norm of the quotient,
divided by the degree. -/
theorem distErr_eq_movedNorm_div [NeZero n] (σ τ : Perm (Fin n)) :
    distErr σ τ = movedNorm (Fin n) (σ⁻¹ * τ) / n := by
  rw [distErr_eq_hammingDist_div, hammingDist_eq_movedNorm]

/-- A permutation of positive degree has distance with errors `0` from itself. -/
@[simp]
theorem distErr_self [NeZero n] (σ : Perm (Fin n)) : distErr σ σ = 0 := by
  simp [distErr_eq_hammingDist_div]

end Equiv.Perm

end
