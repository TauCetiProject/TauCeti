/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The mean of a finite family of vectors

The mean `z̄ = (card ι)⁻¹ • ∑ i, z i` of a finite family `z : ι → E` in a vector space over a field
`R` is its center of mass with equal weights, `Finset.univ.centerMass (fun _ ↦ 1) z`. Through total
inversion, the mean of the empty family is `0`. For a nonempty family this is the affine
`Finset.centroid`, which has no canonical value on the empty family. Mathlib's average
`Finset.expect` needs a `ℚ≥0`-module structure, which a vector space over a general field, such
as an inner product space over `ℝ` or `ℂ`, does not carry as an instance.

Over a field of characteristic zero, this file records the identities of descriptive statistics
used for sample means and scatter operators: the sum of a family is its size times its mean, the
deviations `zᵢ - z̄` sum to zero, and appending a point `y` to a family of `n` points moves the
mean by `(n + 1)⁻¹ (y - z̄)`, including for `n = 0`.

## Main declarations

* `TauCeti.finiteMean`: the mean of a finite family.
* `TauCeti.sum_eq_card_smul_finiteMean`: `∑ i, z i = card ι • z̄`.
* `TauCeti.sum_sub_finiteMean`: `∑ i, (z i - z̄) = 0`.
* `TauCeti.finiteMean_snoc`: the mean after appending a point.
-/

public section

open Finset

namespace TauCeti

variable {R E ι : Type*} [Field R] [AddCommGroup E] [Module R E] [Fintype ι]

variable (R) in
/-- The mean `(card ι)⁻¹ • ∑ i, z i` of a finite family `z` of vectors: its center of mass with
equal weights. The mean of the empty family is `0`. -/
noncomputable def finiteMean (z : ι → E) : E :=
  univ.centerMass (fun _ ↦ (1 : R)) z

theorem finiteMean_def (z : ι → E) : finiteMean R z = univ.centerMass (fun _ ↦ (1 : R)) z :=
  (rfl)

theorem finiteMean_eq_inv_smul_sum (z : ι → E) :
    finiteMean R z = (Fintype.card ι : R)⁻¹ • ∑ i, z i := by
  simp [finiteMean_def, centerMass]

variable [CharZero R]

/-- The sum of a finite family is its size times its mean. -/
theorem sum_eq_card_smul_finiteMean (z : ι → E) :
    ∑ i, z i = (Fintype.card ι : R) • finiteMean R z := by
  rw [finiteMean_eq_inv_smul_sum, smul_smul]
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

/-- The deviations of a finite family from its mean sum to zero. -/
theorem sum_sub_finiteMean (z : ι → E) : ∑ i, (z i - finiteMean R z) = 0 := by
  rw [sum_sub_distrib, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul R,
    ← sum_eq_card_smul_finiteMean, sub_self]

/-- **Appending a point.** Appending `y` to a family `z` of `n` points moves its mean by
`(n + 1)⁻¹ • (y - z̄)`. For `n = 0` this says that the mean of the single point `y` is `y`. -/
theorem finiteMean_snoc {n : ℕ} (z : Fin n → E) (y : E) :
    finiteMean R (Fin.snoc z y : Fin (n + 1) → E) =
      finiteMean R z + ((n : R) + 1)⁻¹ • (y - finiteMean R z) := by
  have hn : (n : R) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [finiteMean_eq_inv_smul_sum, Fintype.card_fin, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [sum_eq_card_smul_finiteMean (R := R), Fintype.card_fin]
  push_cast
  have h : ((n : R) + 1)⁻¹ * ((n : R) + 1) = 1 := inv_mul_cancel₀ hn
  linear_combination (norm := module) h • finiteMean R z

end TauCeti
