/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.Module
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The mean of a finite family of vectors

The mean `m = (card ι)⁻¹ • ∑ i, z i` of a finite family `z : ι → E` in a vector space over a field
`R` is its center of mass with equal weights, `Finset.univ.centerMass (fun _ ↦ 1) z`. Through total
inversion, the mean of the empty family is `0`. For a nonempty family this is the affine
`Finset.centroid`, which has no canonical value on the empty family. Mathlib's average
`Finset.expect` needs a `ℚ≥0`-module structure, which a vector space over a general field, such
as an inner product space over `ℝ` or `ℂ`, does not carry as an instance.

The mean is linear, invariant under reindexing, commutes with `star` and with multiplication by a
fixed element, and is monotone over an ordered field. It agrees with `Finset.expect` whenever the
latter is defined (`TauCeti.finiteMean_eq_expect`), and over `ℝ` or `ℂ` its norm is at most any
uniform bound on the norms of the family.

Over a field of characteristic zero, this file also records the identities of descriptive statistics
used for sample means and scatter operators: the sum of a family is its size times its mean, the
deviations `zᵢ - m` sum to zero, subtracting a constant `c` from a nonempty family subtracts it
from the mean, and appending a point `y` to a family of `n` points moves the mean by
`(n + 1)⁻¹ (y - m)`, including for `n = 0`.

## Main declarations

* `TauCeti.finiteMean`: the mean of a finite family.
* `TauCeti.finiteMean_of_isEmpty`: the mean of the empty family is `0`.
* `TauCeti.finiteMean_comp_equiv`, `TauCeti.finiteMean_comp_mul_left`: invariance under
  reindexing, and under translation on a finite group.
* `TauCeti.finiteMean_add`, `TauCeti.finiteMean_smul`, `TauCeti.finiteMean_sum`,
  `TauCeti.finiteMean_mul_const`, `TauCeti.finiteMean_const_mul`, `TauCeti.star_finiteMean`:
  linearity and compatibility with multiplication and `star`.
* `TauCeti.finiteMean_mono`, `TauCeti.finiteMean_nonneg`: monotonicity over an ordered field.
* `TauCeti.finiteMean_const`: the mean of a constant nonempty family is the constant.
* `TauCeti.finiteMean_eq_expect`: agreement with Mathlib's `𝔼`.
* `TauCeti.norm_finiteMean_le`: the norm of a mean is at most a uniform bound on the norms.
* `TauCeti.sum_eq_card_smul_finiteMean`: `∑ i, z i = card ι • m`.
* `TauCeti.sum_sub_finiteMean`: `∑ i, (z i - m) = 0`.
* `TauCeti.finiteMean_sub_const`: the mean of the deviations `zᵢ - c` is `m - c`.
* `TauCeti.finiteMean_snoc`: the mean after appending a point.
-/

public section

open Finset
open scoped BigOperators

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

/-- The mean of the empty family is `0`. -/
@[simp]
theorem finiteMean_of_isEmpty [IsEmpty ι] (z : ι → E) : finiteMean R z = 0 := by
  simp [finiteMean_eq_inv_smul_sum]

/-- Reindexing a family along an equivalence does not change its mean. -/
theorem finiteMean_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (z : ι → E) :
    finiteMean R (fun k ↦ z (e k)) = finiteMean R z := by
  rw [finiteMean_eq_inv_smul_sum, finiteMean_eq_inv_smul_sum, Fintype.card_congr e, e.sum_comp]

/-- The mean of a function on a finite group is invariant under left translation. -/
@[simp]
theorem finiteMean_comp_mul_left {G : Type*} [Group G] [Fintype G] (g : G) (z : G → E) :
    finiteMean R (fun h ↦ z (g * h)) = finiteMean R z :=
  finiteMean_comp_equiv (Equiv.mulLeft g) z

/-- The mean is additive. -/
@[simp]
theorem finiteMean_add (z w : ι → E) :
    finiteMean R (fun i ↦ z i + w i) = finiteMean R z + finiteMean R w := by
  simp only [finiteMean_eq_inv_smul_sum, sum_add_distrib, smul_add]

/-- The mean commutes with negation. -/
@[simp]
theorem finiteMean_neg (z : ι → E) : finiteMean R (fun i ↦ -z i) = -finiteMean R z := by
  simp only [finiteMean_eq_inv_smul_sum, sum_neg_distrib, smul_neg]

/-- The mean commutes with subtraction. -/
@[simp]
theorem finiteMean_sub (z w : ι → E) :
    finiteMean R (fun i ↦ z i - w i) = finiteMean R z - finiteMean R w := by
  simp only [finiteMean_eq_inv_smul_sum, sum_sub_distrib, smul_sub]

/-- The mean is homogeneous. -/
@[simp]
theorem finiteMean_smul (c : R) (z : ι → E) :
    finiteMean R (fun i ↦ c • z i) = c • finiteMean R z := by
  simp only [finiteMean_eq_inv_smul_sum, ← smul_sum, smul_comm c]

/-- The mean commutes with finite sums. -/
theorem finiteMean_sum {κ : Type*} (s : Finset κ) (z : κ → ι → E) :
    finiteMean R (fun i ↦ ∑ k ∈ s, z k i) = ∑ k ∈ s, finiteMean R (z k) := by
  simp only [finiteMean_eq_inv_smul_sum, smul_sum]
  exact sum_comm

/-- The mean commutes with `star`. -/
@[simp]
theorem star_finiteMean [Star R] [TrivialStar R] [StarAddMonoid E] [StarModule R E] (z : ι → E) :
    star (finiteMean R z) = finiteMean R fun i ↦ star (z i) := by
  simp only [finiteMean_eq_inv_smul_sum, star_smul, star_sum, star_trivial]

section Ring

variable {A : Type*} [NonUnitalNonAssocRing A] [Module R A]

/-- Right multiplication by a fixed element commutes with the mean. -/
theorem finiteMean_mul_const [IsScalarTower R A A] (z : ι → A) (a : A) :
    finiteMean R (fun i ↦ z i * a) = finiteMean R z * a := by
  simp only [finiteMean_eq_inv_smul_sum, smul_mul_assoc, sum_mul]

/-- Left multiplication by a fixed element commutes with the mean. -/
theorem finiteMean_const_mul [SMulCommClass R A A] (a : A) (z : ι → A) :
    finiteMean R (fun i ↦ a * z i) = a * finiteMean R z := by
  simp only [finiteMean_eq_inv_smul_sum, mul_smul_comm, mul_sum]

end Ring

section Order

variable [LinearOrder R] [IsStrictOrderedRing R] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono R E]

/-- The mean over an ordered field is monotone. -/
theorem finiteMean_mono {z w : ι → E} (h : ∀ i, z i ≤ w i) : finiteMean R z ≤ finiteMean R w := by
  rw [finiteMean_eq_inv_smul_sum, finiteMean_eq_inv_smul_sum]
  exact smul_le_smul_of_nonneg_left (sum_le_sum fun i _ ↦ h i) (by positivity)

/-- The mean of a nonnegative family over an ordered field is nonnegative. -/
theorem finiteMean_nonneg {z : ι → E} (h : ∀ i, 0 ≤ z i) : 0 ≤ finiteMean R z := by
  simpa [finiteMean_eq_inv_smul_sum] using finiteMean_mono (R := R) (z := fun _ ↦ 0) h

end Order

variable [CharZero R]

/-- The mean of a constant nonempty family is the constant. -/
@[simp]
theorem finiteMean_const [Nonempty ι] (a : E) : finiteMean R (fun _ : ι ↦ a) = a := by
  rw [finiteMean_eq_inv_smul_sum, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul R,
    inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- The mean is Mathlib's expectation `𝔼` whenever the latter is defined. -/
theorem finiteMean_eq_expect [Module ℚ≥0 E] (z : ι → E) : finiteMean R z = 𝔼 i, z i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · rw [finiteMean_eq_inv_smul_sum, ← Fintype.card_smul_expect, ← Nat.cast_smul_eq_nsmul R,
      inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

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

/-- Subtracting a constant from every member of a nonempty family subtracts it from the mean. -/
theorem finiteMean_sub_const [Nonempty ι] (z : ι → E) (c : E) :
    finiteMean R (fun i ↦ z i - c) = finiteMean R z - c := by
  simp [finiteMean_eq_inv_smul_sum, sum_sub_distrib, smul_sub, ← Nat.cast_smul_eq_nsmul R,
    smul_smul]

/-- **Appending a point.** Appending `y` to a family `z` of `n` points with mean `m` moves the
mean by `(n + 1)⁻¹ • (y - m)`. For `n = 0` this says that the mean of the single point `y` is
`y`. -/
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

section Norm

variable {𝕜 F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Nonempty ι]

/-- The norm of the mean of a nonempty family is at most any uniform bound on the norms of its
members. -/
theorem norm_finiteMean_le {z : ι → F} {r : ℝ} (h : ∀ i, ‖z i‖ ≤ r) : ‖finiteMean 𝕜 z‖ ≤ r := by
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  rw [finiteMean_eq_inv_smul_sum, norm_smul, norm_inv, RCLike.norm_natCast,
    inv_mul_le_iff₀ hcard]
  calc ‖∑ i, z i‖ ≤ ∑ i, ‖z i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, r := sum_le_sum fun i _ ↦ h i
    _ = Fintype.card ι * r := by simp

end Norm

end TauCeti
