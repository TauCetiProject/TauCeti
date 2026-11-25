/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
import TauCeti.NumberTheory.LocalField.Different.Tower

/-!
# The normalized different of a local extension

For a finite separable extension of nonarchimedean local fields `L/K`, the normalized different
is `d(L/K) / e(L/K)`. This measures the different using the valuation on `L` that restricts to
the integral normalization on `K`. It also equals the discriminant exponent divided by the
extension degree. For a completion of a Galois number field above `p`, this is the contribution
of `p` to the root discriminant, expressed as an exponent of `p`.

The definition does not require `L/K` to be Galois. In a tower it increases by the different
exponent of the upper step divided by the ramification index of the entire tower. In particular,
it is unchanged by adjoining an unramified extension to the top field.

## References

* J. W. Jones, *Wild ramification bounds and simple group Galois extensions ramified only at 2*,
  §1.1, equation (1), and §3.1.
* J.-P. Serre, *Local Fields*, Chapter III, §§4 and 6, for the tower law and the tame different.
-/

public section
noncomputable section

namespace TauCeti

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

section TwoFields

variable [Algebra.IsSeparable K L]

/-- The normalized different of a finite separable extension of nonarchimedean local fields.
It is defined as the discriminant exponent divided by the degree, and equals the different
exponent divided by the ramification index. -/
def localRootDiscrExp : ℚ :=
  (discriminantExponent K L : ℚ) / Module.finrank K L

/-- The defining formula for the normalized different. -/
theorem localRootDiscrExp_def :
    localRootDiscrExp K L = (discriminantExponent K L : ℚ) / Module.finrank K L := (rfl)

/-- The normalized different is the different exponent divided by the ramification index. -/
theorem localRootDiscrExp_eq_differentExponent_div_ramificationIndex :
    localRootDiscrExp K L = (differentExponent K L : ℚ) / ramificationIndex K L := by
  rw [localRootDiscrExp_def,
    discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    ← ramificationIndex_mul_inertiaDegree K L, Nat.cast_mul, Nat.cast_mul,
    mul_comm (ramificationIndex K L : ℚ),
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (inertiaDegree_pos (K := K) (L := L)).ne')]

/-- The normalized different is nonnegative. -/
theorem localRootDiscrExp_nonneg : 0 ≤ localRootDiscrExp K L := by
  rw [localRootDiscrExp_def]
  positivity

/-- The normalized different vanishes exactly for unramified extensions. -/
@[simp]
theorem localRootDiscrExp_eq_zero_iff : localRootDiscrExp K L = 0 ↔ IsUnramified K L := by
  simp [localRootDiscrExp_eq_differentExponent_div_ramificationIndex, div_eq_zero_iff,
    (ramificationIndex_pos (K := K) (L := L)).ne']

/-- The normalized different has the value `1 - 1/e` exactly for tamely ramified extensions. -/
@[simp]
theorem localRootDiscrExp_eq_one_sub_inv_iff :
    localRootDiscrExp K L = 1 - (ramificationIndex K L : ℚ)⁻¹ ↔ IsTamelyRamified K L := by
  have he : 1 ≤ ramificationIndex K L := ramificationIndex_pos
  have he₀ : (ramificationIndex K L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt he)
  have ht : ((ramificationIndex K L - 1 : ℕ) : ℚ) / ramificationIndex K L =
      1 - (ramificationIndex K L : ℚ)⁻¹ := by
    rw [Nat.cast_sub he, Nat.cast_one, sub_div, div_self he₀, one_div]
  rw [localRootDiscrExp_eq_differentExponent_div_ramificationIndex, ← ht,
    div_left_inj₀ he₀, Nat.cast_inj,
    differentExponent_eq_ramificationIndex_sub_one_iff]

/-- The normalized different is strictly less than one exactly for tamely ramified extensions. -/
@[simp]
theorem localRootDiscrExp_lt_one_iff : localRootDiscrExp K L < 1 ↔ IsTamelyRamified K L := by
  have he : 0 < (ramificationIndex K L : ℚ) := Nat.cast_pos.mpr ramificationIndex_pos
  rw [localRootDiscrExp_eq_differentExponent_div_ramificationIndex, div_lt_one he,
    Nat.cast_lt, ← not_le,
    ramificationIndex_le_differentExponent_iff, not_isWildlyRamified_iff]

/-- The normalized different is invariant under base-field algebra equivalences of local
extensions with compatible valuations. -/
theorem localRootDiscrExp_eq_of_algEquiv (M : Type*) [Field M] [ValuativeRel M]
    [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M]
    (e : L ≃ₐ[K] M) :
    letI : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
    localRootDiscrExp K L = localRootDiscrExp K M := by
  have := finite_of_valuativeExtension K L
  have := finite_of_valuativeExtension K M
  simp only [localRootDiscrExp_eq_differentExponent_div_ramificationIndex,
    differentExponent_eq_of_algEquiv K L M e,
    ramificationIndex_eq_of_algEquiv K L M e]

end TwoFields

section Tower

variable (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension L M] [Algebra.IsSeparable K M]

/-- In a tower `M/L/K`, the normalized different of `M/K` is the normalized different of
`L/K` plus `d(M/L) / e(M/K)`. Both summands use the integral normalization on `K`. -/
theorem localRootDiscrExp_tower :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    letI : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
    localRootDiscrExp K M = localRootDiscrExp K L +
      (differentExponent L M : ℚ) / ramificationIndex K M := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  have he : (ramificationIndex L M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ramificationIndex_pos.ne'
  simp only [localRootDiscrExp_eq_differentExponent_div_ramificationIndex,
    differentExponent_tower K L M,
    ramificationIndex_tower (K := K) (L := L) M, Nat.cast_add, Nat.cast_mul, add_div]
  rw [mul_comm (ramificationIndex K L : ℚ), mul_div_mul_left _ _ he, add_comm]

/-- The normalized different over a fixed base is nondecreasing in towers. -/
theorem localRootDiscrExp_le_of_tower :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    letI : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
    localRootDiscrExp K L ≤ localRootDiscrExp K M := by
  rw [localRootDiscrExp_tower K L M]
  exact le_add_of_nonneg_right (by positivity)

/-- Extending the top field leaves the normalized different over the base unchanged exactly
when the new step is unramified. -/
@[simp]
theorem localRootDiscrExp_eq_of_tower_iff :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    letI : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
    localRootDiscrExp K M = localRootDiscrExp K L ↔ IsUnramified L M := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  have : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  rw [localRootDiscrExp_tower K L M]
  simp [div_eq_zero_iff, (ramificationIndex_pos (K := K) (L := M)).ne']

end Tower

end TauCeti
