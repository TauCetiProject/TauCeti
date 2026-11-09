/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.JInvariant
public import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Integrality of the level-two Siegel functions

The three level-two Siegel values `g₀`, `g₁`, `g₂` are integral over `ℤ[j(τ)]`.
More generally, if `j(τ)` is integral over a coefficient ring `R`, then each `gᵢ(τ)`
and each `2 / gᵢ(τ)` is integral over `R`. In particular, an algebraic-integer value
of `j` gives algebraic-integer Siegel values, and their inverses are integral away
from `2`. No complex multiplication hypothesis is needed for these implications.

We use Weber's cubic `(g¹² + 16)³ = j g¹²`. For `y = 2 / g`, its reciprocal
form is `(y¹² + 256)³ = j y²⁴`. Both are monic equations whose coefficients
are integral whenever `j` is integral. These equations also hold in the ring of
functions on the upper half-plane, so the integrality assertions apply to the
functions themselves, not only to their values.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §12 (Weber functions).
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5.
-/

public section

open UpperHalfPlane

namespace TauCeti.ModularForm

private theorem isIntegral_of_weber_eq {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {z g : A} (hz : IsIntegral R z)
    (hg : (g ^ 12 + 16) ^ 3 = z * g ^ 12) : IsIntegral R g :=
  isIntegral_of_pow_add_pow_eq_mul_pow hz (isIntegral_natCast 16) (n := 12) (m := 3)
    (k := 1) (by decide) (by decide) (by simpa only [pow_one, Nat.cast_ofNat] using hg)

private theorem isIntegral_of_reciprocal_weber_eq {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {z y : A} (hz : IsIntegral R z)
    (hy : (y ^ 12 + 256) ^ 3 = z * y ^ 24) : IsIntegral R y :=
  isIntegral_of_pow_add_pow_eq_mul_pow hz (isIntegral_natCast 256) (n := 12) (m := 3)
    (k := 2) (by decide) (by decide) (by simpa only [← pow_mul, Nat.cast_ofNat] using hy)

private theorem reciprocal_weber_eq {z g : ℂ}
    (hg : (g ^ 12 + 16) ^ 3 = z * g ^ 12) :
    ((2 / g) ^ 12 + 256) ^ 3 = z * (2 / g) ^ 24 := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    norm_num at hg
  -- Clearing denominators gives `2^24` times the original Weber relation.
  field_simp [hg0]
  linear_combination 16777216 * hg

/-! ### The functions, over any ring over which `j` is integral -/

section Functions

variable {R : Type*} [CommRing R] [Algebra R (ℍ → ℂ)]

/-- The level-two Siegel function `g₀` is integral over any coefficient ring over which `j`
is integral. Take `R = Algebra.adjoin ℤ {j}` for integrality over `ℤ[j]`. -/
theorem isIntegral_siegelFunction_zero_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction ![0, 1 / 2] τ) := by
  apply isIntegral_of_weber_eq hj
  funext τ
  exact siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three τ

/-- The level-two Siegel function `g₁` is integral over any coefficient ring over which `j`
is integral. -/
theorem isIntegral_siegelFunction_half_zero (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction ![1 / 2, 0] τ) := by
  apply isIntegral_of_weber_eq hj
  funext τ
  exact siegelFunction_half_zero_pow_twelve_add_sixteen_pow_three τ

/-- The level-two Siegel function `g₂` is integral over any coefficient ring over which `j`
is integral. -/
theorem isIntegral_siegelFunction_half_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction ![1 / 2, 1 / 2] τ) := by
  apply isIntegral_of_weber_eq hj
  funext τ
  exact siegelFunction_half_half_pow_twelve_add_sixteen_pow_three τ

/-- Twice the inverse of `g₀` is integral over any coefficient ring over which `j` is integral. -/
theorem isIntegral_two_div_siegelFunction_zero_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ 2 / siegelFunction ![0, 1 / 2] τ) := by
  apply isIntegral_of_reciprocal_weber_eq hj
  funext τ
  exact reciprocal_weber_eq (siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three τ)

/-- Twice the inverse of `g₁` is integral over any coefficient ring over which `j` is integral. -/
theorem isIntegral_two_div_siegelFunction_half_zero (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ 2 / siegelFunction ![1 / 2, 0] τ) := by
  apply isIntegral_of_reciprocal_weber_eq hj
  funext τ
  exact reciprocal_weber_eq (siegelFunction_half_zero_pow_twelve_add_sixteen_pow_three τ)

/-- Twice the inverse of `g₂` is integral over any coefficient ring over which `j` is integral. -/
theorem isIntegral_two_div_siegelFunction_half_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ 2 / siegelFunction ![1 / 2, 1 / 2] τ) := by
  apply isIntegral_of_reciprocal_weber_eq hj
  funext τ
  exact reciprocal_weber_eq (siegelFunction_half_half_pow_twelve_add_sixteen_pow_three τ)

end Functions

/-! ### Algebraic-integer values -/

section Values

variable {R : Type*} [CommRing R] [Algebra R ℂ] (τ : ℍ)

/-- If `j(τ)` is integral over `R`, so is `g₀(τ)`. In particular this applies with `R = ℤ`. -/
theorem isIntegral_siegelFunction_zero_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction ![0, 1 / 2] τ) :=
  isIntegral_of_weber_eq hj (siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three τ)

/-- If `j(τ)` is integral over `R`, so is `g₁(τ)`. -/
theorem isIntegral_siegelFunction_half_zero_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction ![1 / 2, 0] τ) :=
  isIntegral_of_weber_eq hj (siegelFunction_half_zero_pow_twelve_add_sixteen_pow_three τ)

/-- If `j(τ)` is integral over `R`, so is `g₂(τ)`. -/
theorem isIntegral_siegelFunction_half_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction ![1 / 2, 1 / 2] τ) :=
  isIntegral_of_weber_eq hj (siegelFunction_half_half_pow_twelve_add_sixteen_pow_three τ)

/-- If `j(τ)` is integral over `R`, so is `2 / g₀(τ)`. -/
theorem isIntegral_two_div_siegelFunction_zero_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (2 / siegelFunction ![0, 1 / 2] τ) :=
  isIntegral_of_reciprocal_weber_eq hj
    (reciprocal_weber_eq (siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three τ))

/-- If `j(τ)` is integral over `R`, so is `2 / g₁(τ)`. -/
theorem isIntegral_two_div_siegelFunction_half_zero_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (2 / siegelFunction ![1 / 2, 0] τ) :=
  isIntegral_of_reciprocal_weber_eq hj
    (reciprocal_weber_eq (siegelFunction_half_zero_pow_twelve_add_sixteen_pow_three τ))

/-- If `j(τ)` is integral over `R`, so is `2 / g₂(τ)`. -/
theorem isIntegral_two_div_siegelFunction_half_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (2 / siegelFunction ![1 / 2, 1 / 2] τ) :=
  isIntegral_of_reciprocal_weber_eq hj
    (reciprocal_weber_eq (siegelFunction_half_half_pow_twelve_add_sixteen_pow_three τ))

end Values

end TauCeti.ModularForm
