/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.GammaTwo
public import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic
import TauCeti.NumberTheory.ModularForms.LevelOne.ModularPolynomial

/-!
# Integrality of the level-two Siegel functions and `γ₂`

The three level-two Siegel values `g₀`, `g₁`, `g₂` and the cube root `γ₂` of `j` are integral over
`ℤ[j(τ)]`. More generally, if `j(τ)` is integral over a coefficient ring `R`, then each `gᵢ(τ)`,
each `2 / gᵢ(τ)`, and `γ₂(τ)` are integral over `R`. Combined with the integrality of `j(τ)` at
imaginary quadratic points (`TauCeti.ModularForm.isIntegral_j_of_quadratic`), it follows that at
every imaginary quadratic point `τ ∈ ℍ` the values `g₀(τ)`, `g₁(τ)`, `g₂(τ)`, `2 / g₀(τ)`,
`2 / g₁(τ)`, `2 / g₂(τ)`, and `γ₂(τ)` are algebraic integers.

We use Weber's cubic `(g¹² + 16)³ = j g¹²` and the relation `γ₂³ = j`. For `y = 2 / g`, the
reciprocal form of Weber's cubic is `(y¹² + 256)³ = j y²⁴`. All of these are monic equations whose
coefficients are integral whenever `j` is integral, and they hold in the ring of functions on the
upper half-plane as well as pointwise.

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

/-- The cube root `γ₂` of `j` is integral over any coefficient ring over which `j` is integral. -/
theorem isIntegral_gammaTwo (hj : IsIntegral R j) : IsIntegral R gammaTwo := by
  have h : gammaTwo ^ 3 = j := funext gammaTwo_pow_three
  exact .of_pow (n := 3) (by decide) (h.symm ▸ hj)

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

/-- If `j(τ)` is integral over `R`, so is `γ₂(τ)`. -/
theorem isIntegral_gammaTwo_apply (hj : IsIntegral R (j τ)) : IsIntegral R (gammaTwo τ) :=
  .of_pow (n := 3) (by decide) ((gammaTwo_pow_three τ).symm ▸ hj)

end Values

/-! ### Values at imaginary quadratic points -/

section Quadratic

variable {τ : ℍ} {a b c : ℤ}

/-- At any imaginary quadratic point `τ ∈ ℍ`, the level-two Siegel value `g₀(τ)` is an algebraic
integer. -/
theorem isIntegral_siegelFunction_zero_half_of_quadratic (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    IsIntegral ℤ (siegelFunction ![0, 1 / 2] τ) :=
  isIntegral_siegelFunction_zero_half_apply τ (isIntegral_j_of_quadratic ha hτ)

/-- At any imaginary quadratic point `τ ∈ ℍ`, the level-two Siegel value `g₁(τ)` is an algebraic
integer. -/
theorem isIntegral_siegelFunction_half_zero_of_quadratic (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    IsIntegral ℤ (siegelFunction ![1 / 2, 0] τ) :=
  isIntegral_siegelFunction_half_zero_apply τ (isIntegral_j_of_quadratic ha hτ)

/-- At any imaginary quadratic point `τ ∈ ℍ`, the level-two Siegel value `g₂(τ)` is an algebraic
integer. -/
theorem isIntegral_siegelFunction_half_half_of_quadratic (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    IsIntegral ℤ (siegelFunction ![1 / 2, 1 / 2] τ) :=
  isIntegral_siegelFunction_half_half_apply τ (isIntegral_j_of_quadratic ha hτ)

/-- At any imaginary quadratic point `τ ∈ ℍ`, `2 / g₀(τ)` is an algebraic integer. -/
theorem isIntegral_two_div_siegelFunction_zero_half_of_quadratic (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    IsIntegral ℤ (2 / siegelFunction ![0, 1 / 2] τ) :=
  isIntegral_two_div_siegelFunction_zero_half_apply τ (isIntegral_j_of_quadratic ha hτ)

/-- At any imaginary quadratic point `τ ∈ ℍ`, `2 / g₁(τ)` is an algebraic integer. -/
theorem isIntegral_two_div_siegelFunction_half_zero_of_quadratic (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    IsIntegral ℤ (2 / siegelFunction ![1 / 2, 0] τ) :=
  isIntegral_two_div_siegelFunction_half_zero_apply τ (isIntegral_j_of_quadratic ha hτ)

/-- At any imaginary quadratic point `τ ∈ ℍ`, `2 / g₂(τ)` is an algebraic integer. -/
theorem isIntegral_two_div_siegelFunction_half_half_of_quadratic (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    IsIntegral ℤ (2 / siegelFunction ![1 / 2, 1 / 2] τ) :=
  isIntegral_two_div_siegelFunction_half_half_apply τ (isIntegral_j_of_quadratic ha hτ)

/-- At any imaginary quadratic point `τ ∈ ℍ`, the cube root `γ₂(τ)` of `j(τ)` is an algebraic
integer. -/
theorem isIntegral_gammaTwo_of_quadratic (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    IsIntegral ℤ (gammaTwo τ) :=
  isIntegral_gammaTwo_apply τ (isIntegral_j_of_quadratic ha hτ)

end Quadratic

end TauCeti.ModularForm
