/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
public import TauCeti.FieldTheory.FunctionField.Differential.Comparison
-- Proof-only: `F(x)⟮y⟯ = F(W)`, the generation hypothesis of the different bound.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GeneratedByY
-- Proof-only: the bound of the different exponent by the derivative of an equation.
import TauCeti.FieldTheory.FunctionField.Different.Derivative

/-!
# The divisor of the invariant differential

Let `W` be an elliptic Weierstrass curve over a field `F`, with function field `F(W)` and
coordinate functions `x` and `y`. Its invariant differential `ω = dx / (2y + a₁x + a₃)` lives in
the Kähler differentials `Ω[F(W)/F]`, and the Kähler–Weil comparison determined by the separating
element `x` carries it to a nonzero Weil differential of `F(W) / F`. This file proves that this
Weil differential has **divisor zero**: `ω` is regular and nonvanishing at every place of `F(W)`
(Silverman, Proposition III.1.5).

The divisor of `dx` is `-2 (x)_∞ + Diff(F(W) / F(x))`, so

`(ω) = -div (2y + a₁x + a₃) - 2 (x)_∞ + Diff(F(W) / F(x))`.

No different exponent has to be computed exactly. At a place `P` where `x` is regular, `y` is a
root of `Y² + (a₁x + a₃) Y - (x³ + a₂x² + a₄x + a₆)`, a monic equation over the valuation ring
below `P` whose derivative at `y` is `2y + a₁x + a₃`; at a pole of `x`, the function `y / x²` is a
root of the monic equation obtained by dividing by `x⁴`, whose coefficients are polynomials in
`1 / x`, and whose derivative at `y / x²` is `(2y + a₁x + a₃) / x²`. Bounding the different
exponent by the order of these derivatives shows that every coefficient of `(ω)` is at most zero.
Since `(ω)` has degree `2g - 2 = 0`, it is zero.

## Main results

All in the namespace `WeierstrassCurve.Affine`:

* `kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential`: the Kähler–Weil
  comparison sends `ω` to `(2y + a₁x + a₃)⁻¹ · dx`.
* `weilDifferentialDivisor_invariantDifferential`: **the invariant differential has divisor
  zero.**

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Proposition III.1.5.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.5.10 and Remark 4.3.7.
-/

public section

open Polynomial TauCeti AlgebraicGeometry

open scoped IntermediateField

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-! ### The local bound -/

section Local

/-- The rational function field acts on `F(W)` through `x`, compatibly with `F[X]`. -/
private theorem isScalarTower_polynomial_ratFunc :
    letI := ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    IsScalarTower F[X] (RatFunc F) W.FunctionField := by
  let _ := ratFuncAlgebraOfTranscendental (transcendental_genericX W)
  refine .of_algebraMap_eq fun p ↦ ?_
  rw [algebraMap_ratFuncAlgebraOfTranscendental_apply, RatFunc.algEquivOfTranscendental_algebraMap,
    algebraMap_eq_aeval_genericX]
  simp

/-- The Weierstrass equation at the generic point, written out in `F(W)`. -/
private theorem genericY_sq_add_eq :
    genericY W ^ 2 + algebraMap F W.FunctionField W.a₁ * genericX W * genericY W +
        algebraMap F W.FunctionField W.a₃ * genericY W =
      genericX W ^ 3 + algebraMap F W.FunctionField W.a₂ * genericX W ^ 2 +
        algebraMap F W.FunctionField W.a₄ * genericX W + algebraMap F W.FunctionField W.a₆ := by
  have h := (equation_iff _ _).mp (equation_genericX_genericY W)
  simpa [WeierstrassCurve.baseChange] using h

variable [W.IsElliptic]

/-- **The local bound behind `(ω) = 0`**: at every place `P` of `F(W)`, the different exponent of
`F(W) / F(x)` is at most `ord_P (2y + a₁x + a₃) + 2 max(-ord_P x, 0)`. -/
private theorem differentExponent_le (P : Place F W.FunctionField) :
    letI := ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    letI := isScalarTower_ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    letI := isFunctionField_iff_functionField.mp W.isFunctionField
    letI := isSeparable_ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    (Place.differentExponent F (RatFunc F) P : ℤ) ≤
      P.ord (invariantDifferentialDenom W) + 2 * (-P.ord (genericX W) ⊔ 0) := by
  let hx := transcendental_genericX W
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp W.isFunctionField
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_polynomial_ratFunc W
  have heq := genericY_sq_add_eq W
  set x := genericX W
  set y := genericY W
  have hX : algebraMap (RatFunc F) W.FunctionField RatFunc.X = x :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hx
  have hC (c : F) : algebraMap (RatFunc F) W.FunctionField (algebraMap F (RatFunc F) c) =
      algebraMap F W.FunctionField c :=
    (IsScalarTower.algebraMap_apply F (RatFunc F) W.FunctionField c).symm
  have hc (c : F) : algebraMap F W.FunctionField c ∈ P.integers := P.algebraMap_mem_integers c
  have hden : invariantDifferentialDenom W =
      2 * y + algebraMap F W.FunctionField W.a₁ * x + algebraMap F W.FunctionField W.a₃ :=
    invariantDifferentialDenom_def W
  -- `omega` treats `genericX W` and its abbreviation `x` as distinct atoms.
  have hxx : P.ord (genericX W) = P.ord x := rfl
  rcases le_or_gt 0 (P.ord x) with hxP | hxP
  · -- `x` is regular at `P`: use the Weierstrass equation for `y` itself.
    have hxi : x ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr hxP
    have hu : 2 * y + algebraMap (RatFunc F) W.FunctionField
        (algebraMap F (RatFunc F) W.a₁ * RatFunc.X + algebraMap F (RatFunc F) W.a₃) =
        invariantDifferentialDenom W := by
      simp only [map_add, map_mul, hX, hC, hden]
      ring
    have h := Place.differentExponent_le_ord_two_mul_add F (RatFunc F) (P' := P)
      (u := algebraMap F (RatFunc F) W.a₁ * RatFunc.X + algebraMap F (RatFunc F) W.a₃)
      (v := RatFunc.X ^ 3 + algebraMap F (RatFunc F) W.a₂ * RatFunc.X ^ 2 +
        algebraMap F (RatFunc F) W.a₄ * RatFunc.X + algebraMap F (RatFunc F) W.a₆) (z := y)
      (by simp only [map_add, map_mul, hX, hC]; exact add_mem (mul_mem (hc _) hxi) (hc _))
      (by
        simp only [map_add, map_mul, map_pow, hX, hC]
        exact add_mem (add_mem (add_mem (pow_mem hxi _) (mul_mem (hc _) (pow_mem hxi _)))
          (mul_mem (hc _) hxi)) (hc _))
      (adjoin_genericY_eq_top W (RatFunc F))
      (by simp only [map_add, map_mul, map_pow, hX, hC]; linear_combination heq)
      (by rw [hu]; exact invariantDifferentialDenom_ne_zero W)
    rw [hu] at h
    omega
  · -- `x` has a pole at `P`: use the equation for `y / x²`, with coefficients in `F[1 / x]`.
    have hx0 : x ≠ 0 := hx.ne_zero
    have hti : x⁻¹ ∈ P.integers := by
      rw [P.mem_integers_iff_ord_nonneg, P.ord_inv]
      omega
    have hgen : (RatFunc F)⟮y * x⁻¹ ^ 2⟯ = ⊤ := by
      refine top_le_iff.mp ((adjoin_genericY_eq_top W (RatFunc F)).symm.le.trans ?_)
      rw [IntermediateField.adjoin_simple_le_iff]
      have hy : y = algebraMap (RatFunc F) W.FunctionField (RatFunc.X ^ 2) * (y * x⁻¹ ^ 2) := by
        rw [map_pow, hX]
        field_simp
      have hmem := mul_mem
        (IntermediateField.algebraMap_mem (RatFunc F)⟮y * x⁻¹ ^ 2⟯ (RatFunc.X ^ 2))
        (IntermediateField.mem_adjoin_simple_self (RatFunc F) (y * x⁻¹ ^ 2))
      rwa [← hy] at hmem
    have hu : 2 * (y * x⁻¹ ^ 2) + algebraMap (RatFunc F) W.FunctionField
        (algebraMap F (RatFunc F) W.a₁ * RatFunc.X⁻¹ +
          algebraMap F (RatFunc F) W.a₃ * RatFunc.X⁻¹ ^ 2) =
        invariantDifferentialDenom W * (x ^ 2)⁻¹ := by
      simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC, hden]
      field_simp
      ring
    have hx2 : (x ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hx0)
    have h := Place.differentExponent_le_ord_two_mul_add F (RatFunc F) (P' := P)
      (u := algebraMap F (RatFunc F) W.a₁ * RatFunc.X⁻¹ +
        algebraMap F (RatFunc F) W.a₃ * RatFunc.X⁻¹ ^ 2)
      (v := RatFunc.X⁻¹ + algebraMap F (RatFunc F) W.a₂ * RatFunc.X⁻¹ ^ 2 +
        algebraMap F (RatFunc F) W.a₄ * RatFunc.X⁻¹ ^ 3 +
        algebraMap F (RatFunc F) W.a₆ * RatFunc.X⁻¹ ^ 4) (z := y * x⁻¹ ^ 2)
      (by
        simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC]
        exact add_mem (mul_mem (hc _) hti) (mul_mem (hc _) (pow_mem hti _)))
      (by
        simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC]
        exact add_mem (add_mem (add_mem hti (mul_mem (hc _) (pow_mem hti _)))
          (mul_mem (hc _) (pow_mem hti _))) (mul_mem (hc _) (pow_mem hti _)))
      hgen
      (by
        simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC]
        field_simp
        linear_combination heq)
      (by rw [hu]; exact mul_ne_zero (invariantDifferentialDenom_ne_zero W) hx2)
    rw [hu, P.ord_mul (invariantDifferentialDenom_ne_zero W) hx2, P.ord_inv, P.ord_pow] at h
    push_cast at h
    omega

end Local

/-! ### The divisor of the invariant differential -/

section Divisor

variable [W.IsElliptic]

/-- **The invariant differential as a Weil differential**: the Kähler–Weil comparison determined
by the separating element `x` sends `ω = dx / (2y + a₁x + a₃)` to `(2y + a₁x + a₃)⁻¹ · dx`. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential :
    letI := weilDifferentialSpaceModule W.isFunctionField
    kaehlerDifferentialEquivWeilDifferentialOfSeparating W.isFunctionField
        (isIntegrallyClosedIn_functionField W) (transcendental_genericX W)
        (invariantDifferential W) =
      (invariantDifferentialDenom W)⁻¹ •
        weilDifferentialOfSeparating W.isFunctionField (transcendental_genericX W) := by
  let _ := weilDifferentialSpaceModule W.isFunctionField
  rw [invariantDifferential_def, map_smul,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self]

/-- The Weil differential attached to the invariant differential is nonzero. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential_ne_zero :
    letI := weilDifferentialSpaceModule W.isFunctionField
    ((kaehlerDifferentialEquivWeilDifferentialOfSeparating W.isFunctionField
        (isIntegrallyClosedIn_functionField W) (transcendental_genericX W)
        (invariantDifferential W) : ↥(weilDifferentialSpace F W.FunctionField)) :
          Module.Dual F ↥(repartitionSpace F W.FunctionField)) ≠ 0 := by
  let _ := weilDifferentialSpaceModule W.isFunctionField
  rw [ne_eq, ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff]
  exact invariantDifferential_ne_zero W

/-- **The invariant differential has divisor zero** (Silverman, Proposition III.1.5): under the
Kähler–Weil comparison determined by `x`, the invariant differential `ω = dx / (2y + a₁x + a₃)`
of an elliptic curve is a Weil differential of `F(W) / F` with neither zeros nor poles. -/
@[simp]
theorem weilDifferentialDivisor_invariantDifferential :
    letI := weilDifferentialSpaceModule W.isFunctionField
    weilDifferentialDivisor W.isFunctionField (isIntegrallyClosedIn_functionField W)
        (kaehlerDifferentialEquivWeilDifferentialOfSeparating W.isFunctionField
          (isIntegrallyClosedIn_functionField W) (transcendental_genericX W)
          (invariantDifferential W)).2
        (kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential_ne_zero W) =
      0 := by
  let _ := weilDifferentialSpaceModule W.isFunctionField
  let hF := W.isFunctionField
  let hex := isIntegrallyClosedIn_functionField W
  let hx := transcendental_genericX W
  -- `(ω) = -div (2y + a₁x + a₃) + (dx)`, by the transformation law of Weil divisors.
  let z : W.FunctionFieldˣ := Units.mk0 (invariantDifferentialDenom W)⁻¹
    (inv_ne_zero (invariantDifferentialDenom_ne_zero W))
  have hD := weilDifferentialDivisor_repartitionDualMul hF hex
    (weilDifferentialOfSeparating hF hx).2
    (by simpa using weilDifferentialOfSeparating_ne_zero hF hx) z
  rw [weilDifferentialDivisor_weilDifferentialOfSeparating] at hD
  have hω : ((kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx
      (invariantDifferential W) : ↥(weilDifferentialSpace F W.FunctionField)) :
        Module.Dual F ↥(repartitionSpace F W.FunctionField)) =
      repartitionDualMul hF (z : W.FunctionField) (weilDifferentialOfSeparating hF hx) := by
    rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential,
      coe_weilDifferentialSpaceModule_smul, Units.val_mk0]
  -- `(ω)` has degree `2g - 2 = 0`, so it suffices to show that `(ω) ≤ 0`.
  refine Divisor.eq_of_le_of_degree_eq hF ?_ ?_
  · -- The divisor depends only on the differential, not on the proofs it carries.
    have hcongr {ω₁ ω₂ : Module.Dual F ↥(repartitionSpace F W.FunctionField)} (h : ω₁ = ω₂)
        {hm₁ : ω₁ ∈ weilDifferentialSpace F W.FunctionField} {hn₁ : ω₁ ≠ 0}
        {hm₂ : ω₂ ∈ weilDifferentialSpace F W.FunctionField} {hn₂ : ω₂ ≠ 0} :
        weilDifferentialDivisor hF hex hm₁ hn₁ = weilDifferentialDivisor hF hex hm₂ hn₂ := by
      subst h
      rfl
    rw [(hcongr hω).trans hD, WeilDivisor.le_iff]
    intro P
    have h := differentExponent_le W P
    simp only [WeilDivisor.coeff_add, WeilDivisor.coeff_zsmul, Divisor.coeff_principal,
      Divisor.coeff_poles, Divisor.coeff_different, WeilDivisor.coeff_zero, z, Units.val_mk0,
      P.ord_inv]
    omega
  · rw [degree_weilDifferentialDivisor, genus_functionField, map_zero]
    norm_num

end Divisor

end WeierstrassCurve.Affine
