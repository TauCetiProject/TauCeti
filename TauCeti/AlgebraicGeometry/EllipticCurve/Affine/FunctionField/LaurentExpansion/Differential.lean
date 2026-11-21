/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.LaurentExpansion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.RingTheory.Kaehler.MapSemilinear
public import TauCeti.RingTheory.LaurentSeries.Derivative

/-!
# Laurent expansions of Kähler differentials on Weierstrass curves

Expanding Kähler differentials of `K(W)` at the point at infinity in the local parameter
`z = -x / y` sends `f dg` to `f(z) g'(z) dz`, recorded as the `K`-linear map
`WeierstrassCurve.differentialLaurentSeries : Ω[K(W)/K] →ₗ[K] K⸨X⸩`. On an elliptic curve `W`, the
invariant differential `ω = dx / (2y + a₁x + a₃)` expands to the normalised invariant differential
of `formalGroup W`, and the expansion is injective.

## Main definitions

* `WeierstrassCurve.differentialLaurentSeries`: the `K`-linear coefficient expansion
  `Ω[K(W)/K] →ₗ[K] K⸨X⸩` in `dz` at infinity.

## Main results

* `WeierstrassCurve.differentialLaurentSeries_D` and
  `WeierstrassCurve.differentialLaurentSeries_smul`: compatibility with exterior differentiation
  and scalar multiplication by rational functions.
* `WeierstrassCurve.differentialLaurentSeries_invariantDifferential`: `ω` expands to the normalised
  invariant differential of `formalGroup W`.
* `WeierstrassCurve.differentialLaurentSeries_injective`,
  `WeierstrassCurve.differentialLaurentSeries_eq_zero_iff`, and
  `WeierstrassCurve.differentialLaurentSeries_inj`: injectivity of the expansion on an elliptic
  curve.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5, IV.1, and IV.4.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- **The Laurent expansion of Kähler differentials at infinity**: pushing `Ω[K(W)/K]` forward
along `W.functionFieldLaurentExpansion` and contracting with `laurentSeriesDerivation K` sends
`f dg` to `f(z) g'(z)` in `K⸨X⸩`, where `z = -x / y` expands to `X`. -/
noncomputable def differentialLaurentSeries :
    KaehlerDifferential K W.toAffine.FunctionField →ₗ[K] K⸨X⸩ where
  toFun η := (TauCeti.laurentSeriesDerivation K).liftKaehlerDifferential
    (KaehlerDifferential.mapSemilinear W.functionFieldLaurentExpansion η)
  map_add' η₁ η₂ := by rw [map_add, map_add]
  map_smul' c η := by
    rw [RingHom.id_apply, ← algebraMap_smul W.toAffine.FunctionField c η,
      KaehlerDifferential.mapSemilinear_smul, AlgHom.commutes, LinearMap.map_smul,
      smul_eq_mul, TauCeti.laurentSeries_algebraMap_mul_eq_smul]

/-- `differentialLaurentSeries` lifts `laurentSeriesDerivation` along the Laurent expansion. -/
theorem differentialLaurentSeries_apply (η : KaehlerDifferential K W.toAffine.FunctionField) :
    W.differentialLaurentSeries η =
      (TauCeti.laurentSeriesDerivation K).liftKaehlerDifferential
        (KaehlerDifferential.mapSemilinear W.functionFieldLaurentExpansion η) :=
  (rfl)

/-- **The differential `d f` expands to the formal derivative of the expansion of `f`.** -/
@[simp]
theorem differentialLaurentSeries_D (f : W.toAffine.FunctionField) :
    W.differentialLaurentSeries (KaehlerDifferential.D K W.toAffine.FunctionField f) =
      _root_.LaurentSeries.derivative K (W.functionFieldLaurentExpansion f) := by
  rw [differentialLaurentSeries_apply, KaehlerDifferential.mapSemilinear_D,
    Derivation.liftKaehlerDifferential_comp_D, TauCeti.laurentSeriesDerivation_apply]

/-- **Scalar multiplication by a rational function becomes multiplication by its expansion.** -/
@[simp]
theorem differentialLaurentSeries_smul (f : W.toAffine.FunctionField)
    (η : KaehlerDifferential K W.toAffine.FunctionField) :
    W.differentialLaurentSeries (f • η) =
      W.functionFieldLaurentExpansion f * W.differentialLaurentSeries η := by
  rw [differentialLaurentSeries_apply, KaehlerDifferential.mapSemilinear_smul,
    LinearMap.map_smul, smul_eq_mul, ← differentialLaurentSeries_apply]

private theorem functionFieldLaurentExpansion_genericY_eq_div_formalW :
    W.functionFieldLaurentExpansion W.toAffine.genericY = -1 / (formalW W : K⸨X⸩) := by
  have h := W.functionFieldLaurentExpansion_neg_inv_genericY
  rw [map_neg, map_inv₀] at h
  rw [← h]
  field_simp [(map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr
    W.toAffine.genericY_ne_zero]

private theorem formalW_coe_ne_zero : (formalW W : K⸨X⸩) ≠ 0 := by
  rw [← W.functionFieldLaurentExpansion_neg_inv_genericY]
  exact (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr
    (neg_ne_zero.mpr (inv_ne_zero W.toAffine.genericY_ne_zero))

private theorem functionFieldLaurentExpansion_genericX_eq_div_formalW :
    W.functionFieldLaurentExpansion W.toAffine.genericX =
      ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) / (formalW W : K⸨X⸩) := by
  have hw0 : (formalW W : K⸨X⸩) ≠ 0 := W.formalW_coe_ne_zero
  have h := W.functionFieldLaurentExpansion_neg_genericX_div_genericY
  rw [map_div₀, map_neg, W.functionFieldLaurentExpansion_genericY_eq_div_formalW] at h
  rw [← h]
  field_simp

private theorem coe_formalInvariantDifferentialDenom :
    (W.formalInvariantDifferentialDenom : K⸨X⸩) =
      1 - algebraMap K K⸨X⸩ W.a₁ * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) -
        algebraMap K K⸨X⸩ W.a₂ * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ 2 -
        2 * algebraMap K K⸨X⸩ W.a₃ * (formalW W : K⸨X⸩) -
        2 * algebraMap K K⸨X⸩ W.a₄ * (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) * (formalW W : K⸨X⸩)) -
        3 * algebraMap K K⸨X⸩ W.a₆ * (formalW W : K⸨X⸩) ^ 2 := by
  have hC (c : K) : ((PowerSeries.C c : K⟦X⟧) : K⸨X⸩) = algebraMap K K⸨X⸩ c := by
    rw [← LaurentSeries.coe_algebraMap, ← PowerSeries.algebraMap_eq,
      IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩]
  rw [formalInvariantDifferentialDenom_def]
  simp only [PowerSeries.smul_eq_C_mul, PowerSeries.coe_sub, PowerSeries.coe_one,
    PowerSeries.coe_pow, hC, map_mul, map_ofNat]

/-- **The invariant differential of an elliptic curve expands at infinity to the normalised
invariant differential of its formal group.** -/
@[simp]
theorem differentialLaurentSeries_invariantDifferential [W.IsElliptic] :
    W.differentialLaurentSeries (Affine.invariantDifferential W.toAffine) =
      ((formalGroup W).invariantDifferential : K⸨X⸩) := by
  let z : K⸨X⸩ := ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)
  let w : K⸨X⸩ := (formalW W : K⸨X⸩)
  have hw0 : w ≠ 0 := W.formalW_coe_ne_zero
  have heq : w = wEquationRHS W z w := by
    have h := congrArg (ofPowerSeries ℤ K) W.formalW_wEquation
    rwa [← LaurentSeries.coe_algebraMap, algebraMap_wEquationRHS, LaurentSeries.coe_algebraMap] at h
  have hmul : ((formalGroup W).invariantDifferential : K⸨X⸩) *
      (W.formalInvariantDifferentialDenom : K⸨X⸩) = 1 := by
    simpa only [PowerSeries.coe_mul, PowerSeries.coe_one] using
      congrArg (ofPowerSeries ℤ K)
        W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
  have hGeq : (W.formalInvariantDifferentialDenom : K⸨X⸩) =
      1 - algebraMap K K⸨X⸩ W.a₁ * z - algebraMap K K⸨X⸩ W.a₂ * z ^ 2 -
        2 * algebraMap K K⸨X⸩ W.a₃ * w - 2 * algebraMap K K⸨X⸩ W.a₄ * (z * w) -
        3 * algebraMap K K⸨X⸩ W.a₆ * w ^ 2 :=
    W.coe_formalInvariantDifferentialDenom
  have hG0 : 1 - algebraMap K K⸨X⸩ W.a₁ * z - algebraMap K K⸨X⸩ W.a₂ * z ^ 2 -
      2 * algebraMap K K⸨X⸩ W.a₃ * w - 2 * algebraMap K K⸨X⸩ W.a₄ * (z * w) -
      3 * algebraMap K K⸨X⸩ W.a₆ * w ^ 2 ≠ 0 :=
    hGeq ▸ right_ne_zero_of_mul_eq_one hmul
  have hdenom : W.functionFieldLaurentExpansion (Affine.invariantDifferentialDenom W.toAffine) =
      (W⁄K⸨X⸩).toAffine.polynomialY.evalEval (z / w) (-1 / w) := by
    rw [Affine.invariantDifferentialDenom_def, Affine.evalEval_polynomialY]
    simp only [map_add, map_mul, map_ofNat, AlgHom.commutes,
      W.functionFieldLaurentExpansion_genericX_eq_div_formalW,
      W.functionFieldLaurentExpansion_genericY_eq_div_formalW,
      WeierstrassCurve.baseChange, map_a₁, map_a₃, z, w]
  have hu : -2 + algebraMap K K⸨X⸩ W.a₁ * z + algebraMap K K⸨X⸩ W.a₃ * w ≠ 0 := by
    intro h0
    have hd0 : W.functionFieldLaurentExpansion (Affine.invariantDifferentialDenom W.toAffine) ≠ 0 :=
      (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr
        (Affine.invariantDifferentialDenom_ne_zero W.toAffine)
    apply hd0
    rw [hdenom, Affine.evalEval_polynomialY]
    simp only [WeierstrassCurve.baseChange, map_a₁, map_a₃]
    field_simp
    linear_combination h0
  have hkey := W.inv_evalEval_polynomialY_smul_derivation_div
    (TauCeti.laurentSeriesDerivation K) heq hG0 hu
  have hx : W.functionFieldLaurentExpansion W.toAffine.genericX = z / w :=
    W.functionFieldLaurentExpansion_genericX_eq_div_formalW
  have hz' : _root_.LaurentSeries.derivative K z = 1 := by
    simp [z]
  rw [Affine.invariantDifferential_def, differentialLaurentSeries_smul,
    differentialLaurentSeries_D, map_inv₀, hdenom, hx]
  simpa only [TauCeti.laurentSeriesDerivation_apply, smul_eq_mul, ← hGeq, hz', mul_one,
    inv_eq_of_mul_eq_one_left hmul] using hkey

/-- **Laurent expansion of Kähler differentials is injective on an elliptic curve.** -/
theorem differentialLaurentSeries_injective [W.IsElliptic] :
    Function.Injective W.differentialLaurentSeries := by
  rw [injective_iff_map_eq_zero]
  intro η hη
  obtain ⟨f, rfl, -⟩ := Affine.existsUnique_smul_invariantDifferential W.toAffine η
  rw [differentialLaurentSeries_smul, differentialLaurentSeries_invariantDifferential,
    mul_eq_zero] at hη
  have hω : ((formalGroup W).invariantDifferential : K⸨X⸩) ≠ 0 := fun h0 ↦ by
    have h1 : (formalGroup W).invariantDifferential = 0 :=
      ofPowerSeries_injective (by rwa [PowerSeries.coe_zero])
    simpa using congrArg PowerSeries.constantCoeff h1
  have hf : f = 0 := W.functionFieldLaurentExpansion.injective (by
    rw [map_zero]
    exact hη.resolve_right hω)
  rw [hf, zero_smul]

/-- **A Kähler differential on an elliptic curve vanishes iff its Laurent expansion vanishes.** -/
@[simp↓]
theorem differentialLaurentSeries_eq_zero_iff [W.IsElliptic]
    (η : KaehlerDifferential K W.toAffine.FunctionField) :
    W.differentialLaurentSeries η = 0 ↔ η = 0 :=
  map_eq_zero_iff W.differentialLaurentSeries W.differentialLaurentSeries_injective

/-- **Two Kähler differentials on an elliptic curve agree iff their Laurent expansions agree.** -/
@[simp↓]
theorem differentialLaurentSeries_inj [W.IsElliptic]
    {η₁ η₂ : KaehlerDifferential K W.toAffine.FunctionField} :
    W.differentialLaurentSeries η₁ = W.differentialLaurentSeries η₂ ↔ η₁ = η₂ :=
  W.differentialLaurentSeries_injective.eq_iff

end WeierstrassCurve
