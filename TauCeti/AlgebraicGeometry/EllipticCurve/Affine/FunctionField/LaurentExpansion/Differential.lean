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
`WeierstrassCurve.differentialLaurentSeries : Ω[K(W)/K] →ₗ[K] K⸨X⸩`. Whenever the
denominator `2y + a₁x + a₃` is nonzero (in particular on any elliptic curve), the invariant
differential `ω = dx / (2y + a₁x + a₃)` expands to the normalised invariant differential of
`formalGroup W`.

## Main definitions

* `WeierstrassCurve.differentialLaurentSeries`: the `K`-linear coefficient expansion
  `Ω[K(W)/K] →ₗ[K] K⸨X⸩` in `dz` at infinity.

## Main results

* `WeierstrassCurve.differentialLaurentSeries_D` and
  `WeierstrassCurve.differentialLaurentSeries_smul`: compatibility with exterior differentiation
  and scalar multiplication by rational functions.
* `WeierstrassCurve.differentialLaurentSeries_invariantDifferential`: `ω` expands to the normalised
  invariant differential of `formalGroup W` whenever its denominator is nonzero.

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

/-- **The invariant differential expands at infinity to the normalised invariant differential of
the formal group**, whenever its denominator `2y + a₁x + a₃` is nonzero. -/
@[simp]
theorem differentialLaurentSeries_invariantDifferential
    (hd : Affine.invariantDifferentialDenom W.toAffine ≠ 0) :
    W.differentialLaurentSeries (Affine.invariantDifferential W.toAffine) =
      ((formalGroup W).invariantDifferential : K⸨X⸩) := by
  let z : K⸨X⸩ := ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)
  let w : K⸨X⸩ := (formalW W : K⸨X⸩)
  have hw0 : w ≠ 0 := W.formalW_coe_ne_zero
  have hmul : ((formalGroup W).invariantDifferential : K⸨X⸩) *
      (W.formalInvariantDifferentialDenom : K⸨X⸩) = 1 := by
    simpa only [PowerSeries.coe_mul, PowerSeries.coe_one] using
      congrArg (ofPowerSeries ℤ K)
        W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
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
      (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr hd
    apply hd0
    rw [hdenom, Affine.evalEval_polynomialY]
    simp only [WeierstrassCurve.baseChange, map_a₁, map_a₃]
    field_simp
    linear_combination h0
  have hkey := W.inv_smul_derivation_div_subst_formalW_of_neg_two_add_ne_zero
    (σ := Unit) (KK := K⸨X⸩) (TauCeti.laurentSeriesDerivation K) (q := (PowerSeries.X : K⟦X⟧))
    (PowerSeries.constantCoeff_X)
    (by simpa [LaurentSeries.coe_algebraMap, z, w] using hu)
  simp only [PowerSeries.X_subst, LaurentSeries.coe_algebraMap,
    TauCeti.laurentSeriesDerivation_apply, smul_eq_mul, inv_eq_of_mul_eq_one_left hmul] at hkey
  have hx : W.functionFieldLaurentExpansion W.toAffine.genericX = z / w :=
    W.functionFieldLaurentExpansion_genericX_eq_div_formalW
  have hz' : _root_.LaurentSeries.derivative K z = 1 := by simp [z]
  rw [Affine.invariantDifferential_def, differentialLaurentSeries_smul,
    differentialLaurentSeries_D, map_inv₀, hdenom, hx]
  simpa only [z, w, hz', mul_one] using hkey

end WeierstrassCurve
