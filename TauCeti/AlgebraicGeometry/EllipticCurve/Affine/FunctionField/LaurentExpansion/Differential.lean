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
import TauCeti.FieldTheory.Separable.SimpleRoot
import Mathlib.RingTheory.Valuation.IsTrivialOn

/-!
# Laurent expansions of Kähler differentials on Weierstrass curves

Expanding Kähler differentials of `K(W)` at the point at infinity in the local parameter
`z = -x / y` sends `f dg` to `f(z) g'(z) dz`, recorded as the `K`-linear map
`WeierstrassCurve.differentialLaurentSeries : Ω[K(W)/K] →ₗ[K] K⸨X⸩`. On any Weierstrass curve
`W`, `z` is a separating element of `K(W)/K`, so `differentialLaurentSeries` is injective; whenever
the denominator `2y + a₁x + a₃` is nonzero (in particular on any elliptic curve), the invariant
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
* `WeierstrassCurve.differentialLaurentSeries_injective`,
  `WeierstrassCurve.differentialLaurentSeries_eq_zero_iff`, and
  `WeierstrassCurve.differentialLaurentSeries_inj`: injectivity of the expansion on any
  Weierstrass curve.

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

private theorem transcendental_neg_genericX_div_genericY :
    Transcendental K (-W.toAffine.genericX / W.toAffine.genericY) :=
  Valuation.transcendental_of_ne_one (v := W.toAffine.infinityPlace) K _
    (by simp [(W.toAffine.transcendental_genericX).ne_zero, W.toAffine.genericY_ne_zero])
    (by simp)

private theorem isSeparable_adjoin_neg_genericX_div_genericY :
    Algebra.IsSeparable (IntermediateField.adjoin K {-W.toAffine.genericX / W.toAffine.genericY})
      W.toAffine.FunctionField := by
  let z : W.toAffine.FunctionField := -W.toAffine.genericX / W.toAffine.genericY
  let w : W.toAffine.FunctionField := -W.toAffine.genericY⁻¹
  let L := IntermediateField.adjoin K {z}
  have hw0 : w ≠ 0 := neg_ne_zero.mpr (inv_ne_zero W.toAffine.genericY_ne_zero)
  have hy_eq : W.toAffine.genericY = -1 / w := by simp [w]
  have hx_eq : W.toAffine.genericX = z / w := by
    have hy0 : W.toAffine.genericY ≠ 0 := W.toAffine.genericY_ne_zero
    simp only [z, w]
    field_simp
  have hgen : IntermediateField.adjoin L {w} = ⊤ := by
    rw [eq_top_iff]
    intro f _
    let M := IntermediateField.adjoin L {w}
    have hzM : z ∈ M := IntermediateField.algebraMap_mem M
      ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
    have hwM : w ∈ M := IntermediateField.mem_adjoin_simple_self L w
    have hyM : W.toAffine.genericY ∈ M := by
      rw [hy_eq]
      exact M.div_mem (M.neg_mem M.one_mem) hwM
    have hxM : W.toAffine.genericX ∈ M := by
      rw [hx_eq]
      exact M.div_mem hzM hwM
    have hcoord : ∀ g : W.toAffine.CoordinateRing,
        algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField g ∈ M := by
      intro g
      have hsub : Algebra.adjoin K {W.toAffine.genericX, W.toAffine.genericY} ≤
          (M.restrictScalars K).toSubalgebra := by
        refine Algebra.adjoin_le ?_
        rintro _ (rfl | rfl)
        · exact hxM
        · exact hyM
      exact hsub (Affine.algebraMap_mem_adjoin_genericX_genericY W.toAffine g)
    obtain ⟨⟨a, b⟩, hf⟩ := IsLocalization.surj
      (nonZeroDivisors W.toAffine.CoordinateRing) f
    have hb0 : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField b ≠ 0 :=
      (map_ne_zero_iff _
        (IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField)).mpr
        (nonZeroDivisors.ne_zero b.property)
    have hf_eq : f = algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField a /
        algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField b :=
      eq_div_of_mul_eq hb0 hf
    rw [hf_eq]
    exact M.div_mem (hcoord a) (hcoord b)
  let c : K →+* L := algebraMap K L
  let z₀ : L := IntermediateField.AdjoinSimple.gen K z
  have hz₀ : algebraMap L W.toAffine.FunctionField z₀ = z := rfl
  let P : Polynomial L :=
    Polynomial.C (c W.a₆) * Polynomial.X ^ 3 +
      Polynomial.C (c W.a₃ + c W.a₄ * z₀) * Polynomial.X ^ 2 +
      Polynomial.C (c W.a₁ * z₀ + c W.a₂ * z₀ ^ 2 - 1) * Polynomial.X +
      Polynomial.C (z₀ ^ 3)
  have hP : Polynomial.aeval w P = 0 := by
    have heq := W.toAffine.equation_genericX_genericY
    rw [Affine.equation_iff', hx_eq, hy_eq] at heq
    simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
    simp only [P, map_add, map_mul, map_sub, map_one, map_pow, Polynomial.aeval_C,
      Polynomial.aeval_X, c, ← IsScalarTower.algebraMap_apply K L W.toAffine.FunctionField, hz₀]
    calc algebraMap K W.toAffine.FunctionField W.a₆ * w ^ 3 +
          (algebraMap K W.toAffine.FunctionField W.a₃ +
            algebraMap K W.toAffine.FunctionField W.a₄ * z) * w ^ 2 +
          (algebraMap K W.toAffine.FunctionField W.a₁ * z +
            algebraMap K W.toAffine.FunctionField W.a₂ * z ^ 2 - 1) * w + z ^ 3
        = w ^ 3 * ((z / w) ^ 3 + algebraMap K W.toAffine.FunctionField W.a₂ * (z / w) ^ 2 +
            algebraMap K W.toAffine.FunctionField W.a₄ * (z / w) +
            algebraMap K W.toAffine.FunctionField W.a₆ -
            ((-1 / w) ^ 2 + algebraMap K W.toAffine.FunctionField W.a₁ * (z / w) * (-1 / w) +
              algebraMap K W.toAffine.FunctionField W.a₃ * (-1 / w))) := by
          field_simp [hw0]
          ring
      _ = 0 := by linear_combination -w ^ 3 * heq
  have hP' : Polynomial.aeval w (Polynomial.derivative P) ≠ 0 := by
    intro h0
    have h1 := congrArg W.functionFieldLaurentExpansion h0
    have hderiv : Polynomial.derivative P =
        Polynomial.C (3 * c W.a₆) * Polynomial.X ^ 2 +
          Polynomial.C (2 * (c W.a₃ + c W.a₄ * z₀)) * Polynomial.X +
          Polynomial.C (c W.a₁ * z₀ + c W.a₂ * z₀ ^ 2 - 1) := by
      simp only [P, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
        Polynomial.derivative_C_mul_X, Polynomial.derivative_C, Nat.cast_ofNat,
        map_mul, map_ofNat, add_zero]
      ring
    rw [hderiv] at h1
    simp only [map_add, map_mul, map_sub, map_one, map_pow, map_ofNat, Polynomial.aeval_C,
      Polynomial.aeval_X, c, ← IsScalarTower.algebraMap_apply K L W.toAffine.FunctionField,
      hz₀, AlgHom.commutes] at h1
    have hz_exp : W.functionFieldLaurentExpansion z = ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) :=
      W.functionFieldLaurentExpansion_neg_genericX_div_genericY
    have hw_exp : W.functionFieldLaurentExpansion w = (formalW W : K⸨X⸩) :=
      W.functionFieldLaurentExpansion_neg_inv_genericY
    rw [hz_exp, hw_exp] at h1
    have hdenom_eq : ((W.formalInvariantDifferentialDenom : K⟦X⟧) : K⸨X⸩) = 0 := by
      have hd_eq : ((W.formalInvariantDifferentialDenom : K⟦X⟧) : K⸨X⸩) =
          -(3 * algebraMap K K⸨X⸩ W.a₆ * (formalW W : K⸨X⸩) ^ 2 +
            2 * (algebraMap K K⸨X⸩ W.a₃ +
              algebraMap K K⸨X⸩ W.a₄ * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)) *
              (formalW W : K⸨X⸩) +
            (algebraMap K K⸨X⸩ W.a₁ * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) +
              algebraMap K K⸨X⸩ W.a₂ * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ 2 - 1)) := by
        rw [formalInvariantDifferentialDenom_def]
        simp only [map_sub, map_one, map_mul, map_pow, map_ofNat, PowerSeries.smul_eq_C_mul,
          ← PowerSeries.algebraMap_eq, ← LaurentSeries.coe_algebraMap,
          ← IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩]
        ring
      rw [hd_eq, h1, map_zero, neg_zero]
    have hdenom_ps : W.formalInvariantDifferentialDenom = 0 :=
      ofPowerSeries_injective (by rwa [PowerSeries.coe_zero])
    simpa using congrArg PowerSeries.constantCoeff hdenom_ps
  exact (TauCeti.finiteDimensional_and_isSeparable_of_aeval_derivative_ne_zero
    hgen hP hP').2

/-- **Laurent expansion of Kähler differentials is injective on any Weierstrass curve.** -/
theorem differentialLaurentSeries_injective :
    Function.Injective W.differentialLaurentSeries := by
  rw [injective_iff_map_eq_zero]
  intro η hη
  let z : W.toAffine.FunctionField := -W.toAffine.genericX / W.toAffine.genericY
  have hz : Transcendental K z := W.transcendental_neg_genericX_div_genericY
  have : Algebra.IsSeparable (IntermediateField.adjoin K {z}) W.toAffine.FunctionField :=
    W.isSeparable_adjoin_neg_genericX_div_genericY
  have hmem : η ∈ Submodule.span W.toAffine.FunctionField
      {KaehlerDifferential.D K W.toAffine.FunctionField z} := by
    rw [TauCeti.span_D_eq_top_of_separating hz]
    exact Submodule.mem_top
  obtain ⟨f, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  have hdz :
      W.differentialLaurentSeries (KaehlerDifferential.D K W.toAffine.FunctionField z) = 1 := by
    rw [differentialLaurentSeries_D, W.functionFieldLaurentExpansion_neg_genericX_div_genericY]
    simp
  rw [differentialLaurentSeries_smul, hdz, mul_one] at hη
  have hf : f = 0 := W.functionFieldLaurentExpansion.injective (by rwa [map_zero])
  rw [hf, zero_smul]

/-- **A Kähler differential on a Weierstrass curve vanishes iff its Laurent expansion vanishes.** -/
@[simp↓]
theorem differentialLaurentSeries_eq_zero_iff
    (η : KaehlerDifferential K W.toAffine.FunctionField) :
    W.differentialLaurentSeries η = 0 ↔ η = 0 :=
  map_eq_zero_iff W.differentialLaurentSeries W.differentialLaurentSeries_injective

/-- **Two Kähler differentials on a Weierstrass curve agree iff their Laurent expansions agree.** -/
@[simp↓]
theorem differentialLaurentSeries_inj
    {η₁ η₂ : KaehlerDifferential K W.toAffine.FunctionField} :
    W.differentialLaurentSeries η₁ = W.differentialLaurentSeries η₂ ↔ η₁ = η₂ :=
  W.differentialLaurentSeries_injective.eq_iff

end WeierstrassCurve
