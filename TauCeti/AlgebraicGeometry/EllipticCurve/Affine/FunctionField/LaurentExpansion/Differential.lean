/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.LaurentExpansion.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Expansion
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GeneratedByY
import TauCeti.FieldTheory.Separable.SimpleRoot

/-!
# Laurent expansions of Kähler differentials on Weierstrass curves

Expanding Kähler differentials of `K(W)` at the point at infinity in the local parameter
`z = -x / y` sends `f dg` to `f(z) g'(z) dz`, recorded by the `K`-linear map
`W.functionFieldLaurentExpansion.differentialLaurentExpansion : Ω[K(W)/K] →ₗ[K] K⸨X⸩`. This map
is injective over any field `K` (`WeierstrassCurve.differentialLaurentExpansion_injective`), because
`z = -x / y` is a separating element of `K(W) / K`. Whenever the denominator `2y + a₁x + a₃` is
nonzero (in particular on any elliptic curve), the invariant differential
`ω = dx / (2y + a₁x + a₃)` expands to the normalised invariant differential of `formalGroup W`.

## Main results

* `WeierstrassCurve.transcendental_and_isSeparable_neg_genericX_div_genericY`: `z = -x / y` is a
  separating element of `K(W) / K` over any field `K` and for any Weierstrass curve `W` (`z` is
  transcendental over `K` and `K(W)` is separable over `K⟮z⟯`).
* `WeierstrassCurve.differentialLaurentExpansion_injective`,
  `WeierstrassCurve.differentialLaurentExpansion_eq_zero_iff`, and
  `WeierstrassCurve.differentialLaurentExpansion_inj`: injectivity of Laurent expansion on Kähler
  differentials over any field `K`.
* `WeierstrassCurve.differentialLaurentExpansion_invariantDifferential`: `ω` expands to the
  normalised invariant differential of `formalGroup W` whenever its denominator is nonzero.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5, IV.1, and IV.4.
-/

public section

open HahnSeries Polynomial
open scoped IntermediateField LaurentSeries PowerSeries

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- The local parameter `z = -x / y` at infinity is transcendental over `K`. -/
private theorem transcendental_neg_genericX_div_genericY :
    Transcendental K (-W.toAffine.genericX / W.toAffine.genericY) := by
  have hzX : W.functionFieldLaurentExpansion (-W.toAffine.genericX / W.toAffine.genericY) =
      ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) :=
    W.functionFieldLaurentExpansion_neg_genericX_div_genericY
  have hX : Transcendental K ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) := by
    rw [← _root_.LaurentSeries.coe_algebraMap, ← IsScalarTower.toAlgHom_apply K K⟦X⟧ K⸨X⸩]
    exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom K K⟦X⟧ K⸨X⸩) (by
      simpa [_root_.LaurentSeries.coe_algebraMap] using
        ofPowerSeries_injective (Γ := ℤ) (R := K))).not.mpr
      (PowerSeries.transcendental_of_constantCoeff_eq_zero
        PowerSeries.constantCoeff_X PowerSeries.X_ne_zero)
  exact (isAlgebraic_algHom_iff W.functionFieldLaurentExpansion
    W.functionFieldLaurentExpansion.injective).not.mp (hzX ▸ hX)

/-- `K(W)` is generated over `K(-x / y)` by `w = -1 / y`. -/
private theorem adjoin_neg_inv_genericY_eq_top :
    K⟮-W.toAffine.genericX / W.toAffine.genericY⟯⟮-W.toAffine.genericY⁻¹⟯ = ⊤ := by
  let x : W.toAffine.FunctionField := W.toAffine.genericX
  let y : W.toAffine.FunctionField := W.toAffine.genericY
  let z : W.toAffine.FunctionField := -x / y
  let w : W.toAffine.FunctionField := -y⁻¹
  have hz_mem : z ∈ (K⟮z⟯⟮w⟯).restrictScalars K :=
    (K⟮z⟯⟮w⟯).algebraMap_mem ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
  have hw_mem : w ∈ (K⟮z⟯⟮w⟯).restrictScalars K :=
    IntermediateField.mem_adjoin_simple_self K⟮z⟯ w
  have hle : K⟮x, y⟯ ≤ (K⟮z⟯⟮w⟯).restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro u (rfl | rfl)
    · have hyw : y = -w⁻¹ := by simp [w]
      have hxz : x = -z * y := by
        have hy0 : y ≠ 0 := W.toAffine.genericY_ne_zero
        simp [z, hy0]
      rw [hxz, hyw]
      exact mul_mem (neg_mem hz_mem) (neg_mem (inv_mem hw_mem))
    · have hyw : y = -w⁻¹ := by simp [w]
      rw [hyw]
      exact neg_mem (inv_mem hw_mem)
  rw [W.toAffine.adjoin_genericX_genericY_eq_top] at hle
  exact eq_top_iff.mpr fun a _ ↦ hle trivial

/-- The cubic `w`-equation polynomial over `K(-x / y)` with root `w = -1 / y`. -/
private noncomputable def wEquationPoly : K⟮-W.toAffine.genericX / W.toAffine.genericY⟯[X] :=
  let z' := IntermediateField.AdjoinSimple.gen K (-W.toAffine.genericX / W.toAffine.genericY)
  Polynomial.C (algebraMap K _ W.a₆) * X ^ 3 +
    Polynomial.C (algebraMap K _ W.a₃ + algebraMap K _ W.a₄ * z') * X ^ 2 +
    Polynomial.C (algebraMap K _ W.a₁ * z' + algebraMap K _ W.a₂ * z' ^ 2 - 1) * X +
    Polynomial.C (z' ^ 3)

/-- `w = -1 / y` is a root of `W.wEquationPoly`. -/
private theorem aeval_neg_inv_genericY_wEquationPoly :
    aeval (-W.toAffine.genericY⁻¹) W.wEquationPoly = 0 := by
  have hw_eq : -W.toAffine.genericY⁻¹ =
      (-W.toAffine.genericX / W.toAffine.genericY) ^ 3 +
        algebraMap K W.toAffine.FunctionField W.a₁ *
          (-W.toAffine.genericX / W.toAffine.genericY) * (-W.toAffine.genericY⁻¹) +
        algebraMap K W.toAffine.FunctionField W.a₂ *
          (-W.toAffine.genericX / W.toAffine.genericY) ^ 2 * (-W.toAffine.genericY⁻¹) +
        algebraMap K W.toAffine.FunctionField W.a₃ * (-W.toAffine.genericY⁻¹) ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ *
          (-W.toAffine.genericX / W.toAffine.genericY) * (-W.toAffine.genericY⁻¹) ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₆ * (-W.toAffine.genericY⁻¹) ^ 3 := by
    have heq := W.wEquation_of_equation W.toAffine.equation_genericX_genericY
    rw [wEquationRHS_def] at heq
    simpa only [← neg_div] using heq
  simp only [wEquationPoly, map_add, map_mul, map_sub, map_pow, map_one, aeval_C, aeval_X,
    ← IsScalarTower.algebraMap_apply K K⟮-W.toAffine.genericX / W.toAffine.genericY⟯
      W.toAffine.FunctionField,
    IntermediateField.AdjoinSimple.algebraMap_gen]
  linear_combination -hw_eq

/-- Formula for the derivative of `W.wEquationPoly`. -/
private theorem derivative_wEquationPoly :
    let z' := IntermediateField.AdjoinSimple.gen K (-W.toAffine.genericX / W.toAffine.genericY)
    W.wEquationPoly.derivative =
      3 * Polynomial.C (algebraMap K _ W.a₆) * X ^ 2 +
        2 * Polynomial.C (algebraMap K _ W.a₃ + algebraMap K _ W.a₄ * z') * X +
        Polynomial.C (algebraMap K _ W.a₁ * z' + algebraMap K _ W.a₂ * z' ^ 2 - 1) := by
  simp only [wEquationPoly, derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_X_pow, derivative_X, mul_one, Nat.cast_ofNat, map_ofNat]
  ring

/-- `w = -1 / y` is a simple root of `W.wEquationPoly`, since the Laurent expansion of
`P'(-1 / y)` has constant term `-1`. -/
private theorem aeval_derivative_wEquationPoly_ne_zero :
    aeval (-W.toAffine.genericY⁻¹) W.wEquationPoly.derivative ≠ 0 := by
  intro h0
  let D : K⟦X⟧ :=
    3 * PowerSeries.C W.a₆ * formalW W ^ 2 +
      2 * (PowerSeries.C W.a₃ + PowerSeries.C W.a₄ * PowerSeries.X) * formalW W +
      (PowerSeries.C W.a₁ * PowerSeries.X + PowerSeries.C W.a₂ * PowerSeries.X ^ 2 - 1)
  have hzX : W.functionFieldLaurentExpansion (-W.toAffine.genericX / W.toAffine.genericY) =
      ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) :=
    W.functionFieldLaurentExpansion_neg_genericX_div_genericY
  have hwW : W.functionFieldLaurentExpansion (-W.toAffine.genericY⁻¹) = (formalW W : K⸨X⸩) :=
    W.functionFieldLaurentExpansion_neg_inv_genericY
  have hc (a : K) : ofPowerSeries ℤ K (PowerSeries.C a) = algebraMap K K⸨X⸩ a := by
    rw [← PowerSeries.algebraMap_eq, ← _root_.LaurentSeries.coe_algebraMap,
      ← IsScalarTower.algebraMap_apply]
  have hD : W.functionFieldLaurentExpansion
      (aeval (-W.toAffine.genericY⁻¹) W.wEquationPoly.derivative) = (D : K⸨X⸩) := by
    simp only [W.derivative_wEquationPoly, D, map_add, map_mul, map_sub, map_pow, map_one,
      map_ofNat, aeval_C, aeval_X,
      ← IsScalarTower.algebraMap_apply K K⟮-W.toAffine.genericX / W.toAffine.genericY⟯
        W.toAffine.FunctionField,
      IntermediateField.AdjoinSimple.algebraMap_gen, AlgHom.commutes, hzX, hwW, hc]
  have h0' := congrArg W.functionFieldLaurentExpansion h0
  rw [hD, map_zero] at h0'
  have hDc : PowerSeries.constantCoeff D = 0 := by
    simpa using congrArg PowerSeries.constantCoeff
      ((map_eq_zero_iff (ofPowerSeries ℤ K) ofPowerSeries_injective).mp h0')
  simp [D] at hDc

/-- **The local parameter `z = -x / y` at infinity is separating for `K(W) / K`**, over any
field `K` and for any Weierstrass curve `W` (even singular in characteristic `2`): `z` is
transcendental over `K` and `K(W)` is separable over `K⟮z⟯`, because `w = -1 / y` is a simple
root of `W.wEquationPoly` over `K⟮z⟯`. -/
theorem transcendental_and_isSeparable_neg_genericX_div_genericY :
    let z : W.toAffine.FunctionField := -W.toAffine.genericX / W.toAffine.genericY
    Transcendental K z ∧ Algebra.IsSeparable K⟮z⟯ W.toAffine.FunctionField :=
  ⟨W.transcendental_neg_genericX_div_genericY,
    (TauCeti.finiteDimensional_and_isSeparable_of_aeval_derivative_ne_zero
      W.adjoin_neg_inv_genericY_eq_top
      W.aeval_neg_inv_genericY_wEquationPoly
      W.aeval_derivative_wEquationPoly_ne_zero).2⟩

/-- **Laurent expansion of Kähler differentials at infinity is injective**, over any field `K` and
for any Weierstrass curve `W`. -/
theorem differentialLaurentExpansion_injective :
    Function.Injective W.functionFieldLaurentExpansion.differentialLaurentExpansion := by
  rw [injective_iff_map_eq_zero]
  intro η hη
  have ⟨htr, hsep⟩ := W.transcendental_and_isSeparable_neg_genericX_div_genericY
  let z := -W.toAffine.genericX / W.toAffine.genericY
  have hmem : η ∈ Submodule.span W.toAffine.FunctionField
      {KaehlerDifferential.D K W.toAffine.FunctionField z} :=
    (TauCeti.span_D_eq_top_of_separating htr).symm ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  subst hc
  have hderiv : _root_.LaurentSeries.derivative K (W.functionFieldLaurentExpansion z) = 1 := by
    simp [z]
  rw [AlgHom.differentialLaurentExpansion_smul, AlgHom.differentialLaurentExpansion_D, hderiv,
    mul_one] at hη
  have hc0 : c = 0 := W.functionFieldLaurentExpansion.injective (by simpa using hη)
  rw [hc0, zero_smul]

/-- **A Kähler differential on `K(W)` vanishes if and only if its Laurent expansion vanishes.** -/
@[simp]
theorem differentialLaurentExpansion_eq_zero_iff
    {η : KaehlerDifferential K W.toAffine.FunctionField} :
    W.functionFieldLaurentExpansion.differentialLaurentExpansion η = 0 ↔ η = 0 :=
  map_eq_zero_iff _ W.differentialLaurentExpansion_injective

/-- **Two Kähler differentials on `K(W)` are equal if and only if their Laurent expansions
agree.** -/
@[simp]
theorem differentialLaurentExpansion_inj
    {η₁ η₂ : KaehlerDifferential K W.toAffine.FunctionField} :
    W.functionFieldLaurentExpansion.differentialLaurentExpansion η₁ =
      W.functionFieldLaurentExpansion.differentialLaurentExpansion η₂ ↔ η₁ = η₂ :=
  W.differentialLaurentExpansion_injective.eq_iff

/-- **The invariant differential expands at infinity to the normalised invariant differential of
the formal group**, whenever its denominator `2y + a₁x + a₃` is nonzero. -/
@[simp]
theorem differentialLaurentExpansion_invariantDifferential
    (hd : Affine.invariantDifferentialDenom W.toAffine ≠ 0) :
    W.functionFieldLaurentExpansion.differentialLaurentExpansion
        (Affine.invariantDifferential W.toAffine) =
      ((formalGroup W).invariantDifferential : K⸨X⸩) := by
  let z : K⸨X⸩ := ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)
  let w : K⸨X⸩ := (formalW W : K⸨X⸩)
  have hw0 : w ≠ 0 :=
    (map_ne_zero_iff (ofPowerSeries ℤ K) ofPowerSeries_injective).mpr W.formalW_ne_zero
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
    have hd0 : W.functionFieldLaurentExpansion (Affine.invariantDifferentialDenom W.toAffine) ≠ 0 :=
      (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr hd
    rw [hdenom, W.evalEval_polynomialY_div z hw0] at hd0
    exact fun h0 ↦ hd0 (by simp [h0])
  have hkey := W.inv_smul_derivation_div_subst_formalW_of_neg_two_add_ne_zero
    (σ := Unit) (KK := K⸨X⸩) (TauCeti.laurentSeriesDerivation K) (q := (PowerSeries.X : K⟦X⟧))
    (PowerSeries.constantCoeff_X)
    (by simpa [LaurentSeries.coe_algebraMap, z, w] using hu)
  simp only [PowerSeries.X_subst, LaurentSeries.coe_algebraMap,
    TauCeti.laurentSeriesDerivation_apply, smul_eq_mul, inv_eq_of_mul_eq_one_left hmul] at hkey
  have hx : W.functionFieldLaurentExpansion W.toAffine.genericX = z / w :=
    W.functionFieldLaurentExpansion_genericX_eq_div_formalW
  have hz' : _root_.LaurentSeries.derivative K z = 1 := by simp [z]
  rw [Affine.invariantDifferential_def, AlgHom.differentialLaurentExpansion_smul,
    AlgHom.differentialLaurentExpansion_D, map_inv₀, hdenom, hx]
  simpa only [z, w, hz', mul_one] using hkey

end WeierstrassCurve
