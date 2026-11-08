/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.LaurentExpansion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic

/-!
# The formal parameter of an isogeny

For an isogeny `φ : W₁ → W₂`, expand `φ*(-x₂/y₂)` at infinity on `W₁` in the
parameter `z₁ = -x₁/y₁`. Pointedness implies that this Laurent series is a power series
with zero constant coefficient. It is nonzero, including for inseparable isogenies.

`Isogeny.formalParameter` is this actual expansion, characterized by
`Isogeny.coe_formalParameter`. Pullback of every rational function is Laurent substitution
by this series (`Isogeny.functionFieldLaurentExpansion_fieldPullback`), and identity and
composition induce identity and composition of series. This supplies the local action
from the actual function-field map, without assuming a formal-group homomorphism or a
convergence theorem.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, IV.4.
-/

public section

open WeierstrassCurve HahnSeries
open scoped LaurentSeries PowerSeries WithZero

namespace TauCeti.Isogeny

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K}
  (φ : Isogeny W₁.toAffine W₂.toAffine)

private theorem isEquiv_comap_expansion :
    ((Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).comap
      (W₁.functionFieldLaurentExpansion.comp φ.fieldPullback).toRingHom).IsEquiv
        W₂.toAffine.infinityPlace :=
  (W₁.isEquiv_comap_functionFieldLaurentExpansion.comap
    φ.fieldPullback.toRingHom).trans φ.isEquiv_comap_infinityPlace

private theorem valuation_expansion_parameter_lt_one :
    Valued.v (W₁.functionFieldLaurentExpansion
      (φ.fieldPullback (-W₂.toAffine.genericX / W₂.toAffine.genericY))) < (1 : ℤᵐ⁰) := by
  apply Valuation.isEquiv_iff_val_lt_one.mp φ.isEquiv_comap_expansion |>.mpr
  rw [neg_div, Valuation.map_neg, Affine.genericX_def, Affine.genericY_def,
    Affine.CoordinateRing.mk_C_eq_algebraMap, Affine.infinityPlace.X_div_mk_Y,
    ← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.mpr (by norm_num)

/-- The expansion of the pulled-back target parameter `-x₂/y₂`, as a power series in `-x₁/y₁`. -/
noncomputable def formalParameter : K⟦X⟧ :=
  PowerSeries.mk fun n ↦ (W₁.functionFieldLaurentExpansion
    (φ.fieldPullback (-W₂.toAffine.genericX / W₂.toAffine.genericY))).coeff n

/-- The formal parameter is the Laurent expansion of the actual function-field pullback. -/
@[simp]
theorem coe_formalParameter :
    (φ.formalParameter : K⸨X⸩) = W₁.functionFieldLaurentExpansion
      (φ.fieldPullback (-W₂.toAffine.genericX / W₂.toAffine.genericY)) := by
  obtain ⟨g, hg⟩ := (LaurentSeries.val_le_one_iff_eq_coe K _).mp
    φ.valuation_expansion_parameter_lt_one.le
  rw [formalParameter, ← hg]
  congr 1
  ext n
  simp

/-- An isogeny's formal parameter has zero constant coefficient, because it maps infinity to
infinity. -/
-- Handle composites before `formalParameter_comp` rewrites them to substitutions.
@[simp↓]
theorem constantCoeff_formalParameter : PowerSeries.constantCoeff φ.formalParameter = 0 := by
  by_contra h
  have hunit : IsUnit φ.formalParameter :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h)
  have hv := LaurentSeries.valuation_coe_of_isUnit hunit
  rw [coe_formalParameter] at hv
  exact φ.valuation_expansion_parameter_lt_one.ne hv

/-- An isogeny's formal parameter is not the zero series, even in positive characteristic. -/
theorem formalParameter_ne_zero : φ.formalParameter ≠ 0 := by
  intro h
  have hz : -W₂.toAffine.genericX / W₂.toAffine.genericY = 0 := by
    apply φ.fieldPullback.injective
    apply W₁.functionFieldLaurentExpansion.injective
    simpa [h] using φ.coe_formalParameter.symm
  have hx := congrArg W₂.functionFieldLaurentExpansion hz
  rw [functionFieldLaurentExpansion_neg_genericX_div_genericY, map_zero] at hx
  apply PowerSeries.X_ne_zero (R := K)
  apply ofPowerSeries_injective (Γ := ℤ)
  simpa only [map_zero] using hx

/-- The Laurent characterization determines the parameter series uniquely. -/
theorem formalParameter_eq_iff (g : K⟦X⟧) :
    φ.formalParameter = g ↔ (g : K⸨X⸩) = W₁.functionFieldLaurentExpansion
      (φ.fieldPullback (-W₂.toAffine.genericX / W₂.toAffine.genericY)) := by
  rw [← coe_formalParameter]
  exact ⟨fun h ↦ congrArg (ofPowerSeries ℤ K) h.symm,
    fun h ↦ ofPowerSeries_injective h.symm⟩

/-- The identity isogeny induces the identity formal parameter. -/
@[simp]
theorem formalParameter_id (W : WeierstrassCurve K) :
    (id W.toAffine).formalParameter = PowerSeries.X := by
  apply (formalParameter_eq_iff _ _).mpr
  rw [id_fieldPullback, AlgHom.id_apply,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- Expanding the pulled-back function `-1/y₂` gives `w₂` evaluated at the formal parameter. -/
theorem coe_subst_formalW_formalParameter :
    ((PowerSeries.subst φ.formalParameter (formalW W₂) : K⟦X⟧) : K⸨X⸩) =
      W₁.functionFieldLaurentExpansion (φ.fieldPullback (-W₂.toAffine.genericY⁻¹)) := by
  let A := W₁.functionFieldLaurentExpansion.comp φ.fieldPullback
  have hyval : W₂.toAffine.infinityPlace W₂.toAffine.genericY = WithZero.exp 3 := by
    rw [Affine.genericY_def]
    exact Affine.infinityPlace.mk_Y W₂
  have hy : W₂.toAffine.genericY ≠ 0 := fun h ↦ by
    rw [h, map_zero] at hyval
    exact WithZero.exp_ne_zero hyval.symm
  have hv : Valued.v (A (-W₂.toAffine.genericY⁻¹)) < (1 : ℤᵐ⁰) := by
    have hlt : W₂.toAffine.infinityPlace (-W₂.toAffine.genericY⁻¹) < 1 := by
      rw [Valuation.map_neg, map_inv₀, hyval, ← WithZero.exp_neg, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by norm_num)
    exact (Valuation.isEquiv_iff_val_lt_one.mp φ.isEquiv_comap_expansion
      (x := -W₂.toAffine.genericY⁻¹)).mpr hlt
  obtain ⟨w, hw⟩ := (LaurentSeries.val_le_one_iff_eq_coe K _).mp hv.le
  have hw₀ : PowerSeries.constantCoeff w = 0 := by
    by_contra h
    have hunit := PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h)
    have hval := LaurentSeries.valuation_coe_of_isUnit hunit
    rw [hw] at hval
    exact hv.ne hval
  have heq : w = wEquationRHS W₂ φ.formalParameter w := by
    apply ofPowerSeries_injective (R := K) (Γ := ℤ)
    rw [← LaurentSeries.coe_algebraMap, algebraMap_wEquationRHS,
      LaurentSeries.coe_algebraMap, hw, coe_formalParameter]
    have h := congrArg A (W₂.wEquation_of_equation
      W₂.toAffine.equation_genericX_genericY hy)
    simpa only [wEquationRHS_def, map_add, map_mul, map_pow, AlgHom.commutes,
      neg_div, A, AlgHom.comp_apply] using h
  rw [← eq_subst_formalW_of_wEquation W₂ φ.constantCoeff_formalParameter hw₀ heq]
  exact hw

-- Not a simp rule: together with `coe_formalParameter` and substitution of `X`, it would loop.
/-- Pullback of rational functions becomes substitution by the isogeny's parameter series.
This identifies the completed local action with the original function-field map. -/
theorem functionFieldLaurentExpansion_fieldPullback (f : W₂.toAffine.FunctionField) :
    W₁.functionFieldLaurentExpansion (φ.fieldPullback f) =
      LaurentSeries.substAlgHom φ.constantCoeff_formalParameter φ.formalParameter_ne_zero
        (W₂.functionFieldLaurentExpansion f) := by
  let A := W₁.functionFieldLaurentExpansion.comp φ.fieldPullback
  let B := (LaurentSeries.substAlgHom φ.constantCoeff_formalParameter
    φ.formalParameter_ne_zero).comp W₂.functionFieldLaurentExpansion
  have hparam : A (-W₂.toAffine.genericX / W₂.toAffine.genericY) =
      B (-W₂.toAffine.genericX / W₂.toAffine.genericY) := by
    simp only [B, AlgHom.comp_apply, functionFieldLaurentExpansion_neg_genericX_div_genericY,
      LaurentSeries.substAlgHom_coe,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero'
        φ.constantCoeff_formalParameter)]
    exact φ.coe_formalParameter.symm
  have hw : A (-W₂.toAffine.genericY⁻¹) = B (-W₂.toAffine.genericY⁻¹) := by
    have hw₂ : W₂.functionFieldLaurentExpansion (-W₂.toAffine.genericY⁻¹) =
        (formalW W₂ : K⸨X⸩) := by
      simpa only [formalParameter_id, id_fieldPullback, AlgHom.id_apply,
        PowerSeries.X_subst] using (id W₂.toAffine).coe_subst_formalW_formalParameter.symm
    simp only [B, AlgHom.comp_apply, hw₂, LaurentSeries.substAlgHom_coe]
    exact φ.coe_subst_formalW_formalParameter.symm
  have hY : A W₂.toAffine.genericY = B W₂.toAffine.genericY := by
    simpa only [map_neg, map_inv₀, neg_inj, inv_inj] using hw
  have hX : A W₂.toAffine.genericX = B W₂.toAffine.genericX := by
    have hy : B W₂.toAffine.genericY ≠ 0 := by
      apply (map_ne_zero_iff B B.injective).mpr
      intro h
      have hv : W₂.toAffine.infinityPlace W₂.toAffine.genericY = WithZero.exp 3 := by
        rw [Affine.genericY_def]
        exact Affine.infinityPlace.mk_Y W₂
      rw [h, map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    simpa only [map_div₀, map_neg, hY, div_left_inj' hy, neg_inj] using hparam
  have hAB : A = B := AlgHom.toRingHom_injective
    (Affine.FunctionField.ringHom_ext (fun c ↦ by simp) hX hY)
  exact DFunLike.congr_fun hAB f

/-- Composition of isogenies induces composition of their formal parameter series. -/
@[simp]
theorem formalParameter_comp {W₃ : WeierstrassCurve K}
    (ψ : Isogeny W₂.toAffine W₃.toAffine) :
    (ψ.comp φ).formalParameter = PowerSeries.subst φ.formalParameter ψ.formalParameter := by
  apply ofPowerSeries_injective (R := K) (Γ := ℤ)
  rw [coe_formalParameter, comp_fieldPullback, AlgHom.comp_apply,
    φ.functionFieldLaurentExpansion_fieldPullback,
    ← ψ.coe_formalParameter, LaurentSeries.substAlgHom_coe]

end TauCeti.Isogeny
