/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.LaurentExpansion.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Inverse
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Neg
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic

/-!
# The formal power series of an isogeny

For an isogeny `φ : W₁ → W₂`, expand `φ*(-x₂/y₂)` at infinity on `W₁` in the
parameter `z₁ = -x₁/y₁`. Pointedness implies that this Laurent series is a power series
with zero constant coefficient. It is nonzero, including for inseparable isogenies.

`Isogeny.formalSeries` is this actual expansion, characterized by
`Isogeny.coe_formalSeries`. Pullback of every rational function is Laurent substitution
by this series (`Isogeny.functionFieldLaurentExpansion_fieldPullback`), which implies that
`Isogeny.formalSeries` is injective (`Isogeny.formalSeries_injective`). Identity, negation,
composition, and base change induce `X`, `formalInverse`, substitution, and coefficientwise map of
series, all without assuming ellipticity.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, IV.4.
-/

public section

open WeierstrassCurve HahnSeries
open scoped LaurentSeries PowerSeries WithZero

namespace TauCeti.Isogeny

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K}
  (φ : Isogeny W₁.toAffine W₂.toAffine)

private theorem exists_powerSeries_constantCoeff_zero_of_infinityPlace_lt_one
    (f : W₂.toAffine.FunctionField) (hf : W₂.toAffine.infinityPlace f < 1) :
    ∃ g : K⟦X⟧, PowerSeries.constantCoeff g = 0 ∧
      (g : K⸨X⸩) = W₁.functionFieldLaurentExpansion (φ.fieldPullback f) := by
  apply (W₁.exists_powerSeries_constantCoeff_zero_functionFieldLaurentExpansion_iff _).mpr
  exact (Valuation.isEquiv_iff_val_lt_one.mp φ.isEquiv_comap_infinityPlace).mpr hf

private theorem exists_powerSeries_parameter :
    ∃ g : K⟦X⟧, PowerSeries.constantCoeff g = 0 ∧
      (g : K⸨X⸩) = W₁.functionFieldLaurentExpansion
        (φ.fieldPullback (-W₂.toAffine.genericX / W₂.toAffine.genericY)) := by
  apply φ.exists_powerSeries_constantCoeff_zero_of_infinityPlace_lt_one
  rw [Affine.infinityPlace_neg_genericX_div_genericY, ← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.mpr (by norm_num)

/-- The expansion of the pulled-back target parameter `-x₂/y₂`, as a power series in `-x₁/y₁`. -/
noncomputable def formalSeries : K⟦X⟧ :=
  PowerSeries.mk fun n ↦ (W₁.functionFieldLaurentExpansion
    (φ.fieldPullback (-W₂.toAffine.genericX / W₂.toAffine.genericY))).coeff n

/-- The formal series is the Laurent expansion of the actual function-field pullback. -/
theorem coe_formalSeries :
    (φ.formalSeries : K⸨X⸩) = W₁.functionFieldLaurentExpansion
      (φ.fieldPullback (-W₂.toAffine.genericX / W₂.toAffine.genericY)) := by
  obtain ⟨g, _, hg⟩ := φ.exists_powerSeries_parameter
  rw [formalSeries, ← hg]
  congr 1
  ext n
  simp

/-- An isogeny's formal series has zero constant coefficient, because it maps infinity to
infinity. -/
-- Handle composites before `formalSeries_comp` rewrites them to substitutions.
@[simp↓]
theorem constantCoeff_formalSeries : PowerSeries.constantCoeff φ.formalSeries = 0 := by
  obtain ⟨g, hg₀, hg⟩ := φ.exists_powerSeries_parameter
  have h : φ.formalSeries = g := ofPowerSeries_injective (φ.coe_formalSeries.trans hg.symm)
  simpa only [h] using hg₀

/-- An isogeny's formal series is not the zero series, even in positive characteristic. -/
theorem formalSeries_ne_zero : φ.formalSeries ≠ 0 := by
  intro h
  have hz : -W₂.toAffine.genericX / W₂.toAffine.genericY = 0 := by
    apply φ.fieldPullback.injective
    apply W₁.functionFieldLaurentExpansion.injective
    simpa [h] using φ.coe_formalSeries.symm
  have hx := congrArg W₂.functionFieldLaurentExpansion hz
  rw [functionFieldLaurentExpansion_neg_genericX_div_genericY, map_zero] at hx
  apply PowerSeries.X_ne_zero (R := K)
  apply ofPowerSeries_injective (Γ := ℤ)
  simpa only [map_zero] using hx

/-- The Laurent characterization determines the parameter series uniquely. -/
theorem formalSeries_eq_iff (g : K⟦X⟧) :
    φ.formalSeries = g ↔ (g : K⸨X⸩) = W₁.functionFieldLaurentExpansion
      (φ.fieldPullback (-W₂.toAffine.genericX / W₂.toAffine.genericY)) := by
  rw [← coe_formalSeries]
  exact ⟨fun h ↦ congrArg (ofPowerSeries ℤ K) h.symm,
    fun h ↦ ofPowerSeries_injective h.symm⟩

/-- The identity isogeny induces the identity formal series. -/
@[simp]
theorem formalSeries_id (W : WeierstrassCurve K) :
    (id W.toAffine).formalSeries = PowerSeries.X := by
  apply (formalSeries_eq_iff _ _).mpr
  rw [id_fieldPullback, AlgHom.id_apply,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- Expanding the pulled-back function `-1/y₂` gives `w₂` evaluated at the formal series. -/
theorem coe_subst_formalW_formalSeries :
    ((PowerSeries.subst φ.formalSeries (formalW W₂) : K⟦X⟧) : K⸨X⸩) =
      W₁.functionFieldLaurentExpansion (φ.fieldPullback (-W₂.toAffine.genericY⁻¹)) := by
  let A := W₁.functionFieldLaurentExpansion.comp φ.fieldPullback
  have hlt : W₂.toAffine.infinityPlace (-W₂.toAffine.genericY⁻¹) < 1 := by
    rw [Valuation.map_neg, map_inv₀, Affine.infinityPlace_genericY,
      ← WithZero.exp_neg, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  obtain ⟨w, hw₀, hw⟩ :=
    φ.exists_powerSeries_constantCoeff_zero_of_infinityPlace_lt_one _ hlt
  have heq : w = wEquationRHS W₂ φ.formalSeries w := by
    apply ofPowerSeries_injective (R := K) (Γ := ℤ)
    rw [← LaurentSeries.coe_algebraMap, algebraMap_wEquationRHS,
      LaurentSeries.coe_algebraMap, hw, coe_formalSeries]
    have h := congrArg A (W₂.wEquation_of_equation W₂.toAffine.equation_genericX_genericY)
    simpa only [AlgHom.map_wEquationRHS, neg_div, A, AlgHom.comp_apply] using h
  rw [← eq_subst_formalW_of_wEquation W₂ φ.constantCoeff_formalSeries hw₀ heq]
  exact hw

-- Not a simp rule: together with `coe_formalSeries` and substitution of `X`, it would loop.
/-- Pullback of rational functions becomes substitution by the isogeny's parameter series.
This identifies the completed local action with the original function-field map. -/
theorem functionFieldLaurentExpansion_fieldPullback (f : W₂.toAffine.FunctionField) :
    W₁.functionFieldLaurentExpansion (φ.fieldPullback f) =
      LaurentSeries.substAlgHom φ.constantCoeff_formalSeries φ.formalSeries_ne_zero
        (W₂.functionFieldLaurentExpansion f) := by
  let A := W₁.functionFieldLaurentExpansion.comp φ.fieldPullback
  let B := (LaurentSeries.substAlgHom φ.constantCoeff_formalSeries
    φ.formalSeries_ne_zero).comp W₂.functionFieldLaurentExpansion
  have hparam : A (-W₂.toAffine.genericX / W₂.toAffine.genericY) =
      B (-W₂.toAffine.genericX / W₂.toAffine.genericY) := by
    simp only [B, AlgHom.comp_apply, functionFieldLaurentExpansion_neg_genericX_div_genericY,
      LaurentSeries.substAlgHom_coe,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero'
        φ.constantCoeff_formalSeries)]
    exact φ.coe_formalSeries.symm
  have hw : A (-W₂.toAffine.genericY⁻¹) = B (-W₂.toAffine.genericY⁻¹) := by
    simp only [B, AlgHom.comp_apply, functionFieldLaurentExpansion_neg_inv_genericY,
      LaurentSeries.substAlgHom_coe]
    exact φ.coe_subst_formalW_formalSeries.symm
  have hY : A W₂.toAffine.genericY = B W₂.toAffine.genericY := by
    simpa only [map_neg, map_inv₀, neg_inj, inv_inj] using hw
  have hX : A W₂.toAffine.genericX = B W₂.toAffine.genericX := by
    have hy : B W₂.toAffine.genericY ≠ 0 :=
      (map_ne_zero_iff B B.injective).mpr W₂.toAffine.genericY_ne_zero
    simpa only [map_div₀, map_neg, hY, div_left_inj₀ hy, neg_inj] using hparam
  have hAB : A = B := AlgHom.toRingHom_injective
    (Affine.FunctionField.ringHom_ext (fun c ↦ by simp) hX hY)
  exact DFunLike.congr_fun hAB f

/-- Composition of isogenies induces composition of their formal series. -/
@[simp]
theorem formalSeries_comp {W₃ : WeierstrassCurve K}
    (ψ : Isogeny W₂.toAffine W₃.toAffine) :
    (ψ.comp φ).formalSeries = PowerSeries.subst φ.formalSeries ψ.formalSeries := by
  apply ofPowerSeries_injective (R := K) (Γ := ℤ)
  rw [coe_formalSeries, comp_fieldPullback, AlgHom.comp_apply,
    φ.functionFieldLaurentExpansion_fieldPullback,
    ← ψ.coe_formalSeries, LaurentSeries.substAlgHom_coe]

/-- **An isogeny is uniquely determined by its formal power series**, with no ellipticity
hypothesis on either curve. -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (K := K) (W₁ := W₁) (W₂ := W₂)) := by
  intro φ ψ h
  have hfp (f : W₂.toAffine.FunctionField) : φ.fieldPullback f = ψ.fieldPullback f := by
    apply W₁.functionFieldLaurentExpansion.injective
    -- `injective` exposes `toRingHom`; restate as `AlgHom` application for `rw`.
    change W₁.functionFieldLaurentExpansion (φ.fieldPullback f) =
      W₁.functionFieldLaurentExpansion (ψ.fieldPullback f)
    rw [φ.functionFieldLaurentExpansion_fieldPullback,
      ψ.functionFieldLaurentExpansion_fieldPullback]
    simp only [h]
  refine Isogeny.ext (AlgHom.ext fun r ↦ ?_)
  have hr := hfp (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField r)
  rwa [fieldPullback_algebraMap, fieldPullback_algebraMap] at hr

-- Fire before `formalSeries_comp`/`formalSeries_map`/etc. expand the inner formal series.
@[simp↓]
theorem formalSeries_inj {φ ψ : Isogeny W₁.toAffine W₂.toAffine} :
    φ.formalSeries = ψ.formalSeries ↔ φ = ψ :=
  formalSeries_injective.eq_iff

private theorem fieldPullback_negIsogeny_genericY_eq (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).fieldPullback W.toAffine.genericY =
      -W.toAffine.genericY *
        (1 - algebraMap K W.toAffine.FunctionField W.a₁ *
            (-W.toAffine.genericX / W.toAffine.genericY) -
          algebraMap K W.toAffine.FunctionField W.a₃ * (-W.toAffine.genericY⁻¹)) := by
  have hy0 : W.toAffine.genericY ≠ 0 := W.toAffine.genericY_ne_zero
  rw [fieldPullback_negIsogeny_genericY, Affine.negY]
  simp only [Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₃]
  field_simp [hy0]
  ring

/-- **The formal series of `negIsogeny` is the geometric formal inverse `W.formalInverse`**, over
every Weierstrass curve and in every characteristic. -/
@[simp]
theorem formalSeries_negIsogeny (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).formalSeries = W.formalInverse := by
  apply (formalSeries_eq_iff _ _).mpr
  let x := W.toAffine.genericX
  let y := W.toAffine.genericY
  let z := -x / y
  let d := 1 - algebraMap K W.toAffine.FunctionField W.a₁ * z -
    algebraMap K W.toAffine.FunctionField W.a₃ * (-y⁻¹)
  have hnegY : (negIsogeny W.toAffine).fieldPullback y = -y * d :=
    fieldPullback_negIsogeny_genericY_eq W
  have hd0 : d ≠ 0 := right_ne_zero_of_mul <| hnegY ▸
    (map_ne_zero_iff _ (negIsogeny W.toAffine).fieldPullback.injective).mpr
      W.toAffine.genericY_ne_zero
  have hrat : (negIsogeny W.toAffine).fieldPullback z * d = -z := by
    -- Unfold `let z := -x / y` on the LHS only, keeping `-z` intact on the RHS.
    change (negIsogeny W.toAffine).fieldPullback (-x / y) * d = -z
    rw [map_div₀, map_neg, fieldPullback_negIsogeny_genericX, hnegY, ← div_div,
      div_mul_cancel₀ _ hd0, div_neg]
  have hexp := congrArg W.functionFieldLaurentExpansion hrat
  have hd_exp : W.functionFieldLaurentExpansion d = ofPowerSeries ℤ K (formalInverseDenom W) := by
    dsimp only [d, z, x, y]
    simp only [map_sub, map_one, map_mul, AlgHom.commutes,
      functionFieldLaurentExpansion_neg_genericX_div_genericY,
      functionFieldLaurentExpansion_neg_inv_genericY, HahnSeries.algebraMap_apply',
      PowerSeries.algebraMap_eq, formalInverseDenom_def]
  rw [map_mul, map_neg, hd_exp, W.functionFieldLaurentExpansion_neg_genericX_div_genericY,
    ← (negIsogeny W.toAffine).coe_formalSeries] at hexp
  have hu : ofPowerSeries ℤ K (formalInverseDenom W) *
      ofPowerSeries ℤ K (PowerSeries.invOfUnit (formalInverseDenom W) 1) = 1 := by
    rw [← map_mul, mul_invOfUnit_formalInverseDenom, map_one]
  rw [← (negIsogeny W.toAffine).coe_formalSeries, formalInverse_def, map_neg, map_mul]
  linear_combination -(ofPowerSeries ℤ K (PowerSeries.invOfUnit (formalInverseDenom W) 1)) * hexp +
    ofPowerSeries ℤ K (negIsogeny W.toAffine).formalSeries * hu

/-- **Base change of an isogeny maps the coefficients of its formal series.** -/
@[simp]
theorem formalSeries_map {L : Type*} [Field L] (σ : K →+* L) :
    (φ.map σ).formalSeries = PowerSeries.map σ φ.formalSeries := by
  apply ((φ.map σ).formalSeries_eq_iff (W₂ := W₂.map σ) _).mpr
  have h := congrArg (HahnSeries.mapRingHom σ) φ.coe_formalSeries
  rw [HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries,
    W₁.mapRingHom_functionFieldLaurentExpansion σ, ← φ.map_fieldPullback_map σ, map_div₀, map_neg,
    Affine.FunctionField.map_genericX, Affine.FunctionField.map_genericY] at h
  exact h

end TauCeti.Isogeny
