/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.LaurentExpansion
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Neg
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Basic
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic
-- Proof-only: the source of an isogeny to an elliptic curve is elliptic.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
-- Proof-only: every isogeny factors as a separable isogeny after an iterated relative Frobenius.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
-- Proof-only: Kähler differential relations pass through Laurent expansion.
import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Expansion
import TauCeti.RingTheory.PowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The formal power series of an isogeny

For an isogeny `φ : W₁ → W₂`, expand `φ*(-x₂/y₂)` at infinity on `W₁` in the
parameter `z₁ = -x₁/y₁`. Pointedness implies that this Laurent series is a power series
with zero constant coefficient. It is nonzero, including for inseparable isogenies, and
determines `φ` (`Isogeny.formalSeries_injective`).

`Isogeny.formalSeries` is this actual expansion, characterized by
`Isogeny.coe_formalSeries`. Pullback of every rational function is Laurent substitution
by this series (`Isogeny.functionFieldLaurentExpansion_fieldPullback`), and identity,
composition, negation, and relative Frobenius induce identity, composition, `formalInverse`,
and `X ^ p` on formal series.

Expanding the global invariant differential `ω = dx / (2y + a₁x + a₃)` along
`W.functionFieldLaurentExpansion` identifies `(e (2y + a₁x + a₃))⁻¹ · (e x)'` with
`(formalGroup W).invariantDifferential`
(`WeierstrassCurve.inv_mul_derivative_laurentExpansion_genericX`). Carrying `φ^* ω₂ = c • ω₁`
through Laurent differentiation and the chain rule gives
`P₂(f_φ) · f_φ' = (coeff 1 f_φ) • P₁` and `φ^* ω₂ = (coeff 1 f_φ) • ω₁`
(Silverman IV.4.2(a)), hence separability criteria on `coeff 1 f_φ` and `f_φ.order`, and
`φ.formalSeries.order = φ.inseparableDegree` (`Isogeny.order_formalSeries`, Silverman IV.4.3).

## Main results

* `TauCeti.Isogeny.formalSeries`, `TauCeti.Isogeny.coe_formalSeries`,
  `TauCeti.Isogeny.functionFieldLaurentExpansion_fieldPullback`,
  `TauCeti.Isogeny.formalSeries_injective`: definition, Laurent pullback characterization, and
  injectivity of the formal series of an isogeny.
* `TauCeti.Isogeny.formalSeries_id`, `TauCeti.Isogeny.formalSeries_comp`,
  `TauCeti.Isogeny.formalSeries_negIsogeny`,
  `TauCeti.Isogeny.formalSeries_relativeFrobeniusIsogeny`,
  `TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny`: formal series of `id`, `ψ ∘ φ`,
  `[-1]`, `F_{W/K}`, and `F_{W/K}^n`.
* `WeierstrassCurve.inv_mul_derivative_laurentExpansion_genericX`: in `K⸨X⸩`,
  `(e (2y + a₁x + a₃))⁻¹ * (e x)'` is `(formalGroup W).invariantDifferential`.
* `TauCeti.Isogeny.pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul`,
  `TauCeti.Isogeny.subst_invariantDifferential_mul_derivative_formalSeries`:
  `φ^* ω₂ = (coeff 1 f_φ) • ω₁` and `P₂(f_φ) · f_φ' = (coeff 1 f_φ) • P₁` (Silverman IV.4.2(a)).
* `TauCeti.Isogeny.isSeparable_iff_coeff_one_formalSeries_ne_zero`,
  `TauCeti.Isogeny.isSeparable_iff_order_formalSeries_eq_one`,
  `TauCeti.Isogeny.order_formalSeries`: differential separability criteria and
  `φ.formalSeries.order = φ.inseparableDegree` (Silverman IV.4.3).

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11–12, III.5, IV.4.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine HahnSeries
open scoped LaurentSeries PowerSeries WithZero

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- Under the Laurent expansion at infinity, `(formalW W : K⸨X⸩)` is nonzero. -/
private theorem coe_formalW_ne_zero : (W.formalW : K⸨X⸩) ≠ 0 := by
  rw [← W.functionFieldLaurentExpansion_neg_inv_genericY, map_neg, map_inv₀]
  exact neg_ne_zero.mpr (inv_ne_zero
    ((map_ne_zero W.functionFieldLaurentExpansion).mpr W.toAffine.genericY_ne_zero))

/-- Under the Laurent expansion at infinity, `genericY` expands to `-1 / w(X)`. -/
theorem functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW :
    W.functionFieldLaurentExpansion W.toAffine.genericY =
      -1 / (W.formalW : K⸨X⸩) := by
  have h := W.functionFieldLaurentExpansion_neg_inv_genericY
  rw [map_neg, map_inv₀] at h
  rw [neg_div, one_div, ← h, inv_neg, inv_inv, neg_neg]

/-- Under the Laurent expansion at infinity, `genericX` expands to `X / w(X)`. -/
theorem functionFieldLaurentExpansion_genericX_eq_X_div_formalW :
    W.functionFieldLaurentExpansion W.toAffine.genericX =
      ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) / (W.formalW : K⸨X⸩) := by
  have h := W.functionFieldLaurentExpansion_neg_genericX_div_genericY
  rw [map_div₀, map_neg, W.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW] at h
  have hw0 : (W.formalW : K⸨X⸩) ≠ 0 := W.coe_formalW_ne_zero
  calc W.functionFieldLaurentExpansion W.toAffine.genericX
      = -((-W.functionFieldLaurentExpansion W.toAffine.genericX / (-1 / (W.formalW : K⸨X⸩))) *
          (-1 / (W.formalW : K⸨X⸩))) := by
        field_simp [hw0]
    _ = ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) / (W.formalW : K⸨X⸩) := by
        rw [h]
        ring

/-- The formal denominator `formalInvariantDifferentialDenom` coerced to `K⸨X⸩`, together with its
nonvanishing. -/
private theorem coe_formalInvariantDifferentialDenom :
    ((W.formalInvariantDifferentialDenom : K⟦X⟧) : K⸨X⸩) =
        1 - algebraMap K K⸨X⸩ W.a₁ * (PowerSeries.X : K⟦X⟧) -
          algebraMap K K⸨X⸩ W.a₂ * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ 2 -
          2 * algebraMap K K⸨X⸩ W.a₃ * (W.formalW : K⸨X⸩) -
          2 * algebraMap K K⸨X⸩ W.a₄ * (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) * (W.formalW : K⸨X⸩)) -
          3 * algebraMap K K⸨X⸩ W.a₆ * (W.formalW : K⸨X⸩) ^ 2 ∧
      ((W.formalInvariantDifferentialDenom : K⟦X⟧) : K⸨X⸩) ≠ 0 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · simp only [formalInvariantDifferentialDenom_def, PowerSeries.smul_eq_C_mul,
      ← _root_.LaurentSeries.coe_algebraMap, ← PowerSeries.algebraMap_eq, map_sub, map_one,
      map_mul, map_pow, map_ofNat, ← IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩]
  · have h' : W.formalInvariantDifferentialDenom = 0 :=
      ofPowerSeries_injective (h.trans (map_zero _).symm)
    simpa [h'] using W.constantCoeff_formalInvariantDifferentialDenom.symm

/-- **The Laurent expansion of the global invariant differential is the formal-group invariant
differential**: in `K⸨X⸩`, `(e (2y + a₁x + a₃))⁻¹ * (e x)' = (formalGroup W).invariantDifferential`,
in every characteristic including `2`. -/
theorem inv_mul_derivative_laurentExpansion_genericX [W.IsElliptic] :
    (W.functionFieldLaurentExpansion (invariantDifferentialDenom W.toAffine))⁻¹ *
        _root_.LaurentSeries.derivative K
          (W.functionFieldLaurentExpansion W.toAffine.genericX) =
      ((formalGroup W).invariantDifferential : K⸨X⸩) := by
  set q : K⸨X⸩ := ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)
  set w : K⸨X⸩ := (W.formalW : K⸨X⸩)
  have hw0 : w ≠ 0 := W.coe_formalW_ne_zero
  have heq : w = wEquationRHS W q w := by
    dsimp only [q, w]
    rw [← _root_.LaurentSeries.coe_algebraMap, ← algebraMap_wEquationRHS,
      _root_.LaurentSeries.coe_algebraMap]
    exact congrArg (ofPowerSeries ℤ K) W.formalW_wEquation
  obtain ⟨hG_eq, hG0⟩ := W.coe_formalInvariantDifferentialDenom
  -- Nonvanishing of `2y + a₁x + a₃` on `W` supplies `-2 + a₁ q + a₃ w ≠ 0`, even in char `2`.
  have hden_eq : W.functionFieldLaurentExpansion (invariantDifferentialDenom W.toAffine) =
      (W⁄K⸨X⸩).toAffine.polynomialY.evalEval (q / w) (-1 / w) := by
    rw [invariantDifferentialDenom_def, map_add, map_add, map_mul, map_mul, map_ofNat,
      AlgHom.commutes, AlgHom.commutes, W.functionFieldLaurentExpansion_genericX_eq_X_div_formalW,
      W.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW, evalEval_polynomialY]
    simp only [WeierstrassCurve.baseChange, map_a₁, map_a₃, q, w]
  have hden0 : W.functionFieldLaurentExpansion (invariantDifferentialDenom W.toAffine) ≠ 0 :=
    (map_ne_zero W.functionFieldLaurentExpansion).mpr
      (invariantDifferentialDenom_ne_zero W.toAffine)
  have hu : -2 + algebraMap K K⸨X⸩ W.a₁ * q + algebraMap K K⸨X⸩ W.a₃ * w ≠ 0 :=
    fun hu0 ↦ hden0 <| by
      rw [hden_eq, evalEval_polynomialY]
      simp only [WeierstrassCurve.baseChange, map_a₁, map_a₃]
      have hdiv : 2 * (-1 / w) + algebraMap K K⸨X⸩ W.a₁ * (q / w) + algebraMap K K⸨X⸩ W.a₃ =
          (-2 + algebraMap K K⸨X⸩ W.a₁ * q + algebraMap K K⸨X⸩ W.a₃ * w) / w := by
        field_simp [hw0]
      rw [hdiv, hu0, zero_div]
  have key := W.inv_evalEval_polynomialY_smul_derivation_div (TauCeti.laurentSeriesDerivation K)
    heq (hG_eq ▸ hG0) hu
  have hDq : _root_.LaurentSeries.derivative K q = 1 := by simp [q, ofPowerSeries_X]
  rw [← hden_eq, ← hG_eq] at key
  rw [W.functionFieldLaurentExpansion_genericX_eq_X_div_formalW]
  simp only [TauCeti.laurentSeriesDerivation_apply, smul_eq_mul] at key
  rw [key, hDq, mul_one, inv_eq_iff_eq_inv]
  have hmul := congrArg (ofPowerSeries ℤ K)
    W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
  rw [map_mul, map_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul

end WeierstrassCurve

namespace TauCeti.Isogeny

section Basic

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
    rw [← _root_.LaurentSeries.coe_algebraMap, algebraMap_wEquationRHS,
      _root_.LaurentSeries.coe_algebraMap, hw, coe_formalSeries]
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

private theorem substAlgHom_congr {f g : K⟦X⟧} (h : f = g)
    (hf : PowerSeries.constantCoeff f = 0) (hf0 : f ≠ 0)
    (hg : PowerSeries.constantCoeff g = 0) (hg0 : g ≠ 0) :
    LaurentSeries.substAlgHom hf hf0 = LaurentSeries.substAlgHom hg hg0 := by
  subst h
  rfl

/-- **An isogeny is determined by its formal power series at infinity.** -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := by
  intro φ₁ φ₂ h
  refine Isogeny.ext (AlgHom.ext fun x ↦ ?_)
  rw [← φ₁.fieldPullback_algebraMap, ← φ₂.fieldPullback_algebraMap]
  have h1 : W₁.functionFieldLaurentExpansion (φ₁.fieldPullback (algebraMap _ _ x)) =
      W₁.functionFieldLaurentExpansion (φ₂.fieldPullback (algebraMap _ _ x)) := by
    rw [φ₁.functionFieldLaurentExpansion_fieldPullback,
      φ₂.functionFieldLaurentExpansion_fieldPullback, substAlgHom_congr h]
  exact W₁.functionFieldLaurentExpansion.injective h1

/-- Two isogenies have equal formal series if and only if they are equal. -/
@[simp]
theorem formalSeries_inj {φ₁ φ₂ : Isogeny W₁.toAffine W₂.toAffine} :
    φ₁.formalSeries = φ₂.formalSeries ↔ φ₁ = φ₂ :=
  formalSeries_injective.eq_iff

/-- **The negation isogeny expands to the formal inverse series.** -/
@[simp]
theorem formalSeries_negIsogeny (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).formalSeries = W.formalInverse := by
  apply (formalSeries_eq_iff _ _).mpr
  have hy : W.functionFieldLaurentExpansion W.toAffine.genericY = -(W.formalW : K⸨X⸩)⁻¹ := by
    rw [W.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW, neg_div, one_div]
  have hx : W.functionFieldLaurentExpansion W.toAffine.genericX =
      (PowerSeries.X : K⟦X⟧) * (W.formalW : K⸨X⸩)⁻¹ := by
    rw [W.functionFieldLaurentExpansion_genericX_eq_X_div_formalW, div_eq_mul_inv]
  have hy0 : W.functionFieldLaurentExpansion W.toAffine.genericY ≠ 0 :=
    (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr W.toAffine.genericY_ne_zero
  have hw0 : (W.formalW : K⸨X⸩) ≠ 0 := fun h0 ↦ hy0 (by rw [hy, h0, inv_zero, neg_zero])
  have hu : (W.formalInverseDenom : K⸨X⸩) *
      ((PowerSeries.invOfUnit W.formalInverseDenom 1 : K⟦X⟧) : K⸨X⸩) = 1 := by
    simpa only [← _root_.LaurentSeries.coe_algebraMap, map_mul, map_one] using
      congrArg (algebraMap K⟦X⟧ K⸨X⸩) W.mul_invOfUnit_formalInverseDenom
  have hu0 : (W.formalInverseDenom : K⸨X⸩) ≠ 0 := left_ne_zero_of_mul_eq_one hu
  have hc (c : K) : ((PowerSeries.C c : K⟦X⟧) : K⸨X⸩) = algebraMap K K⸨X⸩ c := by
    rw [_root_.LaurentSeries.algebraMap_apply, ← PowerSeries.coe_C]
  have hueq : (W.formalInverseDenom : K⸨X⸩) =
      1 - algebraMap K K⸨X⸩ W.a₁ * (PowerSeries.X : K⟦X⟧) -
        algebraMap K K⸨X⸩ W.a₃ * (W.formalW : K⸨X⸩) := by
    rw [formalInverseDenom_def, ← _root_.LaurentSeries.coe_algebraMap]
    simp only [map_sub, map_mul, map_one, _root_.LaurentSeries.coe_algebraMap, hc]
  have hinv : (W.formalInverse : K⸨X⸩) =
      -((PowerSeries.X : K⟦X⟧) *
        ((PowerSeries.invOfUnit W.formalInverseDenom 1 : K⟦X⟧) : K⸨X⸩)) := by
    rw [formalInverse_def, ← _root_.LaurentSeries.coe_algebraMap, map_neg, map_mul]
  rw [map_div₀, map_neg, fieldPullback_negIsogeny_genericX, fieldPullback_negIsogeny_genericY,
    Affine.negY, map_div₀, map_neg]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
    map_sub, map_neg, map_mul, AlgHom.commutes, hx, hy, neg_neg, hinv]
  have hden : (W.formalW : K⸨X⸩)⁻¹ -
      algebraMap K K⸨X⸩ W.a₁ * ((PowerSeries.X : K⟦X⟧) * (W.formalW : K⸨X⸩)⁻¹) -
      algebraMap K K⸨X⸩ W.a₃ = (W.formalW : K⸨X⸩)⁻¹ * (W.formalInverseDenom : K⸨X⸩) := by
    rw [hueq]; field_simp
  rw [hden, eq_div_iff (mul_ne_zero (inv_ne_zero hw0) hu0)]
  linear_combination -((PowerSeries.X : K⟦X⟧) * (W.formalW : K⸨X⸩)⁻¹) * hu

end Basic

/-! ### Invariant differential and linear coefficient -/

section Differential

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- Rewrite `φ^* ω₂ = c • ω₁` as an explicit scalar relation between `d(φ^* x₂)` and `d x₁`. -/
private theorem kaehler_D_fieldPullback_genericX_of_eq_smul {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine) :
    KaehlerDifferential.D K W₁.toAffine.FunctionField
        (φ.fieldPullback W₂.toAffine.genericX) =
      (φ.fieldPullback (invariantDifferentialDenom W₂.toAffine) *
        algebraMap K W₁.toAffine.FunctionField c *
        (invariantDifferentialDenom W₁.toAffine)⁻¹) •
        KaehlerDifferential.D K W₁.toAffine.FunctionField W₁.toAffine.genericX := by
  have hd₂0 : φ.fieldPullback (invariantDifferentialDenom W₂.toAffine) ≠ 0 :=
    (map_ne_zero φ.fieldPullback).mpr (invariantDifferentialDenom_ne_zero W₂.toAffine)
  rw [invariantDifferential_def, invariantDifferential_def, pullbackDifferential_smul,
    pullbackDifferential_D, map_inv₀, ← algebraMap_smul W₁.toAffine.FunctionField c,
    smul_smul] at hc
  calc KaehlerDifferential.D K W₁.toAffine.FunctionField (φ.fieldPullback W₂.toAffine.genericX)
      = φ.fieldPullback (invariantDifferentialDenom W₂.toAffine) •
          ((φ.fieldPullback (invariantDifferentialDenom W₂.toAffine))⁻¹ •
            KaehlerDifferential.D K W₁.toAffine.FunctionField
              (φ.fieldPullback W₂.toAffine.genericX)) := by
        rw [smul_smul, mul_inv_cancel₀ hd₂0, one_smul]
    _ = _ := by rw [hc, smul_smul, mul_assoc]

/-- **Pullback of the formal invariant differential along an isogeny**: if `φ^* ω₂ = c • ω₁`, then
`P₂(f_φ) · f_φ' = c • P₁` in `K⟦X⟧`, where `P_i` is the normalised invariant differential of
`formalGroup W_i` and `f_φ = φ.formalSeries`. -/
theorem subst_invariantDifferential_mul_derivative_formalSeries_of_eq_smul {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine) :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
        PowerSeries.derivative φ.formalSeries =
      c • (formalGroup W₁).invariantDifferential := by
  have : W₁.IsElliptic := φ.isElliptic
  have hexp := TauCeti.derivative_algHom_eq_mul_of_D_eq_smul
    (e := W₁.functionFieldLaurentExpansion) (φ.kaehler_D_fieldPullback_genericX_of_eq_smul hc)
  have hed₂0 : W₁.functionFieldLaurentExpansion
      (φ.fieldPullback (invariantDifferentialDenom W₂.toAffine)) ≠ 0 :=
    (map_ne_zero W₁.functionFieldLaurentExpansion).mpr
      ((map_ne_zero φ.fieldPullback).mpr (invariantDifferentialDenom_ne_zero W₂.toAffine))
  have hlhs : (W₁.functionFieldLaurentExpansion
        (φ.fieldPullback (invariantDifferentialDenom W₂.toAffine)))⁻¹ *
      _root_.LaurentSeries.derivative K
        (W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericX)) =
      ((PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
        PowerSeries.derivative φ.formalSeries : K⟦X⟧) : K⸨X⸩) := by
    rw [φ.functionFieldLaurentExpansion_fieldPullback,
      φ.functionFieldLaurentExpansion_fieldPullback,
      TauCeti.LaurentSeries.derivative_substAlgHom, ← map_inv₀, ← mul_assoc, ← map_mul,
      W₂.inv_mul_derivative_laurentExpansion_genericX, TauCeti.LaurentSeries.substAlgHom_coe,
      PowerSeries.coe_mul, PowerSeries.coe_derivative]
  have hrhs : (W₁.functionFieldLaurentExpansion
        (φ.fieldPullback (invariantDifferentialDenom W₂.toAffine)))⁻¹ *
      (W₁.functionFieldLaurentExpansion
        (φ.fieldPullback (invariantDifferentialDenom W₂.toAffine) *
          algebraMap K W₁.toAffine.FunctionField c *
          (invariantDifferentialDenom W₁.toAffine)⁻¹) *
        _root_.LaurentSeries.derivative K
          (W₁.functionFieldLaurentExpansion W₁.toAffine.genericX)) =
      ((c • (formalGroup W₁).invariantDifferential : K⟦X⟧) : K⸨X⸩) := by
    rw [map_mul, map_mul, map_inv₀, AlgHom.commutes]
    calc _ = algebraMap K K⸨X⸩ c *
          ((W₁.functionFieldLaurentExpansion (invariantDifferentialDenom W₁.toAffine))⁻¹ *
            _root_.LaurentSeries.derivative K
              (W₁.functionFieldLaurentExpansion W₁.toAffine.genericX)) := by
            field_simp [hed₂0]
      _ = ((c • (formalGroup W₁).invariantDifferential : K⟦X⟧) : K⸨X⸩) := by
            rw [W₁.inv_mul_derivative_laurentExpansion_genericX, Algebra.smul_def,
              ← _root_.LaurentSeries.coe_algebraMap,
              IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩ c, ← map_mul]
  apply ofPowerSeries_injective (Γ := ℤ) (R := K)
  rw [← hlhs, hexp, hrhs]

/-- **The pullback scalar on the invariant differential is the linear coefficient of `f_φ`**
(Silverman IV.4.2(a)): if `φ^* ω₂ = c • ω₁`, then `c = coeff 1 φ.formalSeries`. -/
theorem eq_coeff_one_formalSeries_of_pullbackDifferential_eq_smul {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine) :
    c = PowerSeries.coeff 1 φ.formalSeries := by
  have h := congrArg PowerSeries.constantCoeff
    (φ.subst_invariantDifferential_mul_derivative_formalSeries_of_eq_smul hc)
  have hc₂ := PowerSeries.constantCoeff_subst_of_constantCoeff_zero φ.constantCoeff_formalSeries
    (formalGroup W₂).invariantDifferential
  rw [Algebra.algebraMap_self_apply, FormalGroup.constantCoeff_invariantDifferential] at hc₂
  -- `constantCoeff_subst_of_constantCoeff_zero` uses the `MvPowerSeries Unit` constant coefficient.
  have hc₂' : PowerSeries.constantCoeff
      (PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential) = 1 := hc₂
  rw [map_mul, hc₂', one_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative] at h
  simpa [Algebra.smul_def, FormalGroup.constantCoeff_invariantDifferential] using h.symm

/-- **An isogeny pulls the invariant differential back by the linear coefficient of its formal
series** (Silverman IV.4.2(a)): `φ^* ω₂ = (coeff 1 φ.formalSeries) • ω₁`. -/
theorem pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul :
    φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      PowerSeries.coeff 1 φ.formalSeries • invariantDifferential W₁.toAffine := by
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  rwa [φ.eq_coeff_one_formalSeries_of_pullbackDifferential_eq_smul hc] at hc

/-- **The formal invariant differential transforms by `f_φ'`**:
`P₂(f_φ) · f_φ' = (coeff 1 f_φ) • P₁`. -/
theorem subst_invariantDifferential_mul_derivative_formalSeries :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
        PowerSeries.derivative φ.formalSeries =
      PowerSeries.coeff 1 φ.formalSeries • (formalGroup W₁).invariantDifferential :=
  φ.subst_invariantDifferential_mul_derivative_formalSeries_of_eq_smul
    φ.pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul

/-- **An isogeny is separable if and only if the linear coefficient of its formal series is
nonzero** (Silverman IV.4.2(a)). -/
theorem isSeparable_iff_coeff_one_formalSeries_ne_zero :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      PowerSeries.coeff 1 φ.formalSeries ≠ 0 :=
  φ.isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul
    φ.pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul

/-- **An isogeny is separable if and only if its formal series has order one.** -/
theorem isSeparable_iff_order_formalSeries_eq_one :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      φ.formalSeries.order = 1 := by
  -- Express `1 : ℕ∞` as `(1 : ℕ)` to match `PowerSeries.order_eq_nat`.
  rw [φ.isSeparable_iff_coeff_one_formalSeries_ne_zero, show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl,
    PowerSeries.order_eq_nat]
  refine ⟨fun h ↦ ⟨h, fun i hi ↦ ?_⟩, And.left⟩
  obtain rfl : i = 0 := by omega
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  exact φ.constantCoeff_formalSeries

end Differential

/-! ### Relative Frobenius and the order of the formal series -/

section RelativeFrobenius

variable {K : Type*} [Field K] (p : ℕ) [ExpChar K p] (W : WeierstrassCurve K)

/-- **The formal series of the `n`-fold relative Frobenius is `X ^ p ^ n`.** No ellipticity
hypothesis is required. -/
@[simp]
theorem formalSeries_iterateRelativeFrobeniusIsogeny (n : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W.toAffine n).formalSeries = PowerSeries.X ^ p ^ n := by
  apply (formalSeries_eq_iff (W₁ := W) (W₂ := W.map (iterateFrobenius K p n)) _ _).mpr
  have hparam : -(W.map (iterateFrobenius K p n)).toAffine.genericX /
      (W.map (iterateFrobenius K p n)).toAffine.genericY =
      FunctionField.map W.toAffine (iterateFrobenius K p n)
        (-W.toAffine.genericX / W.toAffine.genericY) := by
    rw [map_div₀, map_neg, FunctionField.map_genericX, FunctionField.map_genericY]
  rw [hparam, fieldPullback_iterateRelativeFrobeniusIsogeny_map, map_pow, map_pow,
    W.functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- **The formal series of the relative Frobenius isogeny is `X ^ p`** (Silverman IV.4). No
ellipticity hypothesis is required. -/
@[simp]
theorem formalSeries_relativeFrobeniusIsogeny :
    (relativeFrobeniusIsogeny p W.toAffine).formalSeries = PowerSeries.X ^ p := by
  apply (formalSeries_eq_iff (W₁ := W) (W₂ := W.map (frobenius K p)) _ _).mpr
  have hparam : -(W.map (frobenius K p)).toAffine.genericX /
      (W.map (frobenius K p)).toAffine.genericY =
      FunctionField.map W.toAffine (frobenius K p)
        (-W.toAffine.genericX / W.toAffine.genericY) := by
    rw [map_div₀, map_neg, FunctionField.map_genericX, FunctionField.map_genericY]
  rw [hparam, fieldPullback_relativeFrobeniusIsogeny_map, map_pow, map_pow,
    W.functionFieldLaurentExpansion_neg_genericX_div_genericY]

end RelativeFrobenius

/-- **The order of an isogeny's formal series is its inseparable degree** (Silverman IV.4.3):
factoring `φ = χ ∘ F^r` with `χ` separable and `deg_i φ = p ^ r` rewrites `φ.formalSeries` as
`χ.formalSeries(X ^ p ^ r)`, where `χ.formalSeries` has order `1`. -/
@[simp]
theorem order_formalSeries {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalSeries.order = φ.inseparableDegree := by
  set p := ringExpChar K
  obtain ⟨r, χ, hχ, rfl⟩ := exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  have hr : (χ.comp (iterateRelativeFrobeniusIsogeny p W₁.toAffine r)).inseparableDegree = p ^ r :=
    inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq (r := r) rfl
  have hordχ : (formalSeries (W₁ := W₁.map (iterateFrobenius K p r)) (W₂ := W₂) χ).order = 1 :=
    (isSeparable_iff_order_formalSeries_eq_one
      (W₁ := W₁.map (iterateFrobenius K p r)) (W₂ := W₂) χ).mp hχ
  have hc₀ : PowerSeries.constantCoeff
      (iterateRelativeFrobeniusIsogeny p W₁.toAffine r).formalSeries = 0 :=
    constantCoeff_formalSeries (W₁ := W₁) (W₂ := W₁.map (iterateFrobenius K p r)) _
  rw [hr, formalSeries_comp (W₁ := W₁) (W₂ := W₁.map (iterateFrobenius K p r)) (W₃ := W₂),
    PowerSeries.order_subst hc₀, hordχ, mul_one,
    formalSeries_iterateRelativeFrobeniusIsogeny, PowerSeries.order_X_pow]

end TauCeti.Isogeny
