/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.LaurentExpansion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Basic
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified

/-!
# The formal power series of an isogeny

For an isogeny `φ : W₁ → W₂` of Weierstrass curves over a field `K`, expand `φ*(-x₂/y₂)` at
infinity on `W₁` in the parameter `z₁ = -x₁/y₁`. Pointedness implies that this Laurent series is a
power series with zero constant coefficient. It is nonzero, including for inseparable isogenies.

`Isogeny.formalSeries` is this actual expansion, characterized by `Isogeny.coe_formalSeries`.
Pullback of every rational function is Laurent substitution by this series
(`Isogeny.functionFieldLaurentExpansion_fieldPullback`), so an isogeny is determined by its formal
series (`Isogeny.formalSeries_injective`), identity and composition induce identity and composition
of series, base change along `σ : K →+* L` maps the coefficients (`Isogeny.formalSeries_map`), and
the `n`-fold relative Frobenius induces `X ^ p ^ n`
(`Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny`), all without assuming ellipticity.

When the target curve `W₂` is elliptic, a separable isogeny is unramified at infinity
(`TauCeti.Isogeny.ramificationIdx_eq_one`), so `φ.formalSeries` has order `1`. Factoring an
arbitrary isogeny as `φ = χ ∘ F^r` with `χ` separable and `p ^ r = deg_i φ` gives
`φ.formalSeries.order = φ.inseparableDegree` (`Isogeny.order_formalSeries`), in all characteristics
and without assuming `K` is perfect; in particular `φ` is separable if and only if the linear
coefficient of `φ.formalSeries` is nonzero
(`Isogeny.coeff_one_formalSeries_ne_zero_iff_isSeparable`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11–12, II.4.2,
  III.4.10, III.5 and IV.4.
-/

public section

open WeierstrassCurve HahnSeries
open scoped LaurentSeries PowerSeries WithZero

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

/-- An isogeny is determined by its formal power series. -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := by
  intro φ₁ φ₂ h
  have hsub {g₁ g₂ : K⟦X⟧} (hg : g₁ = g₂) (hc₁ : PowerSeries.constantCoeff g₁ = 0) (hn₁ : g₁ ≠ 0)
      (hc₂ : PowerSeries.constantCoeff g₂ = 0) (hn₂ : g₂ ≠ 0) :
      LaurentSeries.substAlgHom hc₁ hn₁ = LaurentSeries.substAlgHom hc₂ hn₂ := by
    subst hg
    rfl
  refine Isogeny.ext (AlgHom.ext fun x ↦ W₁.functionFieldLaurentExpansion.injective ?_)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← fieldPullback_algebraMap, ← fieldPullback_algebraMap,
    φ₁.functionFieldLaurentExpansion_fieldPullback,
    φ₂.functionFieldLaurentExpansion_fieldPullback,
    hsub h]

/-- Two isogenies are equal if and only if they have the same formal power series. -/
@[simp]
theorem formalSeries_inj {φ₁ φ₂ : Isogeny W₁.toAffine W₂.toAffine} :
    φ₁.formalSeries = φ₂.formalSeries ↔ φ₁ = φ₂ :=
  formalSeries_injective.eq_iff

/-- Composition of isogenies induces composition of their formal series. -/
@[simp]
theorem formalSeries_comp {W₃ : WeierstrassCurve K}
    (ψ : Isogeny W₂.toAffine W₃.toAffine) :
    (ψ.comp φ).formalSeries = PowerSeries.subst φ.formalSeries ψ.formalSeries := by
  apply ofPowerSeries_injective (R := K) (Γ := ℤ)
  rw [coe_formalSeries, comp_fieldPullback, AlgHom.comp_apply,
    φ.functionFieldLaurentExpansion_fieldPullback,
    ← ψ.coe_formalSeries, LaurentSeries.substAlgHom_coe]

end Basic

/-! ### Base change and relative Frobenius -/

section BaseChangeAndFrobenius

variable {K L : Type*} [Field K] [Field L]

/-- **Base change of an isogeny maps the coefficients of its formal series.** -/
@[simp]
theorem formalSeries_map {W₁ W₂ : WeierstrassCurve K} (φ : Isogeny W₁.toAffine W₂.toAffine)
    (σ : K →+* L) :
    (φ.map σ).formalSeries = PowerSeries.map σ φ.formalSeries := by
  apply (formalSeries_eq_iff _ _).mpr
  rw [← Affine.FunctionField.map_neg_genericX_div_genericY, map_fieldPullback_map,
    functionFieldLaurentExpansion_map, ← φ.coe_formalSeries, HahnSeries.mapRingHom_apply,
    map_ofPowerSeries]

/-- **The `n`-fold relative Frobenius induces `X ^ p ^ n` on the formal parameter.** -/
@[simp]
theorem formalSeries_iterateRelativeFrobeniusIsogeny (p : ℕ) [ExpChar K p]
    (W : WeierstrassCurve K) (n : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W.toAffine n).formalSeries = PowerSeries.X ^ p ^ n := by
  apply (formalSeries_eq_iff _ _).mpr
  rw [← Affine.FunctionField.map_neg_genericX_div_genericY,
    fieldPullback_iterateRelativeFrobeniusIsogeny_map, map_pow, map_pow,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- **The relative Frobenius isogeny induces `X ^ p` on the formal parameter.** -/
@[simp]
theorem formalSeries_relativeFrobeniusIsogeny (p : ℕ) [ExpChar K p] (W : WeierstrassCurve K) :
    (relativeFrobeniusIsogeny p W.toAffine).formalSeries = PowerSeries.X ^ p := by
  apply (formalSeries_eq_iff _ _).mpr
  rw [← Affine.FunctionField.map_neg_genericX_div_genericY,
    fieldPullback_relativeFrobeniusIsogeny_map, map_pow, map_pow,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

end BaseChangeAndFrobenius

/-! ### Order and inseparable degree -/

section Order

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **A separable isogeny onto an elliptic curve has formal series of order `1`**, since it is
unramified at infinity. -/
theorem order_formalSeries_eq_one_of_isSeparable
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalSeries.order = 1 := by
  have := φ.isElliptic
  let _ : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    φ.fieldPullback.toRingHom.toAlgebra
  have hfp : ∀ z, algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField z =
      φ.fieldPullback z := fun _ ↦ rfl
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback hfp
  have := φ.finiteDimensional_functionField hfp
  have hrest : (Place.infinity W₁.toAffine).restrict K W₂.toAffine.FunctionField =
      Place.infinity W₂.toAffine := by
    rw [Place.restrict_eq_iff_isEquiv_comap, Place.valuation_infinity, Place.valuation_infinity]
    exact φ.isEquiv_comap_infinityPlace
  have hval := Place.valuation_algebraMap_restrict K W₂.toAffine.FunctionField
    (Place.infinity W₁.toAffine) (-W₂.toAffine.genericX / W₂.toAffine.genericY)
  rw [hfp, hrest, φ.ramificationIdx_eq_one hfp (Place.infinity W₁.toAffine), pow_one,
    Place.valuation_infinity, Place.valuation_infinity,
    Affine.infinityPlace_neg_genericX_div_genericY,
    ← W₁.valuation_functionFieldLaurentExpansion, ← φ.coe_formalSeries,
    TauCeti.LaurentSeries.valuation_coe φ.formalSeries_ne_zero] at hval
  have hord : φ.formalSeries.order.toNat = 1 := by
    have hinj := WithZero.exp_inj.mp hval
    omega
  rw [← PowerSeries.coe_toNat_order φ.formalSeries_ne_zero, hord, Nat.cast_one]

/-- **For an elliptic target `W₂`, the order of an isogeny's formal power series equals its
inseparable degree** (Silverman II.2.12, III.4.10(c) and IV.4). -/
@[simp]
theorem order_formalSeries : φ.formalSeries.order = φ.inseparableDegree := by
  set p := ringExpChar K
  obtain ⟨r, χ, hsep, hχ⟩ := exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  rw [φ.inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ, ← hχ,
    formalSeries_comp (iterateRelativeFrobeniusIsogeny p W₁.toAffine r) χ,
    PowerSeries.order_subst
      (iterateRelativeFrobeniusIsogeny p W₁.toAffine r).constantCoeff_formalSeries,
    formalSeries_iterateRelativeFrobeniusIsogeny, χ.order_formalSeries_eq_one_of_isSeparable,
    mul_one, PowerSeries.order_X_pow]

/-- **An isogeny onto an elliptic curve has formal series of order `1` if and only if it is
separable.** -/
theorem order_formalSeries_eq_one_iff_isSeparable :
    φ.formalSeries.order = 1 ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField := by
  rw [φ.order_formalSeries, ← Nat.cast_one, Nat.cast_inj,
    φ.inseparableDegree_eq_one_iff_isSeparable]

/-- **An isogeny onto an elliptic curve is separable if and only if the linear coefficient of its
formal series is nonzero** (Silverman II.4.2(c), III.5 and IV.4.2(b)). -/
theorem coeff_one_formalSeries_ne_zero_iff_isSeparable :
    PowerSeries.coeff 1 φ.formalSeries ≠ 0 ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField := by
  rw [← φ.order_formalSeries_eq_one_iff_isSeparable]
  constructor
  · intro h1
    refine le_antisymm ?_ (PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
      φ.constantCoeff_formalSeries)
    exact PowerSeries.order_le (n := 1) h1
  · intro hord
    have hto : φ.formalSeries.order.toNat = 1 := by simp [hord]
    exact hto ▸ PowerSeries.coeff_order φ.formalSeries_ne_zero

end Order

end TauCeti.Isogeny
