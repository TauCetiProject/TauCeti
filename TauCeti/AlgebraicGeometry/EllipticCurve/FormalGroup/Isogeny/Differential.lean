/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Basic
-- Proof-only: the source of an isogeny to an elliptic curve is elliptic.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
-- Proof-only: factorisation of every isogeny into a Frobenius power and a separable isogeny.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
-- Proof-only: Kähler differential relations carry across Laurent expansion.
import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Expansion

/-!
# The differential, linear term, and vanishing order of an isogeny's formal series

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`, with formal series
`φ.formalSeries ∈ K⟦X⟧` in the local parameter `z = -x / y` at the point at infinity. By
`TauCeti.Isogeny.existsUnique_pullbackDifferential_invariantDifferential_eq_smul`, `φ` pulls the
invariant differential `ω₂` of `W₂` back to `c • ω₁` for a unique constant `c ∈ K`.

Expanding `ω = dx / (2y + a₁x + a₃)` along `WeierstrassCurve.functionFieldLaurentExpansion`
identifies it in all characteristics with `(formalGroup W).invariantDifferential dX`
(`WeierstrassCurve.inv_mul_derivative_functionFieldLaurentExpansion_genericX`).
Carrying the Kähler relation `φ^*ω₂ = c • ω₁` across this expansion via the chain rule for Laurent
substitution gives the formal differential identity
`ω₂(φ(X)) · φ'(X) = c · ω₁(X)` in `K⟦X⟧`
(`TauCeti.Isogeny.subst_formalSeries_invariantDifferential_mul_derivative_of_eq_smul`),
whose constant term identifies `c` with the linear coefficient of `φ.formalSeries`
(`TauCeti.Isogeny.coeff_one_formalSeries_of_pullbackDifferential_eq_smul`), without any
characteristic or separability restriction.

Combining this linear-coefficient criterion for separability with the formal series `X ^ (p ^ r)`
of the iterated relative Frobenius (`TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny`)
and the Frobenius factorisation `φ = χ ∘ F^r` yields the exact vanishing order
`φ.formalSeries.order = φ.inseparableDegree` (`TauCeti.Isogeny.order_formalSeries`).

## Main results

* `WeierstrassCurve.inv_mul_derivative_functionFieldLaurentExpansion_genericX`:
  in Laurent coordinates at infinity, `(2y + a₁x + a₃)⁻¹ · x'` is the formal-group invariant
  differential `(formalGroup W).invariantDifferential`.
* `TauCeti.Isogeny.formalSeries_relativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny`: the `r`-fold relative Frobenius
  has formal series `X ^ (p ^ r)`.
* `TauCeti.Isogeny.coeff_one_formalSeries_of_pullbackDifferential_eq_smul` and
  `TauCeti.Isogeny.pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul`:
  `φ^*ω₂ = (coeff 1 φ.formalSeries) • ω₁`.
* `TauCeti.Isogeny.subst_formalSeries_invariantDifferential_mul_derivative`:
  `ω₂(φ(X)) · φ'(X) = (coeff 1 φ.formalSeries) · ω₁(X)` in `K⟦X⟧`.
* `TauCeti.Isogeny.isSeparable_iff_coeff_one_formalSeries_ne_zero` and
  `TauCeti.Isogeny.isSeparable_iff_order_formalSeries_eq_one`: differential and order criteria for
  separability on `φ.formalSeries`.
* `TauCeti.Isogeny.order_formalSeries`: `φ.formalSeries.order = φ.inseparableDegree`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.12, III.5, and IV.4.
-/

public section

open HahnSeries KaehlerDifferential WeierstrassCurve WeierstrassCurve.Affine
open scoped LaurentSeries PowerSeries

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- Under `functionFieldLaurentExpansion`, the generic ordinate expands to `-1 / w(X)`. -/
theorem functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW :
    W.functionFieldLaurentExpansion W.toAffine.genericY = -1 / (formalW W : K⸨X⸩) := by
  have hw : (formalW W : K⸨X⸩) = -(W.functionFieldLaurentExpansion W.toAffine.genericY)⁻¹ := by
    simpa [map_neg, map_inv₀] using W.functionFieldLaurentExpansion_neg_inv_genericY.symm
  rw [hw, div_neg, div_inv_eq_mul, neg_mul, one_mul, neg_neg]

/-- Under `functionFieldLaurentExpansion`, the generic abscissa expands to `X / w(X)`. -/
theorem functionFieldLaurentExpansion_genericX_eq_X_div_formalW :
    W.functionFieldLaurentExpansion W.toAffine.genericX =
      (PowerSeries.X : K⟦X⟧) / (formalW W : K⸨X⸩) := by
  have hy : W.functionFieldLaurentExpansion W.toAffine.genericY ≠ 0 :=
    (map_ne_zero W.functionFieldLaurentExpansion).mpr W.toAffine.genericY_ne_zero
  have hparam := W.functionFieldLaurentExpansion_neg_genericX_div_genericY
  rw [map_div₀, map_neg, div_eq_iff hy,
    W.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW] at hparam
  linear_combination -hparam

private theorem coe_formalInvariantDifferentialDenom :
    (W.formalInvariantDifferentialDenom : K⸨X⸩) =
      1 - algebraMap K K⸨X⸩ W.a₁ * (PowerSeries.X : K⟦X⟧) -
        algebraMap K K⸨X⸩ W.a₂ * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ 2 -
        2 * algebraMap K K⸨X⸩ W.a₃ * (formalW W : K⸨X⸩) -
        2 * algebraMap K K⸨X⸩ W.a₄ * (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) * (formalW W : K⸨X⸩)) -
        3 * algebraMap K K⸨X⸩ W.a₆ * (formalW W : K⸨X⸩) ^ 2 := by
  rw [formalInvariantDifferentialDenom_def]
  simp only [Algebra.smul_def, map_sub, map_one, map_mul, map_pow, map_ofNat,
    HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq]

/-- **Laurent expansion of the invariant differential at infinity**: for an elliptic curve `W` over
any field `K` (in arbitrary characteristic), `(2y + a₁x + a₃)⁻¹ · (e x)'` in `K⸨X⸩` is the formal
invariant differential `(formalGroup W).invariantDifferential`. -/
theorem inv_mul_derivative_functionFieldLaurentExpansion_genericX [W.IsElliptic] :
    (W.functionFieldLaurentExpansion (invariantDifferentialDenom W.toAffine))⁻¹ *
        _root_.LaurentSeries.derivative K (W.functionFieldLaurentExpansion W.toAffine.genericX) =
      ((formalGroup W).invariantDifferential : K⸨X⸩) := by
  let q : K⸨X⸩ := ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)
  let w : K⸨X⸩ := (formalW W : K⸨X⸩)
  have heq : w = wEquationRHS W q w := by
    simpa only [q, w, LaurentSeries.coe_algebraMap, algebraMap_wEquationRHS] using
      congrArg (algebraMap K⟦X⟧ K⸨X⸩) W.formalW_wEquation
  have hinv : ((formalGroup W).invariantDifferential : K⸨X⸩) *
      (W.formalInvariantDifferentialDenom : K⸨X⸩) = 1 := by
    rw [← map_mul, W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom,
      map_one]
  have hG := W.coe_formalInvariantDifferentialDenom ▸ right_ne_zero_of_mul_eq_one hinv
  have hdenom_ne : W.functionFieldLaurentExpansion (invariantDifferentialDenom W.toAffine) ≠ 0 :=
    (map_ne_zero W.functionFieldLaurentExpansion).mpr
      (invariantDifferentialDenom_ne_zero W.toAffine)
  have hdenom_eq : W.functionFieldLaurentExpansion (invariantDifferentialDenom W.toAffine) =
      (W⁄K⸨X⸩).toAffine.polynomialY.evalEval (q / w) (-1 / w) := by
    simp [invariantDifferentialDenom_def, Affine.evalEval_polynomialY, WeierstrassCurve.baseChange,
      W.functionFieldLaurentExpansion_genericX_eq_X_div_formalW,
      W.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW, map_ofNat, q, w]
  have hw : w ≠ 0 := fun hw0 ↦ (map_ne_zero W.functionFieldLaurentExpansion).mpr
    W.toAffine.genericY_ne_zero (by
      rw [W.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW,
        show (formalW W : K⸨X⸩) = w from rfl, hw0, div_zero])
  have hu : -2 + algebraMap K K⸨X⸩ W.a₁ * q + algebraMap K K⸨X⸩ W.a₃ * w ≠ 0 := fun hu0 ↦
    hdenom_ne <| by
      rw [hdenom_eq, Affine.evalEval_polynomialY]
      simp only [WeierstrassCurve.baseChange, map_a₁, map_a₃]
      rw [show 2 * (-1 / w) + algebraMap K K⸨X⸩ W.a₁ * (q / w) + algebraMap K K⸨X⸩ W.a₃ =
        (-2 + algebraMap K K⸨X⸩ W.a₁ * q + algebraMap K K⸨X⸩ W.a₃ * w) / w by field_simp,
        hu0, zero_div]
  have hkey := W.inv_evalEval_polynomialY_smul_derivation_div (TauCeti.laurentSeriesDerivation K)
    heq hG hu
  have hDq : _root_.LaurentSeries.derivative K q = 1 := by
    rw [show q = ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) from rfl, ← PowerSeries.coe_derivative,
      PowerSeries.derivative_X, PowerSeries.coe_one]
  rw [hdenom_eq, W.functionFieldLaurentExpansion_genericX_eq_X_div_formalW]
  simp only [TauCeti.laurentSeriesDerivation_apply, smul_eq_mul, hDq, mul_one] at hkey
  exact hkey.trans (inv_eq_of_mul_eq_one_left (W.coe_formalInvariantDifferentialDenom ▸ hinv))

end WeierstrassCurve

namespace TauCeti.Isogeny

section RelativeFrobenius

variable {K : Type*} [Field K] (p : ℕ) [ExpChar K p] (W : WeierstrassCurve K)

/-- **The formal series of the relative Frobenius isogeny is `X ^ p`.** -/
@[simp]
theorem formalSeries_relativeFrobeniusIsogeny :
    (relativeFrobeniusIsogeny p W.toAffine).formalSeries = PowerSeries.X ^ p := by
  apply (formalSeries_eq_iff _ _).mpr
  have hparam :
      -(W.map (frobenius K p)).toAffine.genericX / (W.map (frobenius K p)).toAffine.genericY =
        FunctionField.map W.toAffine (frobenius K p)
          (-W.toAffine.genericX / W.toAffine.genericY) := by
    simp [FunctionField.map_genericX, FunctionField.map_genericY]
  rw [hparam, fieldPullback_relativeFrobeniusIsogeny_map, map_pow, map_pow,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- **The formal series of the `r`-fold relative Frobenius isogeny is `X ^ (p ^ r)`.** -/
@[simp]
theorem formalSeries_iterateRelativeFrobeniusIsogeny (r : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W.toAffine r).formalSeries = PowerSeries.X ^ p ^ r := by
  apply (formalSeries_eq_iff _ _).mpr
  have hparam :
      -(W.map (iterateFrobenius K p r)).toAffine.genericX /
          (W.map (iterateFrobenius K p r)).toAffine.genericY =
        FunctionField.map W.toAffine (iterateFrobenius K p r)
          (-W.toAffine.genericX / W.toAffine.genericY) := by
    simp [FunctionField.map_genericX, FunctionField.map_genericY]
  rw [hparam, fieldPullback_iterateRelativeFrobeniusIsogeny_map, map_pow, map_pow,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

end RelativeFrobenius

section Differential

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

private theorem D_fieldPullback_genericX_of_eq_smul {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine) :
    D K W₁.toAffine.FunctionField (φ.fieldPullback W₂.toAffine.genericX) =
      (φ.fieldPullback (invariantDifferentialDenom W₂.toAffine) *
        algebraMap K W₁.toAffine.FunctionField c *
        (invariantDifferentialDenom W₁.toAffine)⁻¹) •
        D K W₁.toAffine.FunctionField W₁.toAffine.genericX := by
  have hden₂ : φ.fieldPullback (invariantDifferentialDenom W₂.toAffine) ≠ 0 :=
    (map_ne_zero φ.fieldPullback).mpr (invariantDifferentialDenom_ne_zero W₂.toAffine)
  have hc' := congrArg (φ.fieldPullback (invariantDifferentialDenom W₂.toAffine) • ·) hc
  simp only [invariantDifferential_def, pullbackDifferential_smul, pullbackDifferential_D,
    map_inv₀, smul_smul, mul_inv_cancel₀ hden₂, one_smul,
    ← algebraMap_smul W₁.toAffine.FunctionField c] at hc'
  simpa only [mul_assoc] using hc'

/-- **Formal differential identity for an isogeny**: if `φ^*ω₂ = c • ω₁` on Kähler differentials,
then `ω₂(φ(X)) · φ'(X) = c · ω₁(X)` in `K⟦X⟧`, in every characteristic and regardless of whether
`φ` is separable. -/
theorem subst_formalSeries_invariantDifferential_mul_derivative_of_eq_smul {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine) :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
        d⁄dX φ.formalSeries =
      PowerSeries.C c * (formalGroup W₁).invariantDifferential := by
  have := φ.isElliptic
  have hexp := TauCeti.derivative_algHom_eq_mul_of_D_eq_smul (e := W₁.functionFieldLaurentExpansion)
    (φ.D_fieldPullback_genericX_of_eq_smul hc)
  set S := LaurentSeries.substAlgHom φ.constantCoeff_formalSeries φ.formalSeries_ne_zero
  have hden₂_exp :
      W₁.functionFieldLaurentExpansion (φ.fieldPullback (invariantDifferentialDenom W₂.toAffine)) ≠
        0 :=
    (map_ne_zero W₁.functionFieldLaurentExpansion).mpr
      ((map_ne_zero φ.fieldPullback).mpr (invariantDifferentialDenom_ne_zero W₂.toAffine))
  have hlhs :
      (W₁.functionFieldLaurentExpansion
          (φ.fieldPullback (invariantDifferentialDenom W₂.toAffine)))⁻¹ *
        _root_.LaurentSeries.derivative K
          (W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericX)) =
        (((PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
          d⁄dX φ.formalSeries : K⟦X⟧)) : K⸨X⸩) := by
    rw [φ.functionFieldLaurentExpansion_fieldPullback,
      φ.functionFieldLaurentExpansion_fieldPullback,
      LaurentSeries.derivative_substAlgHom, ← mul_assoc, ← map_inv₀ S, ← map_mul S,
      W₂.inv_mul_derivative_functionFieldLaurentExpansion_genericX,
      LaurentSeries.substAlgHom_coe, PowerSeries.coe_mul, PowerSeries.coe_derivative]
  have hrhs :
      (W₁.functionFieldLaurentExpansion
          (φ.fieldPullback (invariantDifferentialDenom W₂.toAffine)))⁻¹ *
        (W₁.functionFieldLaurentExpansion
          (φ.fieldPullback (invariantDifferentialDenom W₂.toAffine) *
            algebraMap K W₁.toAffine.FunctionField c *
            (invariantDifferentialDenom W₁.toAffine)⁻¹) *
          _root_.LaurentSeries.derivative K
            (W₁.functionFieldLaurentExpansion W₁.toAffine.genericX)) =
        ((PowerSeries.C c * (formalGroup W₁).invariantDifferential : K⟦X⟧) : K⸨X⸩) := by
    simp only [map_mul, map_inv₀, AlgHom.commutes, mul_assoc]
    rw [inv_mul_cancel_left₀ hden₂_exp,
      W₁.inv_mul_derivative_functionFieldLaurentExpansion_genericX,
      HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, ← map_mul]
  apply ofPowerSeries_injective (R := K) (Γ := ℤ)
  rw [← hlhs, hexp, hrhs]

/-- **The pullback scalar on the invariant differential is the linear coefficient of
`φ.formalSeries`** (Silverman IV.4.2(b)): if `φ^*ω₂ = c • ω₁`, then `coeff 1 φ.formalSeries = c`,
in all characteristics. -/
theorem coeff_one_formalSeries_of_pullbackDifferential_eq_smul {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine) :
    PowerSeries.coeff 1 φ.formalSeries = c := by
  have h := congrArg PowerSeries.constantCoeff
    (φ.subst_formalSeries_invariantDifferential_mul_derivative_of_eq_smul hc)
  have hsub :
      PowerSeries.constantCoeff
          (PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential) = 1 := by
    change MvPowerSeries.constantCoeff _ = 1
    simpa using PowerSeries.constantCoeff_subst_of_constantCoeff_zero
      φ.constantCoeff_formalSeries (formalGroup W₂).invariantDifferential
  rw [map_mul, map_mul, hsub, one_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_derivative] at h
  simpa using h

/-- **An isogeny pulls the invariant differential back by the linear coefficient of its formal
series**: `φ^*ω₂ = (coeff 1 φ.formalSeries) • ω₁`. -/
theorem pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul :
    φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      PowerSeries.coeff 1 φ.formalSeries • invariantDifferential W₁.toAffine := by
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  rwa [φ.coeff_one_formalSeries_of_pullbackDifferential_eq_smul hc]

/-- **Formal differential identity for an isogeny**:
`ω₂(φ(X)) · φ'(X) = (coeff 1 φ.formalSeries) · ω₁(X)` in `K⟦X⟧`. -/
theorem subst_formalSeries_invariantDifferential_mul_derivative :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
        d⁄dX φ.formalSeries =
      PowerSeries.C (PowerSeries.coeff 1 φ.formalSeries) *
        (formalGroup W₁).invariantDifferential :=
  φ.subst_formalSeries_invariantDifferential_mul_derivative_of_eq_smul
    φ.pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul

/-- **Linear-coefficient criterion for separability**: an isogeny is separable if and only if the
linear coefficient of its formal series is nonzero. -/
theorem isSeparable_iff_coeff_one_formalSeries_ne_zero :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      PowerSeries.coeff 1 φ.formalSeries ≠ 0 :=
  φ.isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul
    φ.pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul

/-- **Order criterion for separability**: an isogeny is separable if and only if its formal series
has vanishing order `1`. -/
theorem isSeparable_iff_order_formalSeries_eq_one :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      φ.formalSeries.order = 1 := by
  rw [φ.isSeparable_iff_coeff_one_formalSeries_ne_zero,
    show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
  refine ⟨fun h ↦ ⟨h, fun i hi ↦ ?_⟩, fun h ↦ h.1⟩
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  simp

/-- A separable isogeny has formal series of order `1`. -/
theorem order_formalSeries_eq_one
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalSeries.order = 1 :=
  φ.isSeparable_iff_order_formalSeries_eq_one.mp ‹_›

/-- **The vanishing order of an isogeny's formal series equals its inseparable degree**:
factoring `φ = χ ∘ F^r` into an `r`-fold relative Frobenius (with formal series `X ^ (p ^ r)`) and a
separable isogeny `χ` (with formal series of order `1`) gives
`φ.formalSeries.order = p ^ r = φ.inseparableDegree`. -/
theorem order_formalSeries : φ.formalSeries.order = φ.inseparableDegree := by
  obtain ⟨p, _⟩ := ExpChar.exists K
  obtain ⟨r, χ, hsep, hχ⟩ := exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  have := hsep
  have hinsep : φ.inseparableDegree = p ^ r :=
    inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ
  have hordχ : (formalSeries (W₁ := W₁.map (iterateFrobenius K p r)) (W₂ := W₂) χ).order = 1 :=
    order_formalSeries_eq_one χ
  have hcomp :
      φ.formalSeries =
        PowerSeries.subst (PowerSeries.X ^ p ^ r)
          (formalSeries (W₁ := W₁.map (iterateFrobenius K p r)) (W₂ := W₂) χ) := by
    rw [← formalSeries_iterateRelativeFrobeniusIsogeny p W₁ r, ← formalSeries_comp, hχ]
  have hconst : PowerSeries.constantCoeff (PowerSeries.X ^ p ^ r : K⟦X⟧) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (expChar_pow_pos K p r).ne']
  rw [hcomp, PowerSeries.order_subst hconst, hordχ, mul_one, PowerSeries.order_pow,
    PowerSeries.order_X, nsmul_eq_mul, mul_one, hinsep, Nat.cast_pow]

end Differential

end TauCeti.Isogeny

end
