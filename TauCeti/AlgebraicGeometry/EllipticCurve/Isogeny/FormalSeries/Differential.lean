/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.RingTheory.LaurentSeries.Basic
import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Expansion
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Differentials, separability, and order of the formal series of an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`. By
`TauCeti.Isogeny.existsUnique_pullbackDifferential_invariantDifferential_eq_smul`, `φ` pulls back
the invariant differential `ω₂` of `W₂` to `c • ω₁` for a unique constant `c ∈ K`. Expanding both
sides at the point at infinity via `WeierstrassCurve.functionFieldLaurentExpansion` and comparing
with the formal-group invariant differential identifies `c` with the linear coefficient of
`φ.formalSeries` (Silverman IV.4.2(a)):
`φ^* ω₂ = (PowerSeries.coeff 1 φ.formalSeries) • ω₁`, and on formal-group invariant differentials
`(P₂ ∘ φ.formalSeries) · (φ.formalSeries)' = (PowerSeries.coeff 1 φ.formalSeries) • P₁`.

Combining this with the differential criterion for separability (`φ^* ω₂ ≠ 0`) and the
factorisation `φ = χ ∘ F^r` into a separable isogeny after an iterated relative Frobenius
(`formalSeries = X ^ (p ^ r)`) yields Silverman IV.4.3:
* `φ` is separable if and only if `PowerSeries.coeff 1 φ.formalSeries ≠ 0`, if and only if
  `φ.formalSeries.order = 1`; a separable isogeny therefore induces a `FormalGroupIso` between the
  formal groups;
* `φ.formalSeries.order = φ.inseparableDegree` over every field `K`.

## Main definitions

* `TauCeti.Isogeny.formalGroupIso`: the formal-group isomorphism induced by a separable isogeny.

## Main results

* `TauCeti.Isogeny.formalSeries_relativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny`: the formal series of relative
  Frobenius and its `n`-th iterate are `X ^ p` and `X ^ (p ^ n)`.
* `TauCeti.Isogeny.coeff_one_formalSeries_eq_of_pullbackDifferential_eq_smul` and
  `TauCeti.Isogeny.pullbackDifferential_invariantDifferential_eq_smul`: `φ^* ω₂ = c • ω₁` with
  `c = PowerSeries.coeff 1 φ.formalSeries`.
* `TauCeti.Isogeny.subst_formalSeries_invariantDifferential_mul_derivative`: pullback of the
  formal-group invariant differential along `φ.formalSeries`.
* `TauCeti.Isogeny.isSeparable_iff_coeff_one_formalSeries_ne_zero` and
  `TauCeti.Isogeny.isSeparable_iff_order_formalSeries_eq_one`: differential and order criteria on
  `φ.formalSeries` for separability of `φ`.
* `TauCeti.Isogeny.order_formalSeries_eq_inseparableDegree`: the order of `φ.formalSeries` equals
  the inseparable degree of `φ`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.12, III.5, IV.4.2 and
  IV.4.3.
-/

public section

open WeierstrassCurve HahnSeries KaehlerDifferential
open scoped LaurentSeries PowerSeries

namespace TauCeti.Isogeny

variable {K : Type*} [Field K]

/-! ### Formal series of relative Frobenius -/

section RelativeFrobenius

/-- The `n`-fold relative Frobenius isogeny induces the formal power series `X ^ (p ^ n)`. -/
@[simp]
theorem formalSeries_iterateRelativeFrobeniusIsogeny (p : ℕ) [ExpChar K p]
    (W : WeierstrassCurve K) (n : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W.toAffine n).formalSeries = PowerSeries.X ^ p ^ n := by
  apply (formalSeries_eq_iff _ _).mpr
  have : ExpChar W.toAffine.FunctionField p :=
    expChar_of_injective_algebraMap (algebraMap K _).injective p
  have hneg : (-W.toAffine.genericX) ^ p ^ n = -W.toAffine.genericX ^ p ^ n := by
    simpa [iterateFrobenius_def] using
      (iterateFrobenius W.toAffine.FunctionField p n).map_neg W.toAffine.genericX
  rw [map_div₀, map_neg, fieldPullback_iterateRelativeFrobeniusIsogeny_genericX,
    fieldPullback_iterateRelativeFrobeniusIsogeny_genericY, ← hneg, ← div_pow, map_pow, map_pow,
    W.functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- The relative Frobenius isogeny induces the formal power series `X ^ p`. -/
@[simp]
theorem formalSeries_relativeFrobeniusIsogeny (p : ℕ) [ExpChar K p] (W : WeierstrassCurve K) :
    (relativeFrobeniusIsogeny p W.toAffine).formalSeries = PowerSeries.X ^ p := by
  apply (formalSeries_eq_iff _ _).mpr
  have : ExpChar W.toAffine.FunctionField p :=
    expChar_of_injective_algebraMap (algebraMap K _).injective p
  have hneg : (-W.toAffine.genericX) ^ p = -W.toAffine.genericX ^ p := by
    simpa [frobenius_def] using (frobenius W.toAffine.FunctionField p).map_neg W.toAffine.genericX
  rw [map_div₀, map_neg, fieldPullback_relativeFrobeniusIsogeny_genericX,
    fieldPullback_relativeFrobeniusIsogeny_genericY, ← hneg, ← div_pow, map_pow, map_pow,
    W.functionFieldLaurentExpansion_neg_genericX_div_genericY]

end RelativeFrobenius

/-! ### Pullback of the invariant differential and the linear coefficient -/

section Differential

variable {W₁ W₂ : WeierstrassCurve K}

private theorem ofPowerSeries_subst_formalInvariantDifferentialDenom (W : WeierstrassCurve K)
    {q₀ : K⟦X⟧} (hs : PowerSeries.HasSubst q₀) :
    ofPowerSeries ℤ K (PowerSeries.subst q₀ W.formalInvariantDifferentialDenom) =
      1 - algebraMap K K⸨X⸩ W.a₁ * ofPowerSeries ℤ K q₀ -
        algebraMap K K⸨X⸩ W.a₂ * (ofPowerSeries ℤ K q₀) ^ 2 -
        2 * algebraMap K K⸨X⸩ W.a₃ * ofPowerSeries ℤ K (PowerSeries.subst q₀ W.formalW) -
        2 * algebraMap K K⸨X⸩ W.a₄ *
          (ofPowerSeries ℤ K q₀ * ofPowerSeries ℤ K (PowerSeries.subst q₀ W.formalW)) -
        3 * algebraMap K K⸨X⸩ W.a₆ * (ofPowerSeries ℤ K (PowerSeries.subst q₀ W.formalW)) ^ 2 := by
  rw [W.subst_formalInvariantDifferentialDenom hs]
  simp only [Algebra.smul_def, map_sub, map_one, map_mul, map_pow, map_ofNat,
    ← HahnSeries.algebraMap_apply' ℤ]

private theorem functionFieldLaurentExpansion_fieldPullback_coords [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericX) =
        ofPowerSeries ℤ K φ.formalSeries /
          ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalW) ∧
      W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY) =
        -1 / ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalW) ∧
      -2 + algebraMap K K⸨X⸩ W₂.a₁ * ofPowerSeries ℤ K φ.formalSeries +
          algebraMap K K⸨X⸩ W₂.a₃ *
            ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalW) ≠ 0 := by
  set q : K⸨X⸩ := ofPowerSeries ℤ K φ.formalSeries
  set w : K⸨X⸩ := ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalW)
  have hw_eq : W₁.functionFieldLaurentExpansion (φ.fieldPullback (-W₂.toAffine.genericY⁻¹)) = w :=
    φ.coe_subst_formalW_formalSeries.symm
  have hy0 : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY) ≠ 0 :=
    (map_ne_zero W₁.functionFieldLaurentExpansion).mpr
      ((map_ne_zero φ.fieldPullback).mpr W₂.toAffine.genericY_ne_zero)
  have hw0 : w ≠ 0 := by
    rw [← hw_eq, map_neg, map_inv₀, map_neg, map_inv₀]
    exact neg_ne_zero.mpr (inv_ne_zero hy0)
  have hy : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY) = -1 / w := by
    have h := hw_eq
    rw [map_neg, map_inv₀, map_neg, map_inv₀] at h
    rw [← h]
    field_simp
  have hx : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericX) = q / w := by
    have h : W₁.functionFieldLaurentExpansion
        (φ.fieldPullback (-W₂.toAffine.genericX / W₂.toAffine.genericY)) = q :=
      φ.coe_formalSeries.symm
    rw [map_div₀, map_neg, map_div₀, map_neg, hy] at h
    rw [← h]
    field_simp
  have hd0 : W₁.functionFieldLaurentExpansion
      (φ.fieldPullback (Affine.invariantDifferentialDenom W₂.toAffine)) ≠ 0 :=
    (map_ne_zero W₁.functionFieldLaurentExpansion).mpr
      ((map_ne_zero φ.fieldPullback).mpr (Affine.invariantDifferentialDenom_ne_zero W₂.toAffine))
  refine ⟨hx, hy, fun hu0 ↦ hd0 ?_⟩
  simp only [Affine.invariantDifferentialDenom_def, map_add, map_mul, map_ofNat, AlgHom.commutes,
    hx, hy]
  have hdiv : 2 * (-1 / w) + algebraMap K K⸨X⸩ W₂.a₁ * (q / w) + algebraMap K K⸨X⸩ W₂.a₃ =
      (-2 + algebraMap K K⸨X⸩ W₂.a₁ * q + algebraMap K K⸨X⸩ W₂.a₃ * w) / w := by
    field_simp
  rw [hdiv, hu0, zero_div]

/-- Expanding `(φ^* W_Y)⁻¹ · (φ^* x)'` at infinity yields
`(P₂ ∘ φ.formalSeries) · (φ.formalSeries)'` in `K⸨X⸩`. -/
private theorem functionFieldLaurentExpansion_fieldPullback_inv_mul_derivative [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (W₁.functionFieldLaurentExpansion
        (φ.fieldPullback (Affine.invariantDifferentialDenom W₂.toAffine)))⁻¹ *
      LaurentSeries.derivative K
        (W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericX)) =
    ofPowerSeries ℤ K
      (PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
        PowerSeries.derivative φ.formalSeries) := by
  have hs : PowerSeries.HasSubst φ.formalSeries :=
    .of_constantCoeff_zero' φ.constantCoeff_formalSeries
  obtain ⟨hx, hy, hu⟩ := φ.functionFieldLaurentExpansion_fieldPullback_coords
  set q : K⸨X⸩ := ofPowerSeries ℤ K φ.formalSeries
  set w : K⸨X⸩ := ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalW)
  have hd : W₁.functionFieldLaurentExpansion
      (φ.fieldPullback (Affine.invariantDifferentialDenom W₂.toAffine)) =
      (W₂⁄K⸨X⸩).toAffine.polynomialY.evalEval (q / w) (-1 / w) := by
    simp only [Affine.invariantDifferentialDenom_def, Affine.evalEval_polynomialY,
      WeierstrassCurve.baseChange, map_a₁, map_a₃, map_add, map_mul, map_ofNat, AlgHom.commutes,
      hx, hy]
  have heq : w = wEquationRHS W₂ q w := by
    have h := congrArg (algebraMap K⟦X⟧ K⸨X⸩) (W₂.subst_formalW_wEquation hs)
    rw [algebraMap_wEquationRHS] at h
    simpa only [LaurentSeries.coe_algebraMap, q, w] using h
  have hPG : ofPowerSeries ℤ K
      (PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential) *
      ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalInvariantDifferentialDenom) =
      1 := by
    have hPG₀ : PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
        PowerSeries.subst φ.formalSeries W₂.formalInvariantDifferentialDenom = 1 := by
      rw [← PowerSeries.subst_mul hs,
        W₂.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom,
        PowerSeries.subst_one]
    simpa only [map_mul, map_one] using congrArg (ofPowerSeries ℤ K) hPG₀
  have hG_expand := ofPowerSeries_subst_formalInvariantDifferentialDenom W₂ hs
  have hG0 := hG_expand ▸ right_ne_zero_of_mul_eq_one hPG
  have hmain := W₂.inv_evalEval_polynomialY_smul_derivation_div
    (TauCeti.laurentSeriesDerivation K) heq hG0 hu
  simp only [TauCeti.laurentSeriesDerivation_apply, smul_eq_mul, q, w, ← hG_expand,
    inv_eq_of_mul_eq_one_left hPG] at hmain
  rw [hd, hx]
  dsimp only [q, w]
  rw [hmain, ← PowerSeries.coe_derivative, map_mul]

/-- If `φ^* ω₂ = c • ω₁`, then pulling back the formal-group invariant differential along
`φ.formalSeries` multiplies the invariant differential of `formalGroup W₁` by `c`. -/
theorem subst_formalSeries_invariantDifferential_mul_derivative_of_pullbackDifferential_eq_smul
    [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine) :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
      PowerSeries.derivative φ.formalSeries =
      c • (formalGroup W₁).invariantDifferential := by
  have := φ.isElliptic
  set d₁ := Affine.invariantDifferentialDenom W₁.toAffine
  set d₂ := Affine.invariantDifferentialDenom W₂.toAffine
  have hd₂ : φ.fieldPullback d₂ ≠ 0 :=
    (map_ne_zero φ.fieldPullback).mpr (Affine.invariantDifferentialDenom_ne_zero W₂.toAffine)
  have hD : D K W₁.toAffine.FunctionField (φ.fieldPullback W₂.toAffine.genericX) =
      (φ.fieldPullback d₂ * (algebraMap K W₁.toAffine.FunctionField c * d₁⁻¹)) •
        D K W₁.toAffine.FunctionField W₁.toAffine.genericX := by
    have hc' := congrArg (φ.fieldPullback d₂ • ·) hc
    simp only [Affine.invariantDifferential_def, d₂, pullbackDifferential_smul,
      pullbackDifferential_D, map_inv₀, ← algebraMap_smul W₁.toAffine.FunctionField c, smul_smul,
      mul_inv_cancel₀ hd₂, one_smul] at hc'
    exact hc'
  have hexp := TauCeti.derivative_algHom_eq_mul_of_D_eq_smul
    (e := W₁.functionFieldLaurentExpansion) hD
  have hed₂ : W₁.functionFieldLaurentExpansion (φ.fieldPullback d₂) ≠ 0 :=
    (map_ne_zero W₁.functionFieldLaurentExpansion).mpr hd₂
  have hlhs := φ.functionFieldLaurentExpansion_fieldPullback_inv_mul_derivative
  have hrhs := (id W₁.toAffine).functionFieldLaurentExpansion_fieldPullback_inv_mul_derivative
  simp only [id_fieldPullback, AlgHom.id_apply, formalSeries_id, PowerSeries.X_subst,
    PowerSeries.derivative_X, mul_one] at hrhs
  apply ofPowerSeries_injective (Γ := ℤ) (R := K)
  rw [← hlhs, hexp, map_mul, map_mul, AlgHom.commutes, map_inv₀, ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ hed₂, one_mul, mul_assoc, hrhs, Algebra.smul_def, map_mul,
    ← HahnSeries.algebraMap_apply' ℤ]

/-- **The pullback scalar of the invariant differential is the linear coefficient of
`φ.formalSeries`** (Silverman IV.4.2(a)): if `φ^* ω₂ = c • ω₁`, then
`PowerSeries.coeff 1 φ.formalSeries = c`. -/
theorem coeff_one_formalSeries_eq_of_pullbackDifferential_eq_smul [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine) :
    PowerSeries.coeff 1 φ.formalSeries = c := by
  have h := congrArg PowerSeries.constantCoeff
    (φ.subst_formalSeries_invariantDifferential_mul_derivative_of_pullbackDifferential_eq_smul hc)
  -- `PowerSeries.constantCoeff` is `MvPowerSeries.constantCoeff` on the `Unit` index type, so
  -- `constantCoeff_subst_of_constantCoeff_zero` evaluates the constant term of the composite.
  have hsub : PowerSeries.constantCoeff
      (PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential) = 1 :=
    (PowerSeries.constantCoeff_subst_of_constantCoeff_zero φ.constantCoeff_formalSeries
      (formalGroup W₂).invariantDifferential).trans
      (by simp [(formalGroup W₂).constantCoeff_invariantDifferential])
  have hder : PowerSeries.constantCoeff (PowerSeries.derivative φ.formalSeries) =
      PowerSeries.coeff 1 φ.formalSeries := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simpa [map_mul, hsub, hder, (formalGroup W₁).constantCoeff_invariantDifferential] using h

/-- **An isogeny pulls back the invariant differential by the linear coefficient of its formal
series** (Silverman IV.4.2(a)): `φ^* ω₂ = (PowerSeries.coeff 1 φ.formalSeries) • ω₁`. -/
theorem pullbackDifferential_invariantDifferential_eq_smul [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      PowerSeries.coeff 1 φ.formalSeries • Affine.invariantDifferential W₁.toAffine := by
  obtain ⟨c, hc, -⟩ := existsUnique_pullbackDifferential_invariantDifferential_eq_smul φ
  rwa [φ.coeff_one_formalSeries_eq_of_pullbackDifferential_eq_smul hc]

/-- **Pullback of the formal-group invariant differential along an isogeny**:
`(P₂ ∘ φ.formalSeries) · (φ.formalSeries)' = (PowerSeries.coeff 1 φ.formalSeries) • P₁`. -/
theorem subst_formalSeries_invariantDifferential_mul_derivative [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
      PowerSeries.derivative φ.formalSeries =
      PowerSeries.coeff 1 φ.formalSeries • (formalGroup W₁).invariantDifferential :=
  φ.subst_formalSeries_invariantDifferential_mul_derivative_of_pullbackDifferential_eq_smul
    φ.pullbackDifferential_invariantDifferential_eq_smul

/-- **A morphism pulls back the invariant differential by the linear coefficient of its formal
series**: `f^* ω₂ = (PowerSeries.coeff 1 f.formalSeries) • ω₁`. -/
theorem Hom.pullbackDifferential_invariantDifferential_eq_smul [W₂.IsElliptic]
    (f : Hom W₁.toAffine W₂.toAffine) :
    f.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      PowerSeries.coeff 1 f.formalSeries • Affine.invariantDifferential W₁.toAffine := by
  rcases Hom.eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · rw [Hom.pullbackDifferential_ofIsogeny, Hom.formalSeries_ofIsogeny,
      Isogeny.pullbackDifferential_invariantDifferential_eq_smul]

end Differential

/-! ### Separability, formal group isomorphisms, and order of the formal series -/

section Separability

variable {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

/-- **An isogeny is separable if and only if the linear coefficient of its formal series is
nonzero** (Silverman IV.4.3). -/
theorem isSeparable_iff_coeff_one_formalSeries_ne_zero (φ : Isogeny W₁.toAffine W₂.toAffine) :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      PowerSeries.coeff 1 φ.formalSeries ≠ 0 :=
  φ.isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul
    φ.pullbackDifferential_invariantDifferential_eq_smul

/-- **An isogeny is separable if and only if its formal series has order `1`**
(Silverman IV.4.3). -/
theorem isSeparable_iff_order_formalSeries_eq_one (φ : Isogeny W₁.toAffine W₂.toAffine) :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      φ.formalSeries.order = 1 := by
  rw [φ.isSeparable_iff_coeff_one_formalSeries_ne_zero, ← Nat.cast_one (R := ℕ∞),
    PowerSeries.order_eq_nat]
  refine ⟨fun h ↦ ⟨h, fun i hi ↦ ?_⟩, And.left⟩
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  simp

/-- **The formal-group isomorphism induced by a separable isogeny** (Silverman IV.4.3). -/
noncomputable def formalGroupIso (φ : Isogeny W₁.toAffine W₂.toAffine)
    [hsep : Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    FormalGroupIso (formalGroup W₁) (formalGroup W₂) :=
  φ.formalGroupHom.toIso <| isUnit_iff_ne_zero.mpr <| by
    simpa using φ.isSeparable_iff_coeff_one_formalSeries_ne_zero.mp hsep

/-- The forward homomorphism of `φ.formalGroupIso` is `φ.formalGroupHom`. -/
@[simp]
theorem formalGroupIso_toHom (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalGroupIso.toHom = φ.formalGroupHom := by
  simp only [formalGroupIso, FormalGroupHom.toIso_toHom]

/-- **The order of the formal series of an isogeny equals its inseparable degree**
(Silverman IV.4.3). -/
theorem order_formalSeries_eq_inseparableDegree (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalSeries.order = (φ.inseparableDegree : ℕ∞) := by
  -- Factor `φ = χ ∘ F^r` in exponential characteristic `p`, where `χ` has order `1` and `F^r`
  -- has formal series `X ^ (p ^ r)` with `p ^ r = φ.inseparableDegree`.
  obtain ⟨p, _⟩ := ExpChar.exists K
  obtain ⟨r, χ, hsep, hχ⟩ := exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  have hinsep : φ.inseparableDegree = p ^ r :=
    inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ
  have hordχ : (formalSeries (W₁ := W₁.map (iterateFrobenius K p r)) (W₂ := W₂) χ).order = 1 :=
    (isSeparable_iff_order_formalSeries_eq_one
      (W₁ := W₁.map (iterateFrobenius K p r)) (W₂ := W₂) χ).mp hsep
  have hcomp : φ.formalSeries =
      PowerSeries.subst ((iterateRelativeFrobeniusIsogeny p W₁.toAffine r).formalSeries)
        (formalSeries (W₁ := W₁.map (iterateFrobenius K p r)) (W₂ := W₂) χ) := by
    rw [← hχ]
    exact formalSeries_comp (W₁ := W₁) (W₂ := W₁.map (iterateFrobenius K p r)) (W₃ := W₂)
      (iterateRelativeFrobeniusIsogeny p W₁.toAffine r) χ
  rw [hcomp, PowerSeries.order_subst
      (iterateRelativeFrobeniusIsogeny p W₁.toAffine r).constantCoeff_formalSeries,
    formalSeries_iterateRelativeFrobeniusIsogeny, PowerSeries.order_X_pow, hordχ, mul_one, hinsep]

end Separability

end TauCeti.Isogeny
