/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.RingTheory.LaurentSeries.Basic
import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Expansion
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Pullback of the invariant differential along the formal series of an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`. By
`TauCeti.Isogeny.existsUnique_pullbackDifferential_invariantDifferential_eq_smul`, `φ` pulls back
the invariant differential `ω₂` of `W₂` to `c • ω₁` for a unique constant `c ∈ K`. Expanding both
sides at the point at infinity via `WeierstrassCurve.functionFieldLaurentExpansion` and comparing
with the formal-group invariant differential identifies `c` with the linear coefficient of
`φ.formalSeries` (Silverman III.5, IV.4):
`φ^* ω₂ = (PowerSeries.coeff 1 φ.formalSeries) • ω₁`, and on formal-group invariant differentials
`(P₂ ∘ φ.formalSeries) · (φ.formalSeries)' = (PowerSeries.coeff 1 φ.formalSeries) • P₁`.

In particular `φ^* ω₂ ≠ 0` exactly when `PowerSeries.coeff 1 φ.formalSeries ≠ 0`, which by
`TauCeti.Isogeny.coeff_one_formalSeries_ne_zero_iff_isSeparable` happens exactly when `φ` is
separable.

## Main results

* `TauCeti.Isogeny.coeff_one_formalSeries_eq_of_pullbackDifferential_eq_smul` and
  `TauCeti.Isogeny.pullbackDifferential_invariantDifferential_eq_smul`: `φ^* ω₂ = c • ω₁` with
  `c = PowerSeries.coeff 1 φ.formalSeries`.
* `TauCeti.Isogeny.Hom.pullbackDifferential_invariantDifferential_eq_smul`: the same for every
  morphism `f : W₁ → W₂`.
* `TauCeti.Isogeny.subst_formalSeries_invariantDifferential_mul_derivative` and
  `TauCeti.Isogeny.Hom.subst_formalSeries_invariantDifferential_mul_derivative`: pullback of the
  formal-group invariant differential along an isogeny or morphism.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5 and IV.4.
-/

public section

open WeierstrassCurve HahnSeries KaehlerDifferential
open scoped LaurentSeries PowerSeries

namespace TauCeti.Isogeny

variable {K : Type*} [Field K]

/-! ### Pullback of the invariant differential and the linear coefficient -/

section Differential

variable {W₁ W₂ : WeierstrassCurve K}

private theorem neg_two_add_formalSeries_ne_zero [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    -2 + algebraMap K K⸨X⸩ W₂.a₁ * ofPowerSeries ℤ K φ.formalSeries +
      algebraMap K K⸨X⸩ W₂.a₃ *
        ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalW) ≠ 0 := by
  set q : K⸨X⸩ := ofPowerSeries ℤ K φ.formalSeries
  set w : K⸨X⸩ := ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalW)
  have hx : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericX) = q / w := by
    rw [φ.functionFieldLaurentExpansion_fieldPullback,
      W₂.substAlgHom_functionFieldLaurentExpansion_genericX]
  have hy : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY) = -1 / w := by
    rw [φ.functionFieldLaurentExpansion_fieldPullback,
      W₂.substAlgHom_functionFieldLaurentExpansion_genericY]
  have hw0 : w ≠ 0 := fun h0 ↦
    (map_ne_zero W₁.functionFieldLaurentExpansion).mpr
      ((map_ne_zero φ.fieldPullback).mpr W₂.toAffine.genericY_ne_zero)
      (by rw [hy, h0, div_zero])
  have hd0 : W₁.functionFieldLaurentExpansion
      (φ.fieldPullback (Affine.invariantDifferentialDenom W₂.toAffine)) ≠ 0 :=
    (map_ne_zero W₁.functionFieldLaurentExpansion).mpr
      ((map_ne_zero φ.fieldPullback).mpr (Affine.invariantDifferentialDenom_ne_zero W₂.toAffine))
  intro hu0
  apply hd0
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
  have hx : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericX) =
      ofPowerSeries ℤ K φ.formalSeries /
        ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalW) := by
    rw [φ.functionFieldLaurentExpansion_fieldPullback,
      W₂.substAlgHom_functionFieldLaurentExpansion_genericX]
  have hy : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY) =
      -1 / ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalW) := by
    rw [φ.functionFieldLaurentExpansion_fieldPullback,
      W₂.substAlgHom_functionFieldLaurentExpansion_genericY]
  have hd : W₁.functionFieldLaurentExpansion
      (φ.fieldPullback (Affine.invariantDifferentialDenom W₂.toAffine)) =
      (W₂⁄K⸨X⸩).toAffine.polynomialY.evalEval
        (ofPowerSeries ℤ K φ.formalSeries /
          ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalW))
        (-1 / ofPowerSeries ℤ K (PowerSeries.subst φ.formalSeries W₂.formalW)) := by
    simp only [Affine.invariantDifferentialDenom_def, Affine.evalEval_polynomialY,
      WeierstrassCurve.baseChange, map_a₁, map_a₃, map_add, map_mul, map_ofNat, AlgHom.commutes,
      hx, hy]
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
  have hmain := W₂.inv_smul_derivation_div_subst_formalW_of_neg_two_add_ne_zero
    (σ := Unit) (KK := K⸨X⸩) (TauCeti.laurentSeriesDerivation K) (q := φ.formalSeries)
    (by rw [← PowerSeries.constantCoeff_eq]; exact φ.constantCoeff_formalSeries)
    (by simpa only [LaurentSeries.coe_algebraMap] using φ.neg_two_add_formalSeries_ne_zero)
  simp only [smul_eq_mul, LaurentSeries.coe_algebraMap, TauCeti.laurentSeriesDerivation_apply,
    inv_eq_of_mul_eq_one_left hPG] at hmain
  rw [hd, hx, hmain, ← PowerSeries.coe_derivative, map_mul]

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
`φ.formalSeries`** (Silverman III.5, IV.4): if `φ^* ω₂ = c • ω₁`, then
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
series** (Silverman III.5, IV.4): `φ^* ω₂ = (PowerSeries.coeff 1 φ.formalSeries) • ω₁`. -/
theorem pullbackDifferential_invariantDifferential_eq_smul [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      PowerSeries.coeff 1 φ.formalSeries • Affine.invariantDifferential W₁.toAffine := by
  obtain ⟨c, hc, -⟩ := existsUnique_pullbackDifferential_invariantDifferential_eq_smul φ
  rwa [φ.coeff_one_formalSeries_eq_of_pullbackDifferential_eq_smul hc]

/-- **Pullback of the formal-group invariant differential along an isogeny**
(Silverman IV.4.2(b)):
`(P₂ ∘ φ.formalSeries) · (φ.formalSeries)' = (PowerSeries.coeff 1 φ.formalSeries) • P₁`. -/
theorem subst_formalSeries_invariantDifferential_mul_derivative [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
      PowerSeries.derivative φ.formalSeries =
      PowerSeries.coeff 1 φ.formalSeries • (formalGroup W₁).invariantDifferential := by
  simpa using φ.formalGroupHom.subst_invariantDifferential_mul_derivative

/-- **Pullback of the formal-group invariant differential along a morphism**
(Silverman IV.4.2(b)):
`(P₂ ∘ f.formalSeries) · (f.formalSeries)' = (PowerSeries.coeff 1 f.formalSeries) • P₁`. -/
theorem Hom.subst_formalSeries_invariantDifferential_mul_derivative [W₂.IsElliptic]
    (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.subst f.formalSeries (formalGroup W₂).invariantDifferential *
      PowerSeries.derivative f.formalSeries =
      PowerSeries.coeff 1 f.formalSeries • (formalGroup W₁).invariantDifferential := by
  simpa using f.formalGroupHom.subst_invariantDifferential_mul_derivative

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

end TauCeti.Isogeny
