/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.LaurentExpansion.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.RingTheory.LaurentSeries.Substitution.Basic
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Pullback of the invariant differential along the formal series of an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`. Expanding `φ^*η` at infinity
in the local parameter `z₁ = -x₁ / y₁` obeys the Laurent chain rule
(`TauCeti.Isogeny.differentialLaurentSeries_pullbackDifferential`). By
`TauCeti.Isogeny.existsUnique_pullbackDifferential_invariantDifferential_eq_smul`, `φ` pulls back
the invariant differential `ω₂` of `W₂` to `c • ω₁` for a unique constant `c ∈ K`. Applying
`WeierstrassCurve.differentialLaurentSeries` to both sides and comparing with the formal-group
invariant differential identifies `c` with the linear coefficient of `φ.formalSeries`
(Silverman III.5, IV.4): `φ^* ω₂ = (PowerSeries.coeff 1 φ.formalSeries) • ω₁`, and on
formal-group invariant differentials
`(P₂ ∘ φ.formalSeries) · (φ.formalSeries)' = (PowerSeries.coeff 1 φ.formalSeries) • P₁`.

In particular `φ^* ω₂ ≠ 0` exactly when `PowerSeries.coeff 1 φ.formalSeries ≠ 0`, which by
`TauCeti.Isogeny.coeff_one_formalSeries_ne_zero_iff_isSeparable` happens exactly when `φ` is
separable.

## Main results

* `TauCeti.Isogeny.differentialLaurentSeries_pullbackDifferential`: Laurent chain rule for
  pulled-back Kähler differentials.
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

/-- **Laurent chain rule for pulled-back Kähler differentials**: expanding `φ^*η` at infinity
substitutes `φ.formalSeries` into the expansion of `η` and multiplies by `(φ.formalSeries)'`. -/
theorem differentialLaurentSeries_pullbackDifferential
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    (η : KaehlerDifferential K W₂.toAffine.FunctionField) :
    W₁.differentialLaurentSeries (φ.pullbackDifferential η) =
      LaurentSeries.substAlgHom φ.constantCoeff_formalSeries φ.formalSeries_ne_zero
        (W₂.differentialLaurentSeries η) *
        _root_.LaurentSeries.derivative K (φ.formalSeries : K⸨X⸩) := by
  have hmem : η ∈ Submodule.span W₂.toAffine.FunctionField
      (Set.range (KaehlerDifferential.D K W₂.toAffine.FunctionField)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem _ h =>
    rcases h with ⟨f, rfl⟩
    rw [pullbackDifferential_D, differentialLaurentSeries_D, differentialLaurentSeries_D,
      φ.functionFieldLaurentExpansion_fieldPullback, LaurentSeries.derivative_substAlgHom]
  | zero => simp
  | add _ _ _ _ h₁ h₂ => simp [h₁, h₂, add_mul]
  | smul f _ _ h =>
    rw [pullbackDifferential_smul, differentialLaurentSeries_smul,
      differentialLaurentSeries_smul, map_mul, mul_assoc, h,
      φ.functionFieldLaurentExpansion_fieldPullback]

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
  have h := congrArg W₁.differentialLaurentSeries hc
  rw [φ.differentialLaurentSeries_pullbackDifferential,
    W₂.differentialLaurentSeries_invariantDifferential, map_smul,
    W₁.differentialLaurentSeries_invariantDifferential, LaurentSeries.substAlgHom_coe,
    ← PowerSeries.coe_derivative, ← PowerSeries.coe_mul, ← PowerSeries.coe_smul] at h
  exact ofPowerSeries_injective h

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
