/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.LaurentExpansion.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic

/-!
# Pullback of the invariant differential along the formal series of an isogeny

Let `φ : W₁ → W₂` be an isogeny of Weierstrass curves over a field `K`. Expanding `φ^*η` at
infinity in the local parameter `z₁ = -x₁ / y₁` obeys the Laurent chain rule
(`TauCeti.Isogeny.differentialLaurentExpansion_pullbackDifferential`), specializing
`TauCeti.differentialLaurentExpansion_mapSemilinear`. When the invariant-differential denominators
`2y + a₁x + a₃` of `W₁` and `W₂` are nonzero, applying
`W₁.functionFieldLaurentExpansion.differentialLaurentExpansion` to an equation `φ^* ω₂ = c • ω₁`
and comparing with the formal-group invariant differential identifies `c` with the linear
coefficient of `φ.formalSeries` (Silverman III.5, IV.4).

When `W₂` (hence `W₁`) is an elliptic curve,
`TauCeti.Isogeny.existsUnique_pullbackDifferential_invariantDifferential_eq_smul` supplies such a
constant `c ∈ K`, giving `φ^* ω₂ = (PowerSeries.coeff 1 φ.formalSeries) • ω₁`, and on
formal-group invariant differentials
`(P₂ ∘ φ.formalSeries) · (φ.formalSeries)' = (PowerSeries.coeff 1 φ.formalSeries) • P₁`.

In particular `φ^* ω₂ ≠ 0` exactly when `PowerSeries.coeff 1 φ.formalSeries ≠ 0`, which by
`TauCeti.Isogeny.coeff_one_formalSeries_ne_zero_iff_isSeparable` happens exactly when `φ` is
separable.

## Main results

* `TauCeti.Isogeny.differentialLaurentExpansion_pullbackDifferential`: Laurent chain rule for
  pulled-back Kähler differentials.
* `TauCeti.Isogeny.coeff_one_formalSeries_eq_of_pullbackDifferential_eq_smul` (and its
  formal-group companion): comparing the pullback scalar `c` with
  `PowerSeries.coeff 1 φ.formalSeries` when both invariant-differential denominators are nonzero.
* `TauCeti.Isogeny.pullbackDifferential_invariantDifferential_eq_smul` and
  `TauCeti.Isogeny.Hom.pullbackDifferential_invariantDifferential_eq_smul`: for elliptic curves,
  `φ^* ω₂ = c • ω₁` with `c = PowerSeries.coeff 1 φ.formalSeries`.
* `TauCeti.Isogeny.subst_formalSeries_invariantDifferential_mul_derivative` and
  `TauCeti.Isogeny.Hom.subst_formalSeries_invariantDifferential_mul_derivative`: pullback of the
  formal-group invariant differential along an isogeny or morphism of elliptic curves.

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
theorem differentialLaurentExpansion_pullbackDifferential
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    (η : KaehlerDifferential K W₂.toAffine.FunctionField) :
    W₁.functionFieldLaurentExpansion.differentialLaurentExpansion (φ.pullbackDifferential η) =
      LaurentSeries.substAlgHom φ.constantCoeff_formalSeries φ.formalSeries_ne_zero
        (W₂.functionFieldLaurentExpansion.differentialLaurentExpansion η) *
        _root_.LaurentSeries.derivative K (φ.formalSeries : K⸨X⸩) := by
  rw [φ.pullbackDifferential_apply]
  exact TauCeti.differentialLaurentExpansion_mapSemilinear
    φ.constantCoeff_formalSeries φ.formalSeries_ne_zero
    φ.functionFieldLaurentExpansion_fieldPullback η

/-- If `φ^* ω₂ = c • ω₁` and both invariant-differential denominators are nonzero, then pulling
back the formal-group invariant differential along `φ.formalSeries` multiplies the invariant
differential of `formalGroup W₁` by `c`. -/
theorem subst_formalSeries_invariantDifferential_mul_derivative_of_pullbackDifferential_eq_smul
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hd₁ : Affine.invariantDifferentialDenom W₁.toAffine ≠ 0)
    (hd₂ : Affine.invariantDifferentialDenom W₂.toAffine ≠ 0)
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine) :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
      PowerSeries.derivative φ.formalSeries =
      c • (formalGroup W₁).invariantDifferential := by
  apply ofPowerSeries_injective (R := K) (Γ := ℤ)
  have h := congrArg W₁.functionFieldLaurentExpansion.differentialLaurentExpansion hc
  rw [φ.differentialLaurentExpansion_pullbackDifferential,
    W₂.differentialLaurentExpansion_invariantDifferential hd₂, map_smul,
    W₁.differentialLaurentExpansion_invariantDifferential hd₁,
    LaurentSeries.substAlgHom_coe] at h
  simpa only [PowerSeries.coe_mul, PowerSeries.coe_derivative, PowerSeries.coe_smul] using h

/-- **The pullback scalar of the invariant differential is the linear coefficient of
`φ.formalSeries`** (Silverman III.5, IV.4): if `φ^* ω₂ = c • ω₁` and both invariant-differential
denominators are nonzero, then `PowerSeries.coeff 1 φ.formalSeries = c`. -/
theorem coeff_one_formalSeries_eq_of_pullbackDifferential_eq_smul
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hd₁ : Affine.invariantDifferentialDenom W₁.toAffine ≠ 0)
    (hd₂ : Affine.invariantDifferentialDenom W₂.toAffine ≠ 0)
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine) :
    PowerSeries.coeff 1 φ.formalSeries = c := by
  have h := congrArg PowerSeries.constantCoeff
    (φ.subst_formalSeries_invariantDifferential_mul_derivative_of_pullbackDifferential_eq_smul
      hd₁ hd₂ hc)
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

/-- **An isogeny of elliptic curves pulls back the invariant differential by the linear
coefficient of its formal series** (Silverman III.5, IV.4): when `W₂` is an elliptic curve,
`φ^* ω₂ = (PowerSeries.coeff 1 φ.formalSeries) • ω₁`. -/
theorem pullbackDifferential_invariantDifferential_eq_smul [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      PowerSeries.coeff 1 φ.formalSeries • Affine.invariantDifferential W₁.toAffine := by
  have := φ.isElliptic
  obtain ⟨c, hc, -⟩ := existsUnique_pullbackDifferential_invariantDifferential_eq_smul φ
  rwa [φ.coeff_one_formalSeries_eq_of_pullbackDifferential_eq_smul
    (Affine.invariantDifferentialDenom_ne_zero W₁.toAffine)
    (Affine.invariantDifferentialDenom_ne_zero W₂.toAffine) hc]

/-- **Pullback of the formal-group invariant differential along an isogeny**
(Silverman IV.4.2(b)): when `W₂` is an elliptic curve,
`(P₂ ∘ φ.formalSeries) · (φ.formalSeries)' = (PowerSeries.coeff 1 φ.formalSeries) • P₁`. -/
theorem subst_formalSeries_invariantDifferential_mul_derivative [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
      PowerSeries.derivative φ.formalSeries =
      PowerSeries.coeff 1 φ.formalSeries • (formalGroup W₁).invariantDifferential := by
  simpa using φ.formalGroupHom.subst_invariantDifferential_mul_derivative

/-- **Pullback of the formal-group invariant differential along a morphism**
(Silverman IV.4.2(b)): when `W₂` is an elliptic curve,
`(P₂ ∘ f.formalSeries) · (f.formalSeries)' = (PowerSeries.coeff 1 f.formalSeries) • P₁`. -/
theorem Hom.subst_formalSeries_invariantDifferential_mul_derivative [W₂.IsElliptic]
    (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.subst f.formalSeries (formalGroup W₂).invariantDifferential *
      PowerSeries.derivative f.formalSeries =
      PowerSeries.coeff 1 f.formalSeries • (formalGroup W₁).invariantDifferential := by
  simpa using f.formalGroupHom.subst_invariantDifferential_mul_derivative

/-- **A morphism of elliptic curves pulls back the invariant differential by the linear
coefficient of its formal series**: when `W₂` is an elliptic curve,
`f^* ω₂ = (PowerSeries.coeff 1 f.formalSeries) • ω₁`. -/
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
