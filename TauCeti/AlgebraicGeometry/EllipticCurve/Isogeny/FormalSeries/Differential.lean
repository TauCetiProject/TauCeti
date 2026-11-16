/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.LaurentExpansion.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic

/-!
# Pullback of the invariant differential and the linear coefficient of `Isogeny.formalSeries`

For an isogeny `φ : W₁ → W₂` of elliptic curves, expanding `φ^*η` at infinity in the local
parameter `z₁ = -x₁ / y₁` obeys the Laurent chain rule
(`TauCeti.Isogeny.differentialLaurentSeries_pullbackDifferential`). Comparing this with the global
pullback identity `φ^*ω₂ = c ω₁`
(`TauCeti.Isogeny.existsUnique_pullbackDifferential_invariantDifferential_eq_smul`) identifies the
constant `c` with the linear coefficient of `φ.formalSeries`:

* `φ^*ω₂ = (coeff 1 φ.formalSeries) • ω₁`,
* `φ` is separable iff `coeff 1 φ.formalSeries ≠ 0`, equivalently `φ.formalSeries.order = 1`.

## Main results

* `TauCeti.Isogeny.differentialLaurentSeries_pullbackDifferential`: Laurent chain rule for
  pulled-back Kähler differentials.
* `TauCeti.Isogeny.pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul`:
  `φ^*ω₂ = (coeff 1 φ.formalSeries) • ω₁`.
* `TauCeti.Isogeny.isSeparable_iff_coeff_one_formalSeries_ne_zero` and
  `TauCeti.Isogeny.isSeparable_iff_order_formalSeries_eq_one`: separability criteria on
  `φ.formalSeries`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.4.2, III.5, IV.1, and
  IV.4.
-/

public section

open HahnSeries WeierstrassCurve
open scoped LaurentSeries PowerSeries

namespace TauCeti.Isogeny

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K}

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

section Elliptic

variable [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **An isogeny pulls the invariant differential back to its formal series' linear coefficient**:
`φ^*ω₂ = (coeff 1 φ.formalSeries) • ω₁`. -/
theorem pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul :
    φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      PowerSeries.coeff 1 φ.formalSeries • Affine.invariantDifferential W₁.toAffine := by
  have := φ.isElliptic
  obtain ⟨c, hc, -⟩ := existsUnique_pullbackDifferential_invariantDifferential_eq_smul φ
  have hexp := congrArg W₁.differentialLaurentSeries hc
  rw [differentialLaurentSeries_pullbackDifferential,
    W₂.differentialLaurentSeries_invariantDifferential, LinearMap.map_smul,
    W₁.differentialLaurentSeries_invariantDifferential, LaurentSeries.substAlgHom_coe,
    ← PowerSeries.coe_derivative, ← PowerSeries.coe_mul, ← PowerSeries.coe_smul] at hexp
  have hps : PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
      d⁄dX φ.formalSeries = c • (formalGroup W₁).invariantDifferential :=
    ofPowerSeries_injective hexp
  have hsub : PowerSeries.constantCoeff
      (PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential) = 1 := by
    rw [PowerSeries.constantCoeff_eq,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero φ.constantCoeff_formalSeries,
      FormalGroup.constantCoeff_invariantDifferential, Algebra.algebraMap_self_apply]
  have hc_eq : PowerSeries.coeff 1 φ.formalSeries = c := by
    have hcc := congrArg PowerSeries.constantCoeff hps
    rw [map_mul, hsub, one_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_derivative] at hcc
    simpa using hcc
  rwa [hc_eq]

/-- **Differential separability criterion on the formal series**: an isogeny `φ` is separable if
and only if the linear coefficient `coeff 1 φ.formalSeries` is nonzero. -/
theorem isSeparable_iff_coeff_one_formalSeries_ne_zero :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      PowerSeries.coeff 1 φ.formalSeries ≠ 0 :=
  isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul φ
    (pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul φ)

/-- **Order separability criterion on the formal series**: an isogeny `φ` is separable if and only
if its formal series has order `1`. -/
theorem isSeparable_iff_order_formalSeries_eq_one :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      φ.formalSeries.order = 1 := by
  rw [isSeparable_iff_coeff_one_formalSeries_ne_zero, ← Nat.cast_one (R := ℕ∞),
    PowerSeries.order_eq_nat]
  constructor
  · refine fun h ↦ ⟨h, fun i hi ↦ ?_⟩
    rw [Nat.lt_one_iff.mp hi, PowerSeries.coeff_zero_eq_constantCoeff,
      φ.constantCoeff_formalSeries]
  · exact And.left

/-- **A separable isogeny has formal series of order `1`.** -/
theorem order_formalSeries_eq_one_of_isSeparable
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalSeries.order = 1 :=
  (isSeparable_iff_order_formalSeries_eq_one φ).mp ‹_›

end Elliptic

end TauCeti.Isogeny

end
