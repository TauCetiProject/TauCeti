/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.RingTheory.PowerSeries.Order

/-!
# Pullback of the invariant differential and the linear coefficient of `Isogeny.formalSeries`

Expanding Kähler differentials of `K(W)` at the point at infinity in the local parameter
`z = -x / y` sends `f dg` to `f(z) g'(z) dz`, recorded as the `K`-linear map
`WeierstrassCurve.differentialLaurentSeries : Ω[K(W)/K] →ₗ[K] K⸨X⸩`. On an elliptic curve `W`, the
invariant differential `ω = dx / (2y + a₁x + a₃)` expands to the normalised invariant differential
`P(z) = (1 - a₁z - a₂z² - 2a₃w(z) - 2a₄zw(z) - 3a₆w(z)²)⁻¹` of `formalGroup W`.

For an isogeny `φ : W₁ → W₂` of elliptic curves, comparing the global pullback identity
`φ^*ω₂ = c ω₁` (`TauCeti.Isogeny.existsUnique_pullbackDifferential_invariantDifferential_eq_smul`)
with the Laurent chain rule identifies the constant `c` with the linear coefficient of
`φ.formalSeries` (Silverman IV.4.2(c)):

* `φ^*ω₂ = (coeff 1 φ.formalSeries) • ω₁`,
* `P₂(φ(T)) · φ'(T) = (coeff 1 φ.formalSeries) • P₁(T)`,
* `φ` is separable iff `coeff 1 φ.formalSeries ≠ 0`, equivalently `φ.formalSeries.order = 1`.

## Main definitions

* `WeierstrassCurve.differentialLaurentSeries`: the `K`-linear coefficient expansion
  `Ω[K(W)/K] →ₗ[K] K⸨X⸩` in `d z` at infinity.

## Main results

* `WeierstrassCurve.differentialLaurentSeries_invariantDifferential`: `ω` expands to the invariant
  differential of `formalGroup W`.
* `TauCeti.Isogeny.pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul`:
  `φ^*ω₂ = (coeff 1 φ.formalSeries) • ω₁`.
* `TauCeti.Isogeny.subst_formalSeries_invariantDifferential_mul_derivative`:
  `P₂(φ(T)) · φ'(T) = (coeff 1 φ.formalSeries) • P₁(T)`.
* `TauCeti.Isogeny.isSeparable_iff_coeff_one_formalSeries_ne_zero` and
  `TauCeti.Isogeny.isSeparable_iff_order_formalSeries_eq_one`: separability criteria on
  `φ.formalSeries`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5 and IV.4.2(c).
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- **The Laurent expansion of Kähler differentials at infinity**: pushing `Ω[K(W)/K]` forward
along `W.functionFieldLaurentExpansion` and contracting with `laurentSeriesDerivation K` sends
`f dg` to `f(z) g'(z)` in `K⸨X⸩`, where `z = -x / y` expands to `X`. -/
noncomputable def differentialLaurentSeries :
    KaehlerDifferential K W.toAffine.FunctionField →ₗ[K] K⸨X⸩ where
  toFun η := (TauCeti.laurentSeriesDerivation K).liftKaehlerDifferential
    (KaehlerDifferential.mapSemilinear W.functionFieldLaurentExpansion η)
  map_add' η₁ η₂ := by rw [map_add, map_add]
  map_smul' c η := by
    rw [RingHom.id_apply, ← algebraMap_smul W.toAffine.FunctionField c η,
      KaehlerDifferential.mapSemilinear_smul, AlgHom.commutes, LinearMap.map_smul,
      smul_eq_mul, TauCeti.laurentSeries_algebraMap_mul_eq_smul]

/-- `differentialLaurentSeries` lifts `laurentSeriesDerivation` along the Laurent expansion. -/
theorem differentialLaurentSeries_apply (η : KaehlerDifferential K W.toAffine.FunctionField) :
    W.differentialLaurentSeries η =
      (TauCeti.laurentSeriesDerivation K).liftKaehlerDifferential
        (KaehlerDifferential.mapSemilinear W.functionFieldLaurentExpansion η) :=
  (rfl)

/-- **The differential `d f` expands to the formal derivative of the expansion of `f`.** -/
@[simp]
theorem differentialLaurentSeries_D (f : W.toAffine.FunctionField) :
    W.differentialLaurentSeries (KaehlerDifferential.D K W.toAffine.FunctionField f) =
      _root_.LaurentSeries.derivative K (W.functionFieldLaurentExpansion f) := by
  rw [differentialLaurentSeries_apply, KaehlerDifferential.mapSemilinear_D,
    Derivation.liftKaehlerDifferential_comp_D, TauCeti.laurentSeriesDerivation_apply]

/-- **Scalar multiplication by a rational function becomes multiplication by its expansion.** -/
@[simp]
theorem differentialLaurentSeries_smul (f : W.toAffine.FunctionField)
    (η : KaehlerDifferential K W.toAffine.FunctionField) :
    W.differentialLaurentSeries (f • η) =
      W.functionFieldLaurentExpansion f * W.differentialLaurentSeries η := by
  rw [differentialLaurentSeries_apply, KaehlerDifferential.mapSemilinear_smul,
    LinearMap.map_smul, smul_eq_mul, ← differentialLaurentSeries_apply]

private theorem functionFieldLaurentExpansion_genericY_eq_div_formalW :
    W.functionFieldLaurentExpansion W.toAffine.genericY = -1 / (formalW W : K⸨X⸩) := by
  have h := W.functionFieldLaurentExpansion_neg_inv_genericY
  rw [map_neg, map_inv₀] at h
  rw [show (formalW W : K⸨X⸩) = -(W.functionFieldLaurentExpansion W.toAffine.genericY)⁻¹ from
    h.symm]
  field_simp [W.toAffine.genericY_ne_zero,
    (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr W.toAffine.genericY_ne_zero]

private theorem formalW_coe_ne_zero : (formalW W : K⸨X⸩) ≠ 0 := by
  rw [← W.functionFieldLaurentExpansion_neg_inv_genericY]
  exact (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr
    (neg_ne_zero.mpr (inv_ne_zero W.toAffine.genericY_ne_zero))

private theorem functionFieldLaurentExpansion_genericX_eq_div_formalW :
    W.functionFieldLaurentExpansion W.toAffine.genericX =
      ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) / (formalW W : K⸨X⸩) := by
  have hw0 : (formalW W : K⸨X⸩) ≠ 0 := W.formalW_coe_ne_zero
  have h := W.functionFieldLaurentExpansion_neg_genericX_div_genericY
  rw [map_div₀, map_neg, W.functionFieldLaurentExpansion_genericY_eq_div_formalW] at h
  rw [show ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) =
      -W.functionFieldLaurentExpansion W.toAffine.genericX / (-1 / (formalW W : K⸨X⸩)) from h.symm]
  field_simp

private theorem coe_formalInvariantDifferentialDenom :
    (W.formalInvariantDifferentialDenom : K⸨X⸩) =
      1 - algebraMap K K⸨X⸩ W.a₁ * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) -
        algebraMap K K⸨X⸩ W.a₂ * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ 2 -
        2 * algebraMap K K⸨X⸩ W.a₃ * (formalW W : K⸨X⸩) -
        2 * algebraMap K K⸨X⸩ W.a₄ * (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) * (formalW W : K⸨X⸩)) -
        3 * algebraMap K K⸨X⸩ W.a₆ * (formalW W : K⸨X⸩) ^ 2 := by
  have hC (c : K) : ((PowerSeries.C c : K⟦X⟧) : K⸨X⸩) = algebraMap K K⸨X⸩ c := by
    rw [← LaurentSeries.coe_algebraMap, ← PowerSeries.algebraMap_eq,
      IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩]
  rw [formalInvariantDifferentialDenom_def]
  simp only [PowerSeries.smul_eq_C_mul, PowerSeries.coe_sub, PowerSeries.coe_one,
    PowerSeries.coe_pow, hC, map_mul, map_ofNat]

/-- **The invariant differential of an elliptic curve expands at infinity to the normalised
invariant differential of its formal group.** -/
@[simp]
theorem differentialLaurentSeries_invariantDifferential [W.IsElliptic] :
    W.differentialLaurentSeries (Affine.invariantDifferential W.toAffine) =
      ((formalGroup W).invariantDifferential : K⸨X⸩) := by
  let z : K⸨X⸩ := ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)
  let w : K⸨X⸩ := (formalW W : K⸨X⸩)
  have hw0 : w ≠ 0 := W.formalW_coe_ne_zero
  have heq : w = wEquationRHS W z w := by
    have h := congrArg (ofPowerSeries ℤ K) W.formalW_wEquation
    rwa [← LaurentSeries.coe_algebraMap, algebraMap_wEquationRHS, LaurentSeries.coe_algebraMap] at h
  have hmul : ((formalGroup W).invariantDifferential : K⸨X⸩) *
      (W.formalInvariantDifferentialDenom : K⸨X⸩) = 1 := by
    simpa only [PowerSeries.coe_mul, PowerSeries.coe_one] using
      congrArg (ofPowerSeries ℤ K)
        W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
  have hGeq : (W.formalInvariantDifferentialDenom : K⸨X⸩) =
      1 - algebraMap K K⸨X⸩ W.a₁ * z - algebraMap K K⸨X⸩ W.a₂ * z ^ 2 -
        2 * algebraMap K K⸨X⸩ W.a₃ * w - 2 * algebraMap K K⸨X⸩ W.a₄ * (z * w) -
        3 * algebraMap K K⸨X⸩ W.a₆ * w ^ 2 :=
    W.coe_formalInvariantDifferentialDenom
  have hG0 : 1 - algebraMap K K⸨X⸩ W.a₁ * z - algebraMap K K⸨X⸩ W.a₂ * z ^ 2 -
      2 * algebraMap K K⸨X⸩ W.a₃ * w - 2 * algebraMap K K⸨X⸩ W.a₄ * (z * w) -
      3 * algebraMap K K⸨X⸩ W.a₆ * w ^ 2 ≠ 0 :=
    hGeq ▸ right_ne_zero_of_mul_eq_one hmul
  have hdenom : W.functionFieldLaurentExpansion (Affine.invariantDifferentialDenom W.toAffine) =
      (W⁄K⸨X⸩).toAffine.polynomialY.evalEval (z / w) (-1 / w) := by
    rw [Affine.invariantDifferentialDenom_def, Affine.evalEval_polynomialY]
    simp only [map_add, map_mul, map_ofNat, AlgHom.commutes,
      W.functionFieldLaurentExpansion_genericX_eq_div_formalW,
      W.functionFieldLaurentExpansion_genericY_eq_div_formalW,
      WeierstrassCurve.baseChange, map_a₁, map_a₃, z, w]
  have hu : -2 + algebraMap K K⸨X⸩ W.a₁ * z + algebraMap K K⸨X⸩ W.a₃ * w ≠ 0 := by
    intro h0
    have hd0 : W.functionFieldLaurentExpansion (Affine.invariantDifferentialDenom W.toAffine) ≠ 0 :=
      (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr
        (Affine.invariantDifferentialDenom_ne_zero W.toAffine)
    apply hd0
    rw [hdenom, Affine.evalEval_polynomialY]
    simp only [WeierstrassCurve.baseChange, map_a₁, map_a₃]
    rw [show 2 * (-1 / w) + algebraMap K K⸨X⸩ W.a₁ * (z / w) + algebraMap K K⸨X⸩ W.a₃ =
      (-2 + algebraMap K K⸨X⸩ W.a₁ * z + algebraMap K K⸨X⸩ W.a₃ * w) / w by field_simp,
      h0, zero_div]
  have hkey := W.inv_evalEval_polynomialY_smul_derivation_div
    (TauCeti.laurentSeriesDerivation K) heq hG0 hu
  have hx : W.functionFieldLaurentExpansion W.toAffine.genericX = z / w :=
    W.functionFieldLaurentExpansion_genericX_eq_div_formalW
  rw [Affine.invariantDifferential_def, differentialLaurentSeries_smul,
    differentialLaurentSeries_D, map_inv₀, hdenom, hx]
  simpa only [TauCeti.laurentSeriesDerivation_apply, smul_eq_mul, ← hGeq,
    show _root_.LaurentSeries.derivative K z = 1 by simp [z], mul_one,
    inv_eq_of_mul_eq_one_left hmul] using hkey

end WeierstrassCurve

namespace TauCeti.Isogeny

open WeierstrassCurve

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

private theorem ofPowerSeries_smul_eq (c : K) (f : K⟦X⟧) :
    ((c • f : K⟦X⟧) : K⸨X⸩) = c • (f : K⸨X⸩) := by
  ext n
  simp

/-- **An isogeny pulls the invariant differential back to its formal series' linear coefficient**
(Silverman IV.4.2(c)): `φ^*ω₂ = (coeff 1 φ.formalSeries) • ω₁`. -/
theorem pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul :
    φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      PowerSeries.coeff 1 φ.formalSeries • Affine.invariantDifferential W₁.toAffine := by
  have := φ.isElliptic
  obtain ⟨c, hc, -⟩ := existsUnique_pullbackDifferential_invariantDifferential_eq_smul φ
  have hexp := congrArg W₁.differentialLaurentSeries hc
  rw [differentialLaurentSeries_pullbackDifferential,
    W₂.differentialLaurentSeries_invariantDifferential, LinearMap.map_smul,
    W₁.differentialLaurentSeries_invariantDifferential, LaurentSeries.substAlgHom_coe,
    ← PowerSeries.coe_derivative, ← PowerSeries.coe_mul, ← ofPowerSeries_smul_eq] at hexp
  have hps : PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
      d⁄dX φ.formalSeries = c • (formalGroup W₁).invariantDifferential :=
    ofPowerSeries_injective hexp
  have hsub : PowerSeries.constantCoeff
      (PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential) = 1 := by
    change MvPowerSeries.constantCoeff
      (PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential) = 1
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero φ.constantCoeff_formalSeries,
      FormalGroup.constantCoeff_invariantDifferential, Algebra.algebraMap_self_apply]
  have hcc := congrArg PowerSeries.constantCoeff hps
  rw [map_mul, hsub, one_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_derivative, zero_add, Nat.cast_zero, zero_add, mul_one,
    PowerSeries.constantCoeff_smul, FormalGroup.constantCoeff_invariantDifferential,
    smul_eq_mul, mul_one] at hcc
  rwa [hcc]

/-- **Formal-group differential pullback along an isogeny**:
`P₂(φ(T)) · φ'(T) = (coeff 1 φ.formalSeries) • P₁(T)`. -/
theorem subst_formalSeries_invariantDifferential_mul_derivative :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
      d⁄dX φ.formalSeries =
      PowerSeries.coeff 1 φ.formalSeries • (formalGroup W₁).invariantDifferential := by
  have := φ.isElliptic
  have hexp := congrArg W₁.differentialLaurentSeries
    (pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul φ)
  rw [differentialLaurentSeries_pullbackDifferential,
    W₂.differentialLaurentSeries_invariantDifferential, LinearMap.map_smul,
    W₁.differentialLaurentSeries_invariantDifferential, LaurentSeries.substAlgHom_coe,
    ← PowerSeries.coe_derivative, ← PowerSeries.coe_mul, ← ofPowerSeries_smul_eq] at hexp
  exact ofPowerSeries_injective hexp

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
  rw [isSeparable_iff_coeff_one_formalSeries_ne_zero,
    show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
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
