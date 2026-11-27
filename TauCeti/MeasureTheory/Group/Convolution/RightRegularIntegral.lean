/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The right regular representation integrated against a kernel

Let `G` be a semigroup with a topology in which multiplication is separately continuous, and `μ`
a measure on `G`. An integrable function `e : G → ℂ` acts on the bounded continuous functions on
`G` by

```text
(ρ(e) F)(x) = ∫ g, e g * F (x * g) ∂μ.
```

The integral is taken pointwise: for each `F` and each `x` it is the Bochner integral of the
scalar function `g ↦ e g * F (x * g)`. In this weak sense `ρ(e)` is the superposition of the right
translations `(R_g F)(x) = F (x * g)` weighted by `e`; it is not an operator-valued Bochner
integral, which need not exist: `g ↦ R_g` is in general not strongly measurable for the operator
norm (on `G = ℝ`, `‖R_g - R_h‖ = 2` whenever `g ≠ h`).
The operator `ρ(e)` has norm at most `∫ ‖e‖`, commutes with left translations, and depends
linearly on `e` and only on its class modulo `μ`-null sets.

For a group with a left-invariant measure, right translation of `ρ(e) F` is integration against a
left translate of `e`, and composition corresponds to convolution: `ρ(e) ∘ ρ(e')` is `ρ` of
`h ↦ ∫ g, e g * e' (g⁻¹ * h) ∂μ`. In particular `ρ(e)` is idempotent when `e` is idempotent for
convolution almost everywhere.

## Main definitions

* `TauCeti.rightRegularIntegral e μ`: the operator `F ↦ (x ↦ ∫ g, e g * F (x * g) ∂μ)` on
  bounded continuous functions, for integrable `e`, and `0` otherwise.

## Main results

* `TauCeti.rightRegularIntegral_apply`, `TauCeti.norm_rightRegularIntegral_le`: the defining
  integral and the bound `‖ρ(e)‖ ≤ ∫ ‖e‖`; `TauCeti.rightRegularIntegral_of_not_integrable`: the
  operator is `0` for non-integrable `e`.
* `TauCeti.rightRegularIntegral_congr_ae`, `TauCeti.rightRegularIntegral_add`,
  `TauCeti.rightRegularIntegral_smul`: `ρ(e)` depends only on the class of `e` modulo null sets,
  and linearly on integrable `e`.
* `TauCeti.rightRegularIntegral_compContinuous_mulLeft`: `ρ(e)` commutes with left translations.
* `TauCeti.rightRegularIntegral_apply_mul`: right translation of `ρ(e) F` is integration against
  a left translate of `e`.
* `TauCeti.rightRegularIntegral_rightRegularIntegral_apply`: `ρ(e) ∘ ρ(e')` is integration
  against the convolution of `e` and `e'`.
* `TauCeti.isIdempotentElem_rightRegularIntegral`: `ρ(e)` is idempotent when `e ⋆ e = e` almost
  everywhere.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction

namespace TauCeti

variable {G : Type*}

section Semigroup

variable [Semigroup G] [TopologicalSpace G] [SeparatelyContinuousMul G] [MeasurableSpace G]
  [OpensMeasurableSpace G] {e : G → ℂ} {μ : Measure G}

omit [Semigroup G] [SeparatelyContinuousMul G] [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The pointwise bound `‖a * F y‖ ≤ ‖a‖ * ‖F‖` for a bounded continuous `F`. -/
private theorem norm_mul_apply_le (a : ℂ) (F : G →ᵇ ℂ) (y : G) : ‖a * F y‖ ≤ ‖a‖ * ‖F‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (F.norm_coe_le_norm _) (norm_nonneg _)

omit [Semigroup G] in
/-- For integrable `e` and bounded continuous `F`, the integrand `g ↦ e g * F (x * g)` is
integrable. -/
private theorem integrable_mul_apply_mul [Mul G] [SeparatelyContinuousMul G]
    (he : Integrable e μ) (F : G →ᵇ ℂ) (x : G) : Integrable (fun g => e g * F (x * g)) μ :=
  he.mul_bdd (F.continuous.comp (continuous_const_mul x)).aestronglyMeasurable
    (Eventually.of_forall fun g => F.norm_coe_le_norm (x * g))

omit [Semigroup G] [SeparatelyContinuousMul G] [OpensMeasurableSpace G] in
private theorem norm_integral_mul_apply_mul_le [Mul G] (he : Integrable e μ) (F : G →ᵇ ℂ)
    (x : G) : ‖∫ g, e g * F (x * g) ∂μ‖ ≤ (∫ g, ‖e g‖ ∂μ) * ‖F‖ := by
  rw [← integral_mul_const]
  exact norm_integral_le_of_norm_le (he.norm.mul_const _)
    (Eventually.of_forall fun g => norm_mul_apply_le (e g) F (x * g))

private theorem continuous_integral_mul_apply_mul [FirstCountableTopology G]
    (he : Integrable e μ) (F : G →ᵇ ℂ) : Continuous fun x => ∫ g, e g * F (x * g) ∂μ :=
  continuous_of_dominated (bound := fun g => ‖e g‖ * ‖F‖)
    (fun x => (integrable_mul_apply_mul he F x).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun g => norm_mul_apply_le (e g) F (x * g))
    (he.norm.mul_const _)
    (Eventually.of_forall fun g =>
      continuous_const.mul (F.continuous.comp (continuous_mul_const g)))

/-- The bounded continuous function `x ↦ ∫ g, e g * F (x * g) ∂μ`, for integrable `e`. -/
private def rightRegularIntegralAux [FirstCountableTopology G] (he : Integrable e μ)
    (F : G →ᵇ ℂ) : G →ᵇ ℂ :=
  .ofNormedAddCommGroup _ (continuous_integral_mul_apply_mul he F) _
    (norm_integral_mul_apply_mul_le he F)

variable [FirstCountableTopology G]

/-- The linear map `F ↦ (x ↦ ∫ g, e g * F (x * g) ∂μ)`, for integrable `e`. -/
private def rightRegularIntegralₗ (he : Integrable e μ) : (G →ᵇ ℂ) →ₗ[ℂ] G →ᵇ ℂ where
  toFun := rightRegularIntegralAux he
  map_add' F F' := by
    ext x
    simp [rightRegularIntegralAux, mul_add,
      integral_add (integrable_mul_apply_mul he F x) (integrable_mul_apply_mul he F' x)]
  map_smul' c F := by
    ext x
    simp [rightRegularIntegralAux, mul_left_comm _ c, integral_const_mul]

private theorem norm_rightRegularIntegralₗ_apply_le (he : Integrable e μ) (F : G →ᵇ ℂ) :
    ‖rightRegularIntegralₗ he F‖ ≤ (∫ g, ‖e g‖ ∂μ) * ‖F‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _))
    (norm_integral_mul_apply_mul_le he F)

open scoped Classical in
variable (e μ) in
/-- **The right regular representation integrated against `e`**: the operator
`F ↦ (x ↦ ∫ g, e g * F (x * g) ∂μ)` on bounded continuous functions, for integrable `e`, and `0`
otherwise. The integral is taken pointwise, for each `F` and `x`; it is not an operator-valued
integral. The operator commutes with left translations, and for a left-invariant measure on a
group composition corresponds to convolution
(`TauCeti.rightRegularIntegral_rightRegularIntegral_apply`). -/
def rightRegularIntegral : (G →ᵇ ℂ) →L[ℂ] G →ᵇ ℂ :=
  if he : Integrable e μ then
    (rightRegularIntegralₗ he).mkContinuous (∫ g, ‖e g‖ ∂μ) (norm_rightRegularIntegralₗ_apply_le he)
  else 0

/-- `ρ(e)` is `0` when `e` is not integrable. -/
@[simp]
theorem rightRegularIntegral_of_not_integrable (he : ¬Integrable e μ) :
    rightRegularIntegral e μ = 0 := by
  simp [rightRegularIntegral, he]

/-- The value of `ρ(e) F` at `x` is `∫ g, e g * F (x * g) ∂μ`, for integrable `e`. -/
@[simp]
theorem rightRegularIntegral_apply (he : Integrable e μ) (F : G →ᵇ ℂ) (x : G) :
    rightRegularIntegral e μ F x = ∫ g, e g * F (x * g) ∂μ := by
  simp only [rightRegularIntegral, he, ↓reduceDIte, LinearMap.mkContinuous_apply,
    rightRegularIntegralₗ, LinearMap.coe_mk, AddHom.coe_mk, rightRegularIntegralAux,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup]

/-- The operator norm of `ρ(e)` is at most `∫ ‖e‖`. -/
theorem norm_rightRegularIntegral_le : ‖rightRegularIntegral e μ‖ ≤ ∫ g, ‖e g‖ ∂μ := by
  have h0 : 0 ≤ ∫ g, ‖e g‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  by_cases he : Integrable e μ
  · refine ContinuousLinearMap.opNorm_le_bound _ h0 fun F =>
      (BoundedContinuousFunction.norm_le (mul_nonneg h0 (norm_nonneg _))).2 fun x => ?_
    rw [rightRegularIntegral_apply he]
    exact norm_integral_mul_apply_mul_le he F x
  · simpa [rightRegularIntegral_of_not_integrable he] using h0

/-- `ρ(e)` only depends on the class of `e` modulo `μ`-null sets. -/
theorem rightRegularIntegral_congr_ae {e' : G → ℂ} (h : e =ᵐ[μ] e') :
    rightRegularIntegral e μ = rightRegularIntegral e' μ := by
  by_cases he : Integrable e μ
  · ext F x
    rw [rightRegularIntegral_apply he, rightRegularIntegral_apply (he.congr h)]
    exact integral_congr_ae (h.mono fun g hg => by simp only [hg])
  · rw [rightRegularIntegral_of_not_integrable he,
      rightRegularIntegral_of_not_integrable fun he' => he (he'.congr h.symm)]

variable (μ) in
/-- `ρ(0) = 0`. -/
@[simp]
theorem rightRegularIntegral_zero : rightRegularIntegral (0 : G → ℂ) μ = 0 := by
  ext F x
  simp [rightRegularIntegral_apply (integrable_zero G ℂ μ)]

/-- `ρ(e + e') = ρ(e) + ρ(e')` for integrable `e` and `e'`. -/
theorem rightRegularIntegral_add {e' : G → ℂ} (he : Integrable e μ) (he' : Integrable e' μ) :
    rightRegularIntegral (e + e') μ = rightRegularIntegral e μ + rightRegularIntegral e' μ := by
  ext F x
  simp [rightRegularIntegral_apply (he.add he'), rightRegularIntegral_apply he,
    rightRegularIntegral_apply he', add_mul,
    integral_add (integrable_mul_apply_mul he F x) (integrable_mul_apply_mul he' F x)]

variable (e μ) in
/-- `ρ(c • e) = c • ρ(e)`. -/
@[simp]
theorem rightRegularIntegral_smul (c : ℂ) :
    rightRegularIntegral (c • e) μ = c • rightRegularIntegral e μ := by
  by_cases he : Integrable e μ
  · ext F x
    simp [rightRegularIntegral_apply (he.smul c), rightRegularIntegral_apply he, mul_assoc,
      integral_const_mul]
  rcases eq_or_ne c 0 with rfl | hc
  · ext F x
    simp
  · ext F x
    simp [rightRegularIntegral_of_not_integrable he,
      rightRegularIntegral_of_not_integrable ((integrable_smul_iff hc e).not.2 he)]

variable (e μ) in
/-- `ρ(-e) = -ρ(e)`. -/
@[simp]
theorem rightRegularIntegral_neg : rightRegularIntegral (-e) μ = -rightRegularIntegral e μ := by
  by_cases he : Integrable e μ
  · ext F x
    simp [rightRegularIntegral_apply he.neg, rightRegularIntegral_apply he, integral_neg]
  · rw [rightRegularIntegral_of_not_integrable he, neg_zero,
      rightRegularIntegral_of_not_integrable (integrable_neg_iff.not.2 he)]

/-- `ρ(e - e') = ρ(e) - ρ(e')` for integrable `e` and `e'`. -/
theorem rightRegularIntegral_sub {e' : G → ℂ} (he : Integrable e μ) (he' : Integrable e' μ) :
    rightRegularIntegral (e - e') μ = rightRegularIntegral e μ - rightRegularIntegral e' μ := by
  rw [sub_eq_add_neg, rightRegularIntegral_add he he'.neg, rightRegularIntegral_neg,
    sub_eq_add_neg]

/-- `ρ(e)` commutes with left translations. -/
@[simp]
theorem rightRegularIntegral_compContinuous_mulLeft (F : G →ᵇ ℂ) (r : G) :
    rightRegularIntegral e μ (F.compContinuous (ContinuousMap.mulLeft r)) =
      (rightRegularIntegral e μ F).compContinuous (ContinuousMap.mulLeft r) := by
  by_cases he : Integrable e μ
  · ext x
    simp [rightRegularIntegral_apply he, mul_assoc]
  · simp [rightRegularIntegral_of_not_integrable he]

end Semigroup

section Group

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [FirstCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {e : G → ℂ} {μ : Measure G}
  [μ.IsMulLeftInvariant]

/-- Right translation of `ρ(e) F` is left translation of `e`:
`(ρ(e) F)(x * b) = ∫ g, e (b⁻¹ * g) * F (x * g) ∂μ`. -/
theorem rightRegularIntegral_apply_mul (he : Integrable e μ) (F : G →ᵇ ℂ) (x b : G) :
    rightRegularIntegral e μ F (x * b) = ∫ g, e (b⁻¹ * g) * F (x * g) ∂μ := by
  rw [rightRegularIntegral_apply he,
    ← integral_mul_left_eq_self (fun g => e (b⁻¹ * g) * F (x * g)) b]
  simp [mul_assoc]

variable [MeasurableMul₂ G] [SFinite μ]

/-- **Composition is convolution**: `ρ(e) (ρ(e') F)` is integration against the convolution
`h ↦ ∫ g, e g * e' (g⁻¹ * h) ∂μ` of `e` and `e'`. -/
theorem rightRegularIntegral_rightRegularIntegral_apply {e' : G → ℂ} (he : Integrable e μ)
    (he' : Integrable e' μ) (F : G →ᵇ ℂ) (x : G) :
    rightRegularIntegral e μ (rightRegularIntegral e' μ F) x =
      ∫ h, (∫ g, e g * e' (g⁻¹ * h) ∂μ) * F (x * h) ∂μ := by
  -- `Φ` is the integrand in the variables `(g, h)` of `ρ(e) ρ(e')`, and `Ψ` is `Φ` after the
  -- shear `(g, h) ↦ (g, g * h)`, which preserves `μ × μ`.
  set Φ : G × G → ℂ := fun q => e q.1 * e' q.2 * F (x * (q.1 * q.2))
  set Ψ : G × G → ℂ := fun q => e q.1 * e' (q.1⁻¹ * q.2) * F (x * q.2)
  have hm := measurePreserving_prod_mul μ μ
  have hm' := (MeasurableEquiv.shearMulRight G).measurableEmbedding
  have hΨΦ : Ψ ∘ (fun q : G × G => (q.1, q.1 * q.2)) = Φ := by
    ext q; simp [Ψ, Φ]
  have hΦ : Integrable Φ (μ.prod μ) :=
    (he.mul_prod he').mul_bdd
      (F.continuous.measurable.comp
        ((measurable_const_mul x).comp measurable_mul)).aestronglyMeasurable
      (Eventually.of_forall fun q => F.norm_coe_le_norm _)
  have hΨ : Integrable Ψ (μ.prod μ) := (hm.integrable_comp_emb hm').1 (hΨΦ ▸ hΦ)
  calc rightRegularIntegral e μ (rightRegularIntegral e' μ F) x
      = ∫ g, ∫ h, Φ (g, h) ∂μ ∂μ := by
        simp_rw [rightRegularIntegral_apply he, rightRegularIntegral_apply he', Φ,
          ← integral_const_mul, mul_assoc]
    _ = ∫ q, Ψ q ∂(μ.prod μ) := by
        rw [← integral_prod Φ hΦ, ← hΨΦ]
        exact hm.integral_comp hm' Ψ
    _ = ∫ h, ∫ g, Ψ (g, h) ∂μ ∂μ := integral_prod_symm Ψ hΨ
    _ = _ := by simp_rw [Ψ, integral_mul_const]

/-- **`ρ(e)` is idempotent when `e` is idempotent for convolution almost everywhere**,
`∫ z, e z * e (z⁻¹ * y) ∂μ = e y` for almost every `y`. -/
theorem isIdempotentElem_rightRegularIntegral
    (he_idem : (fun y => ∫ z, e z * e (z⁻¹ * y) ∂μ) =ᵐ[μ] e) :
    IsIdempotentElem (rightRegularIntegral e μ) := by
  by_cases he : Integrable e μ
  · ext F x
    rw [mul_apply_eq_comp, rightRegularIntegral_rightRegularIntegral_apply he he,
      rightRegularIntegral_apply he]
    refine integral_congr_ae ?_
    filter_upwards [he_idem] with h hh
    rw [hh]
  · rw [rightRegularIntegral_of_not_integrable he]
    exact IsIdempotentElem.zero

end Group

end TauCeti
