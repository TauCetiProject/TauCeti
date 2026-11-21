/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Moments.Variance

/-!
# Unbiased and minimum variance unbiased estimators

For a family of measures `P : Θ → Measure X` and a real function `g` of the parameter, an
estimator `δ : X → ℝ` is unbiased for `g` if it is measurable and, under every `P θ`, integrable
with mean `g θ`. Unbiased estimators of `g₁` and `g₂` add to an unbiased estimator of `g₁ + g₂`,
and scale with `g`.

A square-integrable unbiased estimator `W` of `g` is a uniformly minimum variance unbiased
(UMVU) estimator if at every parameter its variance is at most that of every square-integrable
unbiased estimator of `g`. For finite measures, `W` is UMVU if and only if it is uncorrelated,
under every `P θ`, with every square-integrable unbiased estimator of zero: perturbing `W` by
`a U` for such a `U` changes the variance by `2 a cov[W, U] + a² Var[U]`, which is nonnegative
for all real `a` exactly when the covariance vanishes. Two UMVU estimators of the same `g` agree
`P θ`-almost everywhere, since their difference is an unbiased estimator of zero that is
uncorrelated with both of them and so has variance zero.

## Main definitions

* `TauCeti.IsUnbiasedEstimator P δ g`: `δ` is an unbiased estimator of `g`.
* `TauCeti.IsMinimumVarianceUnbiasedEstimator P W g`: `W` is a UMVU estimator of `g`.

## Main results

* `TauCeti.isMinimumVarianceUnbiasedEstimator_iff_covariance_eq_zero`: the covariance
  characterization of UMVU estimators.
* `TauCeti.IsMinimumVarianceUnbiasedEstimator.ae_eq`: two UMVU estimators of the same function of
  the parameter agree almost everywhere.

The definitions and the covariance characterization are adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>), files `CKSD/Inference/Basic.lean`,
`CKSD/Inference/Model.lean` and `CKSD/Inference/Estimation.lean`.

## References

* M. J. Schervish, *Theory of Statistics*, Springer (1995), Definition 5.4 and Theorem 5.9.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {Θ X : Type*} [MeasurableSpace X] {P : Θ → Measure X} {δ δ₁ δ₂ W W' : X → ℝ}
  {g g₁ g₂ : Θ → ℝ}

/-- `δ` is an unbiased estimator of `g`: it is measurable and, under every `P θ`, integrable with
mean `g θ`. -/
def IsUnbiasedEstimator (P : Θ → Measure X) (δ : X → ℝ) (g : Θ → ℝ) : Prop :=
  Measurable δ ∧ ∀ θ, Integrable δ (P θ) ∧ ∫ x, δ x ∂P θ = g θ

/-- The defining property of an unbiased estimator. -/
theorem isUnbiasedEstimator_iff :
    IsUnbiasedEstimator P δ g ↔ Measurable δ ∧ ∀ θ, Integrable δ (P θ) ∧ ∫ x, δ x ∂P θ = g θ :=
  Iff.rfl

namespace IsUnbiasedEstimator

/-- An unbiased estimator from measurability, integrability and the means. -/
theorem mk (hδ : Measurable δ) (hint : ∀ θ, Integrable δ (P θ))
    (hmean : ∀ θ, ∫ x, δ x ∂P θ = g θ) : IsUnbiasedEstimator P δ g :=
  ⟨hδ, fun θ ↦ ⟨hint θ, hmean θ⟩⟩

/-- An unbiased estimator is measurable. -/
theorem measurable (h : IsUnbiasedEstimator P δ g) : Measurable δ := h.1

/-- An unbiased estimator is integrable under every `P θ`. -/
theorem integrable (h : IsUnbiasedEstimator P δ g) (θ : Θ) : Integrable δ (P θ) := (h.2 θ).1

/-- The mean of an unbiased estimator of `g` under `P θ` is `g θ`. -/
theorem integral_eq (h : IsUnbiasedEstimator P δ g) (θ : Θ) : ∫ x, δ x ∂P θ = g θ := (h.2 θ).2

/-- The sum of unbiased estimators of `g₁` and `g₂` is an unbiased estimator of `g₁ + g₂`. -/
theorem add (h₁ : IsUnbiasedEstimator P δ₁ g₁) (h₂ : IsUnbiasedEstimator P δ₂ g₂) :
    IsUnbiasedEstimator P (fun x ↦ δ₁ x + δ₂ x) (fun θ ↦ g₁ θ + g₂ θ) :=
  .mk (h₁.measurable.add h₂.measurable) (fun θ ↦ (h₁.integrable θ).add (h₂.integrable θ))
    fun θ ↦ by
      rw [integral_add (h₁.integrable θ) (h₂.integrable θ), h₁.integral_eq, h₂.integral_eq]

/-- The difference of unbiased estimators of `g₁` and `g₂` is an unbiased estimator of
`g₁ - g₂`. -/
theorem sub (h₁ : IsUnbiasedEstimator P δ₁ g₁) (h₂ : IsUnbiasedEstimator P δ₂ g₂) :
    IsUnbiasedEstimator P (fun x ↦ δ₁ x - δ₂ x) (fun θ ↦ g₁ θ - g₂ θ) :=
  .mk (h₁.measurable.sub h₂.measurable) (fun θ ↦ (h₁.integrable θ).sub (h₂.integrable θ))
    fun θ ↦ by
      rw [integral_sub (h₁.integrable θ) (h₂.integrable θ), h₁.integral_eq, h₂.integral_eq]

/-- A multiple `c δ` of an unbiased estimator of `g` is an unbiased estimator of `c g`. -/
theorem const_mul (h : IsUnbiasedEstimator P δ g) (c : ℝ) :
    IsUnbiasedEstimator P (fun x ↦ c * δ x) (fun θ ↦ c * g θ) :=
  .mk (measurable_const.mul h.measurable) (fun θ ↦ (h.integrable θ).const_mul c)
    fun θ ↦ by rw [integral_const_mul, h.integral_eq]

end IsUnbiasedEstimator

/-- `W` is a uniformly minimum variance unbiased estimator of `g`: a square-integrable unbiased
estimator of `g` whose variance under every `P θ` is at most that of every square-integrable
unbiased estimator of `g`. -/
def IsMinimumVarianceUnbiasedEstimator (P : Θ → Measure X) (W : X → ℝ) (g : Θ → ℝ) : Prop :=
  IsUnbiasedEstimator P W g ∧ (∀ θ, MemLp W 2 (P θ)) ∧
    ∀ W', IsUnbiasedEstimator P W' g → (∀ θ, MemLp W' 2 (P θ)) → ∀ θ, Var[W; P θ] ≤ Var[W'; P θ]

/-- The defining property of a UMVU estimator. -/
theorem isMinimumVarianceUnbiasedEstimator_iff :
    IsMinimumVarianceUnbiasedEstimator P W g ↔
      IsUnbiasedEstimator P W g ∧ (∀ θ, MemLp W 2 (P θ)) ∧
        ∀ W', IsUnbiasedEstimator P W' g → (∀ θ, MemLp W' 2 (P θ)) →
          ∀ θ, Var[W; P θ] ≤ Var[W'; P θ] :=
  Iff.rfl

namespace IsMinimumVarianceUnbiasedEstimator

/-- A UMVU estimator from unbiasedness, square integrability and the variance bound. -/
theorem mk (hW : IsUnbiasedEstimator P W g) (hW2 : ∀ θ, MemLp W 2 (P θ))
    (hle : ∀ W', IsUnbiasedEstimator P W' g → (∀ θ, MemLp W' 2 (P θ)) →
      ∀ θ, Var[W; P θ] ≤ Var[W'; P θ]) :
    IsMinimumVarianceUnbiasedEstimator P W g :=
  ⟨hW, hW2, hle⟩

/-- A UMVU estimator of `g` is an unbiased estimator of `g`. -/
theorem isUnbiasedEstimator (h : IsMinimumVarianceUnbiasedEstimator P W g) :
    IsUnbiasedEstimator P W g := h.1

/-- A UMVU estimator is square-integrable under every `P θ`. -/
theorem memLp (h : IsMinimumVarianceUnbiasedEstimator P W g) (θ : Θ) : MemLp W 2 (P θ) := h.2.1 θ

/-- The variance of a UMVU estimator is at most that of every square-integrable unbiased
estimator of the same `g`. -/
theorem variance_le (h : IsMinimumVarianceUnbiasedEstimator P W g)
    (hW' : IsUnbiasedEstimator P W' g) (hW'2 : ∀ θ, MemLp W' 2 (P θ)) (θ : Θ) :
    Var[W; P θ] ≤ Var[W'; P θ] :=
  h.2.2 W' hW' hW'2 θ

/-- A UMVU estimator is uncorrelated, under every `P θ`, with every square-integrable unbiased
estimator of zero. -/
theorem covariance_eq_zero (h : IsMinimumVarianceUnbiasedEstimator P W g) {U : X → ℝ}
    (hU : IsUnbiasedEstimator P U (fun _ ↦ 0)) (hU2 : ∀ θ, MemLp U 2 (P θ)) (θ : Θ)
    [IsFiniteMeasure (P θ)] :
    cov[W, U; P θ] = 0 := by
  have hquad (a : ℝ) : 0 ≤ Var[U; P θ] * (a * a) + 2 * cov[W, U; P θ] * a + 0 := by
    have hWa := h.isUnbiasedEstimator.add (hU.const_mul a)
    have hle := h.variance_le (W' := fun x ↦ W x + a * U x) (by simpa using hWa)
      (fun t ↦ (h.memLp t).add ((hU2 t).const_mul a)) θ
    rw [variance_fun_add (h.memLp θ) ((hU2 θ).const_mul a), covariance_const_mul_right,
      variance_const_mul] at hle
    nlinarith
  have hd := discrim_le_zero hquad
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg cov[W, U; P θ]]

end IsMinimumVarianceUnbiasedEstimator

/-- The covariance characterization of UMVU estimators: a square-integrable unbiased estimator
`W` of `g` is UMVU if and only if it is uncorrelated, under every `P θ`, with every
square-integrable unbiased estimator of zero. -/
theorem isMinimumVarianceUnbiasedEstimator_iff_covariance_eq_zero (P : Θ → Measure X)
    [∀ θ, IsFiniteMeasure (P θ)] (W : X → ℝ) (g : Θ → ℝ) (hW : IsUnbiasedEstimator P W g)
    (hW2 : ∀ θ, MemLp W 2 (P θ)) :
    IsMinimumVarianceUnbiasedEstimator P W g ↔
      ∀ U, IsUnbiasedEstimator P U (fun _ ↦ 0) → (∀ θ, MemLp U 2 (P θ)) →
        ∀ θ, cov[W, U; P θ] = 0 := by
  refine ⟨fun h U hU hU2 θ ↦ h.covariance_eq_zero hU hU2 θ, fun h ↦ .mk hW hW2 ?_⟩
  intro W' hW' hW'2 θ
  have hU2 (t : Θ) : MemLp (fun x ↦ W' x - W x) 2 (P t) := (hW'2 t).sub (hW2 t)
  have hadd := variance_fun_add (hW2 θ) (hU2 θ)
  simp only [add_sub_cancel] at hadd
  rw [hadd, h _ (by simpa using hW'.sub hW) hU2 θ, mul_zero, add_zero]
  exact le_add_of_nonneg_right (variance_nonneg _ _)

/-- Two UMVU estimators of the same function of the parameter agree `P θ`-almost everywhere. -/
theorem IsMinimumVarianceUnbiasedEstimator.ae_eq (hW : IsMinimumVarianceUnbiasedEstimator P W g)
    (hW' : IsMinimumVarianceUnbiasedEstimator P W' g) (θ : Θ) [IsFiniteMeasure (P θ)] :
    W =ᵐ[P θ] W' := by
  have hU := hW'.isUnbiasedEstimator.sub hW.isUnbiasedEstimator
  simp only [sub_self] at hU
  have hU2 (t : Θ) : MemLp (fun x ↦ W' x - W x) 2 (P t) := (hW'.memLp t).sub (hW.memLp t)
  have hvar : Var[fun x ↦ W' x - W x; P θ] = 0 := by
    rw [← covariance_self (hU.measurable.aemeasurable),
      covariance_fun_sub_left (hW'.memLp θ) (hW.memLp θ) (hU2 θ),
      hW'.covariance_eq_zero hU hU2 θ, hW.covariance_eq_zero hU hU2 θ, sub_zero]
  filter_upwards [ae_eq_integral_of_variance_eq_zero (hU2 θ) hvar] with x hx
  rw [hU.integral_eq θ, sub_eq_zero] at hx
  exact hx.symm

end TauCeti
