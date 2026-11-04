/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.FactorsThrough
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.Calculus.FDeriv.Measurable
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.MeasureTheory.Integral.Measurable
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The continuity equation

Let `E` be a finite-dimensional real normed space, `μ : ℝ → Measure E` a family of Borel measures
and `v : ℝ → E → E` a Borel velocity field. The *continuity equation* on the time interval `(a, b)`
is `∂ₜ μₜ + div (vₜ μₜ) = 0`, understood in the sense of distributions: for every smooth compactly
supported test function `φ : ℝ × E → ℝ` whose support lies in `(a, b) × E`,
`∫_a^b ∫_E (∂ₜ φ (t, x) + ⟨∇ₓ φ (t, x), vₜ x⟩) dμₜ(x) dt = 0`.
In a normed space the integrand is the space-time derivative of `φ` applied to the space-time
velocity `(1, vₜ x)`, that is `fderiv ℝ φ (t, x) (1, v t x)`; this fixes the sign convention of the
equation together with its test-function identity. Finite dimensionality is essential: in an
infinite-dimensional space every compactly supported continuous function vanishes, so the identity
would be vacuous. The definition `TauCeti.IsContinuityEquation` also records the measurability of
the time slices `t ↦ μₜ` and of `v`, and the integrability of the total mass `t ↦ μₜ E` and of
`∫ ‖vₜ‖ dμₜ` over `(a, b)`, which make every integral in the identity absolutely convergent.

The continuity equation is the Eulerian description of mass moving with velocity `v`. Its basic
source of solutions is the Lagrangian one: if `P` is a finite measure on a parameter space `Ω` and
`γ : Ω → ℝ → E` is a measurable family of absolutely continuous curves with
`deriv γ_ω t = vₜ (γ_ω t)` for almost every `(ω, t)`, and with finite expected length
`∫ ∫_a^b ‖vₜ (γ_ω t)‖ dt dP(ω) < ∞`, then the laws `μₜ = (γ · t)₊ P` of the
positions at time `t` solve the continuity equation with velocity `v`
(`TauCeti.isContinuityEquation_map`). For `Ω` a space of curves and `γ` the evaluation map this is
the statement for a law on paths. A translating law, a stationary law and a Dirac mass moving along
an absolutely continuous curve are special cases.

The curves need not follow a common velocity field. If `γ_ω` has derivative `V ω t` at almost
every time, with `V` jointly measurable and of finite expected length, then the laws `μₜ` solve the
continuity equation with the *barycentric velocity* `v`: its value at the position `γ_ω t` is the
conditional expectation of `V ω t` given the time `t` and the position `γ_ω t`, for the measure
`dt ⊗ P` (`TauCeti.exists_isContinuityEquation_map`). By Jensen's inequality,
`∫_a^b ∫ ‖vₜ‖ ^ p dμₜ dt ≤ ∫ ∫_a^b ‖V ω t‖ ^ p dt dP(ω)` for every `p ≥ 1`: the action of the
velocity field is at most the expected action of the curves.

## Main definitions

* `TauCeti.IsContinuityEquation μ v a b`: the family `μ` solves the continuity equation with
  velocity `v` in the sense of distributions on the time interval `(a, b)`.

## Main results

* `TauCeti.IsContinuityEquation.mono`: a solution on `(a, b)` is a solution on every subinterval.
* `TauCeti.IsContinuityEquation.congr`: the velocity field matters only `μₜ`-almost everywhere, for
  almost every time `t`.
* `TauCeti.IsContinuityEquation.lintegral_lintegral_enorm_fderiv_lt_top`,
  `TauCeti.IsContinuityEquation.ae_integrable_fderiv` and
  `TauCeti.IsContinuityEquation.integrableOn_integral_fderiv`: for every `C¹` compactly supported
  test function, the integrand of the continuity equation is absolutely integrable against `μₜ dt`,
  integrable against `μₜ` for almost every `t`, and its spatial integral is integrable in time.
* `TauCeti.IsContinuityEquation.integrableOn_integral_of_norm_le`: the spatial integral of a
  bounded jointly strongly measurable function with values in a normed real vector space is
  integrable over `(a, b)`.
* `TauCeti.IsContinuityEquation.integrableOn_integral_fderiv_of_norm_fderiv_le`: for a real-valued
  function with bounded derivative, the spatial integral of the integrand of the continuity
  equation is integrable over `(a, b)`.
* `TauCeti.isContinuityEquation_map`: the laws at time `t` of a measurable family of absolutely
  continuous curves following `v`, with finite expected length, solve the continuity equation with
  velocity `v`.
* `TauCeti.exists_isContinuityEquation_map`: the laws at time `t` of a measurable family of
  absolutely continuous curves with finite expected length solve the continuity equation with
  their barycentric velocity, whose `p`-action is at most the expected `p`-action of the curves.
* `TauCeti.isContinuityEquation_map_add_smul`: a law translating with constant velocity `w`
  solves the continuity equation with velocity field `w`.
* `TauCeti.isContinuityEquation_const`: a stationary law solves it with velocity field `0`.
* `TauCeti.isContinuityEquation_dirac`: a Dirac mass moving along an absolutely continuous curve
  `γ` solves it with any velocity field equal to `deriv γ` along `γ`.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §8.1, and §8.3 for the barycentric velocity of
  a law on curves.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §4.1.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The family of measures `μ : ℝ → Measure E` solves the continuity equation
`∂ₜ μₜ + div (vₜ μₜ) = 0` with velocity field `v` on the time interval `(a, b)`, in the sense of
distributions: for every smooth compactly supported `φ : ℝ × E → ℝ` with support in `(a, b) × E`,
`∫_a^b ∫ (∂ₜ φ (t, x) + ⟨∇ₓ φ (t, x), vₜ x⟩) dμₜ(x) dt = 0`, the integrand being written as the
space-time derivative `fderiv ℝ φ (t, x)` applied to `(1, v t x)`. The time slices `t ↦ μₜ` and the
velocity field are measurable, and the total mass and `∫ ‖vₜ‖ dμₜ` are integrable over `(a, b)`.
The space `E` is finite-dimensional with its Borel σ-algebra, so that the test functions separate
measures and every integrand in the identity is measurable. -/
structure IsContinuityEquation [FiniteDimensional ℝ E] [BorelSpace E] (μ : ℝ → Measure E)
    (v : ℝ → E → E) (a b : ℝ) : Prop where
  /-- The time slices `t ↦ μₜ` form a measurable family of measures. -/
  measurable : Measurable μ
  /-- The velocity field is jointly measurable in time and space. -/
  measurable_velocity : Measurable (uncurry v)
  /-- The total mass of `μₜ` is integrable over the time interval. -/
  lintegral_measure_univ_lt_top : ∫⁻ t in Ioo a b, μ t univ < ∞
  /-- The velocity field is integrable against `μₜ dt`. -/
  lintegral_lintegral_enorm_lt_top : ∫⁻ t in Ioo a b, ∫⁻ x, ‖v t x‖ₑ ∂μ t < ∞
  /-- The distributional identity `∫_a^b ∫ (∂ₜ φ + ⟨∇ₓ φ, vₜ⟩) dμₜ dt = 0`. -/
  integral_integral_fderiv_eq_zero ⦃φ : ℝ × E → ℝ⦄ (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ univ) :
    ∫ t in Ioo a b, ∫ x, fderiv ℝ φ (t, x) (1, v t x) ∂μ t = 0

variable [FiniteDimensional ℝ E] [BorelSpace E] {μ : ℝ → Measure E} {v w : ℝ → E → E} {a b c d : ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Outside the time projection of the support of the test function, the integrand of the
continuity equation vanishes identically. -/
private lemma integral_fderiv_eq_zero_of_notMem {φ : ℝ × E → ℝ} {I : Set ℝ}
    (hφs : tsupport φ ⊆ I ×ˢ univ) {t : ℝ} (ht : t ∉ I) (ν : Measure E) (u : E → E) :
    ∫ x, fderiv ℝ φ (t, x) (1, u x) ∂ν = 0 := by
  have h (x : E) : fderiv ℝ φ (t, x) = 0 := fderiv_of_notMem_tsupport ℝ fun hx ↦ ht (hφs hx).1
  simp [h]

namespace IsContinuityEquation

/-- A solution of the continuity equation on `(a, b)` solves it on every subinterval `(c, d)`. -/
theorem mono (h : IsContinuityEquation μ v a b) (hac : a ≤ c) (hdb : d ≤ b) :
    IsContinuityEquation μ v c d where
  measurable := h.measurable
  measurable_velocity := h.measurable_velocity
  lintegral_measure_univ_lt_top :=
    (lintegral_mono_set (Ioo_subset_Ioo hac hdb)).trans_lt h.lintegral_measure_univ_lt_top
  lintegral_lintegral_enorm_lt_top :=
    (lintegral_mono_set (Ioo_subset_Ioo hac hdb)).trans_lt h.lintegral_lintegral_enorm_lt_top
  integral_integral_fderiv_eq_zero φ hφ hφc hφs := by
    have hsub := Ioo_subset_Ioo hac hdb
    rw [← h.integral_integral_fderiv_eq_zero hφ hφc (hφs.trans (prod_mono hsub subset_rfl))]
    exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hsub
      fun t ht ↦ integral_fderiv_eq_zero_of_notMem hφs ht.2 _ _).symm

/-- The velocity field of a solution of the continuity equation matters only `μₜ`-almost
everywhere, for almost every time `t`: replacing it by a measurable field which agrees with it
there gives another solution. -/
theorem congr (h : IsContinuityEquation μ v a b) (hw : Measurable (uncurry w))
    (hvw : ∀ᵐ t, t ∈ Ioo a b → v t =ᵐ[μ t] w t) : IsContinuityEquation μ w a b where
  measurable := h.measurable
  measurable_velocity := hw
  lintegral_measure_univ_lt_top := h.lintegral_measure_univ_lt_top
  lintegral_lintegral_enorm_lt_top := by
    refine Eq.trans_lt (setLIntegral_congr_fun_ae measurableSet_Ioo ?_)
      h.lintegral_lintegral_enorm_lt_top
    filter_upwards [hvw] with t ht hmem
    exact lintegral_congr_ae <| (ht hmem).mono fun x hx ↦ by simp [hx]
  integral_integral_fderiv_eq_zero φ hφ hφc hφs := by
    refine Eq.trans (setIntegral_congr_ae measurableSet_Ioo ?_)
      (h.integral_integral_fderiv_eq_zero hφ hφc hφs)
    filter_upwards [hvw] with t ht hmem
    exact integral_congr_ae <| (ht hmem).mono fun x hx ↦ by simp [hx]

/-- For almost every time `t ∈ (a, b)` the slice `μₜ` has finite mass. -/
private lemma ae_measure_univ_ne_top (h : IsContinuityEquation μ v a b) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), μ t univ ≠ ∞ :=
  (ae_lt_top ((Measure.measurable_coe .univ).comp h.measurable)
    h.lintegral_measure_univ_lt_top.ne).mono fun _ ht ↦ ht.ne

/-- The integrand of the continuity equation is absolutely integrable against `μₜ dt` on `(a, b)`,
for every `C¹` compactly supported test function `φ`. -/
theorem lintegral_lintegral_enorm_fderiv_lt_top (h : IsContinuityEquation μ v a b)
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫⁻ t in Ioo a b, ∫⁻ x, ‖fderiv ℝ φ (t, x) (1, v t x)‖ₑ ∂μ t < ∞ := by
  obtain ⟨C, hC⟩ :=
    (hφ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hφc.fderiv ℝ)
  have hle (t : ℝ) (x : E) :
      ‖fderiv ℝ φ (t, x) (1, v t x)‖ₑ ≤ ENNReal.ofReal C * (1 + ‖v t x‖ₑ) := by
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (norm_nonneg _),
      ← ENNReal.ofReal_mul ((norm_nonneg _).trans (hC 0))]
    exact ENNReal.ofReal_le_ofReal <|
      (fderiv ℝ φ _).le_of_opNorm_le_of_le (hC _) (by simp [Prod.norm_def])
  have hv (t : ℝ) : Measurable fun x ↦ 1 + ‖v t x‖ₑ :=
    measurable_const.add (h.measurable_velocity.comp measurable_prodMk_left).enorm
  have hm : Measurable fun t ↦ μ t univ := (Measure.measurable_coe .univ).comp h.measurable
  calc ∫⁻ t in Ioo a b, ∫⁻ x, ‖fderiv ℝ φ (t, x) (1, v t x)‖ₑ ∂μ t
      ≤ ∫⁻ t in Ioo a b, ENNReal.ofReal C * (μ t univ + ∫⁻ x, ‖v t x‖ₑ ∂μ t) := by
        refine lintegral_mono fun t ↦ (lintegral_mono (hle t)).trans_eq ?_
        rw [lintegral_const_mul _ (hv t), lintegral_add_left measurable_const, lintegral_one]
    _ < ∞ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left hm]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.add_lt_top.2 ⟨h.lintegral_measure_univ_lt_top,
            h.lintegral_lintegral_enorm_lt_top⟩)

/-- For almost every time `t ∈ (a, b)`, the integrand of the continuity equation is integrable
against `μₜ`, for every `C¹` compactly supported test function `φ`. -/
theorem ae_integrable_fderiv (h : IsContinuityEquation μ v a b) {φ : ℝ × E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ t, t ∈ Ioo a b → Integrable (fun x ↦ fderiv ℝ φ (t, x) (1, v t x)) (μ t) := by
  have hF : Measurable fun q : ℝ × E ↦ fderiv ℝ φ q (1, v q.1 q.2) :=
    (measurable_fderiv_apply ℝ φ).comp
      (measurable_id.prodMk (measurable_const.prodMk h.measurable_velocity))
  rw [← ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [ae_lt_top' (hF.enorm.aemeasurable_lintegral_measure
      h.measurable h.ae_measure_univ_ne_top)
    (h.lintegral_lintegral_enorm_fderiv_lt_top hφ hφc).ne] with t ht
  exact ⟨(hF.comp measurable_prodMk_left).aestronglyMeasurable, ht⟩

/-- The spatial integral of the integrand of the continuity equation is integrable over `(a, b)`,
for every `C¹` compactly supported test function `φ`. -/
theorem integrableOn_integral_fderiv (h : IsContinuityEquation μ v a b) {φ : ℝ × E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    IntegrableOn (fun t ↦ ∫ x, fderiv ℝ φ (t, x) (1, v t x) ∂μ t) (Ioo a b) := by
  have hF : Measurable fun q : ℝ × E ↦ fderiv ℝ φ q (1, v q.1 q.2) :=
    (measurable_fderiv_apply ℝ φ).comp
      (measurable_id.prodMk (measurable_const.prodMk h.measurable_velocity))
  refine ⟨hF.stronglyMeasurable.aestronglyMeasurable_integral_measure
    h.measurable h.ae_measure_univ_ne_top, ?_⟩
  exact (lintegral_mono fun t ↦ enorm_integral_le_lintegral_enorm _).trans_lt
    (h.lintegral_lintegral_enorm_fderiv_lt_top hφ hφc)

/-- For almost every time `t ∈ (a, b)`, the slice `μₜ` is finite and `vₜ` is `μₜ`-integrable. -/
theorem ae_isFiniteMeasure_and_integrable (h : IsContinuityEquation μ v a b) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), IsFiniteMeasure (μ t) ∧ Integrable (v t) (μ t) := by
  have hm : Measurable fun t ↦ μ t univ := (Measure.measurable_coe .univ).comp h.measurable
  filter_upwards [ae_lt_top hm h.lintegral_measure_univ_lt_top.ne,
    ae_lt_top' (h.measurable_velocity.enorm.aemeasurable_lintegral_measure
      h.measurable h.ae_measure_univ_ne_top)
      h.lintegral_lintegral_enorm_lt_top.ne] with t h₁ h₂
  exact ⟨⟨h₁⟩, (h.measurable_velocity.comp measurable_prodMk_left).aestronglyMeasurable, h₂⟩

/-- The total mass of `μₜ` is integrable over `(a, b)`. -/
theorem integrableOn_measureReal_univ (h : IsContinuityEquation μ v a b) :
    IntegrableOn (fun t ↦ (μ t).real univ) (Ioo a b) := by
  simp_rw [measureReal_def]
  exact integrable_toReal_of_lintegral_ne_top
    ((Measure.measurable_coe .univ).comp h.measurable).aemeasurable
    h.lintegral_measure_univ_lt_top.ne

/-- The `μₜ`-integral of `‖vₜ‖` is integrable over `(a, b)`. -/
theorem integrableOn_integral_norm (h : IsContinuityEquation μ v a b) :
    IntegrableOn (fun t ↦ ∫ x, ‖v t x‖ ∂μ t) (Ioo a b) := by
  refine (integrable_toReal_of_lintegral_ne_top
    (h.measurable_velocity.enorm.aemeasurable_lintegral_measure
      h.measurable h.ae_measure_univ_ne_top)
    h.lintegral_lintegral_enorm_lt_top.ne).congr (ae_of_all _ fun t ↦ ?_)
  exact (integral_norm_eq_lintegral_enorm
    (h.measurable_velocity.comp measurable_prodMk_left).aestronglyMeasurable).symm

/-- For a bounded jointly strongly measurable function `f` of time and space with values in a
normed real vector space, the function
`t ↦ ∫ f (t, x) dμₜ(x)` is integrable over `(a, b)`. -/
theorem integrableOn_integral_of_norm_le (h : IsContinuityEquation μ v a b) {f : ℝ × E → F}
    (hf : StronglyMeasurable f) {M : ℝ} (hM : ∀ q, ‖f q‖ ≤ M) :
    IntegrableOn (fun t ↦ ∫ x, f (t, x) ∂μ t) (Ioo a b) := by
  refine (h.integrableOn_measureReal_univ.const_mul M).mono'
    (hf.aestronglyMeasurable_integral_measure (f := fun t x ↦ f (t, x))
      h.measurable h.ae_measure_univ_ne_top) ?_
  filter_upwards [h.ae_isFiniteMeasure_and_integrable] with t ⟨_, _⟩
  exact norm_integral_le_of_norm_le_const (ae_of_all _ fun x ↦ hM _)

/-- For a function `u` of time and space with bounded derivative, the spatial integral
`t ↦ ∫ fderiv ℝ u (t, x) (1, vₜ x) dμₜ(x)` of the integrand of the continuity equation is
integrable over `(a, b)`. -/
theorem integrableOn_integral_fderiv_of_norm_fderiv_le (h : IsContinuityEquation μ v a b)
    {u : ℝ × E → ℝ} {M : ℝ} (hM : ∀ q, ‖fderiv ℝ u q‖ ≤ M) :
    IntegrableOn (fun t ↦ ∫ x, fderiv ℝ u (t, x) (1, v t x) ∂μ t) (Ioo a b) := by
  have hF : Measurable (uncurry fun t x ↦ fderiv ℝ u (t, x) (1, v t x)) :=
    (measurable_fderiv_apply ℝ u).comp
      (measurable_id.prodMk (measurable_const.prodMk h.measurable_velocity))
  refine ((h.integrableOn_measureReal_univ.add h.integrableOn_integral_norm).const_mul M).mono'
    (hF.stronglyMeasurable.aestronglyMeasurable_integral_measure
      h.measurable h.ae_measure_univ_ne_top) ?_
  filter_upwards [h.ae_isFiniteMeasure_and_integrable] with t ⟨_, hvi⟩
  have hbi : Integrable (fun x ↦ M * (1 + ‖v t x‖)) (μ t) :=
    ((integrable_const 1).add hvi.norm).const_mul M
  refine (norm_integral_le_of_norm_le hbi (ae_of_all _ fun x ↦ (fderiv ℝ u _).le_of_opNorm_le_of_le
    (hM _) (norm_prod_le_iff.2 ⟨by simp, by simp⟩))).trans_eq ?_
  rw [integral_const_mul, integral_add (integrable_const 1) hvi.norm, integral_const,
    smul_eq_mul, mul_one, Pi.add_apply]

end IsContinuityEquation

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Along a curve `γ` absolutely continuous on `[a, b]` with derivative `V`, the integrand of the
continuity equation integrates to zero over `(a, b)` for every `C¹` test function supported in
`(a, b) × E`: it is the derivative of `t ↦ φ (t, γ t)`, which vanishes at both endpoints. -/
private lemma integral_fderiv_eq_zero_of_hasDerivAt {φ : ℝ × E → ℝ} (hφ1 : ContDiff ℝ 1 φ)
    (hφs : tsupport φ ⊆ Ioo a b ×ˢ univ) {γ V : ℝ → E}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hd : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt γ (V t) t) :
    ∫ t in Ioo a b, fderiv ℝ φ (t, γ t) (1, V t) = 0 := by
  rcases lt_or_ge a b with hab | hab
  swap
  · simp [Ioo_eq_empty_of_le hab]
  have hzero (s : ℝ) (hs : s ∉ Ioo a b) : φ (s, γ s) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hs (hφs h).1
  have hd' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt (fun t ↦ (t, γ t)) (1, V t) t := by
    rw [uIoc_of_le hab.le]
    filter_upwards [hd, compl_mem_ae_iff.2 (measure_singleton b)] with t ht htb hmem
    exact (hasDerivAt_id' t).prodMk (ht ⟨hmem.1, hmem.2.lt_of_ne htb⟩)
  have := (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval.prodMk
    hγ).integral_fderiv_apply_eq_sub hd' hφ1
  simp only [id, hzero a (by simp), hzero b (by simp), sub_self] at this
  rwa [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] at this

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- For a `C¹` compactly supported test function `φ`, the integrand of the continuity equation
along a time and position `G` and a velocity `Y` is integrable against a finite measure whenever
`Y` is: the space-time velocity `(1, Y)` is integrable. -/
private lemma integrable_fderiv_apply_one {S : Type*} [MeasurableSpace S] {ν : Measure S}
    [IsFiniteMeasure ν] {φ : ℝ × E → ℝ} (hφ1 : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    {G : S → ℝ × E} (hG : AEStronglyMeasurable G ν) {Y : S → E} (hY : Integrable Y ν) :
    Integrable (fun q ↦ fderiv ℝ φ (G q) (1, Y q)) ν :=
  integrable_fderiv_apply hφ1 hφc hG ((integrable_const 1).prodMk hY)

/-- **Lagrangian solutions of the continuity equation.** Let `P` be a finite measure on a parameter
space `Ω` and `γ : Ω → ℝ → E` a jointly measurable family of curves. If `P`-almost every curve is
absolutely continuous on `[a, b]` and follows the velocity field `v`, in the sense that
`deriv γ_ω t = vₜ (γ_ω t)` for almost every `t ∈ (a, b)`, and the expected length
`∫ ∫_a^b ‖vₜ (γ_ω t)‖ dt dP(ω)` is finite, then the laws `(γ · t)₊ P` of the positions at time `t`
solve the continuity equation with velocity `v` on `(a, b)`. -/
theorem isContinuityEquation_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {γ : Ω → ℝ → E}
    (hγ : Measurable (uncurry γ)) (hv : Measurable (uncurry v))
    (hac : ∀ᵐ ω ∂P, AbsolutelyContinuousOnInterval (γ ω) a b)
    (hderiv : ∀ᵐ ω ∂P, ∀ᵐ t, t ∈ Ioo a b → HasDerivAt (γ ω) (v t (γ ω t)) t)
    (hint : ∫⁻ ω, (∫⁻ t in Ioo a b, ‖v t (γ ω t)‖ₑ) ∂P < ∞) :
    IsContinuityEquation (fun t ↦ P.map (γ · t)) v a b := by
  have hγt (t : ℝ) : Measurable (γ · t) := hγ.comp measurable_prodMk_right
  -- the curves read as a function of `(t, ω)`
  have hγ' : Measurable fun q : ℝ × Ω ↦ γ q.2 q.1 := hγ.comp measurable_swap
  have hvγ : Measurable fun q : ℝ × Ω ↦ ‖v q.1 (γ q.2 q.1)‖ₑ :=
    (hv.comp (measurable_fst.prodMk hγ')).enorm
  have hint' : ∫⁻ t in Ioo a b, ∫⁻ ω, ‖v t (γ ω t)‖ₑ ∂P < ∞ := by
    rwa [← lintegral_lintegral_swap (f := fun ω t ↦ ‖v t (γ ω t)‖ₑ)
      (hvγ.comp measurable_swap).aemeasurable]
  refine ⟨MeasureTheory.measurable_map_of_measurable_uncurry (hγ.comp measurable_swap), hv, ?_, ?_,
    fun φ hφ hφc hφs ↦ ?_⟩
  · simp only [Measure.map_apply (hγt _) MeasurableSet.univ, preimage_univ, setLIntegral_const]
    exact ENNReal.mul_lt_top (measure_lt_top P univ) measure_Ioo_lt_top
  · have hmap (t : ℝ) : ∫⁻ x, ‖v t x‖ₑ ∂P.map (γ · t) = ∫⁻ ω, ‖v t (γ ω t)‖ₑ ∂P :=
      lintegral_map (hv.comp measurable_prodMk_left).enorm (hγt t)
    simpa only [hmap] using hint'
  -- the integrand `(t, x) ↦ fderiv ℝ φ (t, x) (1, v t x)` is measurable and has linear growth
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hF : Measurable fun q : ℝ × E ↦ fderiv ℝ φ q (1, v q.1 q.2) :=
    (measurable_fderiv_apply ℝ φ).comp (measurable_id.prodMk (measurable_const.prodMk hv))
  have hpush (t : ℝ) : ∫ x, fderiv ℝ φ (t, x) (1, v t x) ∂P.map (γ · t) =
      ∫ ω, fderiv ℝ φ (t, γ ω t) (1, v t (γ ω t)) ∂P :=
    integral_map (hγt t).aemeasurable (hF.comp measurable_prodMk_left).aestronglyMeasurable
  simp_rw [hpush]
  -- swap the order of integration, then integrate along each curve
  have : IsFiniteMeasure (volume.restrict (Ioo a b)) := ⟨by simp⟩
  have hInt : Integrable (uncurry fun t ω ↦ fderiv ℝ φ (t, γ ω t) (1, v t (γ ω t)))
      ((volume.restrict (Ioo a b)).prod P) := by
    refine integrable_fderiv_apply_one hφ1 hφc (measurable_fst.prodMk hγ').aestronglyMeasurable
      ⟨(hv.comp (measurable_fst.prodMk hγ')).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa only [lintegral_prod _ hvγ.aemeasurable] using hint'
  rw [integral_integral_swap hInt]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hac, hderiv] with ω hω hω'
  exact integral_fderiv_eq_zero_of_hasDerivAt hφ1 hφs hω hω'

/-- Let `G : S → ℝ × E` record a time and a position, and let `u ∘ G` be the conditional expectation
of a velocity `W : S → E` given `G`, for a finite measure `ν` on `S`. Then `u ∘ G` can replace `W`
in the integrand of the continuity equation, integrated against `ν`: the space derivative of a test
function, evaluated at `G`, is a bounded `G`-measurable factor which the conditional expectation
pulls out. -/
private lemma integral_fderiv_apply_comp_eq_of_condExp {S : Type*}
    [MeasurableSpace S] {ν : Measure S} [IsFiniteMeasure ν] {G : S → ℝ × E} (hG : Measurable G)
    {W : S → E} (hWint : Integrable W ν) {u : ℝ × E → E}
    (hcu : ν[W | MeasurableSpace.comap G inferInstance] = u ∘ G)
    (hcint : Integrable (fun q ↦ u (G q)) ν) {φ : ℝ × E → ℝ} (hφ1 : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) :
    ∫ q, fderiv ℝ φ (G q) (1, u (G q)) ∂ν = ∫ q, fderiv ℝ φ (G q) (1, W q) ∂ν := by
  have hm : MeasurableSpace.comap G inferInstance ≤ (inferInstance : MeasurableSpace S) :=
    hG.comap_le
  have hDφ := hφ1.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hDφ.bounded_above_of_compact_support (hφc.fderiv ℝ)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- the space derivative of `φ` along `G`, a bounded `G`-measurable field of linear forms
  set L : S → E →L[ℝ] ℝ := fun q ↦ (fderiv ℝ φ (G q)).comp (ContinuousLinearMap.inr ℝ ℝ E)
  have hLC (q : S) : ‖L q‖ ≤ C :=
    ContinuousLinearMap.opNorm_le_bound _ hC0 fun w ↦
      (fderiv ℝ φ (G q)).le_of_opNorm_le_of_le (hC _) (by simp [Prod.norm_def])
  have hL : StronglyMeasurable[MeasurableSpace.comap G inferInstance] L :=
    (hDφ.clm_comp continuous_const).stronglyMeasurable.comp_measurable (comap_measurable G)
  have hL_apply (q : S) (w : E) : L q w = fderiv ℝ φ (G q) (0, w) := by simp [L]
  -- the integrand splits into a time part and the space part `L q (Y q)`
  have hsplit {Y : S → E} (hY : Integrable Y ν) :
      ∫ q, fderiv ℝ φ (G q) (1, Y q) ∂ν =
        ∫ q, fderiv ℝ φ (G q) (1, 0) ∂ν + ∫ q, L q (Y q) ∂ν := by
    have hA : Integrable (fun q ↦ fderiv ℝ φ (G q) (1, 0)) ν :=
      integrable_fderiv_apply_one hφ1 hφc hG.aestronglyMeasurable (integrable_zero S E ν)
    have hLY : Integrable (fun q ↦ L q (Y q)) ν := by
      refine ((integrable_fderiv_apply_one hφ1 hφc hG.aestronglyMeasurable hY).sub hA).congr
        (.of_forall fun q ↦ ?_)
      simp only [Pi.sub_apply, hL_apply, ← map_sub, Prod.mk_sub_mk, sub_self, sub_zero]
    rw [← integral_add hA hLY]
    congr 1 with q
    rw [hL_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [hsplit hcint, hsplit hWint]
  congr 1
  have := condExp_stronglyMeasurable_bilin_of_bound (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)) hm
    hL hWint C (.of_forall hLC)
  simp only [ContinuousLinearMap.id_apply, hcu, Function.comp_apply] at this
  rw [← integral_condExp hm (f := fun q ↦ L q (W q))]
  exact (integral_congr_ae this).symm

/-- **The barycentric velocity of a law on curves.** Let `P` be a finite measure on a parameter
space `Ω` and `γ : Ω → ℝ → E` a jointly measurable family of curves, `P`-almost every one of which
is absolutely continuous on `[a, b]` with derivative `V ω t` at almost every `t ∈ (a, b)`, where
`V` is jointly measurable with finite expected length `∫ ∫_a^b ‖V ω t‖ dt dP(ω)`. Then the laws
`μₜ = (γ · t)₊ P` of the positions at time `t` solve the continuity equation on `(a, b)` with a
velocity field `v` whose value at the position `γ ω t` is the conditional expectation of the
velocity `V ω t` given the time and the position, for the measure `dt ⊗ P` on `(a, b) × Ω`. By
Jensen's inequality its action is at most the expected action of the curves:
`∫_a^b ∫ ‖vₜ‖ ^ p dμₜ dt ≤ ∫ ∫_a^b ‖V ω t‖ ^ p dt dP(ω)` for every `p ≥ 1`.

Unlike `TauCeti.isContinuityEquation_map`, the curves need not follow a common velocity field:
curves crossing at the same position at the same time may have different velocities there, which
the conditional expectation averages. -/
theorem exists_isContinuityEquation_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {γ V : Ω → ℝ → E}
    (hγ : Measurable (uncurry γ)) (hV : Measurable (uncurry V))
    (hac : ∀ᵐ ω ∂P, AbsolutelyContinuousOnInterval (γ ω) a b)
    (hderiv : ∀ᵐ ω ∂P, ∀ᵐ t, t ∈ Ioo a b → HasDerivAt (γ ω) (V ω t) t)
    (hint : ∫⁻ ω, (∫⁻ t in Ioo a b, ‖V ω t‖ₑ) ∂P < ∞) :
    ∃ v : ℝ → E → E, IsContinuityEquation (fun t ↦ P.map (γ · t)) v a b ∧
      (fun q : ℝ × Ω ↦ v q.1 (γ q.2 q.1)) =
        ((volume.restrict (Ioo a b)).prod P)[fun q ↦ V q.2 q.1 |
          MeasurableSpace.comap (fun q : ℝ × Ω ↦ (q.1, γ q.2 q.1)) inferInstance] ∧
      ∀ p : ℝ, 1 ≤ p → ∫⁻ t in Ioo a b, ∫⁻ x, ‖v t x‖ₑ ^ p ∂P.map (γ · t) ≤
        ∫⁻ ω, (∫⁻ t in Ioo a b, ‖V ω t‖ₑ ^ p) ∂P := by
  have : IsFiniteMeasure (volume.restrict (Ioo a b)) := ⟨by simp⟩
  set ν := (volume.restrict (Ioo a b)).prod P with hν
  -- the time and position `G`, and the velocity `W`, as functions on `(a, b) × Ω`
  set G : ℝ × Ω → ℝ × E := fun q ↦ (q.1, γ q.2 q.1)
  have hG : Measurable G := measurable_fst.prodMk (hγ.comp measurable_swap)
  have hγt (t : ℝ) : Measurable (γ · t) := hγ.comp measurable_prodMk_right
  set W : ℝ × Ω → E := fun q ↦ V q.2 q.1
  have hW : Measurable W := hV.comp measurable_swap
  have hWint : Integrable W ν := by
    refine ⟨hW.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hν, lintegral_prod _ hW.enorm.aemeasurable,
      lintegral_lintegral_swap (f := fun t ω ↦ ‖V ω t‖ₑ) hW.enorm.aemeasurable]
    exact hint
  -- the conditional expectation of the velocity is a function `u` of the time and the position
  obtain ⟨u, hu, hcu⟩ := (stronglyMeasurable_condExp (μ := ν) (f := W)
    (m := MeasurableSpace.comap G inferInstance)).exists_eq_measurable_comp
  -- Jensen's inequality for the conditional expectation, read on the time slices
  have hbound (p : ℝ) (hp : 1 ≤ p) : ∫⁻ t in Ioo a b, ∫⁻ x, ‖u (t, x)‖ₑ ^ p ∂P.map (γ · t) ≤
      ∫⁻ ω, (∫⁻ t in Ioo a b, ‖V ω t‖ₑ ^ p) ∂P := by
    have h := MeasureTheory.lintegral_enorm_condExp_rpow_le (μ := ν)
      (m := MeasurableSpace.comap G inferInstance) hW.aestronglyMeasurable hp
    rw [hcu] at h
    have hmap (t : ℝ) : ∫⁻ x, ‖u (t, x)‖ₑ ^ p ∂P.map (γ · t) = ∫⁻ ω, ‖u (t, γ ω t)‖ₑ ^ p ∂P :=
      lintegral_map ((hu.measurable.comp measurable_prodMk_left).enorm.pow_const _) (hγt t)
    simp_rw [hmap]
    rw [lintegral_lintegral_swap (f := fun ω t ↦ ‖V ω t‖ₑ ^ p)
      (hV.enorm.pow_const _).aemeasurable]
    rwa [hν, lintegral_prod _ ((hu.measurable.comp hG).enorm.pow_const _).aemeasurable,
      lintegral_prod _ (hW.enorm.pow_const _).aemeasurable] at h
  refine ⟨fun t x ↦ u (t, x), ⟨MeasureTheory.measurable_map_of_measurable_uncurry
    (hγ.comp measurable_swap), hu.measurable, ?_, ?_, fun φ hφ hφc hφs ↦ ?_⟩, hcu.symm, hbound⟩
  · simp only [Measure.map_apply (hγt _) MeasurableSet.univ, preimage_univ, setLIntegral_const]
    exact ENNReal.mul_lt_top (measure_lt_top P univ) measure_Ioo_lt_top
  · have h1 := hbound 1 le_rfl
    simp only [ENNReal.rpow_one] at h1
    exact h1.trans_lt hint
  -- push the slices back to `(a, b) × Ω`, replace `u ∘ G` by `W`, and integrate along each curve
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hcint : Integrable (fun q ↦ u (G q)) ν := by
    rw [← Function.comp_def, ← hcu]
    exact integrable_condExp
  have hF : Measurable fun q : ℝ × E ↦ fderiv ℝ φ q (1, u q) :=
    (measurable_fderiv_apply ℝ φ).comp
      (measurable_id.prodMk (measurable_const.prodMk hu.measurable))
  have hpush (t : ℝ) : ∫ x, fderiv ℝ φ (t, x) (1, u (t, x)) ∂P.map (γ · t) =
      ∫ ω, fderiv ℝ φ (t, γ ω t) (1, u (t, γ ω t)) ∂P :=
    integral_map (hγt t).aemeasurable (hF.comp measurable_prodMk_left).aestronglyMeasurable
  simp_rw [hpush]
  calc ∫ t in Ioo a b, ∫ ω, fderiv ℝ φ (t, γ ω t) (1, u (t, γ ω t)) ∂P
      = ∫ q, fderiv ℝ φ (G q) (1, u (G q)) ∂ν :=
      (integral_prod _ (integrable_fderiv_apply_one hφ1 hφc hG.aestronglyMeasurable hcint)).symm
    _ = ∫ q, fderiv ℝ φ (G q) (1, W q) ∂ν :=
      integral_fderiv_apply_comp_eq_of_condExp hG hWint hcu hcint hφ1 hφc
    _ = ∫ ω, (∫ t in Ioo a b, fderiv ℝ φ (t, γ ω t) (1, V ω t)) ∂P :=
      integral_prod_symm _ (integrable_fderiv_apply_one hφ1 hφc hG.aestronglyMeasurable hWint)
    _ = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hac, hderiv] with ω hω hω'
      exact integral_fderiv_eq_zero_of_hasDerivAt hφ1 hφs hω hω'

/-- **A translating law solves the continuity equation.** Translating a finite measure `μ` with
constant velocity `w`, so that its law at time `t` is the pushforward of `μ` by `x ↦ x + t • w`,
solves the continuity equation with the constant velocity field `w`. -/
theorem isContinuityEquation_map_add_smul (μ : Measure E) [IsFiniteMeasure μ] (w : E) (a b : ℝ) :
    IsContinuityEquation (fun t ↦ μ.map (· + t • w)) (fun _ _ ↦ w) a b := by
  refine isContinuityEquation_map μ (γ := fun x t ↦ x + t • w)
    (continuous_fst.add (continuous_snd.smul continuous_const)).measurable
    (measurable_const : Measurable fun _ : ℝ × E ↦ w)
    (.of_forall fun x ↦ (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
      |>.absolutelyContinuousOnInterval)
    (.of_forall fun x ↦ .of_forall fun t _ ↦ ?_) ?_
  · simpa using ((hasDerivAt_id' t).smul_const w).const_add x
  · simp only [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top measure_Ioo_lt_top)
      (measure_lt_top μ univ)

/-- **A stationary law solves the continuity equation.** A finite measure which does not move
solves the continuity equation with velocity field `0`. -/
theorem isContinuityEquation_const (μ : Measure E) [IsFiniteMeasure μ] (a b : ℝ) :
    IsContinuityEquation (fun _ ↦ μ) (fun _ _ ↦ 0) a b := by
  simpa using isContinuityEquation_map_add_smul μ 0 a b

/-- **A moving Dirac mass solves the continuity equation.** If `γ` is a measurable curve which is
absolutely continuous on `[a, b]` and `v` is a measurable velocity field with
`deriv γ t = vₜ (γ t)` for almost every `t ∈ (a, b)`, then the Dirac masses `δ_{γ t}` solve the
continuity equation with velocity `v` on `(a, b)`. The finite length `∫_a^b ‖vₜ (γ t)‖ dt < ∞`
follows from absolute continuity in finite dimension. -/
theorem isContinuityEquation_dirac {γ : ℝ → E} (hγm : Measurable γ)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hv : Measurable (uncurry v))
    (hderiv : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt γ (v t (γ t)) t) :
    IsContinuityEquation (fun t ↦ Measure.dirac (γ t)) v a b := by
  have hint : ∫⁻ t in Ioo a b, ‖v t (γ t)‖ₑ < ∞ := by
    rcases lt_or_ge a b with hab | hab
    swap
    · simp [Ioo_eq_empty_of_le hab]
    have hd : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (v t (γ t)) t := by
      rw [uIoc_of_le hab.le]
      filter_upwards [hderiv, compl_mem_ae_iff.2 (measure_singleton b)] with t ht htb hmem
      exact ht ⟨hmem.1, hmem.2.lt_of_ne htb⟩
    have hI := (hγ.intervalIntegrable_of_ae_hasDerivAt hd).1
    exact (hI.mono_set Ioo_subset_Ioc_self).2
  simpa [Measure.map_const] using isContinuityEquation_map (Measure.dirac ()) (γ := fun _ ↦ γ)
    (hγm.comp measurable_snd) hv (.of_forall fun _ ↦ hγ) (.of_forall fun _ ↦ hderiv)
    (by simpa using hint)

end TauCeti
