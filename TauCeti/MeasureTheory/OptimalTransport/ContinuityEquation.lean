/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Probability.Kernel.MeasurableIntegral
import TauCeti.Analysis.Calculus.FDeriv.Measurable
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
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
* `TauCeti.isContinuityEquation_map`: the laws at time `t` of a measurable family of absolutely
  continuous curves following `v`, with finite expected length, solve the continuity equation with
  velocity `v`.
* `TauCeti.isContinuityEquation_map_add_smul`: a law translating with constant velocity `w`
  solves the continuity equation with velocity field `w`.
* `TauCeti.isContinuityEquation_const`: a stationary law solves it with velocity field `0`.
* `TauCeti.isContinuityEquation_dirac`: a Dirac mass moving along an absolutely continuous curve
  `γ` solves it with any velocity field equal to `deriv γ` along `γ`.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §8.1.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §4.1.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

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

end IsContinuityEquation

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A measurable family of measures, rescaled by `(1 + μₜ E)⁻¹` to have mass at most one, as a
kernel. It lets the measurability results for finite kernels apply to `μ`. -/
private noncomputable def normalizedKernel (hμ : Measurable μ) : ProbabilityTheory.Kernel ℝ E where
  toFun t := (1 + μ t univ)⁻¹ • μ t
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ((measurable_const.add ((Measure.measurable_coe .univ).comp hμ)).inv).mul
      ((Measure.measurable_coe hs).comp hμ)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private lemma normalizedKernel_apply (hμ : Measurable μ) (t : ℝ) :
    normalizedKernel hμ t = (1 + μ t univ)⁻¹ • μ t := rfl

omit [FiniteDimensional ℝ E] [BorelSpace E] in
private instance (hμ : Measurable μ) : ProbabilityTheory.IsFiniteKernel (normalizedKernel hμ) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun t ↦ ?_⟩⟩
  rw [normalizedKernel_apply, Measure.smul_apply, smul_eq_mul]
  rcases eq_or_ne (μ t univ) ∞ with h | h
  · simp [h]
  rw [ENNReal.inv_mul_le_iff (by simp) (by simp [h]), mul_one]
  exact le_add_self

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private lemma lintegral_eq_mul_normalizedKernel (hμ : Measurable μ) {t : ℝ} (ht : μ t univ ≠ ∞)
    (f : E → ℝ≥0∞) : ∫⁻ x, f x ∂μ t = (1 + μ t univ) * ∫⁻ x, f x ∂normalizedKernel hμ t := by
  rw [normalizedKernel_apply, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp [ht]), one_mul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private lemma integral_eq_mul_normalizedKernel (hμ : Measurable μ) {t : ℝ} (ht : μ t univ ≠ ∞)
    (f : E → ℝ) : ∫ x, f x ∂μ t = (1 + μ t univ).toReal * ∫ x, f x ∂normalizedKernel hμ t := by
  have h0 : (1 + μ t univ).toReal ≠ 0 := (ENNReal.toReal_pos (by simp) (by simp [ht])).ne'
  rw [normalizedKernel_apply, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv, ← mul_assoc,
    mul_inv_cancel₀ h0, one_mul]

namespace IsContinuityEquation

/-- For almost every time `t ∈ (a, b)` the slice `μₜ` has finite mass. -/
private lemma ae_measure_univ_ne_top (h : IsContinuityEquation μ v a b) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), μ t univ ≠ ∞ :=
  (ae_lt_top ((Measure.measurable_coe .univ).comp h.measurable)
    h.lintegral_measure_univ_lt_top.ne).mono fun _ ht ↦ ht.ne

/-- The `μₜ`-integral of a jointly measurable function is almost everywhere measurable in time. -/
private lemma aemeasurable_lintegral (h : IsContinuityEquation μ v a b) {f : ℝ → E → ℝ≥0∞}
    (hf : Measurable (uncurry f)) :
    AEMeasurable (fun t ↦ ∫⁻ x, f t x ∂μ t) (volume.restrict (Ioo a b)) := by
  have hm : Measurable fun t ↦ 1 + μ t univ :=
    measurable_const.add ((Measure.measurable_coe .univ).comp h.measurable)
  have hκ := hf.lintegral_kernel_prod_right (κ := normalizedKernel h.measurable)
  refine (hm.mul hκ).aemeasurable.congr ?_
  filter_upwards [h.ae_measure_univ_ne_top] with t ht
  exact (lintegral_eq_mul_normalizedKernel h.measurable ht _).symm

/-- The `μₜ`-integral of a jointly measurable function is almost everywhere strongly measurable in
time. -/
private lemma aestronglyMeasurable_integral (h : IsContinuityEquation μ v a b) {f : ℝ → E → ℝ}
    (hf : StronglyMeasurable (uncurry f)) :
    AEStronglyMeasurable (fun t ↦ ∫ x, f t x ∂μ t) (volume.restrict (Ioo a b)) := by
  have hm : Measurable fun t ↦ 1 + μ t univ :=
    measurable_const.add ((Measure.measurable_coe .univ).comp h.measurable)
  have hκ := hf.integral_kernel_prod_right (κ := normalizedKernel h.measurable)
  refine (hm.ennreal_toReal.stronglyMeasurable.mul hκ).aestronglyMeasurable.congr ?_
  filter_upwards [h.ae_measure_univ_ne_top] with t ht
  exact (integral_eq_mul_normalizedKernel h.measurable ht _).symm

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
  filter_upwards [ae_lt_top' (h.aemeasurable_lintegral
      (f := fun t x ↦ ‖fderiv ℝ φ (t, x) (1, v t x)‖ₑ) hF.enorm)
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
  refine ⟨h.aestronglyMeasurable_integral hF.stronglyMeasurable, ?_⟩
  exact (lintegral_mono fun t ↦ enorm_integral_le_lintegral_enorm _).trans_lt
    (h.lintegral_lintegral_enorm_fderiv_lt_top hφ hφc)

end IsContinuityEquation

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
  obtain ⟨C, hC⟩ :=
    (hφ1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hφc.fderiv ℝ)
  have hpush (t : ℝ) : ∫ x, fderiv ℝ φ (t, x) (1, v t x) ∂P.map (γ · t) =
      ∫ ω, fderiv ℝ φ (t, γ ω t) (1, v t (γ ω t)) ∂P :=
    integral_map (hγt t).aemeasurable (hF.comp measurable_prodMk_left).aestronglyMeasurable
  simp_rw [hpush]
  -- swap the order of integration, then integrate along each curve
  have : IsFiniteMeasure (volume.restrict (Ioo a b)) := ⟨by simp⟩
  have hInt : Integrable (uncurry fun t ω ↦ fderiv ℝ φ (t, γ ω t) (1, v t (γ ω t)))
      ((volume.restrict (Ioo a b)).prod P) := by
    refine Integrable.mono' (g := fun q ↦ C * (1 + ‖v q.1 (γ q.2 q.1)‖)) ?_
      (hF.comp (measurable_fst.prodMk hγ')).aestronglyMeasurable
      (.of_forall fun q ↦ (fderiv ℝ φ _).le_of_opNorm_le_of_le (hC _) (by simp [Prod.norm_def]))
    refine ((integrable_const 1).add ?_).const_mul C
    refine ⟨(hv.comp (measurable_fst.prodMk hγ')).norm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa only [enorm_norm, lintegral_prod _ hvγ.aemeasurable] using hint'
  rw [integral_integral_swap hInt]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hac, hderiv] with ω hω hω'
  rcases lt_or_ge a b with hab | hab
  swap
  · simp [Ioo_eq_empty_of_le hab]
  -- the integrand is the derivative of `t ↦ φ (t, γ ω t)`, which vanishes at both endpoints
  have hzero (s : ℝ) (hs : s ∉ Ioo a b) : φ (s, γ ω s) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hs (hφs h).1
  have hd : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt (fun t ↦ (t, γ ω t)) (1, v t (γ ω t)) t := by
    rw [uIoc_of_le hab.le]
    filter_upwards [hω', compl_mem_ae_iff.2 (measure_singleton b)] with t ht htb hmem
    exact (hasDerivAt_id' t).prodMk (ht ⟨hmem.1, hmem.2.lt_of_ne htb⟩)
  have := (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval.prodMk
    hω).integral_fderiv_apply_eq_sub hd hφ1
  simp only [id, hzero a (by simp), hzero b (by simp), sub_self] at this
  rwa [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] at this

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
