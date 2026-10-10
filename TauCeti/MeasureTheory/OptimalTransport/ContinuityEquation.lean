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
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The continuity equation

Let `E` be a real normed space, `μ : ℝ → Measure E` a family of Borel measures and
`v : ℝ → E → E` a Borel velocity field. The *continuity equation* on the time interval `(a, b)` is
`∂ₜ μₜ + div (vₜ μₜ) = 0`, understood in the sense of distributions: for every smooth compactly
supported test function `φ : ℝ × E → ℝ` whose support lies in `(a, b) × E`,
`∫_a^b ∫_E (∂ₜ φ (t, x) + ⟨∇ₓ φ (t, x), vₜ x⟩) dμₜ(x) dt = 0`.
In a normed space the integrand is the space-time derivative of `φ` applied to the space-time
velocity `(1, vₜ x)`, that is `fderiv ℝ φ (t, x) (1, v t x)`; this fixes the sign convention of the
equation together with its test-function identity. The definition `TauCeti.IsContinuityEquation`
also records the measurability of the time slices `t ↦ μₜ` and of `v`, and the integrability of the
total mass `t ↦ μₜ E` and of `∫ ‖vₜ‖ dμₜ` over `(a, b)`, which make every integral in the identity
absolutely convergent.

The continuity equation is the Eulerian description of mass moving with velocity `v`. Its basic
source of solutions is the Lagrangian one: if `P` is a finite measure on a parameter space `Ω` and
`γ : Ω → ℝ → E` is a measurable family of absolutely continuous curves with `γ̇_ω(t) = vₜ(γ_ω(t))`
for almost every `(ω, t)`, then the laws `μₜ = (γ · t)₊ P` of the positions at time `t` solve the
continuity equation with velocity `v` (`TauCeti.isContinuityEquation_map`). For `Ω` a space of
curves and `γ` the evaluation map this is the statement for a law on paths. A translating law, a
stationary law and a Dirac mass moving along an absolutely continuous curve are special cases.

## Main definitions

* `TauCeti.IsContinuityEquation μ v a b`: the family `μ` solves the continuity equation with
  velocity `v` in the sense of distributions on the time interval `(a, b)`.

## Main results

* `TauCeti.IsContinuityEquation.mono`: a solution on `(a, b)` is a solution on every subinterval.
* `TauCeti.IsContinuityEquation.congr`: the velocity field matters only `μₜ`-almost everywhere, for
  almost every time `t`.
* `TauCeti.isContinuityEquation_map`: the laws at time `t` of a measurable family of absolutely
  continuous curves following `v` solve the continuity equation with velocity `v`.
* `TauCeti.isContinuityEquation_map_add_smul`: a law translating with constant velocity `w`
  solves the continuity equation with velocity field `w`.
* `TauCeti.isContinuityEquation_const`: a stationary law solves it with velocity field `0`.
* `TauCeti.isContinuityEquation_dirac`: a Dirac mass moving along an absolutely continuous curve
  `γ` solves it with any velocity field equal to `γ̇` along `γ`.

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
velocity field are measurable, and the total mass and `∫ ‖vₜ‖ dμₜ` are integrable over `(a, b)`. -/
structure IsContinuityEquation (μ : ℝ → Measure E) (v : ℝ → E → E) (a b : ℝ) : Prop where
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

variable {μ : ℝ → Measure E} {v w : ℝ → E → E} {a b c d : ℝ}

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

omit [MeasurableSpace E] in
/-- If an absolutely continuous curve `γ` has derivative `V t` at almost every time of `(a, b)`,
then integrating `t ↦ fderiv ℝ φ (t, γ t) (1, V t)` over `(a, b)` gives zero for every `C¹`
compactly supported `φ` with support in `(a, b) × E`: this integrand is the derivative of
`t ↦ φ (t, γ t)`, which vanishes at both endpoints. -/
private lemma integral_fderiv_prodMk_eq_zero {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ univ) {γ : ℝ → E}
    (hγ : AbsolutelyContinuousOnInterval γ a b) {V : ℝ → E}
    (hV : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt γ (V t) t) :
    ∫ t in Ioo a b, fderiv ℝ φ (t, γ t) (1, V t) = 0 := by
  rcases lt_or_ge a b with hab | hab
  swap
  · simp [Ioo_eq_empty_of_le hab]
  obtain ⟨K, hK⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc one_ne_zero
  have hg : AbsolutelyContinuousOnInterval (fun t ↦ φ (t, γ t)) a b :=
    hK.comp_absolutelyContinuousOnInterval
      (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval.prodMk hγ)
  have hzero (s : ℝ) (hs : s ∉ Ioo a b) : φ (s, γ s) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hs (hφs h).1
  have hderiv : ∀ᵐ t, t ∈ Ioo a b →
      deriv (fun t ↦ φ (t, γ t)) t = fderiv ℝ φ (t, γ t) (1, V t) := by
    filter_upwards [hV] with t ht hmem
    exact (HasFDerivAt.comp_hasDerivAt t (hφ.differentiable one_ne_zero (t, γ t)).hasFDerivAt
      ((hasDerivAt_id' t).prodMk (ht hmem))).deriv
  rw [← setIntegral_congr_ae measurableSet_Ioo hderiv, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab.le, hg.integral_deriv_eq_sub,
    hzero a (by simp), hzero b (by simp), sub_self]

omit [MeasurableSpace E] in
/-- The integrand of the continuity equation grows at most linearly in the velocity. -/
private lemma exists_norm_fderiv_apply_le {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) : ∃ C, ∀ q w, ‖fderiv ℝ φ q (1, w)‖ ≤ C * (1 + ‖w‖) := by
  obtain ⟨C, hC⟩ :=
    (hφ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hφc.fderiv ℝ)
  refine ⟨C, fun q w ↦ ((fderiv ℝ φ q).le_opNorm _).trans
    (mul_le_mul (hC q) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hC q)))⟩
  rw [Prod.norm_def, norm_one]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left zero_le_one)

/-- The integrand of the continuity equation, as a function of the space-time point and of the
velocity, is measurable. -/
private lemma measurable_fderiv_apply [SecondCountableTopology E] [BorelSpace E]
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Measurable fun q : (ℝ × E) × E ↦ fderiv ℝ φ q.1 (1, q.2) :=
  (((hφ.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply
    (continuous_const.prodMk continuous_snd)).measurable

/-- **Lagrangian solutions of the continuity equation.** Let `P` be a finite measure on a parameter
space `Ω` and `γ : Ω → ℝ → E` a jointly measurable family of curves. If `P`-almost every curve is
absolutely continuous on `[a, b]` and follows the velocity field `v`, in the sense that
`γ̇_ω(t) = vₜ (γ_ω t)` for almost every `t ∈ (a, b)`, and the expected length
`∫ ∫_a^b ‖vₜ (γ_ω t)‖ dt dP(ω)` is finite, then the laws `(γ · t)₊ P` of the positions at time `t`
solve the continuity equation with velocity `v` on `(a, b)`. -/
theorem isContinuityEquation_map [SecondCountableTopology E] [BorelSpace E] {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {γ : Ω → ℝ → E}
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
    (measurable_fderiv_apply hφ1).comp (measurable_id.prodMk hv)
  obtain ⟨C, hC⟩ := exists_norm_fderiv_apply_le hφ1 hφc
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
      (.of_forall fun q ↦ hC _ _)
    refine ((integrable_const 1).add ?_).const_mul C
    refine ⟨(hv.comp (measurable_fst.prodMk hγ')).norm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa only [enorm_norm, lintegral_prod _ hvγ.aemeasurable] using hint'
  rw [integral_integral_swap hInt]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hac, hderiv] with ω hω hω'
  exact integral_fderiv_prodMk_eq_zero hφ1 hφc hφs hω hω'

/-- **A translating law solves the continuity equation.** Translating a finite measure `μ` with
constant velocity `w`, so that its law at time `t` is the pushforward of `μ` by `x ↦ x + t • w`,
solves the continuity equation with the constant velocity field `w`. -/
theorem isContinuityEquation_map_add_smul [SecondCountableTopology E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (w : E) (a b : ℝ) :
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
theorem isContinuityEquation_const [SecondCountableTopology E] [BorelSpace E] (μ : Measure E)
    [IsFiniteMeasure μ] (a b : ℝ) : IsContinuityEquation (fun _ ↦ μ) (fun _ _ ↦ 0) a b := by
  simpa using isContinuityEquation_map_add_smul μ 0 a b

/-- **A moving Dirac mass solves the continuity equation.** If `γ` is a measurable curve which is
absolutely continuous on `[a, b]` and `v` is a measurable velocity field with `γ̇ t = vₜ (γ t)` for
almost every `t ∈ (a, b)` and `∫_a^b ‖vₜ (γ t)‖ dt < ∞`, then the Dirac masses `δ_{γ t}` solve the
continuity equation with velocity `v` on `(a, b)`. -/
theorem isContinuityEquation_dirac [SecondCountableTopology E] [BorelSpace E] {γ : ℝ → E}
    (hγm : Measurable γ) (hγ : AbsolutelyContinuousOnInterval γ a b) (hv : Measurable (uncurry v))
    (hderiv : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt γ (v t (γ t)) t)
    (hint : ∫⁻ t in Ioo a b, ‖v t (γ t)‖ₑ < ∞) :
    IsContinuityEquation (fun t ↦ Measure.dirac (γ t)) v a b := by
  simpa [Measure.map_const] using isContinuityEquation_map (Measure.dirac ()) (γ := fun _ ↦ γ)
    (hγm.comp measurable_snd) hv (.of_forall fun _ ↦ hγ) (.of_forall fun _ ↦ hderiv)
    (by simpa using hint)

end TauCeti
