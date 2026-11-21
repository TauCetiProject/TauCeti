/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Derivatives of improper tail integrals

For an integrable function `f` on `(a, ∞)`, its tail integral `t ↦ ∫ s in Ioi t, f s`
has strict derivative `-f t` at each `t > a` where `f` is continuous. If `f` is continuous on
the whole ray, the derivative identity also gives a formula for every higher iterated
derivative. These results apply to Banach-space-valued integrands and support differential
closure arguments for improper integrals.

For a real function `g` integrable on the right tail `I ∩ Ioi x` of a measurable set `I`
(in particular on `(x, ∞)` or `(x, b)`), with tail integral `Ψ v = ∫ u in I ∩ Ioi v, g u`, the
product `g * Ψ ^ k` is integrable on `I ∩ Ioi x` with integral `Ψ x ^ (k + 1) / (k + 1)`
(`MeasureTheory.IntegrableOn.mul_pow_integral_inter_Ioi`,
`MeasureTheory.IntegrableOn.integral_inter_Ioi_mul_pow_integral_inter_Ioi`, and the `(x, ∞)` and
`(x, b)` forms `mul_pow_integral_Ioi`, `integral_Ioi_mul_pow_integral_Ioi`,
`mul_pow_integral_Ioo`, `integral_Ioo_mul_pow_integral_Ioo`), and `g * exp ∘ Ψ` is integrable on
`I ∩ Ioi x` with integral `exp (Ψ x) - 1`
(`MeasureTheory.IntegrableOn.mul_exp_integral_inter_Ioi`,
`MeasureTheory.IntegrableOn.integral_inter_Ioi_mul_exp_integral_inter_Ioi`). The tail integral of
a nonnegative function is antitone (`MeasureTheory.antitoneOn_integral_inter_Ioi`,
`MeasureTheory.antitoneOn_integral_Ioi`).

For a compactly supported `C¹` map `u` on a real normed space, integrating its derivative along a
ray from `w` recovers `-u w` (`HasCompactSupport.integral_Ioi_fderiv_apply_ray`). For general
Banach-space-valued integrands, `TauCeti.integral_comp_add_mul_left_Ioi'` records the affine
change of variables `y = c + b * x` (`0 < b`) on `Ioi a`.

The integrals of a function integrable on a strip `ℝ × T` over the rectangles `[a i, b i] × T`
converge to its integral over the strip as `a i → -∞` and `b i → ∞`
(`TauCeti.tendsto_setIntegral_Icc_prod`).

If nonnegative functions `f` and `g` satisfy `∫_{φ i} f ≤ ∫_{φ i} g + e i` along an exhaustion `φ`
with errors `e i → 0`, and `g` is integrable, then `f` is integrable with `∫ f ≤ ∫ g`
(`MeasureTheory.AECover.integrable_and_integral_le_of_setIntegral_le_add`). For the truncations
`[-n, n] × T` of a strip `ℝ × T` this is
`TauCeti.integrableOn_univ_prod_and_setIntegral_le_of_setIntegral_Icc_prod_le_add`.

The preimages of the balls `closedBall x₀ (r i)` under a continuous map exhaust the space as the
radii `r i` tend to infinity (`TauCeti.aecover_preimage_closedBall`), so the integrals of an
integrable function over them converge to its integral. A nonnegative function whose integrals over
these preimages converge as the radii `r i` tend to infinity has the limit as its integral
over the whole space (`TauCeti.lintegral_ofReal_eq_of_tendsto_setIntegral_closedBall`). For
example, the plane `ℝ × ℝ` is exhausted by the Euclidean discs `{‖w‖ ≤ r}` of `ℂ`.

## References

* Mathlib's `intervalIntegral.integral_Ioi_sub_Ioi'`,
  `intervalIntegral.integral_hasStrictDerivAt_right`,
  `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` and
  `HasCompactSupport.integral_Ioi_deriv_eq`.
-/

public section

open Set Filter intervalIntegral
open scoped Topology

namespace MeasureTheory.IntegrableOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : ℝ → E} {a t : ℝ}

/-- At a continuity point strictly inside an integrable ray, the tail integral is strictly
differentiable with derivative equal to the negated integrand. -/
theorem hasStrictDerivAt_integral_Ioi (hint : IntegrableOn f (Ioi a)) (hcont : ContinuousAt f t)
    (ht : a < t) : HasStrictDerivAt (fun u ↦ ∫ s in Ioi u, f s) (-f t) t := by
  have hfinite : HasStrictDerivAt (fun u ↦ ∫ s in t..u, f s) (f t) t :=
    integral_hasStrictDerivAt_right IntervalIntegrable.refl
      (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
        hint.aestronglyMeasurable (Ioi_mem_nhds ht)) hcont
  have heq : (fun u ↦ (∫ s in Ioi t, f s) - ∫ s in t..u, f s) =ᶠ[𝓝 t]
      (fun u ↦ ∫ s in Ioi u, f s) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    rw [← integral_Ioi_sub_Ioi' (hint.mono_set (Ioi_subset_Ioi ht.le))
      (hint.mono_set (Ioi_subset_Ioi hu.le)), sub_sub_cancel]
  exact (hfinite.const_sub (∫ s in Ioi t, f s)).congr_of_eventuallyEq heq

/-- At a continuity point strictly inside an integrable ray, the tail integral has derivative
equal to the negated integrand. -/
theorem hasDerivAt_integral_Ioi (hint : IntegrableOn f (Ioi a)) (hcont : ContinuousAt f t)
    (ht : a < t) : HasDerivAt (fun u ↦ ∫ s in Ioi u, f s) (-f t) t :=
  (hint.hasStrictDerivAt_integral_Ioi hcont ht).hasDerivAt

/-- The derivative of an improper tail integral is the negated integrand at each continuity
point strictly inside the integrable ray. -/
theorem deriv_integral_Ioi (hint : IntegrableOn f (Ioi a)) (hcont : ContinuousAt f t)
    (ht : a < t) : deriv (fun u ↦ ∫ s in Ioi u, f s) t = -f t :=
  (hint.hasDerivAt_integral_Ioi hcont ht).deriv

/-- For a continuous integrand on an integrable ray, the derivative of order `n + 1` of its
tail integral is the negated derivative of order `n` of the integrand at each interior point.
The identity concerns total iterated derivatives and does not assume higher smoothness. -/
theorem iteratedDeriv_integral_Ioi (hint : IntegrableOn f (Ioi a))
    (hcont : ContinuousOn f (Ioi a)) (n : ℕ) (ht : a < t) :
    iteratedDeriv (n + 1) (fun u ↦ ∫ s in Ioi u, f s) t = -iteratedDeriv n f t := by
  have heq : deriv (fun u ↦ ∫ s in Ioi u, f s) =ᶠ[𝓝 t] (fun u ↦ -f u) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact hint.deriv_integral_Ioi (hcont.continuousAt (isOpen_Ioi.mem_nhds hu)) hu
  rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_fun_neg]

section Real

open scoped Nat

variable {g : ℝ → ℝ} {x : ℝ}

/-- If `g` is integrable on `(x, ∞)`, with tail integral `Ψ v = ∫ u in Ioi v, g u`, then
`v ↦ g v * Ψ v ^ k` is integrable on `(x, ∞)`. -/
theorem mul_pow_integral_Ioi (hint : IntegrableOn g (Ioi x)) (k : ℕ) :
    IntegrableOn (fun v ↦ g v * (∫ u in Ioi v, g u) ^ k) (Ioi x) := by
  have hΨ : ContinuousOn (fun v ↦ ∫ u in Ioi v, g u) (Ioi x) :=
    hint.continuousOn_Ici_primitive_Ioi.mono Ioi_subset_Ici_self
  refine Integrable.mono' (hint.norm.mul_const ((∫ u in Ioi x, ‖g u‖) ^ k))
    (hint.aestronglyMeasurable.mul ((hΨ.pow k).aestronglyMeasurable measurableSet_Ioi)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [norm_mul, norm_pow]
  gcongr
  exact (norm_integral_le_integral_norm _).trans (setIntegral_mono_set hint.norm
    (ae_of_all _ fun _ ↦ norm_nonneg _) (Ioi_subset_Ioi hv.le).eventuallySubset)

/-- For `g` integrable on `(x, ∞)`, with tail integral `Ψ v = ∫ u in Ioi v, g u`, the integral
of `g * Ψ ^ k` over `(x, ∞)` is `Ψ x ^ (k + 1) / (k + 1)`. This identity is behind the factorial
decay of the Picard increments of Volterra integral equations on a half-line. -/
theorem integral_Ioi_mul_pow_integral_Ioi (hint : IntegrableOn g (Ioi x)) (k : ℕ) :
    ∫ v in Ioi x, g v * (∫ u in Ioi v, g u) ^ k = (∫ u in Ioi x, g u) ^ (k + 1) / (k + 1) := by
  set Ψ : ℝ → ℝ := fun v ↦ ∫ u in Ioi v, g u
  -- on `[x, y]`, `Ψ` is `Ψ x` minus a primitive of `g`
  have hΨeq {y : ℝ} (hy : x ≤ y) : Ψ y = Ψ x - ∫ u in x..y, g u := by
    simp only [Ψ, ← intervalIntegral.integral_interval_add_Ioi hint
      (hint.mono_set (Ioi_subset_Ioi hy)), add_sub_cancel_left]
  have hfin {y : ℝ} (hy : x ≤ y) :
      ∫ v in x..y, g v * Ψ v ^ k = (Ψ x ^ (k + 1) - Ψ y ^ (k + 1)) / (k + 1) := by
    have hgi : IntervalIntegrable g volume x y :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).2 (hint.mono_set Ioc_subset_Ioi_self)
    have hΨac : AbsolutelyContinuousOnInterval Ψ x y :=
      ((LipschitzWith.const (Ψ x)).lipschitzOnWith.absolutelyContinuousOnInterval.sub
        (hgi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)).congr
        fun v hv ↦ (hΨeq (uIcc_of_le hy ▸ hv).1).symm
    have hpow (n : ℕ) : AbsolutelyContinuousOnInterval (fun v ↦ Ψ v ^ n) x y := by
      induction n with
      | zero =>
        simpa using (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
      | succ n ih => simpa only [pow_succ] using ih.fun_mul hΨac
    have hderiv : ∀ᵐ v, v ∈ uIoc x y →
        deriv (fun v ↦ Ψ v ^ (k + 1)) v = -((k + 1) * (g v * Ψ v ^ k)) := by
      filter_upwards [hgi.ae_hasDerivAt_integral, Measure.ae_ne volume y] with v hv hvy hvI
      rw [uIoc_of_le hy] at hvI
      have hvI' : v ∈ Ioo x y := ⟨hvI.1, hvI.2.lt_of_ne hvy⟩
      have hΨv : HasDerivAt Ψ (-g v) v := by
        rw [← zero_sub]
        refine ((hasDerivAt_const v (Ψ x)).sub (hv (Ioc_subset_Icc_self.trans
          (uIcc_of_le hy).symm.subset hvI) x left_mem_uIcc)).congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds hvI'.1 hvI'.2] with w hw
        exact hΨeq hw.1.le
      rw [(hΨv.fun_pow (k + 1)).deriv]
      push_cast
      ring
    have := hpow (k + 1) |>.integral_deriv_eq_sub
    rw [intervalIntegral.integral_congr_ae hderiv, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul] at this
    field_simp
    linarith
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi x
    (hint.mul_pow_integral_Ioi k) tendsto_id) ?_
  have htend : Tendsto Ψ atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  have hlim := ((htend.pow (k + 1)).const_sub (Ψ x ^ (k + 1))).div_const ((k : ℝ) + 1)
  rw [zero_pow k.succ_ne_zero, sub_zero] at hlim
  exact hlim.congr' ((eventually_ge_atTop x).mono fun y hy ↦ (hfin hy).symm)

/-- If `I` is measurable and `g` is integrable on `I ∩ Ioi x`, with tail integral
`Ψ v = ∫ u in I ∩ Ioi v, g u`, then `v ↦ g v * Ψ v ^ k` is integrable on `I ∩ Ioi x`. -/
theorem mul_pow_integral_inter_Ioi {I : Set ℝ} (hI : MeasurableSet I)
    (hint : IntegrableOn g (I ∩ Ioi x)) (k : ℕ) :
    IntegrableOn (fun v ↦ g v * (∫ u in I ∩ Ioi v, g u) ^ k) (I ∩ Ioi x) := by
  have hint' : IntegrableOn (I.indicator g) (Ioi x) := by
    rwa [IntegrableOn, integrable_indicator_iff hI, IntegrableOn, Measure.restrict_restrict hI]
  have hind : (I.indicator fun v ↦ g v * (∫ u in I ∩ Ioi v, g u) ^ k) =
      fun v ↦ I.indicator g v * (∫ u in Ioi v, I.indicator g u) ^ k := by
    ext v
    by_cases hv : v ∈ I <;> simp [hv, setIntegral_indicator hI, inter_comm (Ioi v) I]
  rw [IntegrableOn, ← Measure.restrict_restrict hI, ← IntegrableOn, ← integrable_indicator_iff hI,
    hind]
  exact hint'.mul_pow_integral_Ioi k

/-- For a measurable set `I` and `g` integrable on `I ∩ Ioi x`, with tail integral
`Ψ v = ∫ u in I ∩ Ioi v, g u`, the integral of `g * Ψ ^ k` over `I ∩ Ioi x` is
`Ψ x ^ (k + 1) / (k + 1)`. -/
theorem integral_inter_Ioi_mul_pow_integral_inter_Ioi {I : Set ℝ} (hI : MeasurableSet I)
    (hint : IntegrableOn g (I ∩ Ioi x)) (k : ℕ) :
    ∫ v in I ∩ Ioi x, g v * (∫ u in I ∩ Ioi v, g u) ^ k =
      (∫ u in I ∩ Ioi x, g u) ^ (k + 1) / (k + 1) := by
  have hint' : IntegrableOn (I.indicator g) (Ioi x) := by
    rwa [IntegrableOn, integrable_indicator_iff hI, IntegrableOn, Measure.restrict_restrict hI]
  have hind : (I.indicator fun v ↦ g v * (∫ u in I ∩ Ioi v, g u) ^ k) =
      fun v ↦ I.indicator g v * (∫ u in Ioi v, I.indicator g u) ^ k := by
    ext v
    by_cases hv : v ∈ I <;> simp [hv, setIntegral_indicator hI, inter_comm (Ioi v) I]
  rw [inter_comm I (Ioi x), ← setIntegral_indicator hI, hind,
    hint'.integral_Ioi_mul_pow_integral_Ioi k, ← setIntegral_indicator hI]

/-- If `g` is integrable on `(x, b)`, with tail integral `Ψ v = ∫ u in Ioo v b, g u`, then
`v ↦ g v * Ψ v ^ k` is integrable on `(x, b)`. -/
theorem mul_pow_integral_Ioo {b : ℝ} (hint : IntegrableOn g (Ioo x b)) (k : ℕ) :
    IntegrableOn (fun v ↦ g v * (∫ u in Ioo v b, g u) ^ k) (Ioo x b) := by
  rw [← Iio_inter_Ioi] at hint ⊢
  simpa only [Iio_inter_Ioi] using hint.mul_pow_integral_inter_Ioi measurableSet_Iio k

/-- For `g` integrable on `(x, b)`, with tail integral `Ψ v = ∫ u in Ioo v b, g u`, the integral
of `g * Ψ ^ k` over `(x, b)` is `Ψ x ^ (k + 1) / (k + 1)`. -/
theorem integral_Ioo_mul_pow_integral_Ioo {b : ℝ} (hint : IntegrableOn g (Ioo x b)) (k : ℕ) :
    ∫ v in Ioo x b, g v * (∫ u in Ioo v b, g u) ^ k =
      (∫ u in Ioo x b, g u) ^ (k + 1) / (k + 1) := by
  rw [← Iio_inter_Ioi] at hint ⊢
  simpa only [Iio_inter_Ioi] using
    hint.integral_inter_Ioi_mul_pow_integral_inter_Ioi measurableSet_Iio k

/-- If `I` is measurable and `g` is integrable on `I ∩ Ioi x`, with tail integral
`Ψ v = ∫ u in I ∩ Ioi v, g u`, then `v ↦ g v * exp (Ψ v)` is integrable on `I ∩ Ioi x`. -/
theorem mul_exp_integral_inter_Ioi {I : Set ℝ} (hI : MeasurableSet I)
    (hint : IntegrableOn g (I ∩ Ioi x)) :
    IntegrableOn (fun v ↦ g v * Real.exp (∫ u in I ∩ Ioi v, g u)) (I ∩ Ioi x) := by
  have hmeas : AEStronglyMeasurable
      (fun v ↦ g v * Real.exp (∫ u in I ∩ Ioi v, g u)) (volume.restrict (I ∩ Ioi x)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n v ↦ ∑ k ∈ Finset.range n, (k ! : ℝ)⁻¹ * (g v * (∫ u in I ∩ Ioi v, g u) ^ k))
      (fun n ↦ Finset.aestronglyMeasurable_fun_sum _ fun k _ ↦
        ((hint.mul_pow_integral_inter_Ioi hI k).const_mul _).aestronglyMeasurable)
      (ae_of_all _ fun v ↦ ?_)
    have hsum : HasSum (fun k : ℕ ↦ (k ! : ℝ)⁻¹ * (g v * (∫ u in I ∩ Ioi v, g u) ^ k))
        (g v * Real.exp (∫ u in I ∩ Ioi v, g u)) := by
      have hexp := (NormedSpace.expSeries_div_hasSum_exp (∫ u in I ∩ Ioi v, g u)).mul_left (g v)
      rw [← Real.exp_eq_exp_ℝ] at hexp
      exact hexp.congr_fun fun k ↦ by ring
    exact hsum.tendsto_sum_nat
  refine Integrable.mono' (hint.norm.mul_const (Real.exp (∫ u in I ∩ Ioi x, ‖g u‖))) hmeas ?_
  filter_upwards [ae_restrict_mem (hI.inter measurableSet_Ioi)] with v hv
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  gcongr
  exact (le_abs_self _).trans ((norm_integral_le_integral_norm _).trans
    (setIntegral_mono_set hint.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
      (inter_subset_inter_right I (Ioi_subset_Ioi hv.2.le)).eventuallySubset))

/-- For a measurable set `I` and `g` integrable on `I ∩ Ioi x`, with tail integral
`Ψ v = ∫ u in I ∩ Ioi v, g u`, the integral of `g * exp ∘ Ψ` over `I ∩ Ioi x` is
`exp (Ψ x) - 1`. -/
theorem integral_inter_Ioi_mul_exp_integral_inter_Ioi {I : Set ℝ} (hI : MeasurableSet I)
    (hint : IntegrableOn g (I ∩ Ioi x)) :
    ∫ v in I ∩ Ioi x, g v * Real.exp (∫ u in I ∩ Ioi v, g u) =
      Real.exp (∫ u in I ∩ Ioi x, g u) - 1 := by
  set Ψ : ℝ → ℝ := fun v ↦ ∫ u in I ∩ Ioi v, g u
  set M : ℝ := ∫ u in I ∩ Ioi x, ‖g u‖
  let F : ℕ → ℝ → ℝ := fun k v ↦ (k ! : ℝ)⁻¹ * (g v * Ψ v ^ k)
  have hFint : ∀ k, IntegrableOn (F k) (I ∩ Ioi x) := fun k ↦
    (hint.mul_pow_integral_inter_Ioi hI k).const_mul _
  have hFsum : Summable fun k ↦ ∫ v in I ∩ Ioi x, ‖F k v‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun k ↦ ?_) ((Real.summable_pow_div_factorial M).mul_left M)
    calc ∫ v in I ∩ Ioi x, ‖F k v‖
        ≤ ∫ v in I ∩ Ioi x, (M ^ k / k !) * ‖g v‖ := by
          refine setIntegral_mono_on (hFint k).norm (hint.norm.const_mul _)
            (hI.inter measurableSet_Ioi) fun v hv ↦ ?_
          have hΨle : ‖Ψ v‖ ≤ M := (norm_integral_le_integral_norm _).trans
            (setIntegral_mono_set hint.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
              (inter_subset_inter_right I (Ioi_subset_Ioi hv.2.le)).eventuallySubset)
          simp only [F, norm_mul, norm_inv, Real.norm_natCast, norm_pow]
          rw [div_eq_mul_inv, mul_comm (M ^ k), mul_assoc, mul_comm (‖g v‖)]
          gcongr
      _ = M * (M ^ k / k !) := by rw [integral_const_mul]; ring
  have hser := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hpt : ∀ v, ∑' k, F k v = g v * Real.exp (Ψ v) := fun v ↦ by
    have hexp := (NormedSpace.expSeries_div_hasSum_exp (Ψ v)).mul_left (g v)
    rw [← Real.exp_eq_exp_ℝ] at hexp
    exact (hexp.congr_fun fun k ↦ by simp only [F]; ring).tsum_eq
  simp only [hpt] at hser
  have hterm : ∀ k, ∫ v in I ∩ Ioi x, F k v = Ψ x ^ (k + 1) / (k + 1)! := fun k ↦ by
    dsimp only [F, Ψ]
    rw [integral_const_mul, hint.integral_inter_Ioi_mul_pow_integral_inter_Ioi hI k,
      Nat.factorial_succ]
    push_cast
    field_simp
  simp only [hterm] at hser
  have htarget : HasSum (fun k : ℕ ↦ Ψ x ^ (k + 1) / (k + 1)!) (Real.exp (Ψ x) - 1) := by
    have hexp := NormedSpace.expSeries_div_hasSum_exp (Ψ x)
    rw [← Real.exp_eq_exp_ℝ] at hexp
    simpa [Nat.factorial_zero] using (hasSum_nat_add_iff' 1).2 hexp
  exact hser.unique htarget

end Real

end MeasureTheory.IntegrableOn

namespace MeasureTheory

/-- If `I` is measurable and `f` is nonnegative on `I` and integrable on `I ∩ Ioi x` for every
`x ∈ I`, then its tail integral `x ↦ ∫ v in I ∩ Ioi x, f v` is antitone on `I`. -/
theorem antitoneOn_integral_inter_Ioi {f : ℝ → ℝ} {I : Set ℝ} (hI : MeasurableSet I)
    (hf : ∀ v ∈ I, 0 ≤ f v) (hint : ∀ x ∈ I, IntegrableOn f (I ∩ Ioi x)) :
    AntitoneOn (fun x ↦ ∫ v in I ∩ Ioi x, f v) I := fun x hx _ _ hxy ↦
  setIntegral_mono_set (hint x hx) ((ae_restrict_iff' (hI.inter measurableSet_Ioi)).2
    (ae_of_all _ fun v hv ↦ hf v hv.1))
    (inter_subset_inter_right I (Ioi_subset_Ioi hxy)).eventuallySubset

/-- If `f` is nonnegative on `(a, ∞)` and integrable on `(x, ∞)` for every `x > a`, then its tail
integral `x ↦ ∫ v in Ioi x, f v` is antitone on `(a, ∞)`. -/
theorem antitoneOn_integral_Ioi {f : ℝ → ℝ} {a : ℝ} (hf : ∀ v ∈ Ioi a, 0 ≤ f v)
    (hint : ∀ x ∈ Ioi a, IntegrableOn f (Ioi x)) :
    AntitoneOn (fun x ↦ ∫ v in Ioi x, f v) (Ioi a) := fun x (hx : a < x) _ _ hxy ↦
  setIntegral_mono_set (hint x hx) ((ae_restrict_iff' measurableSet_Ioi).2
    (ae_of_all _ fun v hv ↦ hf v (hx.trans hv))) (Ioi_subset_Ioi hxy).eventuallySubset

end MeasureTheory

section Ray

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Integrating the derivative of a compactly supported `C¹` map `u` along the ray from `w` in a
nonzero direction `e` recovers `-u w`. This is the directional form of
`HasCompactSupport.integral_Ioi_deriv_eq`, for the restriction `r ↦ u (w + r • e)` of `u` to the
line through `w` in direction `e`. -/
theorem HasCompactSupport.integral_Ioi_fderiv_apply_ray {u : E → F}
    (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) (w : E) {e : E} (he : e ≠ 0) :
    ∫ r in Ioi (0 : ℝ), fderiv ℝ u (w + r • e) e = -u w := by
  have hline : HasCompactSupport fun r : ℝ => u (w + r • e) :=
    hc.comp_isClosedEmbedding
      ((Homeomorph.addLeft w).isClosedEmbedding.comp (isClosedEmbedding_smul_left he))
  have hderiv (r : ℝ) : deriv (fun r : ℝ => u (w + r • e)) r = fderiv ℝ u (w + r • e) e := by
    simpa [Function.comp_def] using
      ((hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r
        (((hasDerivAt_id' r).smul_const e).const_add w)).deriv
  have h := hline.integral_Ioi_deriv_eq (f := fun r : ℝ => u (w + r • e))
    (hu.comp (by fun_prop : ContDiff ℝ 1 fun r : ℝ => w + r • e)) 0
  simpa only [hderiv, zero_smul, add_zero] using h

end Ray

namespace MeasureTheory.AECover

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [l.NeBot]
  [l.IsCountablyGenerated] {φ : ι → Set α}

/-- **Integral bounds from an exhaustion.** Let `φ` cover `μ`-almost everything along `l`, and
let `f` and `g` be almost everywhere nonnegative, with `g` integrable and `f` integrable on each
`φ i`. If eventually `∫_{φ i} f ≤ ∫_{φ i} g + e i` with errors `e i → 0`, then `f` is integrable
and `∫ f ≤ ∫ g`. -/
theorem integrable_and_integral_le_of_setIntegral_le_add (hφ : AECover μ l φ) {f g : α → ℝ}
    {e : ι → ℝ} (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (hgi : Integrable g μ) (he : Tendsto e l (𝓝 0))
    (hle : ∀ᶠ i in l, ∫ x in φ i, f x ∂μ ≤ ∫ x in φ i, g x ∂μ + e i) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ := by
  have hfint : Integrable f μ := by
    refine hφ.integrable_of_integral_bounded_of_nonneg_ae (∫ x, g x ∂μ + 1) hfi hf ?_
    filter_upwards [hle, he.eventually (gt_mem_nhds zero_lt_one)] with i hi hei
    exact hi.trans (add_le_add (setIntegral_le_integral hgi hg) hei.le)
  refine ⟨hfint, le_of_tendsto_of_tendsto (hφ.integral_tendsto_of_countably_generated hfint) ?_ hle⟩
  simpa using (hφ.integral_tendsto_of_countably_generated hgi).add he

end MeasureTheory.AECover

namespace TauCeti

open MeasureTheory

/-- **Integrals over a strip are limits over its truncations.** Let `T` be measurable and `f`
integrable on the strip `ℝ × T`. If `a i → -∞` and `b i → ∞` along a countably generated filter,
the integrals of `f` over the rectangles `[a i, b i] × T` converge to its integral over the
strip. -/
theorem tendsto_setIntegral_Icc_prod {ι β F : Type*} [MeasurableSpace β] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {μ : Measure (ℝ × β)} {l : Filter ι} [l.IsCountablyGenerated]
    {a b : ι → ℝ} (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) {T : Set β}
    (hT : MeasurableSet T) {f : ℝ × β → F} (hf : IntegrableOn f (univ ×ˢ T) μ) :
    Tendsto (fun i ↦ ∫ z in Icc (a i) (b i) ×ˢ T, f z ∂μ) l (𝓝 (∫ z in univ ×ˢ T, f z ∂μ)) := by
  have hφ : AECover (μ.restrict (univ ×ˢ T)) l fun i ↦ Icc (a i) (b i) ×ˢ T :=
    aecover_restrict_of_ae_imp (MeasurableSet.univ.prod hT) (ae_of_all _ fun z hz ↦
      ((ha.eventually_le_atBot z.1).and (hb.eventually_ge_atTop z.1)).mono fun _ h ↦
        ⟨⟨h.1, h.2⟩, hz.2⟩) fun _ ↦ measurableSet_Icc.prod hT
  refine (hφ.integral_tendsto_of_countably_generated hf).congr fun i ↦ ?_
  rw [Measure.restrict_restrict (measurableSet_Icc.prod hT),
    inter_eq_left.2 (prod_mono (subset_univ _) subset_rfl)]

/-- **Integral bounds over a strip from its truncations.** Let `T ⊆ ℝ` be measurable, and let `f`
and `g` be nonnegative on the strip `ℝ × T`, with `g` integrable there and `f` integrable on each
truncation `[-n, n] × T`. If `∫_{[-n, n] × T} f ≤ ∫_{[-n, n] × T} g + e n` with errors `e n → 0`,
then `f` is integrable on the strip and `∫_{ℝ × T} f ≤ ∫_{ℝ × T} g`. -/
theorem integrableOn_univ_prod_and_setIntegral_le_of_setIntegral_Icc_prod_le_add {T : Set ℝ}
    (hT : MeasurableSet T) {f g : ℝ × ℝ → ℝ} {e : ℕ → ℝ} (hf : ∀ z ∈ univ ×ˢ T, 0 ≤ f z)
    (hg : ∀ z ∈ univ ×ˢ T, 0 ≤ g z) (hfi : ∀ n : ℕ, IntegrableOn f (Icc (-(n : ℝ)) n ×ˢ T))
    (hgi : IntegrableOn g (univ ×ˢ T)) (he : Tendsto e atTop (𝓝 0))
    (hle : ∀ n : ℕ, ∫ z in Icc (-(n : ℝ)) n ×ˢ T, f z ≤
      (∫ z in Icc (-(n : ℝ)) n ×ˢ T, g z) + e n) :
    IntegrableOn f (univ ×ˢ T) ∧ ∫ z in univ ×ˢ T, f z ≤ ∫ z in univ ×ˢ T, g z := by
  have hS : MeasurableSet (univ ×ˢ T : Set (ℝ × ℝ)) := MeasurableSet.univ.prod hT
  -- The truncations exhaust the strip.
  have hφ : AECover (volume.restrict (univ ×ˢ T)) atTop fun n : ℕ ↦ Icc (-(n : ℝ)) n ×ˢ T :=
    aecover_restrict_of_ae_imp hS (ae_of_all _ fun z hz ↦
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop |z.1|).mono fun _ hn ↦
        ⟨abs_le.1 hn, hz.2⟩) fun _ ↦ measurableSet_Icc.prod hT
  have hres (n : ℕ) : (volume.restrict (univ ×ˢ T)).restrict (Icc (-(n : ℝ)) n ×ˢ T) =
      volume.restrict (Icc (-(n : ℝ)) n ×ˢ T) := by
    rw [Measure.restrict_restrict (measurableSet_Icc.prod hT),
      inter_eq_left.2 (prod_mono (subset_univ _) subset_rfl)]
  refine hφ.integrable_and_integral_le_of_setIntegral_le_add
    ((ae_restrict_iff' hS).2 (ae_of_all _ hf)) ((ae_restrict_iff' hS).2 (ae_of_all _ hg))
    (fun n ↦ ?_) hgi he (Eventually.of_forall fun n ↦ ?_)
  · rw [IntegrableOn, hres]
    exact hfi n
  · simpa only [hres] using hle n

/-- **The preimages of growing balls exhaust the space.** If the radii `r i` tend to infinity along
`l`, the preimages of the balls `closedBall x₀ (r i)` under a continuous map `g` form an
`AECover`: every point eventually lies in them. -/
theorem aecover_preimage_closedBall {α X ι : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [PseudoMetricSpace X] {μ : Measure α} {l : Filter ι} {g : α → X}
    {x₀ : X} (hg : Continuous g) {r : ι → ℝ} (hr : Tendsto r l atTop) :
    AECover μ l fun i ↦ g ⁻¹' Metric.closedBall x₀ (r i) :=
  ⟨ae_of_all _ fun z ↦ hr.eventually_ge_atTop (dist (g z) x₀),
    fun _ ↦ (Metric.isClosed_closedBall.preimage hg).measurableSet⟩

/-- **Exhausting a space by balls.** If a nonnegative function is integrable on the preimages of
the balls `closedBall x₀ (r i)` under a continuous map `g`, and its integrals over them converge
to `c` as the radii `r i` tend to infinity, then its integral over the whole space is `c`. -/
theorem lintegral_ofReal_eq_of_tendsto_setIntegral_closedBall {α X ι : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [PseudoMetricSpace X]
    {μ : Measure α} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {g : α → X} {x₀ : X}
    (hg : Continuous g) {r : ι → ℝ} (hr : Tendsto r l atTop) {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f)
    (hfi : ∀ i, IntegrableOn f (g ⁻¹' Metric.closedBall x₀ (r i)) μ)
    {c : ℝ} (hc : Tendsto (fun i ↦ ∫ z in g ⁻¹' Metric.closedBall x₀ (r i), f z ∂μ) l (𝓝 c)) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂μ = ENNReal.ofReal c := by
  have hφ : AECover μ l fun i ↦ g ⁻¹' Metric.closedBall x₀ (r i) :=
    aecover_preimage_closedBall hg hr
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hφ.integrable_of_integral_tendsto_of_nonneg_ae c hfi hf hc) hf,
    hφ.integral_eq_of_tendsto_of_nonneg_ae c hf hfi hc]

/-- Affine substitution `y = c + b * x` (`0 < b`) in a Bochner integral over `Ioi a`. -/
theorem integral_comp_add_mul_left_Ioi' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (a c : ℝ) {b : ℝ} (hb : 0 < b) :
    b • ∫ x in Ioi a, g (c + b * x) = ∫ y in Ioi (c + b * a), g y := by
  rw [integral_comp_mul_left_Ioi' (fun y ↦ g (c + y)) a hb,
    ← (measurePreserving_add_left volume c).setIntegral_preimage_emb (measurableEmbedding_addLeft c)
      g (Ioi (c + b * a)),
    preimage_const_add_Ioi, add_sub_cancel_left]

end TauCeti
