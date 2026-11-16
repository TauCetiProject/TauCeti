/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi

/-!
# Upper-tail moments of Tricomi's incomplete Gamma function

This file develops the logarithmic upper-tail moment integrals

`I_k(a, x) = ∫_{0}^{∞} s ^ k * exp(a * s - x * exp s) ds`

(`TauCeti.tricomiTailMoment`) for real `a` and `x > 0`. Under `t = x * exp s`, `x ^ a * I_0(a, x)`
is the real upper incomplete Gamma integral `∫_{x}^{∞} t ^ (a - 1) * exp(-t) dt`, and `I_k(a, x)`
is the `k`-th `a`-derivative of `I_0(a, x)`.

## Main definitions and results

* `TauCeti.tricomiTailMoment`: the `k`-th upper-tail moment `I_k(a, x)`.
* `TauCeti.integrableOn_tricomiTailIntegrand`, `TauCeti.tricomiTailMoment_zero_pos`,
  `TauCeti.continuousOn_tricomiTailMoment_zero`: integrability, positivity, and joint continuity.
* `TauCeti.hasDerivAt_tricomiTailMoment_left`, `TauCeti.hasDerivAt_tricomiTailMoment_zero_right`,
  `TauCeti.tricomiTailMoment_zero_recurrence`: partial derivatives in `a` and `x` and the shift
  recurrence `x * I_0(a + 1, x) = a * I_0(a, x) + exp(-x)`.
* `TauCeti.tricomiTailMoment_variance_le`: for `a < 0` and `x > 0`, the variance of the log-concave
  density proportional to `exp(a * s - x * exp s)` on `(0, ∞)` is at most `a ^ (-2)`.
* `Complex.tricomiIncompleteGamma_ofReal_re_eq_sub_div_Gamma`: for `a ∉ -ℕ` and `x > 0`,
  `Re γ*(a, x) = x ^ (-a) - I_0(a, x) / Γ(a)`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.2](https://dlmf.nist.gov/8.2) and
  [§8.13(iii)](https://dlmf.nist.gov/8.13#iii).
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Nat Topology Interval

namespace TauCeti

/-! ### Upper-tail moment integrals and regularity -/

/-- The `k`-th logarithmic upper-tail moment `∫_{0}^{∞} s ^ k * exp(a * s - x * exp s) ds`. -/
def tricomiTailMoment (k : ℕ) (a x : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (a * s - x * Real.exp s)

/-- Defining integral of `tricomiTailMoment`. -/
theorem tricomiTailMoment_def (k : ℕ) (a x : ℝ) :
    tricomiTailMoment k a x = ∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (a * s - x * Real.exp s) :=
  (rfl)

private theorem exists_tail_bound (k : ℕ) (A : ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ≤ A, ∀ x ≥ x₀, ∀ s ≥ (0 : ℝ),
      s ^ k * Real.exp (a * s - x * Real.exp s) ≤ C * Real.exp ((-1 : ℝ) * s) := by
  let B : ℝ := max A 0 + 2
  have hB : 0 < B := by positivity
  let s₀ : ℝ := Real.log (B / x₀)
  have hxs₀ : x₀ * Real.exp s₀ = B := by
    rw [Real.exp_log (div_pos hB hx₀), mul_div_cancel₀ _ hx₀.ne']
  refine ⟨(k ! : ℝ) * Real.exp (B * (s₀ - 1)), by positivity, fun a ha x hx s hs => ?_⟩
  have hpow : s ^ k ≤ (k ! : ℝ) * Real.exp s := by
    have h := Real.pow_div_factorial_le_exp s hs k
    rwa [div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos k)), mul_comm] at h
  have hexp_ge : B * (s - s₀ + 1) ≤ x * Real.exp s := calc
    B * (s - s₀ + 1) ≤ B * Real.exp (s - s₀) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hB.le
    _ = x₀ * Real.exp s := by rw [← hxs₀, mul_assoc, ← Real.exp_add, add_sub_cancel]
    _ ≤ x * Real.exp s := mul_le_mul_of_nonneg_right hx (Real.exp_pos s).le
  have hlin : (a + 1) * s - x * Real.exp s ≤ B * (s₀ - 1) - s := by
    have hmul : (a + 1) * s ≤ (B - 1) * s :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_left A 0]) hs
    linarith
  calc s ^ k * Real.exp (a * s - x * Real.exp s)
      ≤ ((k ! : ℝ) * Real.exp s) * Real.exp (a * s - x * Real.exp s) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (k ! : ℝ) * Real.exp ((a + 1) * s - x * Real.exp s) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ (k ! : ℝ) * Real.exp (B * (s₀ - 1) - s) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlin) (Nat.cast_nonneg _)
    _ = (k ! : ℝ) * Real.exp (B * (s₀ - 1)) * Real.exp ((-1 : ℝ) * s) := by
        rw [neg_one_mul, sub_eq_add_neg, Real.exp_add, mul_assoc]

/-- The upper-tail moment integrand `s ^ k * exp(a * s - x * exp s)` is integrable on `(0, ∞)`
for every `k : ℕ`, `a : ℝ`, and `x > 0`. -/
theorem integrableOn_tricomiTailIntegrand (k : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => s ^ k * Real.exp (a * s - x * Real.exp s)) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := exists_tail_bound k a hx
  refine ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).const_mul C).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs.le k) (Real.exp_pos _).le)]
  exact hC a le_rfl x le_rfl s hs.le

private theorem tendsto_tailIntegrand_atTop (k : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s : ℝ => s ^ k * Real.exp (a * s - x * Real.exp s)) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_tail_bound k a hx
  refine squeeze_zero' ?_ ?_ (by simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact mul_nonneg (pow_nonneg hs k) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    simpa [neg_one_mul] using hC a le_rfl x le_rfl s hs

/-- The zeroth upper-tail moment is strictly positive for every real `a` and `x > 0`. -/
theorem tricomiTailMoment_zero_pos (a : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < tricomiTailMoment 0 a x := by
  have hint := integrableOn_tricomiTailIntegrand 0 a hx
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun _ ht => ht.1
  have hle : ∫ s in Ioc (0 : ℝ) 1, Real.exp (a * s - x * Real.exp s) ≤
      tricomiTailMoment 0 a x := by
    simpa [tricomiTailMoment] using setIntegral_mono_set hint
      (Eventually.of_forall fun _ => by simp [Real.exp_nonneg]) (ae_of_all _ hsub)
  have hlow : Real.exp (min a 0 - x * Real.exp 1) ≤
      ∫ s in Ioc (0 : ℝ) 1, Real.exp (a * s - x * Real.exp s) := by
    have hconst : ∫ _s in Ioc (0 : ℝ) 1, Real.exp (min a 0 - x * Real.exp 1) =
        Real.exp (min a 0 - x * Real.exp 1) := by simp
    rw [← hconst]
    refine setIntegral_mono_on (integrableOn_const (by simp))
      ((hint.mono_set hsub).congr_fun (fun _ _ => by simp) measurableSet_Ioc)
      measurableSet_Ioc fun s hs => Real.exp_le_exp.mpr ?_
    have h1 : min a 0 ≤ a * s := by
      rcases le_or_gt a 0 with ha | ha
      · rw [min_eq_left ha]; nlinarith [hs.1, hs.2]
      · rw [min_eq_right ha.le]; exact mul_nonneg ha.le hs.1.le
    have h2 : x * Real.exp s ≤ x * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs.2) hx.le
    linarith
  exact lt_of_lt_of_le (Real.exp_pos _) (hlow.trans hle)

/-- The zeroth upper-tail moment is jointly continuous on `ℝ × (0, ∞)`. -/
theorem continuousOn_tricomiTailMoment_zero :
    ContinuousOn (fun p : ℝ × ℝ => tricomiTailMoment 0 p.1 p.2) (univ ×ˢ Ioi 0) := by
  intro ⟨a₀, x₀⟩ ⟨_, hx₀⟩
  have hmem : Iic (a₀ + 1) ×ˢ Ici (x₀ / 2) ∈ 𝓝 (a₀, x₀) :=
    prod_mem_nhds (Iic_mem_nhds (by linarith)) (Ici_mem_nhds (half_lt_self hx₀))
  obtain ⟨C, _, hC⟩ := exists_tail_bound 0 (a₀ + 1) (half_pos hx₀)
  refine (continuousAt_of_dominated (bound := fun s => C * Real.exp ((-1 : ℝ) * s))
    (Eventually.of_forall fun p => Continuous.aestronglyMeasurable (by fun_prop))
    ?_ ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).const_mul C)
    (Eventually.of_forall fun _ => by fun_prop)).continuousWithinAt
  filter_upwards [hmem] with p hp
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_of_nonneg (by simp [Real.exp_nonneg])]
  exact hC p.1 hp.1 p.2 hp.2 s hs.le

/-- Differentiating `I_k(a, x)` with respect to `a` raises the moment index to `k + 1`. -/
theorem hasDerivAt_tricomiTailMoment_left (k : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun b => tricomiTailMoment k b x) (tricomiTailMoment (k + 1) a x) a := by
  obtain ⟨C, _, hC⟩ := exists_tail_bound (k + 1) (a + 1) hx
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball a 1)
    (F := fun b s => s ^ k * Real.exp (b * s - x * Real.exp s))
    (F' := fun b s => s ^ (k + 1) * Real.exp (b * s - x * Real.exp s))
    (bound := fun s => C * Real.exp ((-1 : ℝ) * s))
    (Metric.ball_mem_nhds a zero_lt_one)
    (Eventually.of_forall fun b => Continuous.aestronglyMeasurable (by fun_prop))
    (integrableOn_tricomiTailIntegrand k a hx)
    (Continuous.aestronglyMeasurable (by fun_prop))
    ?_ ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).const_mul C) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs b hb
    have hb' : b ≤ a + 1 := by
      have := Metric.mem_ball.mp hb; rw [Real.dist_eq, abs_lt] at this; linarith
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs.le _) (Real.exp_pos _).le)]
    exact hC b hb' x le_rfl s hs.le
  · filter_upwards with s b _
    have h1 : HasDerivAt (fun b => b * s - x * Real.exp s) s b := by
      simpa using ((hasDerivAt_id b).mul_const s).sub_const (x * Real.exp s)
    convert h1.exp.const_mul (s ^ k) using 1
    ring

/-- Differentiating `I_0(a, x)` with respect to `x` yields `-I_0(a + 1, x)`. -/
theorem hasDerivAt_tricomiTailMoment_zero_right (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => tricomiTailMoment 0 a y) (-tricomiTailMoment 0 (a + 1) x) x := by
  obtain ⟨C, _, hC⟩ := exists_tail_bound 0 (a + 1) (half_pos hx)
  have hint0 : IntegrableOn (fun s : ℝ => Real.exp (a * s - x * Real.exp s)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using integrableOn_tricomiTailIntegrand 0 a hx
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball x (x / 2))
    (F := fun y s => Real.exp (a * s - y * Real.exp s))
    (F' := fun y s => -Real.exp ((a + 1) * s - y * Real.exp s))
    (bound := fun s => C * Real.exp ((-1 : ℝ) * s))
    (Metric.ball_mem_nhds x (half_pos hx))
    (Eventually.of_forall fun y => Continuous.aestronglyMeasurable (by fun_prop))
    hint0 (Continuous.aestronglyMeasurable (by fun_prop))
    ?_ ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).const_mul C) ?_).2
  · simp only [tricomiTailMoment, pow_zero, one_mul, integral_neg] at h ⊢
    exact h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs y hy
    have hy' : x / 2 ≤ y := by
      have := Metric.mem_ball.mp hy; rw [Real.dist_eq, abs_lt] at this; linarith
    rw [norm_neg, Real.norm_of_nonneg (Real.exp_pos _).le]
    simpa only [pow_zero, one_mul] using hC (a + 1) le_rfl y hy' s hs.le
  · filter_upwards with s y _
    have h1 : HasDerivAt (fun y => a * s - y * Real.exp s) (-Real.exp s) y := by
      simpa using (hasDerivAt_const y (a * s)).fun_sub ((hasDerivAt_id y).mul_const (Real.exp s))
    convert h1.exp using 1
    rw [show (a + 1) * s - y * Real.exp s = (a * s - y * Real.exp s) + s by ring, Real.exp_add]
    ring

/-- The zeroth upper-tail moment satisfies the shift recurrence
`x * I_0(a + 1, x) = a * I_0(a, x) + exp(-x)` for every real `a` and `x > 0`. -/
theorem tricomiTailMoment_zero_recurrence (a : ℝ) {x : ℝ} (hx : 0 < x) :
    x * tricomiTailMoment 0 (a + 1) x = a * tricomiTailMoment 0 a x + Real.exp (-x) := by
  have hd : ∀ s ∈ Ici (0 : ℝ),
      HasDerivAt (fun s => Real.exp (a * s - x * Real.exp s))
        (a * Real.exp (a * s - x * Real.exp s) -
          x * Real.exp ((a + 1) * s - x * Real.exp s)) s := fun s _ => by
    have h1 : HasDerivAt (fun s => a * s - x * Real.exp s) (a - x * Real.exp s) s := by
      simpa using ((hasDerivAt_id s).const_mul a).fun_sub ((Real.hasDerivAt_exp s).const_mul x)
    convert h1.exp using 1
    rw [show (a + 1) * s - x * Real.exp s = (a * s - x * Real.exp s) + s by ring, Real.exp_add]
    ring
  have hint0 : IntegrableOn (fun s => Real.exp (a * s - x * Real.exp s)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using integrableOn_tricomiTailIntegrand 0 a hx
  have hint1 : IntegrableOn (fun s => Real.exp ((a + 1) * s - x * Real.exp s)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using integrableOn_tricomiTailIntegrand 0 (a + 1) hx
  have htend : Tendsto (fun s => Real.exp (a * s - x * Real.exp s)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using tendsto_tailIntegrand_atTop 0 a hx
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    ((hint0.const_mul a).sub (hint1.const_mul x)) htend
  rw [integral_sub (hint0.const_mul a) (hint1.const_mul x), integral_const_mul,
    integral_const_mul] at hftc
  simp only [mul_zero, Real.exp_zero, mul_one, zero_sub] at hftc
  simp only [tricomiTailMoment, pow_zero, one_mul]
  linarith

/-! ### Log-concave variance bound for `a < 0` -/

private def tailSurvival (a x s : ℝ) : ℝ :=
  tricomiTailMoment 0 a x - ∫ u in (0 : ℝ)..s, Real.exp (a * u - x * Real.exp u)

private theorem hasDerivAt_tailSurvival (a x s : ℝ) :
    HasDerivAt (tailSurvival a x) (-Real.exp (a * s - x * Real.exp s)) s := by
  have hcont : Continuous fun u : ℝ => Real.exp (a * u - x * Real.exp u) := by fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 s)
    (hcont.stronglyMeasurableAtFilter volume (𝓝 s)) hcont.continuousAt
  exact ((hasDerivAt_const s (tricomiTailMoment 0 a x)).fun_sub hd).congr_deriv (zero_sub _)

private theorem tailSurvival_eq_shift (a : ℝ) {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    tailSurvival a x s = ∫ v in Ioi (0 : ℝ), Real.exp (a * (s + v) - x * Real.exp (s + v)) := by
  have hp_int : IntegrableOn (fun u => Real.exp (a * u - x * Real.exp u)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using integrableOn_tricomiTailIntegrand 0 a hx
  have hsub := intervalIntegral.integral_Ioi_sub_Ioi hp_int hs
  have hshift := (measurePreserving_add_left volume s).setIntegral_image_emb
    (measurableEmbedding_addLeft s) (fun u => Real.exp (a * u - x * Real.exp u)) (Ioi 0)
  rw [image_const_add_Ioi, add_zero] at hshift
  simp only [tailSurvival, tricomiTailMoment, pow_zero, one_mul]
  linarith

private theorem tailSurvival_eq_mul_tailMoment (a : ℝ) {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    tailSurvival a x s = Real.exp (a * s) * tricomiTailMoment 0 a (x * Real.exp s) := by
  rw [tailSurvival_eq_shift a hx hs, tricomiTailMoment, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [pow_zero, one_mul]
  rw [← Real.exp_add, Real.exp_add s v]
  congr 1; ring

private theorem tailSurvival_pos (a : ℝ) {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    0 < tailSurvival a x s := by
  rw [tailSurvival_eq_mul_tailMoment a hx hs]
  exact mul_pos (Real.exp_pos _) (tricomiTailMoment_zero_pos a (mul_pos hx (Real.exp_pos s)))

private theorem tailSurvival_le_exp (a : ℝ) {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    tailSurvival a x s ≤ tricomiTailMoment 0 a x * Real.exp (a * s) := by
  rw [tailSurvival_eq_mul_tailMoment a hx hs, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  refine setIntegral_mono_on (integrableOn_tricomiTailIntegrand 0 a (mul_pos hx (Real.exp_pos s)))
    (integrableOn_tricomiTailIntegrand 0 a hx) measurableSet_Ioi fun v _ => ?_
  simp only [pow_zero, one_mul]
  refine Real.exp_le_exp.mpr ?_
  have h1 : x ≤ x * Real.exp s := le_mul_of_one_le_right hx.le (Real.one_le_exp hs)
  nlinarith [Real.exp_pos v]

private theorem tailSurvival_submul (a : ℝ) {x s t : ℝ} (hx : 0 < x)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    tailSurvival a x (s + t) * tricomiTailMoment 0 a x ≤
      tailSurvival a x s * tailSurvival a x t := by
  let p : ℝ → ℝ := fun u => Real.exp (a * u - x * Real.exp u)
  have hp_int : IntegrableOn p (Ioi 0) := by
    simpa only [p, pow_zero, one_mul] using integrableOn_tricomiTailIntegrand 0 a hx
  have hp_shift_int : ∀ {r : ℝ}, 0 ≤ r → IntegrableOn (fun v => p (r + v)) (Ioi 0) :=
    fun {r} hr => by
      have h := (measurePreserving_add_left volume r).integrableOn_image
        (measurableEmbedding_addLeft r) (f := p) (s := Ioi 0)
      rw [image_const_add_Ioi, add_zero] at h
      exact h.mp (hp_int.mono_set (Ioi_subset_Ioi hr))
  have hp_ineq : ∀ {u : ℝ}, 0 ≤ u →
      p u * tailSurvival a x (u + t) ≤ p (u + t) * tailSurvival a x u := fun {u} hu => by
    rw [tailSurvival_eq_shift a hx (add_nonneg hu ht), tailSurvival_eq_shift a hx hu,
      ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on ((hp_shift_int (add_nonneg hu ht)).const_mul _)
      ((hp_shift_int hu).const_mul _) measurableSet_Ioi fun v hv => ?_
    simp only [p, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hfact : 0 ≤ Real.exp u * (Real.exp t - 1) * (Real.exp v - 1) :=
      mul_nonneg (mul_nonneg (Real.exp_pos u).le (sub_nonneg.mpr (Real.one_le_exp ht)))
        (sub_nonneg.mpr (Real.one_le_exp hv.le))
    have hexp_id : Real.exp u + Real.exp (u + t + v) - Real.exp (u + t) - Real.exp (u + v) =
        Real.exp u * (Real.exp t - 1) * (Real.exp v - 1) := by
      rw [Real.exp_add (u + t) v, Real.exp_add u t, Real.exp_add u v]; ring
    have : 0 ≤ x * (Real.exp u + Real.exp (u + t + v) - Real.exp (u + t) - Real.exp (u + v)) :=
      mul_nonneg hx.le (hexp_id ▸ hfact)
    linarith
  let q : ℝ → ℝ := fun u => tailSurvival a x (u + t) / tailSurvival a x u
  have hq_deriv : ∀ u ∈ Ici (0 : ℝ),
      HasDerivAt q
        ((-p (u + t) * tailSurvival a x u + tailSurvival a x (u + t) * p u) /
          (tailSurvival a x u) ^ 2) u := fun u hu => by
    have h1 : HasDerivAt (fun u => tailSurvival a x (u + t)) (-p (u + t)) u :=
      (hasDerivAt_tailSurvival a x (u + t)).comp_add_const u t
    exact (h1.div (hasDerivAt_tailSurvival a x u) (tailSurvival_pos a hx hu).ne').congr_deriv
      (by ring)
  have hq_anti : AntitoneOn q (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun u hu => (hq_deriv u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hq_deriv u (interior_subset hu)).differentiableAt.differentiableWithinAt)
      fun u hu => ?_
    have hu' : 0 ≤ u := interior_subset hu
    rw [(hq_deriv u hu').deriv]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hp_ineq hu']) (sq_nonneg _)
  have hle := hq_anti (le_refl 0) hs hs
  simp only [q, zero_add] at hle
  have h0 : tailSurvival a x 0 = tricomiTailMoment 0 a x := by
    simp [tailSurvival, intervalIntegral.integral_same]
  have hmul := (div_le_div_iff₀ (tailSurvival_pos a hx hs) (tailSurvival_pos a hx le_rfl)).mp hle
  rw [h0, mul_comm (tailSurvival a x t)] at hmul
  exact hmul

/-- For `a < 0` and `x > 0`, the variance of the probability density proportional to
`exp(a * s - x * exp s)` on `(0, ∞)` is bounded above by `(a ^ 2)⁻¹`. -/
theorem tricomiTailMoment_variance_le {a x : ℝ} (ha : a < 0) (hx : 0 < x) :
    tricomiTailMoment 2 a x / tricomiTailMoment 0 a x -
        (tricomiTailMoment 1 a x / tricomiTailMoment 0 a x) ^ 2 ≤
      (a ^ 2)⁻¹ := by
  let p : ℝ → ℝ := fun s => Real.exp (a * s - x * Real.exp s)
  let T : ℝ → ℝ := tailSurvival a x
  have hI0_pos : 0 < tricomiTailMoment 0 a x := tricomiTailMoment_zero_pos a hx
  have hT_cont : Continuous T := continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_tailSurvival a x s).continuousAt
  have hT_int : IntegrableOn T (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi ha 0).const_mul (tricomiTailMoment 0 a x)).mono'
      hT_cont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (tailSurvival_pos a hx hs.le).le]
    exact tailSurvival_le_exp a hx hs.le
  have hskT_tendsto : ∀ k : ℕ, Tendsto (fun s => s ^ k * T s) atTop (𝓝 0) := fun k => by
    have hpoly : Tendsto (fun s : ℝ => s ^ k * Real.exp (a * s)) atTop (𝓝 0) := by
      have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
        (tendsto_id.const_mul_atTop (show 0 < -a by linarith))).const_mul ((-a) ^ k)⁻¹
      simp only [mul_zero] at h1
      refine h1.congr fun s => ?_
      simp only [Function.comp_apply, id_eq]
      have hne : (-a) ^ k ≠ 0 := pow_ne_zero k (by linarith)
      rw [mul_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul, neg_mul, neg_neg]
    refine squeeze_zero' ?_ ?_ (by simpa using hpoly.const_mul (tricomiTailMoment 0 a x))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      exact mul_nonneg (pow_nonneg hs k) (tailSurvival_pos a hx hs).le
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      simpa [mul_left_comm] using mul_le_mul_of_nonneg_left (tailSurvival_le_exp a hx hs)
        (pow_nonneg hs k)
  have hsT_int : IntegrableOn (fun s => s * T s) (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (by linarith : a / 2 < 0) 0).const_mul
      (tricomiTailMoment 0 a x * (2 / (-a)))).mono'
      (continuous_id.mul hT_cont).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (mul_nonneg hs.le (tailSurvival_pos a hx hs.le).le)]
    have hpos : 0 < -a / 2 := by linarith
    have hlin : (-a / 2) * s ≤ Real.exp ((-a / 2) * s) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    have hs_le : s * Real.exp (a * s) ≤ (2 / (-a)) * Real.exp ((a / 2) * s) := by
      have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (a * s)).le
      rw [← Real.exp_add, show -a / 2 * s + a * s = a / 2 * s by ring] at hmul
      have hdiv := mul_le_mul_of_nonneg_left hmul (inv_pos.mpr hpos).le
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at hdiv
      rwa [inv_div] at hdiv
    calc s * T s ≤ s * (tricomiTailMoment 0 a x * Real.exp (a * s)) :=
          mul_le_mul_of_nonneg_left (tailSurvival_le_exp a hx hs.le) hs.le
      _ = tricomiTailMoment 0 a x * (s * Real.exp (a * s)) := by ring
      _ ≤ tricomiTailMoment 0 a x * ((2 / (-a)) * Real.exp ((a / 2) * s)) :=
          mul_le_mul_of_nonneg_left hs_le hI0_pos.le
      _ = tricomiTailMoment 0 a x * (2 / (-a)) * Real.exp ((a / 2) * s) := by ring
  -- First IBP: `∫_{0}^{∞} T = tricomiTailMoment 1 a x ≤ tricomiTailMoment 0 a x / (-a)`.
  have hIBP1 : ∫ s in Ioi (0 : ℝ), T s = tricomiTailMoment 1 a x := by
    have hp1 : IntegrableOn (fun s => s * p s) (Ioi 0) := by
      simpa only [p, pow_one] using integrableOn_tricomiTailIntegrand 1 a hx
    have h := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := 0) (b' := 0)
      (u := id) (u' := fun _ => 1) (v := T) (v' := fun s => -p s)
      (fun s _ => hasDerivAt_id s) (fun s _ => hasDerivAt_tailSurvival a x s)
      (hp1.neg.congr (Eventually.of_forall fun s => by simp [Pi.mul_apply]))
      (hT_int.congr (Eventually.of_forall fun s => by simp [Pi.mul_apply]))
      (by simpa [Pi.mul_def] using
        (((continuous_id.mul hT_cont).tendsto 0).mono_left nhdsWithin_le_nhds))
      (by simpa [Pi.mul_def, pow_one] using hskT_tendsto 1)
    simp only [id_eq, mul_neg, integral_neg, one_mul, sub_zero, zero_sub, neg_inj] at h
    simpa [tricomiTailMoment, p] using h.symm
  have hI1_le : tricomiTailMoment 1 a x ≤ tricomiTailMoment 0 a x / (-a) := by
    rw [← hIBP1]
    have hmono := setIntegral_mono_on hT_int ((integrableOn_exp_mul_Ioi ha 0).const_mul _)
      measurableSet_Ioi fun s hs => tailSurvival_le_exp a hx hs.le
    rw [integral_const_mul, integral_exp_mul_Ioi ha 0] at hmono
    simpa [mul_zero, Real.exp_zero, div_neg, neg_div, div_eq_mul_inv] using hmono
  -- Second tail `U(s) = ∫_{0}^{∞} T(s + t) dt` and two IBPs yield `I₂ * I₀ ≤ 2 * I₁²`.
  let U : ℝ → ℝ := fun s => (∫ u in Ioi (0 : ℝ), T u) - ∫ u in (0 : ℝ)..s, T u
  have hU_deriv : ∀ s : ℝ, HasDerivAt U (-T s) s := fun s => by
    have hd := intervalIntegral.integral_hasDerivAt_right (hT_cont.intervalIntegrable 0 s)
      (hT_cont.stronglyMeasurableAtFilter volume (𝓝 s)) hT_cont.continuousAt
    exact ((hasDerivAt_const s _).fun_sub hd).congr_deriv (zero_sub _)
  have hU_cont : Continuous U := continuous_iff_continuousAt.mpr fun s => (hU_deriv s).continuousAt
  have hU_shift : ∀ {s : ℝ}, 0 ≤ s → U s = ∫ t in Ioi (0 : ℝ), T (s + t) := fun {s} hs => by
    have hsub := intervalIntegral.integral_Ioi_sub_Ioi hT_int hs
    have hshift := (measurePreserving_add_left volume s).setIntegral_image_emb
      (measurableEmbedding_addLeft s) T (Ioi 0)
    rw [image_const_add_Ioi, add_zero] at hshift
    dsimp only [U]; linarith
  have hU_bound : ∀ {s : ℝ}, 0 ≤ s →
      U s * tricomiTailMoment 0 a x ≤ T s * tricomiTailMoment 1 a x := fun {s} hs => by
    rw [hU_shift hs, ← integral_mul_const, ← hIBP1, ← integral_const_mul]
    have hT_shift_int : IntegrableOn (fun t => T (s + t)) (Ioi 0) := by
      have h := (measurePreserving_add_left volume s).integrableOn_image
        (measurableEmbedding_addLeft s) (f := T) (s := Ioi 0)
      rw [image_const_add_Ioi, add_zero] at h
      exact h.mp (hT_int.mono_set (Ioi_subset_Ioi hs))
    exact setIntegral_mono_on (hT_shift_int.mul_const _)
      (hT_int.const_mul _) measurableSet_Ioi fun t ht => tailSurvival_submul a hx hs ht.le
  have hU_nonneg : ∀ {s : ℝ}, 0 ≤ s → 0 ≤ U s := fun {s} hs => by
    rw [hU_shift hs]
    exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      (tailSurvival_pos a hx (add_nonneg hs ht.le)).le
  have hU_le : ∀ {s : ℝ}, 0 ≤ s →
      U s ≤ tricomiTailMoment 1 a x / tricomiTailMoment 0 a x * T s := fun {s} hs => by
    have := (le_div_iff₀ hI0_pos).mpr (hU_bound hs)
    linarith [show T s * tricomiTailMoment 1 a x / tricomiTailMoment 0 a x =
      tricomiTailMoment 1 a x / tricomiTailMoment 0 a x * T s by ring]
  have hU_int : IntegrableOn U (Ioi 0) := by
    refine (hT_int.const_mul (tricomiTailMoment 1 a x / tricomiTailMoment 0 a x)).mono'
      hU_cont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (hU_nonneg hs.le)]
    exact hU_le hs.le
  have hsU_tendsto : Tendsto (fun s => s * U s) atTop (𝓝 0) := by
    have hdom := (hskT_tendsto 1).const_mul (tricomiTailMoment 1 a x / tricomiTailMoment 0 a x)
    rw [mul_zero] at hdom
    refine squeeze_zero' ?_ ?_ hdom
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      exact mul_nonneg hs (hU_nonneg hs)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      simpa [pow_one, mul_left_comm] using mul_le_mul_of_nonneg_left (hU_le hs) hs
  have hIBP2 : ∫ s in Ioi (0 : ℝ), U s = ∫ s in Ioi (0 : ℝ), s * T s := by
    have h := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := 0) (b' := 0)
      (u := id) (u' := fun _ => 1) (v := U) (v' := fun s => -T s)
      (fun s _ => hasDerivAt_id s) (fun s _ => hU_deriv s)
      (hsT_int.neg.congr (Eventually.of_forall fun s => by simp [Pi.mul_apply]))
      (hU_int.congr (Eventually.of_forall fun s => by simp [Pi.mul_apply]))
      (by simpa [Pi.mul_def] using
        (((continuous_id.mul hU_cont).tendsto 0).mono_left nhdsWithin_le_nhds))
      (by simpa [Pi.mul_def] using hsU_tendsto)
    simp only [id_eq, mul_neg, integral_neg, one_mul, sub_zero, zero_sub, neg_inj] at h
    exact h.symm
  have hIBP3 : 2 * ∫ s in Ioi (0 : ℝ), s * T s = tricomiTailMoment 2 a x := by
    have hp2 : IntegrableOn (fun s => s ^ 2 * p s) (Ioi 0) := by
      simpa only [p] using integrableOn_tricomiTailIntegrand 2 a hx
    have h := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := 0) (b' := 0)
      (u := fun s => s ^ 2) (u' := fun s => 2 * s) (v := T) (v' := fun s => -p s)
      (fun s _ => (hasDerivAt_pow 2 s).congr_deriv (by ring))
      (fun s _ => hasDerivAt_tailSurvival a x s)
      (hp2.neg.congr (Eventually.of_forall fun s => by simp [Pi.mul_apply]))
      ((hsT_int.const_mul 2).congr
        (Eventually.of_forall fun s => by simp [Pi.mul_apply, mul_assoc]))
      (by simpa [Pi.mul_def] using
        ((((continuous_pow 2).mul hT_cont).tendsto 0).mono_left nhdsWithin_le_nhds))
      (by simpa [Pi.mul_def] using hskT_tendsto 2)
    simp only [mul_neg, integral_neg, mul_assoc, integral_const_mul, sub_zero, zero_sub,
      neg_inj] at h
    simpa [tricomiTailMoment, p] using h.symm
  have hU_int_le : (∫ s in Ioi (0 : ℝ), U s) * tricomiTailMoment 0 a x ≤
      (tricomiTailMoment 1 a x) ^ 2 := by
    have hmono := setIntegral_mono_on (hU_int.mul_const _) (hT_int.mul_const _) measurableSet_Ioi
      fun s hs => hU_bound hs.le
    rw [integral_mul_const, integral_mul_const, hIBP1, ← sq] at hmono
    exact hmono
  have hI1_nonneg : 0 ≤ tricomiTailMoment 1 a x := by
    rw [← hIBP1]
    exact setIntegral_nonneg measurableSet_Ioi fun s hs => (tailSurvival_pos a hx hs.le).le
  have hkey : tricomiTailMoment 2 a x * tricomiTailMoment 0 a x ≤
      2 * (tricomiTailMoment 1 a x) ^ 2 := by
    rw [← hIBP3, ← hIBP2]; linarith
  have hratio_sq : (tricomiTailMoment 1 a x / tricomiTailMoment 0 a x) ^ 2 ≤ (a ^ 2)⁻¹ := by
    have hratio : tricomiTailMoment 1 a x / tricomiTailMoment 0 a x ≤ (-a)⁻¹ := by
      rw [div_le_iff₀ hI0_pos]; simpa [div_eq_mul_inv, mul_comm] using hI1_le
    simpa [inv_pow, neg_sq] using
      sq_le_sq' (by linarith [div_nonneg hI1_nonneg hI0_pos.le,
        inv_nonneg.mpr (show 0 ≤ -a by linarith)]) hratio
  have hdiv : tricomiTailMoment 2 a x / tricomiTailMoment 0 a x ≤
      2 * (tricomiTailMoment 1 a x / tricomiTailMoment 0 a x) ^ 2 := by
    rw [div_pow, div_le_iff₀ hI0_pos]
    have hne : tricomiTailMoment 0 a x ≠ 0 := hI0_pos.ne'
    calc tricomiTailMoment 2 a x
        = tricomiTailMoment 2 a x * tricomiTailMoment 0 a x / tricomiTailMoment 0 a x := by
            field_simp
      _ ≤ 2 * (tricomiTailMoment 1 a x) ^ 2 / tricomiTailMoment 0 a x :=
          div_le_div_of_nonneg_right hkey hI0_pos.le
      _ = 2 * ((tricomiTailMoment 1 a x) ^ 2 / (tricomiTailMoment 0 a x) ^ 2) *
            tricomiTailMoment 0 a x := by field_simp
  linarith

end TauCeti

namespace Complex

/-! ### Splitting identity for `Re γ*(a, x)` when `x > 0` -/

private theorem tricomiIncompleteGamma_ofReal_re_eq_sub_div_Gamma_of_pos {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) :
    (tricomiIncompleteGamma a x).re =
      x ^ (-a) - TauCeti.tricomiTailMoment 0 a x / Real.Gamma a := by
  have hconv : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent ha
  have hsplit : (∫ t in (0 : ℝ)..x, Real.exp (-t) * t ^ (a - 1)) +
      (∫ t in Ioi x, Real.exp (-t) * t ^ (a - 1)) = Real.Gamma a := by
    rw [Real.Gamma_eq_integral ha]
    exact intervalIntegral.integral_interval_add_Ioi hconv (hconv.mono_set (Ioi_subset_Ioi hx.le))
  -- Lower part `[0, x]`: substitute `t = x * u`.
  have hlow : ∫ t in (0 : ℝ)..x, Real.exp (-t) * t ^ (a - 1) =
      x ^ a * Real.Gamma a * (tricomiIncompleteGamma a x).re := by
    have hsub := intervalIntegral.integral_comp_mul_left
      (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) hx.ne' (a := (0 : ℝ)) (b := 1)
    simp only [mul_zero, mul_one, smul_eq_mul] at hsub
    have hrewrite : ∫ u in (0 : ℝ)..1, Real.exp (-(x * u)) * (x * u) ^ (a - 1) =
        x ^ (a - 1) * ∫ u in (0 : ℝ)..1, u ^ (a - 1) * Real.exp (-(x * u)) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
      rw [uIoc_of_le zero_le_one] at hu; rw [Real.mul_rpow hx.le hu.1.le]; ring
    have hΓ_ne : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    have hγ : ∫ u in (0 : ℝ)..1, u ^ (a - 1) * Real.exp (-(x * u)) =
        Real.Gamma a * (tricomiIncompleteGamma a x).re := by
      rw [tricomiIncompleteGamma_ofReal_re_eq_integral ha x]; field_simp
    rw [hrewrite, hγ] at hsub
    have hpow : x * x ^ (a - 1) = x ^ a := by
      rw [mul_comm, ← Real.rpow_add_one hx.ne', sub_add_cancel]
    have hmul := congrArg (x * ·) hsub
    simp only [← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul] at hmul
    rw [← hmul, hpow]
  -- Upper part `(x, ∞)`: substitute `t = x * exp s`.
  have hhigh : ∫ t in Ioi x, Real.exp (-t) * t ^ (a - 1) =
      x ^ a * TauCeti.tricomiTailMoment 0 a x := by
    have h1 := integral_comp_mul_left_Ioi (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) 1 hx
    have h2 := integral_comp_exp_Ioi (fun u : ℝ => Real.exp (-(x * u)) * (x * u) ^ (a - 1)) 0
    simp only [mul_one, Real.exp_zero, smul_eq_mul] at h1 h2
    have h3 : ∫ t in Ioi x, Real.exp (-t) * t ^ (a - 1) =
        x * ∫ s in Ioi (0 : ℝ), Real.exp s * (Real.exp (-(x * Real.exp s)) *
          (x * Real.exp s) ^ (a - 1)) := by
      rw [h2, h1, ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]
    rw [h3, ← integral_const_mul, TauCeti.tricomiTailMoment_def, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [pow_zero, one_mul]
    have hxe : 0 < x * Real.exp s := mul_pos hx (Real.exp_pos s)
    have hpow : x * Real.exp s * (x * Real.exp s) ^ (a - 1) = x ^ a * Real.exp (a * s) := by
      rw [mul_comm (x * Real.exp s), ← Real.rpow_add_one hxe.ne', sub_add_cancel,
        Real.mul_rpow hx.le (Real.exp_pos s).le, ← Real.exp_mul, mul_comm s a]
    calc x * (Real.exp s * (Real.exp (-(x * Real.exp s)) * (x * Real.exp s) ^ (a - 1)))
        = (x * Real.exp s * (x * Real.exp s) ^ (a - 1)) * Real.exp (-(x * Real.exp s)) := by ring
      _ = x ^ a * Real.exp (a * s) * Real.exp (-(x * Real.exp s)) := by rw [hpow]
      _ = x ^ a * Real.exp (a * s - x * Real.exp s) := by
          rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]
  rw [hlow, hhigh] at hsplit
  have hΓ_ne : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hxa_ne : x ^ a ≠ 0 := (Real.rpow_pos_of_pos hx a).ne'
  rw [Real.rpow_neg hx.le]
  field_simp
  linarith

/-- For every regular real parameter `a ∉ -ℕ` and every `x > 0`,
`Re γ*(a, x) = x ^ (-a) - I_0(a, x) / Γ(a)`. -/
theorem tricomiIncompleteGamma_ofReal_re_eq_sub_div_Gamma {a : ℝ}
    (ha : ∀ m : ℕ, a ≠ -(m : ℝ)) {x : ℝ} (hx : 0 < x) :
    (tricomiIncompleteGamma a x).re =
      x ^ (-a) - TauCeti.tricomiTailMoment 0 a x / Real.Gamma a := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-a)
  induction N generalizing a with
  | zero =>
    exact tricomiIncompleteGamma_ofReal_re_eq_sub_div_Gamma_of_pos (by simpa using hN) hx
  | succ N ih =>
    have ha1 : ∀ m : ℕ, a + 1 ≠ -(m : ℝ) := fun m hm => ha (m + 1) (by push_cast; linarith)
    have hrec_γ : (tricomiIncompleteGamma a x).re =
        x * (tricomiIncompleteGamma (a + 1 : ℝ) x).re + Real.exp (-x) / Real.Gamma (a + 1) := by
      have h := congrArg Complex.re
        (tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one (a : ℂ) (x : ℂ))
      rw [add_re, re_ofReal_mul] at h
      have hdiv : (cexp (-(x : ℂ)) / Gamma ((a : ℂ) + 1)).re =
          Real.exp (-x) / Real.Gamma (a + 1) := by
        rw [← ofReal_neg, ← ofReal_exp, ← ofReal_one, ← ofReal_add, Gamma_ofReal, ← ofReal_div,
          ofReal_re]
      rw [hdiv, ← ofReal_one, ← ofReal_add] at h
      exact h
    have hrec_I := TauCeti.tricomiTailMoment_zero_recurrence a hx
    have ha0 : a ≠ 0 := by simpa using ha 0
    have hΓ_ne : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero ha
    have hpow : x * x ^ (-(a + 1)) = x ^ (-a) := by
      rw [mul_comm, ← Real.rpow_add_one hx.ne', show -(a + 1) + 1 = -a by ring]
    rw [hrec_γ, ih ha1 (by push_cast at hN; linarith), mul_sub, hpow, Real.Gamma_add_one ha0]
    field_simp
    linarith

end Complex
