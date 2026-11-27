/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.WeakConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shifted singular-value resolvent on the imaginary axis

For a shift of modulus `r`, the limiting transform of the Hermitian dilation at `iη`
has imaginary part `u > 0` satisfying `u = (η + u) / ((η + u)^2 + r^2)`.
Solving this scalar equation on the nonnegative half-line gives a residual bound that turns
approximate resolvent identities into convergence at each positive height. The solution's
normalization at infinity gives tightness, so convergence on the imaginary axis then yields
weak convergence by analytic uniqueness of the resolvent transform.
At the boundary the solution tends to `√(1 - r^2)`, with the square root taken to be zero
when `r^2 ≥ 1`.

## References

* C. Bordenave and D. Chafaï, *Around the circular law*, Probab. Surv. 9 (2012), 1–89,
  Corollary 4.10 and §4.6.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- The left side of the shifted equation after multiplying by its denominator and
dividing by the positive factor `η + u`. -/
private def shiftedResolventEquation (r η u : ℝ) : ℝ :=
  u * (η + u) + r ^ 2 * (u / (η + u))

private theorem le_shiftedResolventEquation_sub (r : ℝ) {η u v : ℝ}
    (hη : 0 ≤ η) (hu : 0 ≤ u) (huv : u ≤ v) :
    η * (v - u) ≤ shiftedResolventEquation r η v - shiftedResolventEquation r η u := by
  have hv : 0 ≤ v := hu.trans huv
  have hdiv : u / (η + u) ≤ v / (η + v) := by
    rcases hu.eq_or_lt with rfl | hu'
    · rw [zero_div]
      exact div_nonneg hv (add_nonneg hη hv)
    · have hv' := hu'.trans_le huv
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith
  have hmul := mul_le_mul_of_nonneg_left hdiv (sq_nonneg r)
  have hsquare := mul_le_mul huv huv hu hv
  unfold shiftedResolventEquation
  nlinarith

private theorem exists_shiftedResolventEquation_eq_one (r : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ u : ℝ, u ∈ Icc 0 1 ∧ shiftedResolventEquation r η u = 1 := by
  have hc : ContinuousOn (shiftedResolventEquation r η) (Icc 0 1) := by
    unfold shiftedResolventEquation
    fun_prop (disch := exact fun _ hx ↦ (add_pos_of_pos_of_nonneg hη hx.1).ne')
  apply intermediate_value_Icc zero_le_one hc
  constructor
  · simp [shiftedResolventEquation]
  · unfold shiftedResolventEquation
    have : 0 ≤ r ^ 2 * (1 / (η + 1)) := by positivity
    linarith

/-- Imaginary part of the shifted singular-value resolvent at height `η > 0`.
At nonpositive heights use its limiting value at zero. The parameter `r` is the modulus
of the shift, and only `r^2` enters the equation. -/
def shiftedSingularValueResolventIm (r η : ℝ) : ℝ :=
  if hη : 0 < η then (exists_shiftedResolventEquation_eq_one r hη).choose
  else √(1 - r ^ 2)

private theorem shiftedSingularValueResolventIm_spec (r : ℝ) {η : ℝ} (hη : 0 < η) :
    shiftedSingularValueResolventIm r η ∈ Icc 0 1 ∧
      shiftedResolventEquation r η (shiftedSingularValueResolventIm r η) = 1 := by
  rw [shiftedSingularValueResolventIm, dite_eq_left hη]
  exact (exists_shiftedResolventEquation_eq_one r hη).choose_spec

/-- At nonpositive heights the imaginary part is defined to be its limiting value at zero. -/
@[simp]
theorem shiftedSingularValueResolventIm_of_nonpos (r : ℝ) {η : ℝ} (hη : η ≤ 0) :
    shiftedSingularValueResolventIm r η = √(1 - r ^ 2) := by
  rw [shiftedSingularValueResolventIm, dite_eq_right hη.not_gt]

/-- At height zero the imaginary part takes its limiting value. -/
theorem shiftedSingularValueResolventIm_zero (r : ℝ) :
    shiftedSingularValueResolventIm r 0 = √(1 - r ^ 2) :=
  shiftedSingularValueResolventIm_of_nonpos r le_rfl

/-- The imaginary part is nonnegative. -/
theorem shiftedSingularValueResolventIm_nonneg (r η : ℝ) :
    0 ≤ shiftedSingularValueResolventIm r η := by
  by_cases hη : 0 < η
  · exact (shiftedSingularValueResolventIm_spec r hη).1.1
  · rw [shiftedSingularValueResolventIm_of_nonpos r (le_of_not_gt hη)]
    exact Real.sqrt_nonneg _

/-- The imaginary part is at most one. -/
theorem shiftedSingularValueResolventIm_le_one (r η : ℝ) :
    shiftedSingularValueResolventIm r η ≤ 1 := by
  by_cases hη : 0 < η
  · exact (shiftedSingularValueResolventIm_spec r hη).1.2
  · rw [shiftedSingularValueResolventIm_of_nonpos r (le_of_not_gt hη)]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (sub_le_self 1 (sq_nonneg r))

/-- The imaginary part solves the cubic form of the fixed-point equation at nonnegative
height. -/
theorem shiftedSingularValueResolventIm_mul_eq (r : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    shiftedSingularValueResolventIm r η * ((η + shiftedSingularValueResolventIm r η) ^ 2 + r ^ 2) =
      η + shiftedSingularValueResolventIm r η := by
  rcases hη.eq_or_lt with rfl | hη
  · simp only [zero_add, shiftedSingularValueResolventIm_zero]
    rcases le_total (r ^ 2) 1 with hr | hr
    · rw [Real.sq_sqrt (sub_nonneg.2 hr)]
      ring
    · rw [Real.sqrt_eq_zero_of_nonpos (sub_nonpos.2 hr), zero_mul]
  have hp : 0 < η + shiftedSingularValueResolventIm r η :=
    add_pos_of_pos_of_nonneg hη (shiftedSingularValueResolventIm_nonneg r η)
  have heq := (shiftedSingularValueResolventIm_spec r hη).2
  unfold shiftedResolventEquation at heq
  field_simp [hp.ne'] at heq
  linear_combination heq

private theorem shiftedSingularValueResolventIm_mul_sub (r : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    shiftedSingularValueResolventIm r η *
      ((η + shiftedSingularValueResolventIm r η) ^ 2 + r ^ 2 - 1) = η := by
  linear_combination shiftedSingularValueResolventIm_mul_eq r hη

/-- The shifted singular-value resolvent satisfies its fixed-point equation at nonnegative
height. At zero this equation can also have other solutions. -/
theorem shiftedSingularValueResolventIm_eq_div (r : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    shiftedSingularValueResolventIm r η =
      (η + shiftedSingularValueResolventIm r η) /
        ((η + shiftedSingularValueResolventIm r η) ^ 2 + r ^ 2) := by
  have hmul := shiftedSingularValueResolventIm_mul_eq r hη
  by_cases hden : (η + shiftedSingularValueResolventIm r η) ^ 2 + r ^ 2 = 0
  · rw [hden, div_zero]
    rw [hden, mul_zero] at hmul
    linarith [shiftedSingularValueResolventIm_nonneg r η]
  · exact (eq_div_iff hden).2 hmul

/-- The imaginary part is strictly positive at positive height. -/
theorem shiftedSingularValueResolventIm_pos (r : ℝ) {η : ℝ} (hη : 0 < η) :
    0 < shiftedSingularValueResolventIm r η := by
  have hu := shiftedSingularValueResolventIm_nonneg r η
  rw [shiftedSingularValueResolventIm_eq_div r hη.le]
  positivity

private theorem mul_abs_sub_le_abs_shiftedResolventEquation_sub (r η : ℝ) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    η * |u - v| ≤ |shiftedResolventEquation r η u - shiftedResolventEquation r η v| := by
  rcases le_or_gt 0 η with hη | hη
  · rcases le_total v u with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact (le_shiftedResolventEquation_sub r hη hv h).trans (le_abs_self _)
    · rw [abs_sub_comm u v, abs_of_nonneg (sub_nonneg.2 h), abs_sub_comm]
      exact (le_shiftedResolventEquation_sub r hη hu h).trans (le_abs_self _)
  · exact (mul_nonpos_of_nonpos_of_nonneg hη.le (abs_nonneg _)).trans (abs_nonneg _)

/-- The deviation from the solution is bounded by the absolute residual of the cubic equation
`v * ((η + v)^2 + r^2) = η + v`, divided by the squared height. -/
theorem abs_sub_shiftedSingularValueResolventIm_le (r : ℝ) {η v : ℝ}
    (hη : 0 < η) (hv : 0 ≤ v) :
    |v - shiftedSingularValueResolventIm r η| ≤
      |v * ((η + v) ^ 2 + r ^ 2) - (η + v)| / η ^ 2 := by
  have hp : 0 < η + v := add_pos_of_pos_of_nonneg hη hv
  have h := mul_abs_sub_le_abs_shiftedResolventEquation_sub r η hv
    (shiftedSingularValueResolventIm_nonneg r η)
  rw [(shiftedSingularValueResolventIm_spec r hη).2, mul_comm η] at h
  have hres : shiftedResolventEquation r η v - 1 =
      (v * ((η + v) ^ 2 + r ^ 2) - (η + v)) / (η + v) := by
    unfold shiftedResolventEquation
    field_simp [hp.ne']
  rw [hres, abs_div, abs_of_pos hp] at h
  calc
    |v - shiftedSingularValueResolventIm r η| ≤
        |v * ((η + v) ^ 2 + r ^ 2) - (η + v)| / (η + v) / η := (le_div_iff₀ hη).2 h
    _ ≤ |v * ((η + v) ^ 2 + r ^ 2) - (η + v)| / η ^ 2 := by
      rw [div_div, pow_two η]
      gcongr
      linarith

/-- A nonnegative solution of the fixed-point equation at positive height is unique. -/
theorem eq_shiftedSingularValueResolventIm_iff (r : ℝ) {η v : ℝ}
    (hη : 0 < η) (hv : 0 ≤ v) :
    v = shiftedSingularValueResolventIm r η ↔ v = (η + v) / ((η + v) ^ 2 + r ^ 2) := by
  constructor
  · rintro rfl
    exact shiftedSingularValueResolventIm_eq_div r hη.le
  · intro heq
    have heq' := (eq_div_iff (by positivity)).1 heq
    have h := abs_sub_shiftedSingularValueResolventIm_le r hη hv
    rw [heq', sub_self, abs_zero, zero_div] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- A nonnegative family with vanishing residual at a fixed positive height tends to
the imaginary part of the shifted singular-value resolvent. -/
theorem tendsto_nhds_shiftedSingularValueResolventIm_of_tendsto_mul_sub (r : ℝ) {η : ℝ}
    (hη : 0 < η) {ι : Type*} {l : Filter ι} {v : ι → ℝ} (hv : ∀ᶠ i in l, 0 ≤ v i)
    (h : Tendsto (fun i ↦ v i * ((η + v i) ^ 2 + r ^ 2) - (η + v i)) l (𝓝 0)) :
    Tendsto v l (𝓝 (shiftedSingularValueResolventIm r η)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb : Tendsto (fun i ↦ |v i * ((η + v i) ^ 2 + r ^ 2) - (η + v i)| / η ^ 2)
      l (𝓝 0) := by
    simpa only [abs_zero, zero_div] using h.abs.div_const (η ^ 2)
  refine squeeze_zero' (.of_forall fun _ ↦ dist_nonneg) ?_ hb
  filter_upwards [hv] with i hi
  rw [Real.dist_eq]
  exact abs_sub_shiftedSingularValueResolventIm_le r hη hi

/-- The imaginary-axis solution has the normalization of a probability resolvent at infinity. -/
theorem tendsto_mul_shiftedSingularValueResolventIm (r : ℝ) :
    Tendsto (fun η ↦ η * shiftedSingularValueResolventIm r η) atTop (𝓝 1) := by
  have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hu : Tendsto (fun η ↦ shiftedSingularValueResolventIm r η / η) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hinv
    · filter_upwards [eventually_gt_atTop 0] with η hη
      exact div_nonneg (shiftedSingularValueResolventIm_nonneg r η) hη.le
    · filter_upwards [eventually_gt_atTop 0] with η hη
      rw [← one_div]
      exact div_le_div_of_nonneg_right (shiftedSingularValueResolventIm_le_one r η) hη.le
  have hsum := hu.const_add 1
  have hr := hinv.const_mul r
  have hlim := hsum.div ((hsum.pow 2).add (hr.pow 2)) (by norm_num)
  simp only [add_zero, mul_zero, one_pow, zero_pow (by decide : 2 ≠ 0), div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with η hη
  set u := shiftedSingularValueResolventIm r η
  have hu₀ : 0 ≤ u := shiftedSingularValueResolventIm_nonneg r η
  have hden : 0 < (1 + u / η) ^ 2 + (r * η⁻¹) ^ 2 := by positivity
  apply (div_eq_iff hden.ne').2
  field_simp [hη.ne']
  linear_combination -shiftedSingularValueResolventIm_mul_sub r hη.le

/-- Probability laws whose resolvent transforms on the positive imaginary axis converge to
purely imaginary values obeying the shifted equation have a weak limit. The hypothesis is
given in residual form, and the normalized solution at infinity supplies tightness. -/
theorem exists_tendsto_of_tendsto_resolventTransform_im_mul_sub (r : ℝ)
    (μs : ℕ → ProbabilityMeasure ℝ)
    (hre : ∀ η : ℝ, 0 < η →
      Tendsto (fun i ↦ (resolventTransform (μs i : Measure ℝ) (η * Complex.I)).re)
        atTop (𝓝 0))
    (hres : ∀ η : ℝ, 0 < η →
      Tendsto (fun i ↦ (resolventTransform (μs i : Measure ℝ) (η * Complex.I)).im *
        ((η + (resolventTransform (μs i : Measure ℝ) (η * Complex.I)).im) ^ 2 + r ^ 2) -
        (η + (resolventTransform (μs i : Measure ℝ) (η * Complex.I)).im)) atTop (𝓝 0)) :
    ∃ μ : ProbabilityMeasure ℝ, Tendsto μs atTop (𝓝 μ) ∧ ∀ η : ℝ, 0 < η →
      resolventTransform (μ : Measure ℝ) (η * Complex.I) =
        shiftedSingularValueResolventIm r η * Complex.I := by
  have haxis (η : ℝ) (hη : 0 < η) :
      Tendsto (fun i ↦ resolventTransform (μs i : Measure ℝ) (η * Complex.I)) atTop
        (𝓝 ((shiftedSingularValueResolventIm r η : ℂ) * Complex.I)) := by
    have hpos i : 0 ≤ (resolventTransform (μs i : Measure ℝ) (η * Complex.I)).im :=
      (im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) (by simpa using hη)).le
    have him := tendsto_nhds_shiftedSingularValueResolventIm_of_tendsto_mul_sub r hη
      (.of_forall hpos) (hres η hη)
    have hre' := Complex.continuous_ofReal.continuousAt.tendsto.comp (hre η hη)
    have him' := Complex.continuous_ofReal.continuousAt.tendsto.comp him
    simpa only [Function.comp_apply, Complex.re_add_im, Complex.ofReal_zero, zero_add]
      using hre'.add (him'.mul_const Complex.I)
  let p (η : ℝ) : ℂ := (η : ℂ) * Complex.I
  have hp (η : ℝ) : (p η).im = η := by simp [p]
  let D := p '' Ioi (1 : ℝ)
  have hacc : p 1 ∈ closure (D \ {p 1}) := by
    have hpcont : Continuous p := Complex.continuous_ofReal.mul continuous_const
    have hone : (1 : ℝ) ∈ closure (Ioi 1) := by simp [closure_Ioi]
    have hsub : D ⊆ D \ {p 1} := by
      rintro _ ⟨η, hη, rfl⟩
      refine ⟨mem_image_of_mem p hη, ?_⟩
      intro heq
      exact hη.ne' (by simpa only [hp] using congrArg Complex.im heq)
    exact closure_mono hsub (mem_closure_image hpcont.continuousAt hone)
  let g (z : ℂ) : ℂ := (shiftedSingularValueResolventIm r z.im : ℂ) * Complex.I
  have hg : Tendsto (fun η : ℝ ↦ η * Complex.I * g (η * Complex.I)) atTop (𝓝 (-1)) := by
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_mul_shiftedSingularValueResolventIm r)
    simp only [Complex.ofReal_one] at hc
    refine hc.neg.congr fun η ↦ ?_
    simp only [Function.comp_apply, g, Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_mul]
    rw [mul_mul_mul_comm, Complex.I_mul_I, mul_neg_one]
  have htight : IsTightMeasureSet {(μs i : Measure ℝ) | i} :=
    isTightMeasureSet_range_of_tendsto_resolventTransform (g := g) hg (by simpa [g] using haxis)
  obtain ⟨μ, hμ, -⟩ :=
    ProbabilityMeasure.existsUnique_tendsto_of_isTightMeasureSet_of_tendsto_resolventTransform
      (f := g) htight (by simp [hp]) hacc (by
        rintro _ ⟨η, hη, rfl⟩
        simpa only [g, hp] using haxis η (zero_lt_one.trans hη))
  exact ⟨μ, hμ, fun η hη ↦ tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_resolventTransform_of_tendsto hμ (by simpa using hη.ne'))
    (haxis η hη)⟩

private theorem sqrt_sub_le_shiftedSingularValueResolventIm (r : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    √(1 - r ^ 2) - η ≤ shiftedSingularValueResolventIm r η := by
  rcases hη.eq_or_lt with rfl | hη
  · simp
  set u := shiftedSingularValueResolventIm r η
  have hu : 0 < u := shiftedSingularValueResolventIm_pos r hη
  have heq : u * ((η + u) ^ 2 + r ^ 2 - 1) = η :=
    shiftedSingularValueResolventIm_mul_sub r hη.le
  have hmul : 0 < u * ((η + u) ^ 2 + r ^ 2 - 1) := by rwa [heq]
  have hp : 0 < (η + u) ^ 2 + r ^ 2 - 1 := pos_of_mul_pos_right hmul hu.le
  have h : √(1 - r ^ 2) ≤ η + u := (Real.sqrt_le_iff.2 ⟨by positivity, by linarith⟩)
  linarith

private theorem shiftedSingularValueResolventIm_le_sqrt_add (r : ℝ) {η ε : ℝ}
    (hη : 0 ≤ η) (hηε : η ≤ ε ^ 3) :
    shiftedSingularValueResolventIm r η ≤ √(1 - r ^ 2) + ε := by
  have hε : 0 ≤ ε := (by decide : Odd 3).pow_nonneg_iff.1 (hη.trans hηε)
  set u := shiftedSingularValueResolventIm r η
  set a := √(1 - r ^ 2)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hu : 0 ≤ u := shiftedSingularValueResolventIm_nonneg r η
  have ha₂ : a ^ 2 = max (1 - r ^ 2) 0 := Real.sq_sqrt'
  have heq : u * ((η + u) ^ 2 + r ^ 2 - 1) = η :=
    shiftedSingularValueResolventIm_mul_sub r hη
  by_contra! h
  have hgap : 0 ≤ u - a := by linarith
  have hleft : (u - a) ^ 3 ≤ u * (u ^ 2 - a ^ 2) := by
    calc
      (u - a) ^ 3 = (u - a) * (u - a) * (u - a) := by ring
      _ ≤ u * (u - a) * (u + a) := by gcongr <;> linarith
      _ = u * (u ^ 2 - a ^ 2) := by ring
  have hright : u * (u ^ 2 - a ^ 2) ≤ η := by
    rw [← heq]
    apply mul_le_mul_of_nonneg_left _ hu
    have := le_max_left (1 - r ^ 2) 0
    nlinarith [mul_nonneg hη hu]
  have hc : ε ^ 3 < (u - a) ^ 3 := pow_lt_pow_left₀ (by linarith) hε (by decide)
  linarith

/-- As the height decreases to zero, the positive solution converges to the square root
of `1 - r^2` inside the unit disc and to zero on and outside its boundary. -/
theorem tendsto_shiftedSingularValueResolventIm_nhdsGT_zero (r : ℝ) :
    Tendsto (shiftedSingularValueResolventIm r) (𝓝[>] 0) (𝓝 (√(1 - r ^ 2))) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hb : 0 < min (ε / 2) ((ε / 2) ^ 3) := lt_min (by positivity) (by positivity)
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (gt_mem_nhds hb)] with η hη hb'
  have hη' : 0 < η := hη
  have hb'' := lt_min_iff.1 hb'
  have hlo := sqrt_sub_le_shiftedSingularValueResolventIm r hη'.le
  have hhi := shiftedSingularValueResolventIm_le_sqrt_add r hη'.le hb''.2.le
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end TauCeti
