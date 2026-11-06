/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A kernel with an arctangent primitive that concentrates at a zero

Let `f` be continuous on `[a, b]` with `f a = 0`, differentiable on `(a, b)` with positive
derivative `f'`. For `j > 0` consider the kernel

`k_j(x) = f'(x) j / (f(x) √(f(x) - j²))`.

Since the real square root vanishes on negative numbers and division by zero gives zero, `k_j`
vanishes where `f ≤ j²`; where `f > j²` it is the derivative of `2 arctan (√(f(x) - j²) / j)`.
Although `k_j` is unbounded at the point where `f = j²`, it is nonnegative, so it is integrable on
`[a, x]` for every `x ∈ [a, b]`, with

`∫_a^x k_j = 2 arctan (√(f(x) - j²) / j)`
(`TauCeti.integral_mul_div_mul_sqrt_sub_sq`).

As `j → 0⁺` this tends to `π` for every `x ∈ (a, b]`, so the integral of `k_j` over `[x, b]`
tends to `0`: the kernels `k_j / π` concentrate at `a`. Consequently, for every `ψ` continuous on
`[a, b]`,

`∫_a^b ψ(x) k_j(x) dx → π ψ(a)` as `j → 0⁺`
(`TauCeti.tendsto_integral_mul_mul_div_mul_sqrt_sub_sq`).

This is the local computation behind quadratures of the form `∫ j dz / (g(z) √(f(z) - j²))` near a
common simple zero `a` of `f` and `g`: writing `1 / g = ψ f' / f` with `ψ = f / (g f')` continuous
at `a`, the contribution of a neighbourhood of `a` tends to `π ψ(a)` as `j → 0⁺`. For the
spherical pendulum this computes the limits of the rotation angle at the poles of the sphere.

## Implementation notes

Mathlib's `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto` asks the kernels to tend to
`0` uniformly away from `a`, which would need a bound on `f'` up to `b`. The estimate here uses only
the explicit primitive, so `f'` is only required to be positive on `(a, b)`.

## Main declarations

* `TauCeti.intervalIntegrable_mul_div_mul_sqrt_sub_sq`,
  `TauCeti.integral_mul_div_mul_sqrt_sub_sq`: the integrability of `k_j` on `[a, x]` and its
  integral.
* `TauCeti.tendsto_integral_mul_mul_div_mul_sqrt_sub_sq`: `∫_a^b ψ k_j → π ψ(a)`.
-/

public section

open Filter Real Set MeasureTheory
open scoped Topology

namespace TauCeti

variable {a b : ℝ} {f f' : ℝ → ℝ}

/-- The kernel vanishes where `f ≤ j²`. -/
private theorem mul_div_mul_sqrt_sub_sq_eq_zero {j t : ℝ} (ht : f t ≤ j ^ 2) :
    f' t * j / (f t * √(f t - j ^ 2)) = 0 := by
  rw [Real.sqrt_eq_zero'.2 (sub_nonpos.2 ht), mul_zero, div_zero]

/-- Where `f > j²`, the kernel is the derivative of `2 arctan (√(f - j²) / j)`. -/
private theorem hasDerivAt_two_mul_arctan_sqrt_sub_sq_div {j t : ℝ} (hj : 0 < j)
    (ht : j ^ 2 < f t) (hd : HasDerivAt f (f' t) t) :
    HasDerivAt (fun x ↦ 2 * arctan (√(f x - j ^ 2) / j))
      (f' t * j / (f t * √(f t - j ^ 2))) t := by
  have hpos : 0 < f t - j ^ 2 := sub_pos.2 ht
  have hs : 0 < √(f t - j ^ 2) := Real.sqrt_pos.2 hpos
  have hsq : √(f t - j ^ 2) ^ 2 = f t - j ^ 2 := Real.sq_sqrt hpos.le
  have hf : 0 < f t := (sq_nonneg j).trans_lt ht
  convert (((hd.sub_const (j ^ 2)).sqrt hpos.ne').div_const j).arctan.const_mul 2 using 1
  field_simp
  rw [hsq]
  ring

/-- A function with positive derivative on `(a, b)` is strictly increasing on `[a, b]`. -/
private theorem strictMonoOn_of_hasDerivAt_pos (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Ioo a b, 0 < f' x) :
    StrictMonoOn f (Icc a b) :=
  strictMonoOn_of_deriv_pos (convex_Icc a b) hf fun x hx ↦ by
    rw [interior_Icc] at hx
    rw [(hderiv x hx).deriv]
    exact hpos x hx

/-- At a point where `f` is positive, `2 arctan (√(f x - j²) / j) → π` as `j → 0⁺`. -/
private theorem tendsto_two_mul_arctan_sqrt_sub_sq_div {x : ℝ} (hx : 0 < f x) :
    Tendsto (fun j ↦ 2 * arctan (√(f x - j ^ 2) / j)) (𝓝[>] 0) (𝓝 π) := by
  have hsqrt : Tendsto (fun j : ℝ ↦ √(f x - j ^ 2)) (𝓝[>] 0) (𝓝 √(f x)) := by
    have : Continuous fun j : ℝ ↦ √(f x - j ^ 2) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hatTop : Tendsto (fun j : ℝ ↦ √(f x - j ^ 2) / j) (𝓝[>] 0) atTop := by
    simp_rw [div_eq_mul_inv]
    exact hsqrt.pos_mul_atTop (Real.sqrt_pos.2 hx) tendsto_inv_nhdsGT_zero
  have := ((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hatTop).const_mul 2
  rwa [mul_div_cancel₀ π two_ne_zero] at this

section Kernel

variable (hf : ContinuousOn f (Icc a b)) (hfa : f a = 0)
  (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Ioo a b, 0 < f' x)
include hf hfa hderiv hpos

/-- The kernel is nonnegative on `(a, b)`. -/
private theorem mul_div_mul_sqrt_sub_sq_nonneg {j t : ℝ} (hj : 0 < j) (ht : t ∈ Ioo a b) :
    0 ≤ f' t * j / (f t * √(f t - j ^ 2)) := by
  have hft : 0 < f t := by
    rw [← hfa]
    exact strictMonoOn_of_hasDerivAt_pos hf hderiv hpos ⟨le_rfl, (ht.1.trans ht.2).le⟩
      (Ioo_subset_Icc_self ht) ht.1
  exact div_nonneg (mul_nonneg (hpos t ht).le hj.le) (mul_nonneg hft.le (Real.sqrt_nonneg _))

omit hfa in
/-- The kernel vanishes identically on `[a, y]` when `f y ≤ j²`. -/
private theorem eqOn_mul_div_mul_sqrt_sub_sq_zero {j y : ℝ} (hy : y ∈ Icc a b)
    (hfy : f y ≤ j ^ 2) :
    EqOn (fun t ↦ f' t * j / (f t * √(f t - j ^ 2))) 0 (uIcc a y) := by
  intro t ht
  rw [uIcc_of_le hy.1] at ht
  have hmono := (strictMonoOn_of_hasDerivAt_pos hf hderiv hpos).monotoneOn
  exact mul_div_mul_sqrt_sub_sq_eq_zero
    ((hmono ⟨ht.1, ht.2.trans hy.2⟩ hy ht.2).trans hfy)

/-- The integrability of the kernel on `[a, x]`, together with its integral
`2 arctan (√(f x - j²) / j)`. -/
private theorem intervalIntegrable_and_integral_mul_div_mul_sqrt_sub_sq {j x : ℝ} (hj : 0 < j)
    (hx : x ∈ Icc a b) :
    IntervalIntegrable (fun t ↦ f' t * j / (f t * √(f t - j ^ 2))) volume a x ∧
      ∫ t in a..x, f' t * j / (f t * √(f t - j ^ 2)) = 2 * arctan (√(f x - j ^ 2) / j) := by
  have hzero : ∀ y ∈ Icc a b, f y ≤ j ^ 2 →
      IntervalIntegrable (fun t ↦ f' t * j / (f t * √(f t - j ^ 2))) volume a y ∧
        ∫ t in a..y, f' t * j / (f t * √(f t - j ^ 2)) = 0 := fun y hy hfy ↦ by
    have heq := eqOn_mul_div_mul_sqrt_sub_sq_zero hf hderiv hpos hy hfy
    refine ⟨(intervalIntegrable_congr (heq.mono Ioc_subset_Icc_self)).2 intervalIntegrable_const,
      ?_⟩
    rw [intervalIntegral.integral_congr heq]
    simp
  rcases le_or_gt (f x) (j ^ 2) with hle | hlt
  · rw [Real.sqrt_eq_zero'.2 (sub_nonpos.2 hle), zero_div, arctan_zero, mul_zero]
    exact hzero x hx hle
  -- `f` crosses `j²` at some `z ∈ (a, x)`; the kernel vanishes on `[a, z]`.
  obtain ⟨z, hz, hfz⟩ := intermediate_value_Ioo hx.1 (hf.mono (Icc_subset_Icc_right hx.2))
    ⟨by rw [hfa]; positivity, hlt⟩
  have hzab : z ∈ Icc a b := ⟨hz.1.le, hz.2.le.trans hx.2⟩
  obtain ⟨hint₁, hval₁⟩ := hzero z hzab hfz.le
  have hmono := strictMonoOn_of_hasDerivAt_pos hf hderiv hpos
  have hIoo : ∀ t ∈ Ioo z x, t ∈ Ioo a b := fun t ht ↦ ⟨hz.1.trans ht.1, ht.2.trans_le hx.2⟩
  have hcont : ContinuousOn (fun t ↦ 2 * arctan (√(f t - j ^ 2) / j)) (Icc z x) :=
    continuousOn_const.mul (continuous_arctan.comp_continuousOn
      (((hf.mono (Icc_subset_Icc hzab.1 hx.2)).sub continuousOn_const).sqrt.div_const j))
  have hd : ∀ t ∈ Ioo z x, HasDerivAt (fun t ↦ 2 * arctan (√(f t - j ^ 2) / j))
      (f' t * j / (f t * √(f t - j ^ 2))) t := fun t ht ↦ by
    refine hasDerivAt_two_mul_arctan_sqrt_sub_sq_div hj ?_ (hderiv t (hIoo t ht))
    rw [← hfz]
    exact hmono hzab (Ioo_subset_Icc_self (hIoo t ht)) ht.1
  have hnn : ∀ t ∈ Ioo z x, 0 ≤ f' t * j / (f t * √(f t - j ^ 2)) := fun t ht ↦
    mul_div_mul_sqrt_sub_sq_nonneg hf hfa hderiv hpos hj (hIoo t ht)
  have hint₂ : IntervalIntegrable (fun t ↦ f' t * j / (f t * √(f t - j ^ 2))) volume z x := by
    refine intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (g := fun t ↦ 2 * arctan (√(f t - j ^ 2) / j)) ?_ ?_ ?_
    · rwa [uIcc_of_le hz.2.le]
    · rwa [min_eq_left hz.2.le, max_eq_right hz.2.le]
    · rwa [min_eq_left hz.2.le, max_eq_right hz.2.le]
  refine ⟨hint₁.trans hint₂, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂, hval₁, zero_add,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg hz.2.le hcont hd hnn, hfz,
    sub_self, Real.sqrt_zero, zero_div, arctan_zero, mul_zero, sub_zero]

/-- The kernel `f' j / (f √(f - j²))` is integrable on `[a, x]` for every `x ∈ [a, b]`, although
it is in general unbounded where `f = j²`. -/
theorem intervalIntegrable_mul_div_mul_sqrt_sub_sq {j x : ℝ} (hj : 0 < j) (hx : x ∈ Icc a b) :
    IntervalIntegrable (fun t ↦ f' t * j / (f t * √(f t - j ^ 2))) volume a x :=
  (intervalIntegrable_and_integral_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hx).1

/-- If `f` is continuous on `[a, b]`, vanishes at `a` and has positive derivative `f'` on
`(a, b)`, then for `j > 0` and `x ∈ [a, b]`,
`∫_a^x f'(t) j / (f(t) √(f(t) - j²)) dt = 2 arctan (√(f(x) - j²) / j)`. -/
theorem integral_mul_div_mul_sqrt_sub_sq {j x : ℝ} (hj : 0 < j) (hx : x ∈ Icc a b) :
    ∫ t in a..x, f' t * j / (f t * √(f t - j ^ 2)) = 2 * arctan (√(f x - j ^ 2) / j) :=
  (intervalIntegrable_and_integral_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hx).2

/-- Against a weight bounded by `η` on `[c, d] ⊆ [a, b]`, the integral of the kernel over `[c, d]`
is at most `η` times the increment `2 arctan (√(f d - j²) / j) - 2 arctan (√(f c - j²) / j)` of its
primitive. -/
private theorem norm_integral_mul_mul_div_mul_sqrt_sub_sq_le {j c d η : ℝ} {g : ℝ → ℝ}
    (hj : 0 < j) (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (hcd : c ≤ d)
    (hg : ∀ x ∈ Icc c d, |g x| ≤ η) :
    ‖∫ x in c..d, g x * (f' x * j / (f x * √(f x - j ^ 2)))‖ ≤
      η * (2 * arctan (√(f d - j ^ 2) / j) - 2 * arctan (√(f c - j ^ 2) / j)) := by
  have hint_c := intervalIntegrable_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hc
  have hint_d := intervalIntegrable_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hd
  rw [← integral_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hd,
    ← integral_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hc,
    intervalIntegral.integral_interval_sub_left hint_d hint_c,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le hcd ?_
    ((hint_c.symm.trans hint_d).const_mul _)
  -- The kernel is nonnegative on `(a, b)`, so off the null set `{b}`.
  have hb : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [hb] with t htb ht
  have hk := mul_div_mul_sqrt_sub_sq_nonneg hf hfa hderiv hpos hj
    ⟨hc.1.trans_lt ht.1, lt_of_le_of_ne (ht.2.trans hd.2) htb⟩
  rw [norm_mul, Real.norm_of_nonneg hk]
  exact mul_le_mul_of_nonneg_right (hg t (Ioc_subset_Icc_self ht)) hk

/-- **Concentration of the kernel at `a`.** If `f` is continuous on `[a, b]`, vanishes at `a` and
has positive derivative `f'` on `(a, b)`, then for every `ψ` continuous on `[a, b]`,
`∫_a^b ψ(x) f'(x) j / (f(x) √(f(x) - j²)) dx → π ψ(a)` as `j → 0⁺`. -/
theorem tendsto_integral_mul_mul_div_mul_sqrt_sub_sq (hab : a < b) {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Icc a b)) :
    Tendsto (fun j ↦ ∫ x in a..b, ψ x * (f' x * j / (f x * √(f x - j ^ 2))))
      (𝓝[>] 0) (𝓝 (π * ψ a)) := by
  set k : ℝ → ℝ → ℝ := fun j x ↦ f' x * j / (f x * √(f x - j ^ 2)) with hk
  set G : ℝ → ℝ → ℝ := fun j x ↦ 2 * arctan (√(f x - j ^ 2) / j) with hG
  have hmono := strictMonoOn_of_hasDerivAt_pos hf hderiv hpos
  have hlim : ∀ x ∈ Ioc a b, Tendsto (fun j ↦ G j x) (𝓝[>] 0) (𝓝 π) := fun x hx ↦
    tendsto_two_mul_arctan_sqrt_sub_sq_div (by
      rw [← hfa]; exact hmono ⟨le_rfl, hab.le⟩ (Ioc_subset_Icc_self hx) hx.1)
  have haIcc : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hbIcc : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hint : ∀ j, 0 < j → ∀ x ∈ Icc a b, IntervalIntegrable (k j) volume a x :=
    fun j hj x hx ↦ intervalIntegrable_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hx
  have hψsub : ContinuousOn (fun x ↦ ψ x - ψ a) (Icc a b) := hψ.sub continuousOn_const
  -- The error term `∫ (ψ - ψ a) k_j` tends to `0`: split `[a, b]` at a point `c` close to `a`.
  have herr : Tendsto (fun j ↦ ∫ x in a..b, (ψ x - ψ a) * k j x) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hψsub
    obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousWithinAt_iff.1 (hψ a haIcc) (ε / (4 * π))
      (by positivity)
    set c := min b (a + δ / 2) with hc
    have hac : a < c := lt_min hab (by linarith)
    have hcIcc : c ∈ Icc a b := ⟨hac.le, min_le_left _ _⟩
    have htail : Tendsto (fun j ↦ M * (G j b - G j c)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((hlim b ⟨hab, le_rfl⟩).sub (hlim c ⟨hac, hcIcc.2⟩)).const_mul M
    filter_upwards [htail.eventually (gt_mem_nhds (half_pos hε)), self_mem_nhdsWithin]
      with j hjM hj
    rw [Set.mem_Ioi] at hj
    have hint_ac := hint j hj c hcIcc
    have hcont_ac : ContinuousOn (fun x ↦ ψ x - ψ a) (uIcc a c) := by
      rw [uIcc_of_le hac.le]; exact hψsub.mono (Icc_subset_Icc_right hcIcc.2)
    have hcont_cb : ContinuousOn (fun x ↦ ψ x - ψ a) (uIcc c b) := by
      rw [uIcc_of_le hcIcc.2]; exact hψsub.mono (Icc_subset_Icc_left hac.le)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint_ac.continuousOn_mul hcont_ac)
      ((hint_ac.symm.trans (hint j hj b hbIcc)).continuousOn_mul hcont_cb), Real.dist_eq,
      sub_zero]
    -- Near `a`, `|ψ - ψ a| ≤ ε / (4π)`, and `∫_a^c k_j = G j c ≤ π`.
    have h₁ := norm_integral_mul_mul_div_mul_sqrt_sub_sq_le hf hfa hderiv hpos
      (g := fun x ↦ ψ x - ψ a) (η := ε / (4 * π)) hj haIcc hcIcc hac.le fun x hx ↦ by
        rw [← Real.dist_eq]
        refine (hδψ ⟨hx.1, hx.2.trans hcIcc.2⟩ ?_).le
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hx.1)]
        linarith [hx.2.trans (min_le_right b (a + δ / 2))]
    -- Away from `a`, `|ψ - ψ a| ≤ M`, and `∫_c^b k_j = G j b - G j c → 0`.
    have h₂ := norm_integral_mul_mul_div_mul_sqrt_sub_sq_le hf hfa hderiv hpos
      (g := fun x ↦ ψ x - ψ a) (η := M) hj hcIcc hbIcc hcIcc.2 fun x hx ↦ by
        simpa using hM x ⟨hac.le.trans hx.1, hx.2⟩
    have hGa : 2 * arctan (√(f a - j ^ 2) / j) = 0 := by
      simp [hfa, Real.sqrt_eq_zero', sq_nonneg]
    rw [hGa, sub_zero, Real.norm_eq_abs] at h₁
    rw [Real.norm_eq_abs] at h₂
    have h₃ : ε / (4 * π) * (2 * arctan (√(f c - j ^ 2) / j)) ≤ ε / 4 := by
      calc ε / (4 * π) * (2 * arctan (√(f c - j ^ 2) / j)) ≤ ε / (4 * π) * π := by
            gcongr
            linarith [arctan_lt_pi_div_two (√(f c - j ^ 2) / j)]
        _ = ε / 4 := by field_simp
    simp only [hk, hG] at hjM ⊢
    exact (abs_add_le _ _).trans_lt (by linarith)
  -- The main term is `ψ a ∫_a^b k_j = ψ a G j b → π ψ a`.
  have hmain : Tendsto (fun j ↦ ψ a * G j b + ∫ x in a..b, (ψ x - ψ a) * k j x) (𝓝[>] 0)
      (𝓝 (π * ψ a)) := by
    simpa [mul_comm] using ((hlim b ⟨hab, le_rfl⟩).const_mul (ψ a)).add herr
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with j hj
  rw [Set.mem_Ioi] at hj
  have hintb := hint j hj b hbIcc
  have hcont : ContinuousOn (fun x ↦ ψ x - ψ a) (uIcc a b) := by rwa [uIcc_of_le hab.le]
  simp only [hk, hG]
  rw [← integral_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hbIcc,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hintb.const_mul _) (hintb.continuousOn_mul hcont)]
  exact intervalIntegral.integral_congr fun x _ ↦ by simp only [hk]; ring

end Kernel

end TauCeti
