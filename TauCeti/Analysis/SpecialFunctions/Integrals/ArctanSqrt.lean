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

The same holds for a family: if `f_i`, `ψ_i` and `j_i` depend on a parameter `i` running along a
filter, with `j_i → 0⁺`, `f_i` bounded below at each `x ∈ (a, b]`, the `ψ_i` uniformly bounded and
`ψ_i(x) → L` as `i` runs along the filter and `x → a⁺` jointly, then `∫_a^b ψ_i k_{j_i} → π L`
(`TauCeti.tendsto_integral_mul_mul_div_mul_sqrt_sub_sq_of_tendsto`). Without any limit, a weight
bounded by `η` on `[a, x]` gives `|∫_a^x ψ k_j| ≤ η π`
(`TauCeti.abs_integral_mul_mul_div_mul_sqrt_sub_sq_le`).

This is the local computation behind quadratures of the form `∫ j dz / (g(z) √(f(z) - j²))` near a
common simple zero `a` of `f` and `g`: writing `1 / g = ψ f' / f` with `ψ = f / (g f')` continuous
at `a`, the contribution of a neighbourhood of `a` tends to `π ψ(a)` as `j → 0⁺`. For the
spherical pendulum this computes the limits of the rotation angle at the poles of the sphere,
jointly in the energy and the angular momentum.

## Implementation notes

Mathlib's `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto` asks the kernels to tend to
`0` uniformly away from `a`, which would need a bound on `f'` up to `b`. The estimate here uses only
the explicit primitive, so `f'` is only required to be positive on `(a, b)`.

## Main declarations

* `TauCeti.intervalIntegrable_mul_div_mul_sqrt_sub_sq`,
  `TauCeti.integral_mul_div_mul_sqrt_sub_sq`: the integrability of `k_j` on `[a, x]` and its
  integral.
* `TauCeti.abs_integral_mul_mul_div_mul_sqrt_sub_sq_le`: `|∫_a^x ψ k_j| ≤ η π` for `|ψ| ≤ η`.
* `TauCeti.tendsto_integral_mul_mul_div_mul_sqrt_sub_sq_of_tendsto`: `∫_a^b ψ_i k_{j_i} → π L` for
  a family.
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
  have hsq : √(f t - j ^ 2) ^ 2 = f t - j ^ 2 := Real.sq_sqrt hpos.le
  have hf : 0 < f t := (sq_nonneg j).trans_lt ht
  convert (((hd.sub_const (j ^ 2)).sqrt hpos.ne').div_const j).arctan.const_mul 2 using 1
  field_simp
  rw [hsq]
  ring

/-- If `g i` is eventually at least `m > 0` and `j i → 0⁺`, then
`2 arctan (√(g i - (j i)²) / j i) → π`. -/
private theorem tendsto_two_mul_arctan_sqrt_sub_sq_div {ι : Type*} {l : Filter ι} {g j : ι → ℝ}
    {m : ℝ} (hm : 0 < m) (hg : ∀ᶠ i in l, m ≤ g i) (hj : Tendsto j l (𝓝[>] 0)) :
    Tendsto (fun i ↦ 2 * arctan (√(g i - j i ^ 2) / j i)) l (𝓝 π) := by
  have hsq : ∀ᶠ i in l, j i ^ 2 < m / 2 := by
    have : Tendsto (fun i ↦ j i ^ 2) l (𝓝 0) := by
      simpa using (tendsto_nhds_of_tendsto_nhdsWithin hj).pow 2
    exact this.eventually (gt_mem_nhds (half_pos hm))
  have hinv : Tendsto (fun i ↦ √(m / 2) * (j i)⁻¹) l atTop :=
    (tendsto_inv_nhdsGT_zero.comp hj).const_mul_atTop (Real.sqrt_pos.2 (half_pos hm))
  have hatTop : Tendsto (fun i ↦ √(g i - j i ^ 2) / j i) l atTop := by
    refine tendsto_atTop_mono' l ?_ hinv
    filter_upwards [hg, hsq, hj self_mem_nhdsWithin] with i hgi hsqi hji
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith))
      (inv_nonneg.2 (le_of_lt hji))
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
    exact (strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b) hf
        (fun x hx ↦ (hderiv x (by rwa [interior_Icc] at hx)).hasDerivWithinAt)
        fun x hx ↦ hpos x (by rwa [interior_Icc] at hx))
      ⟨le_rfl, (ht.1.trans ht.2).le⟩ (Ioo_subset_Icc_self ht) ht.1
  exact div_nonneg (mul_nonneg (hpos t ht).le hj.le) (mul_nonneg hft.le (Real.sqrt_nonneg _))

omit hfa in
/-- The kernel vanishes identically on `[a, y]` when `f y ≤ j²`. -/
private theorem eqOn_mul_div_mul_sqrt_sub_sq_zero {j y : ℝ} (hy : y ∈ Icc a b)
    (hfy : f y ≤ j ^ 2) :
    EqOn (fun t ↦ f' t * j / (f t * √(f t - j ^ 2))) 0 (uIcc a y) := by
  intro t ht
  rw [uIcc_of_le hy.1] at ht
  have hmono := (strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b) hf
      (fun x hx ↦ (hderiv x (by rwa [interior_Icc] at hx)).hasDerivWithinAt)
      fun x hx ↦ hpos x (by rwa [interior_Icc] at hx)).monotoneOn
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
  have hmono := strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b) hf
      (fun x hx ↦ (hderiv x (by rwa [interior_Icc] at hx)).hasDerivWithinAt)
      fun x hx ↦ hpos x (by rwa [interior_Icc] at hx)
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

/-- Against a weight bounded by `η` on `[a, x]`, the integral of the kernel over `[a, x]` is at most
`η π` in absolute value: the kernel is nonnegative and its integral over `[a, x]` is
`2 arctan (√(f x - j²) / j) < π`. -/
theorem abs_integral_mul_mul_div_mul_sqrt_sub_sq_le {j x η : ℝ} {g : ℝ → ℝ} (hj : 0 < j)
    (hx : x ∈ Icc a b) (hg : ∀ y ∈ Icc a x, |g y| ≤ η) :
    |∫ y in a..x, g y * (f' y * j / (f y * √(f y - j ^ 2)))| ≤ η * π := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hg a ⟨le_rfl, hx.1⟩)
  have h := norm_integral_mul_mul_div_mul_sqrt_sub_sq_le hf hfa hderiv hpos hj
    ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1 hg
  have hGa : 2 * arctan (√(f a - j ^ 2) / j) = 0 := by
    simp [hfa, Real.sqrt_eq_zero', sq_nonneg]
  rw [hGa, sub_zero, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (by linarith [arctan_lt_pi_div_two (√(f x - j ^ 2) / j)]) hη)

/-- Split at `c ∈ [a, b]`: against a weight within `η` of `L` on `[a, c]` and within `η'` of `L`
on `[c, b]`, the integral of `(ψ - L) k_j` over `[a, b]` is at most
`η π + η' (2 arctan (√(f b - j²) / j) - 2 arctan (√(f c - j²) / j))` in absolute value. -/
private theorem abs_integral_sub_mul_mul_div_mul_sqrt_sub_sq_le {j c η η' L : ℝ} {ψ : ℝ → ℝ}
    (hj : 0 < j) (hc : c ∈ Icc a b) (hψ : ContinuousOn ψ (Icc a b))
    (hη : ∀ x ∈ Icc a c, |ψ x - L| ≤ η) (hη' : ∀ x ∈ Icc c b, |ψ x - L| ≤ η') :
    |∫ x in a..b, (ψ x - L) * (f' x * j / (f x * √(f x - j ^ 2)))| ≤
      η * π + η' * (2 * arctan (√(f b - j ^ 2) / j) - 2 * arctan (√(f c - j ^ 2) / j)) := by
  have hbIcc : b ∈ Icc a b := ⟨hc.1.trans hc.2, le_rfl⟩
  have hψsub : ContinuousOn (fun x ↦ ψ x - L) (Icc a b) := hψ.sub continuousOn_const
  have hint_ac := intervalIntegrable_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hc
  have hint_cb := hint_ac.symm.trans
    (intervalIntegrable_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hbIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint_ac.continuousOn_mul (by
      rw [uIcc_of_le hc.1]; exact hψsub.mono (Icc_subset_Icc_right hc.2)))
    (hint_cb.continuousOn_mul (by
      rw [uIcc_of_le hc.2]; exact hψsub.mono (Icc_subset_Icc_left hc.1)))]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_integral_mul_mul_div_mul_sqrt_sub_sq_le hf hfa hderiv hpos hj hc hη
  · simpa only [Real.norm_eq_abs] using
      norm_integral_mul_mul_div_mul_sqrt_sub_sq_le hf hfa hderiv hpos hj hc hbIcc hc.2 hη'

/-- The integral of `ψ k_j` over `[a, b]` is `L ∫_a^b k_j = L · 2 arctan (√(f b - j²) / j)` plus
the integral of `(ψ - L) k_j`. -/
private theorem integral_mul_mul_div_mul_sqrt_sub_sq_eq {j L : ℝ} {ψ : ℝ → ℝ} (hab : a ≤ b)
    (hj : 0 < j) (hψ : ContinuousOn ψ (Icc a b)) :
    ∫ x in a..b, ψ x * (f' x * j / (f x * √(f x - j ^ 2))) =
      L * (2 * arctan (√(f b - j ^ 2) / j)) +
        ∫ x in a..b, (ψ x - L) * (f' x * j / (f x * √(f x - j ^ 2))) := by
  have hbIcc : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hintb := intervalIntegrable_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hbIcc
  rw [← integral_mul_div_mul_sqrt_sub_sq hf hfa hderiv hpos hj hbIcc,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hintb.const_mul _)
      (hintb.continuousOn_mul (by rw [uIcc_of_le hab]; exact hψ.sub continuousOn_const))]
  exact intervalIntegral.integral_congr fun x _ ↦ by ring

end Kernel

/-- **Concentration of the kernel at `a`, for a family.** For `i` along a filter `l`, let `f i`
eventually be continuous on `[a, b]`, vanish at `a` and have positive derivative `f' i` on
`(a, b)`, and let `f i x` be eventually bounded below by a positive constant at each
`x ∈ (a, b]`. Let `j i → 0⁺`, and let the weights `ψ i` be eventually continuous and uniformly
bounded on `[a, b]`, and tend to `L` as `i` runs along `l` and `x → a⁺` jointly. Then
`∫_a^b ψ i x · f' i x j i / (f i x √(f i x - (j i)²)) dx → π L`. -/
theorem tendsto_integral_mul_mul_div_mul_sqrt_sub_sq_of_tendsto {ι : Type*} {l : Filter ι}
    {f f' ψ : ι → ℝ → ℝ} {j : ι → ℝ} {L : ℝ} (hab : a < b)
    (hf : ∀ᶠ i in l, ContinuousOn (f i) (Icc a b)) (hfa : ∀ᶠ i in l, f i a = 0)
    (hderiv : ∀ᶠ i in l, ∀ x ∈ Ioo a b, HasDerivAt (f i) (f' i x) x)
    (hpos : ∀ᶠ i in l, ∀ x ∈ Ioo a b, 0 < f' i x)
    (hfx : ∀ x ∈ Ioc a b, ∃ m > 0, ∀ᶠ i in l, m ≤ f i x) (hj : Tendsto j l (𝓝[>] 0))
    (hψ : ∀ᶠ i in l, ContinuousOn (ψ i) (Icc a b))
    (hψM : ∃ M, ∀ᶠ i in l, ∀ x ∈ Icc a b, |ψ i x| ≤ M)
    (hψa : Tendsto (Function.uncurry ψ) (l ×ˢ 𝓝[≥] a) (𝓝 L)) :
    Tendsto (fun i ↦ ∫ x in a..b, ψ i x * (f' i x * j i / (f i x * √(f i x - j i ^ 2)))) l
      (𝓝 (π * L)) := by
  set k : ι → ℝ → ℝ := fun i x ↦ f' i x * j i / (f i x * √(f i x - j i ^ 2))
  set G : ι → ℝ → ℝ := fun i x ↦ 2 * arctan (√(f i x - j i ^ 2) / j i) with hG
  have hlim : ∀ x ∈ Ioc a b, Tendsto (fun i ↦ G i x) l (𝓝 π) := fun x hx ↦ by
    obtain ⟨m, hm, hmx⟩ := hfx x hx
    exact tendsto_two_mul_arctan_sqrt_sub_sq_div hm hmx hj
  have hjpos : ∀ᶠ i in l, 0 < j i := hj self_mem_nhdsWithin
  obtain ⟨M, hM⟩ := hψM
  -- The error term `∫ (ψ i - L) k_i` tends to `0`: split `[a, b]` at a point `c` close to `a`.
  have herr : Tendsto (fun i ↦ ∫ x in a..b, (ψ i x - L) * k i x) l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨pa, hpa, pb, hpb, hp⟩ :=
      eventually_prod_iff.1 (Metric.tendsto_nhds.1 hψa (ε / (4 * π)) (by positivity))
    obtain ⟨u, hu, hus⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hpb
    rw [mem_Ioi] at hu
    set c := min b ((a + u) / 2)
    have hac : a < c := lt_min hab (by linarith)
    have hcu : c < u := (min_le_right _ _).trans_lt (by linarith)
    have hcIcc : c ∈ Icc a b := ⟨hac.le, min_le_left _ _⟩
    -- Away from `a`, `|ψ i - L| ≤ M + |L|`, and `∫_c^b k_i = G i b - G i c → 0`.
    have htail : Tendsto (fun i ↦ (M + |L|) * (G i b - G i c)) l (𝓝 0) := by
      simpa using ((hlim b ⟨hab, le_rfl⟩).sub (hlim c ⟨hac, hcIcc.2⟩)).const_mul (M + |L|)
    filter_upwards [htail.eventually (gt_mem_nhds (half_pos hε)), hpa, hM, hf, hfa, hderiv, hpos,
      hψ, hjpos] with i hiM hia hiψ hfi hfai hderivi hposi hψi hji
    rw [Real.dist_eq, sub_zero]
    -- Near `a`, `|ψ i - L| ≤ ε / (4π)`.
    refine (abs_integral_sub_mul_mul_div_mul_sqrt_sub_sq_le hfi hfai hderivi hposi hji hcIcc hψi
      (η := ε / (4 * π)) (η' := M + |L|) (fun x hx ↦ ?_) fun x hx ↦ ?_).trans_lt ?_
    · have := hp hia (hus ⟨hx.1, hx.2.trans_lt hcu⟩)
      rw [Function.uncurry_apply_pair, Real.dist_eq] at this
      exact this.le
    · exact (abs_sub _ _).trans (by gcongr; exact hiψ x ⟨hac.le.trans hx.1, hx.2⟩)
    · have : ε / (4 * π) * π = ε / 4 := by field_simp
      simp only [hG] at hiM
      linarith
  -- The main term is `L ∫_a^b k_i = L G i b → π L`.
  have hmain : Tendsto (fun i ↦ L * G i b + ∫ x in a..b, (ψ i x - L) * k i x) l
      (𝓝 (π * L)) := by
    simpa [mul_comm] using ((hlim b ⟨hab, le_rfl⟩).const_mul L).add herr
  refine hmain.congr' ?_
  filter_upwards [hf, hfa, hderiv, hpos, hψ, hjpos] with i hfi hfai hderivi hposi hψi hji
  exact (integral_mul_mul_div_mul_sqrt_sub_sq_eq hfi hfai hderivi hposi hab.le hji hψi).symm

/-- **Concentration of the kernel at `a`.** If `f` is continuous on `[a, b]`, vanishes at `a` and
has positive derivative `f'` on `(a, b)`, then for every `ψ` continuous on `[a, b]`,
`∫_a^b ψ(x) f'(x) j / (f(x) √(f(x) - j²)) dx → π ψ(a)` as `j → 0⁺`. -/
theorem tendsto_integral_mul_mul_div_mul_sqrt_sub_sq {f f' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfa : f a = 0)
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Ioo a b, 0 < f' x)
    (hab : a < b) {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Icc a b)) :
    Tendsto (fun j ↦ ∫ x in a..b, ψ x * (f' x * j / (f x * √(f x - j ^ 2))))
      (𝓝[>] 0) (𝓝 (π * ψ a)) := by
  have hmono := strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b) hf
    (fun x hx ↦ (hderiv x (by rwa [interior_Icc] at hx)).hasDerivWithinAt)
    fun x hx ↦ hpos x (by rwa [interior_Icc] at hx)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ
  refine tendsto_integral_mul_mul_div_mul_sqrt_sub_sq_of_tendsto (f := fun _ ↦ f)
    (f' := fun _ ↦ f') (ψ := fun _ ↦ ψ) (j := id) hab (.of_forall fun _ ↦ hf)
    (.of_forall fun _ ↦ hfa) (.of_forall fun _ ↦ hderiv) (.of_forall fun _ ↦ hpos)
    (fun x hx ↦ ⟨f x, by rw [← hfa]; exact hmono ⟨le_rfl, hab.le⟩ (Ioc_subset_Icc_self hx) hx.1,
      .of_forall fun _ ↦ le_rfl⟩) tendsto_id (.of_forall fun _ ↦ hψ)
    ⟨M, .of_forall fun _ x hx ↦ hM x hx⟩ ?_
  rw [← nhdsWithin_Icc_eq_nhdsGE hab]
  exact (hψ a ⟨le_rfl, hab.le⟩).tendsto.comp tendsto_snd

end TauCeti
