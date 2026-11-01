/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Power growth from a differential inequality

The inequality `α f(t) ≤ t f'(t)` makes `f(t) / t^α` nondecreasing on positive
intervals. It gives power bounds at smaller radii from data at a larger radius,
including when `f` vanishes. No division by `f` or positivity assumption on `f` is needed.

The inequality `f ^ (1 - β) ≤ K f'`, with `0 < β`, makes `f ^ β` grow at least linearly, with slope
`β / K`. For a monotone `f` it only needs to hold at almost every point, with `f'` the derivative
that a monotone function has almost everywhere
(`TauCeti.mul_sub_le_mul_rpow_sub_rpow_of_rpow_le_mul_deriv`). This gives lower power bounds
`f(t) ≥ (β t / K) ^ (1/β)` for functions vanishing at zero, such as the measure of a set in
concentric balls, which is monotone in the radius but need not be differentiable.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- An Euler differential inequality makes the power-normalized function nondecreasing
on any convex set of positive real numbers. Only continuity is required at boundary points;
the derivative and differential inequality are needed only on the interior. -/
theorem monotoneOn_div_rpow_of_mul_le_mul_deriv {f f' : ℝ → ℝ} {s : Set ℝ} {α : ℝ}
    (hs : Convex ℝ s) (hpos : ∀ t ∈ s, 0 < t)
    (hcont : ContinuousOn f s)
    (hf : ∀ t ∈ interior s, HasDerivAt f (f' t) t)
    (hle : ∀ t ∈ interior s, α * f t ≤ t * f' t) :
    MonotoneOn (fun t ↦ f t / t ^ α) s := by
  have hd (t : ℝ) (ht : t ∈ interior s) :=
    (hf t ht).div (Real.hasDerivAt_rpow_const (Or.inl (hpos t (interior_subset ht)).ne'))
      (Real.rpow_pos_of_pos (hpos t (interior_subset ht)) α).ne'
  have hpow : ContinuousOn (fun t : ℝ ↦ t ^ α) s :=
    continuousOn_id.rpow_const (fun t ht ↦ Or.inl (hpos t ht).ne')
  apply monotoneOn_of_deriv_nonneg hs
    (hcont.div hpow
      (fun t ht ↦ (Real.rpow_pos_of_pos (hpos t ht) α).ne'))
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hd t ht).deriv]
  apply div_nonneg _ (sq_nonneg _)
  rw [Real.rpow_sub_one (hpos t (interior_subset ht)).ne']
  have h := hle t ht
  have hp := Real.rpow_pos_of_pos (hpos t (interior_subset ht)) α
  have htpos := hpos t (interior_subset ht)
  convert div_nonneg (mul_nonneg (sub_nonneg.mpr h) hp.le) htpos.le using 1
  field_simp

/-- **Power growth from an almost-everywhere differential inequality.** Let `f` be monotone on
`[a, b]`, nonnegative at `a` and positive on `(a, b)`, and let `0 < β` and `0 ≤ K`. If
`f ^ (1 - β) ≤ K f'` at almost every point of `(a, b)`, then

`β (b - a) ≤ K (f b ^ β - f a ^ β)`.

No differentiability is assumed: `f'` is `deriv f`, which is the derivative of `f` at almost every
point because `f` is monotone. -/
theorem mul_sub_le_mul_rpow_sub_rpow_of_rpow_le_mul_deriv {f : ℝ → ℝ} {a b β K : ℝ}
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) (ha : 0 ≤ f a) (hpos : ∀ t ∈ Ioo a b, 0 < f t)
    (hβ : 0 < β) (hK : 0 ≤ K) (hd : ∀ᵐ t, t ∈ Ioo a b → f t ^ (1 - β) ≤ K * deriv f t) :
    β * (b - a) ≤ K * (f b ^ β - f a ^ β) := by
  have hg : MonotoneOn (fun t => f t ^ β) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun s hs t ht hst =>
      Real.rpow_le_rpow (ha.trans (hf (left_mem_Icc.2 hab) hs hs.1)) (hf hs ht hst) hβ.le
  -- At almost every point of `(a, b)`, `f` is differentiable and `β ≤ K (f ^ β)'`.
  have hle : (fun _ => β) ≤ᵐ[volume.restrict (Icc a b)]
      fun t => K * deriv (fun t => f t ^ β) t := by
    rw [← restrict_Ioo_eq_restrict_Icc, Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hf.ae_differentiableWithinAt_of_mem, hd] with t hdiff ht hmem
    have hft := hpos t hmem
    rw [(((hdiff (Ioo_subset_Icc_self hmem)).differentiableAt
      (Icc_mem_nhds hmem.1 hmem.2)).hasDerivAt.rpow_const (Or.inl hft.ne')).deriv]
    have h1 : f t ^ (β - 1) * f t ^ (1 - β) = 1 := by
      rw [← Real.rpow_add hft, sub_add_sub_cancel', sub_self, Real.rpow_zero]
    calc β = β * f t ^ (β - 1) * f t ^ (1 - β) := by rw [mul_assoc, h1, mul_one]
      _ ≤ β * f t ^ (β - 1) * (K * deriv f t) :=
        mul_le_mul_of_nonneg_left (ht hmem) (mul_pos hβ (Real.rpow_pos_of_pos hft _)).le
      _ = K * (deriv f t * β * f t ^ (β - 1)) := by ring
  have hint := intervalIntegral.integral_mono_ae_restrict hab intervalIntegrable_const
    (hg.intervalIntegrable_deriv.const_mul K) hle
  rw [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul] at hint
  have hmem := hg.intervalIntegral_deriv_mem_uIcc
  rw [uIcc_of_le (sub_nonneg.2 (hg (by simp) (by simp) hab))] at hmem
  calc β * (b - a) = (b - a) * β := mul_comm _ _
    _ ≤ _ := hint
    _ ≤ _ := mul_le_mul_of_nonneg_left hmem.2 hK

end TauCeti

end
