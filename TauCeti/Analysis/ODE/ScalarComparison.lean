/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

/-!
# Scalar differential inequalities on closed intervals

An integrating factor compares endpoint values from an inequality in the interior. The scalar
function can have either sign or vanish, and its derivative need not extend to the endpoints.
The variable coefficient need only be continuous in the interior and interval integrable;
its values at the endpoints need not agree with its one-sided limits.

The weighted comparison applies to `f' + f / (t - T) + q * f ≥ 0`. It includes `T = a`,
without requiring the singular coefficient at the initial endpoint. These are the scalar
estimates consumed by the finite-start and ancient integrated trace Harnack arguments.
The zero-energy theorem is a separate consequence requiring no sign condition on its rate.

## Main results

* `TauCeti.mul_exp_neg_integral_le_of_deriv_add_mul_nonneg`: lower endpoint comparison.
* `TauCeti.le_mul_exp_integral_of_deriv_le_mul`: upper endpoint comparison.
* `TauCeti.mul_sub_mul_exp_neg_integral_le_of_deriv_add_div_add_mul_nonneg`: time-weighted bound.
* `TauCeti.eq_zero_on_interval_of_deriv_le_mul`: uniqueness for a nonnegative scalar energy.

Morgan–Tian, *Ricci Flow and the Poincaré Conjecture* (2007), Theorem 4.40, supplies the
geometric context. These scalar estimates do not establish the geometric Harnack inequality.

Formalization references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public section

open Set MeasureTheory
open scoped intervalIntegral

namespace TauCeti

/-- An integrating factor gives a lower bound even when `f` vanishes or is negative. -/
theorem mul_exp_neg_integral_le_of_deriv_add_mul_nonneg
    {a b : ℝ} (hab : a ≤ b) {f f' q : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hq : ContinuousOn q (Ioo a b))
    (hqInt : IntervalIntegrable q volume a b)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hineq : ∀ t ∈ Ioo a b, 0 ≤ f' t + q t * f t) :
    f a * Real.exp (-(∫ t in a..b, q t)) ≤ f b := by
  let Q : ℝ → ℝ := fun t ↦ ∫ s in a..t, q s
  have hQ : ContinuousOn Q (Icc a b) := by
    simpa only [Q, uIcc_of_le hab] using
      (intervalIntegral.continuousOn_primitive_interval' hqInt left_mem_uIcc)
  have hQ' (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt Q (q t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hqInt.mono_set (uIcc_subset_uIcc_left (by
        simpa only [uIcc_of_le hab] using Ioo_subset_Icc_self ht))
    · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hq t ht
    · exact hq.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hprod (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun s ↦ f s * Real.exp (Q s))
        ((f' t + q t * f t) * Real.exp (Q t)) t := by
    convert! (hf' t ht).mul (hQ' t ht).exp using 1
    ring
  have hmono : MonotoneOn (fun t ↦ f t * Real.exp (Q t)) (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (hf.mul (Real.continuous_exp.comp_continuousOn hQ))
    · intro t ht
      exact (hprod t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      exact mul_nonneg (hineq t (by simpa only [interior_Icc] using ht))
        (Real.exp_pos _).le
  -- Divide by the strictly positive factor, without a sign condition on `f`.
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  simpa only [Q, intervalIntegral.integral_same, Real.exp_zero, mul_one] using
    hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

/-- The upper integrating-factor comparison for a signed scalar function. The coefficient
is continuous only in the interior and integrable on the whole interval. -/
theorem le_mul_exp_integral_of_deriv_le_mul
    {a b : ℝ} (hab : a ≤ b) {f f' q : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hq : ContinuousOn q (Ioo a b))
    (hqInt : IntervalIntegrable q volume a b)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hineq : ∀ t ∈ Ioo a b, f' t ≤ q t * f t) :
    f b ≤ f a * Real.exp (∫ t in a..b, q t) := by
  have h := mul_exp_neg_integral_le_of_deriv_add_mul_nonneg hab
    (f := fun t ↦ -f t) (f' := fun t ↦ -f' t) (q := fun t ↦ -q t)
    hf.neg hq.neg hqInt.neg (fun t ht ↦ (hf' t ht).neg)
    (fun t ht ↦ by simpa only [neg_mul_neg, neg_add_eq_sub] using sub_nonneg.mpr (hineq t ht))
  simpa only [intervalIntegral.integral_neg, neg_neg, neg_mul, neg_le_neg_iff] using h

/-- The finite-start comparison retains the elapsed-time factors at both endpoints. -/
theorem mul_sub_mul_exp_neg_integral_le_of_deriv_add_div_add_mul_nonneg
    {T a b : ℝ} (hTa : T ≤ a) (hab : a ≤ b) {f f' q : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hq : ContinuousOn q (Ioo a b))
    (hqInt : IntervalIntegrable q volume a b)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hineq : ∀ t ∈ Ioo a b, 0 ≤ f' t + f t / (t - T) + q t * f t) :
    f a * (a - T) * Real.exp (-(∫ t in a..b, q t)) ≤ f b * (b - T) := by
  apply mul_exp_neg_integral_le_of_deriv_add_mul_nonneg hab
    (hf.mul (continuousOn_id.sub continuousOn_const)) hq hqInt
    (f' := fun t ↦ f' t * (t - T) + f t)
  · intro t ht
    convert! (hf' t ht).mul ((hasDerivAt_id t).sub_const T) using 1
    simp only [id_eq, mul_one]
  · intro t ht
    have htT : 0 < t - T := sub_pos.mpr (hTa.trans_lt ht.1)
    simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, add_mul, div_mul_cancel₀ _ htT.ne',
      mul_assoc] using mul_nonneg (hineq t ht) htT.le

/-- A nonnegative continuous energy, initially zero and satisfying `E′ ≤ C E`
at interior times, is zero throughout the closed interval. Degenerate and empty
intervals are allowed, and `C` may have either sign. -/
theorem eq_zero_on_interval_of_deriv_le_mul
    {a b C : ℝ} {E : ℝ → ℝ}
    (hE : ContinuousOn E (Icc a b))
    (hEd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ E t)
    (hE0 : E a = 0)
    (hEn : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hE' : ∀ t ∈ Ioo a b, deriv E t ≤ C * E t) :
    EqOn E (fun _ ↦ 0) (Icc a b) := by
  intro t ht
  have hsub : Ioo a t ⊆ Ioo a b := fun s hs ↦ ⟨hs.1, hs.2.trans_le ht.2⟩
  have hle := le_mul_exp_integral_of_deriv_le_mul ht.1
    (hE.mono (Icc_subset_Icc le_rfl ht.2)) continuousOn_const intervalIntegrable_const
    (fun s hs ↦ (hEd s (hsub hs)).hasDerivAt) (fun s hs ↦ hE' s (hsub hs))
  exact le_antisymm (by simpa only [hE0, zero_mul] using hle) (hEn t ht)

end TauCeti
