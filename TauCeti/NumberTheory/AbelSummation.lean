/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.AbelSummation

/-!
# Summing an `O(t log t)` partial-sum bound against a logarithmic weight

Mathlib's `summable_mul_of_bigO_atTop'` converts a bound on the partial sums of a sequence into
the convergence of a weighted series, provided the weight is differentiable and the derivative of
the weight against the partial sums admits an integrable majorant. This file performs that
conversion once, for the weight `(t (1 + log t) ^ 3)⁻¹` and partial sums growing like `t log t`.

The weight is written with `1 + log t` rather than `log t` so that it stays positive and smooth at
`t = 1`, where Abel summation starts. Its derivative against an `O(t log t)` partial sum is
`O((t (1 + log t) ^ 2)⁻¹)`, which is integrable at infinity by comparison with Mathlib's
log-Cauchy density `integrableOn_Ioi_zero_inv_mul_one_add_log_sq`.

## Main declarations

* `TauCeti.summable_div_mul_one_add_log_cube`: if the partial sums `∑_{1 ≤ k ≤ t} u k` of a
  nonnegative sequence are `O(t log t)`, then `∑ u n / (n (1 + log n) ^ 3)` converges.
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory Set
open scoped Topology

variable {t : ℝ}

/-! ### The comparison weight -/

/-- The weight `(t (1 + log t) ^ 3)⁻¹` against which a partial-sum bound is summed. -/
private noncomputable def decayWeight (t : ℝ) : ℝ := (t * (1 + Real.log t) ^ 3)⁻¹

/-- `1 + log t` is positive to the right of `exp (-1)`, so the comparison weight is positive on a
neighbourhood of `Ici 1`. -/
private lemma one_add_log_pos (ht : Real.exp (-1) < t) : 0 < 1 + Real.log t := by
  have h := Real.log_lt_log (Real.exp_pos _) ht
  rw [Real.log_exp] at h
  linarith

private lemma exp_neg_one_lt_one : Real.exp (-1) < 1 :=
  Real.exp_lt_one_iff.2 (by norm_num)

private lemma decayWeight_pos (ht : Real.exp (-1) < t) : 0 < decayWeight t := by
  have h := one_add_log_pos ht
  have ht0 : (0 : ℝ) < t := lt_trans (Real.exp_pos _) ht
  exact inv_pos.2 (by positivity)

private lemma hasDerivAt_decayWeight (ht : Real.exp (-1) < t) :
    HasDerivAt decayWeight
      (-(((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2)) t := by
  have hlog := one_add_log_pos ht
  have ht0 : (0 : ℝ) < t := lt_trans (Real.exp_pos _) ht
  have ht0' : t ≠ 0 := ht0.ne'
  have hlog' : (1 : ℝ) + Real.log t ≠ 0 := hlog.ne'
  have h1 : HasDerivAt (fun u : ℝ ↦ 1 + Real.log u) t⁻¹ t :=
    (Real.hasDerivAt_log ht0').const_add 1
  refine ((hasDerivAt_id' (x := t)).fun_mul (h1.fun_pow 3) |>.inv
    (by positivity)).congr_deriv ?_
  push_cast
  field_simp

/-- On a neighbourhood of `Ici 1` the comparison weight is positive, so taking its norm changes
nothing. -/
private lemma norm_decayWeight_eventuallyEq (ht : 1 ≤ t) :
    (fun u : ℝ ↦ ‖decayWeight u‖) =ᶠ[𝓝 t] decayWeight := by
  have hmem : t ∈ Ioi (Real.exp (-1)) := lt_of_lt_of_le exp_neg_one_lt_one ht
  filter_upwards [isOpen_Ioi.mem_nhds hmem] with u hu
  exact Real.norm_of_nonneg (decayWeight_pos hu).le

private lemma differentiableAt_norm_decayWeight (ht : 1 ≤ t) :
    DifferentiableAt ℝ (fun u : ℝ ↦ ‖decayWeight u‖) t :=
  (norm_decayWeight_eventuallyEq ht).differentiableAt_iff.2
    (hasDerivAt_decayWeight (lt_of_lt_of_le exp_neg_one_lt_one ht)).differentiableAt

private lemma deriv_norm_decayWeight (ht : 1 ≤ t) :
    deriv (fun u : ℝ ↦ ‖decayWeight u‖) t =
      -(((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2) := by
  rw [(norm_decayWeight_eventuallyEq ht).deriv_eq]
  exact (hasDerivAt_decayWeight (lt_of_lt_of_le exp_neg_one_lt_one ht)).deriv

private lemma locallyIntegrableOn_deriv_norm_decayWeight :
    LocallyIntegrableOn (deriv fun u : ℝ ↦ ‖decayWeight u‖) (Ici 1) := by
  refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
  have hne : ∀ u ∈ Ici (1 : ℝ), u ≠ 0 := fun u hu ↦ by
    have : (1 : ℝ) ≤ u := hu
    linarith
  have hlog : ∀ u ∈ Ici (1 : ℝ), 1 + Real.log u ≠ 0 := fun u hu ↦ by
    have : (1 : ℝ) ≤ u := hu
    exact (one_add_log_pos (lt_of_lt_of_le exp_neg_one_lt_one this)).ne'
  refine ContinuousOn.congr (f := fun u : ℝ ↦
    -(((1 + Real.log u) ^ 3 + 3 * (1 + Real.log u) ^ 2) / (u * (1 + Real.log u) ^ 3) ^ 2)) ?_
    fun u hu ↦ deriv_norm_decayWeight hu
  have hcont : ContinuousOn (fun u : ℝ ↦ 1 + Real.log u) (Ici 1) :=
    continuousOn_const.add (Real.continuousOn_log.comp continuousOn_id fun u hu ↦ hne u hu)
  refine (((hcont.pow 3).add ((hcont.pow 2).const_smul (3 : ℝ))).div
    ((continuousOn_id.mul (hcont.pow 3)).pow 2) fun u hu ↦ ?_).neg.congr fun u hu ↦ by
      simp [smul_eq_mul]
  exact pow_ne_zero 2 (mul_ne_zero (hne u hu) (pow_ne_zero 3 (hlog u hu)))

/-- The majorant `(t (1 + log t) ^ 2)⁻¹` produced by Abel summation is integrable at infinity: on
`Ioi 1` it is dominated by Mathlib's log-Cauchy density `(t (1 + (log t) ^ 2))⁻¹`. -/
private lemma integrableAtFilter_inv_mul_one_add_log_sq :
    IntegrableAtFilter (fun u : ℝ ↦ (u * (1 + Real.log u) ^ 2)⁻¹) atTop := by
  refine ⟨Ioi 1, Ioi_mem_atTop 1, ?_⟩
  have hmaj : IntegrableOn (fun u : ℝ ↦ (u * (1 + Real.log u ^ 2))⁻¹) (Ioi (1 : ℝ)) :=
    ((integrableOn_Ioi_zero_inv_mul_one_add_log_sq (b := 1) one_ne_zero).congr_fun
      (fun u _ ↦ by rw [one_mul]) measurableSet_Ioi).mono_set (Ioi_subset_Ioi zero_le_one)
  refine MeasureTheory.Integrable.mono hmaj (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : (1 : ℝ) < u := hu
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu1
  have hL : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1.le
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  gcongr
  nlinarith

/-! ### The hypotheses of Abel summation -/

/-- The boundedness hypothesis of Abel summation: an `O(t log t)` partial sum times the comparison
weight is bounded, because `log t ≤ (1 + log t) ^ 3` for `t ≥ 1`. -/
private lemma decayWeight_mul_le {C S : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hS : S ≤ C * t * Real.log t) : decayWeight t * S ≤ C := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hL : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hu : (0 : ℝ) < 1 + Real.log t := by linarith
  have hkey : (t * (1 + Real.log t) ^ 3)⁻¹ * (C * t * Real.log t) =
      C * (Real.log t / (1 + Real.log t) ^ 3) := by
    field_simp
  have hratio : Real.log t / (1 + Real.log t) ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [pow_pos hu 3, pow_pos hu 2, sq_nonneg (Real.log t)]
  rw [decayWeight]
  calc (t * (1 + Real.log t) ^ 3)⁻¹ * S
      ≤ (t * (1 + Real.log t) ^ 3)⁻¹ * (C * t * Real.log t) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = C * (Real.log t / (1 + Real.log t) ^ 3) := hkey
    _ ≤ C := by nlinarith

/-- The majorant hypothesis of Abel summation: the derivative of the comparison weight times an
`O(t log t)` partial sum is `O((t (1 + log t) ^ 2)⁻¹)`, because
`log t (4 + log t) ≤ 4 (1 + log t) ^ 2`. -/
private lemma norm_deriv_decayWeight_mul_le {C S : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C) (hS0 : 0 ≤ S)
    (hS : S ≤ C * t * Real.log t) :
    ‖-(((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2) * S‖ ≤
      4 * C * ‖(t * (1 + Real.log t) ^ 2)⁻¹‖ := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hL : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hu : (0 : ℝ) < 1 + Real.log t := by linarith
  have hX : (0 : ℝ) < (1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2 := by
    have h3 := pow_pos hu 3
    have h2 := pow_pos hu 2
    linarith
  have hY : (0 : ℝ) < (t * (1 + Real.log t) ^ 3) ^ 2 :=
    pow_pos (mul_pos ht0 (pow_pos hu 3)) 2
  have hden : (0 : ℝ) < t * (1 + Real.log t) ^ 4 := mul_pos ht0 (pow_pos hu 4)
  have hdiv : (0 : ℝ) ≤ ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
      (t * (1 + Real.log t) ^ 3) ^ 2 := le_of_lt (div_pos hX hY)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hdiv,
    abs_of_nonneg hS0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t * (1 + Real.log t) ^ 2)⁻¹)]
  have hkey : ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
      (t * (1 + Real.log t) ^ 3) ^ 2 * (C * t * Real.log t) =
        C * Real.log t * (4 + Real.log t) / (t * (1 + Real.log t) ^ 4) := by
    field_simp
    ring
  have hgoal : 4 * C * (t * (1 + Real.log t) ^ 2)⁻¹ =
      4 * C * (1 + Real.log t) ^ 2 / (t * (1 + Real.log t) ^ 4) := by
    field_simp
  calc ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2 * S
      ≤ ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
          (t * (1 + Real.log t) ^ 3) ^ 2 * (C * t * Real.log t) :=
        mul_le_mul_of_nonneg_left hS hdiv
    _ = C * Real.log t * (4 + Real.log t) / (t * (1 + Real.log t) ^ 4) := hkey
    _ ≤ 4 * C * (1 + Real.log t) ^ 2 / (t * (1 + Real.log t) ^ 4) := by
        gcongr ?_ / _
        nlinarith [mul_nonneg hC hL, mul_nonneg hC (mul_nonneg hL hL)]
    _ = 4 * C * (t * (1 + Real.log t) ^ 2)⁻¹ := hgoal.symm

/-! ### The weighted series -/

/-- **Abel summation turns an `O(t log t)` growth bound into a convergent series.** If the partial
sums of a nonnegative sequence `u` satisfy `∑_{1 ≤ k ≤ t} u k = O(t log t)`, then
`∑ u n / (n (1 + log n) ^ 3)` converges: summation by parts against the weight
`(t (1 + log t) ^ 3)⁻¹` leaves the integrable majorant `(t (1 + log t) ^ 2)⁻¹`. -/
theorem summable_div_mul_one_add_log_cube {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    (hgrowth : (fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, u k) =O[atTop] fun t : ℝ ↦ t * Real.log t) :
    Summable fun n : ℕ ↦ u n / (n * (1 + Real.log n) ^ 3) := by
  have hnorm : ∀ k : ℕ, ‖u k‖ = u k := fun k ↦ Real.norm_of_nonneg (hu k)
  obtain ⟨C, hC⟩ := hgrowth.bound
  have hbound : ∀ᶠ v : ℝ in atTop,
      ∑ k ∈ Finset.Icc 1 ⌊v⌋₊, u k ≤ max C 0 * v * Real.log v := by
    filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with v hv hv1
    have h0 : (0 : ℝ) ≤ Real.log v := Real.log_nonneg hv1
    have hle : ∑ k ∈ Finset.Icc 1 ⌊v⌋₊, u k ≤ C * (v * Real.log v) := by
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ ↦ hu k),
        Real.norm_of_nonneg (by positivity)] at hv
      exact hv
    nlinarith [le_max_left C 0, mul_nonneg (by linarith : (0 : ℝ) ≤ v) h0]
  have hbdd : (fun n : ℕ ↦ ‖decayWeight n‖ * ∑ k ∈ Finset.Icc 1 n, ‖u k‖) =O[atTop]
      fun _ : ℕ ↦ (1 : ℝ) := by
    refine .of_bound (max C 0) ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbound,
      eventually_ge_atTop 1] with n hn hn1
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    rw [Nat.floor_natCast] at hn
    simp only [hnorm, norm_one, mul_one]
    rw [Real.norm_of_nonneg (le_of_lt (decayWeight_pos
      (lt_of_lt_of_le exp_neg_one_lt_one hn1')))]
    rw [Real.norm_of_nonneg (mul_nonneg (le_of_lt (decayWeight_pos
      (lt_of_lt_of_le exp_neg_one_lt_one hn1'))) (Finset.sum_nonneg fun k _ ↦ hu k))]
    exact decayWeight_mul_le hn1' (le_max_right C 0) (by linarith [hn])
  have hg1 : (fun v : ℝ ↦ deriv (fun w : ℝ ↦ ‖decayWeight w‖) v *
      ∑ k ∈ Finset.Icc 1 ⌊v⌋₊, ‖u k‖) =O[atTop]
        fun v : ℝ ↦ (v * (1 + Real.log v) ^ 2)⁻¹ := by
    refine .of_bound (4 * max C 0) ?_
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with v hv hv1
    simp only [hnorm]
    rw [deriv_norm_decayWeight hv1]
    exact norm_deriv_decayWeight_mul_le hv1 (le_max_right C 0)
      (Finset.sum_nonneg fun k _ ↦ hu k) hv
  have habel : Summable fun n : ℕ ↦ decayWeight n * u n :=
    summable_mul_of_bigO_atTop' (f := decayWeight) u
      (fun v hv ↦ differentiableAt_norm_decayWeight hv)
      locallyIntegrableOn_deriv_norm_decayWeight hbdd hg1
      integrableAtFilter_inv_mul_one_add_log_sq
  refine habel.congr fun n ↦ ?_
  rw [decayWeight, inv_mul_eq_div]

end TauCeti
