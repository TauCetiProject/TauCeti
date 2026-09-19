/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.AbelSummation

/-!
# Consequences of Abel summation for partial sums

Mathlib's `Mathlib/NumberTheory/AbelSummation.lean` proves the summation-by-parts identity
`∑_{k ≤ x} f k c k = f x ∑_{k ≤ x} c k - ∫ f' (t) ∑_{k ≤ t} c k dt` and derives convergence
criteria from it. This file draws two further consequences from a growth hypothesis on the
partial sums `∑_{1 ≤ k ≤ t} c k`.

* **A logarithmic weight.** Mathlib's `summable_mul_of_bigO_atTop'` converts a bound on the partial
  sums of a sequence into the convergence of a weighted series, provided the weight is
  differentiable and the derivative of the weight against the partial sums admits an integrable
  majorant. This file performs that conversion once, for the weight `(t (1 + log t) ^ 3)⁻¹` and
  partial sums growing like `t log t`. The weight is written with `1 + log t` rather than `log t`
  so that it stays positive and smooth at `t = 1`, where Abel summation starts. Its derivative
  against an `O(t log t)` partial sum is `O((t (1 + log t) ^ 2)⁻¹)`, which is integrable at
  infinity by comparison with Mathlib's log-Cauchy density
  `integrableOn_Ioi_zero_inv_mul_one_add_log_sq`.
* **A power weight.** If the partial sums grow like `κ x`, then the partial sums weighted by
  `n ^ τ`, for an exponent `τ > -1`, grow like `κ x ^ (τ + 1) / (τ + 1)`. This is the step that
  moves a Tauberian conclusion for the coefficients `a n n ^ (1 - σ)` back to the coefficients
  `a n`.

## Main declarations

* `TauCeti.summable_div_mul_one_add_log_cube`: if the partial sums `∑_{1 ≤ k ≤ t} u k` of a
  nonnegative sequence are `O(t log t)`, then `∑ u n / (n (1 + log n) ^ 3)` converges.
* `TauCeti.isLittleO_integral_rpow_sub_one_mul`: a remainder `E t = o(t)` has
  `∫ t in 1..x, t ^ (τ - 1) * E t = o(x ^ (τ + 1))`.
* `TauCeti.tendsto_rpow_inv_mul_sum_Icc_rpow_mul`: if `x⁻¹ ∑_{1 ≤ n ≤ x} c n → κ`, then
  `(x ^ (τ + 1))⁻¹ ∑_{1 ≤ n ≤ x} n ^ τ c n → κ / (τ + 1)` for `τ > -1`.
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

/-! ### Partial sums against a power weight -/

/-- **A remainder `o(t)` integrates to `o(x ^ (τ + 1))` against `t ^ (τ - 1)`.** If `E` is
interval integrable above `1` and `E t = o(t)`, then for every exponent `τ > -1` the weighted
integral `∫ t in 1..x, t ^ (τ - 1) * E t` is `o(x ^ (τ + 1))`. -/
theorem isLittleO_integral_rpow_sub_one_mul {E : ℝ → ℝ} {τ : ℝ} (hτ : -1 < τ)
    (hE_int : ∀ x, 1 ≤ x → IntervalIntegrable E volume 1 x) (hE : E =o[atTop] id) :
    (fun x : ℝ ↦ ∫ t in (1 : ℝ)..x, t ^ (τ - 1) * E t) =o[atTop] fun x ↦ x ^ (τ + 1) := by
  have hτ1 : 0 < τ + 1 := by linarith
  have hint {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun t ↦ t ^ (τ - 1) * E t) volume a b := by
    have hE' : IntervalIntegrable E volume a b := (hE_int b (ha.trans hab)).mono_set <| by
      rw [uIcc_of_le (ha.trans hab), uIcc_of_le hab]
      exact Icc_subset_Icc ha le_rfl
    refine hE'.continuousOn_mul fun t ht ↦ ?_
    rw [uIcc_of_le hab] at ht
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).continuousWithinAt
  rw [isLittleO_iff]
  intro ε hε
  -- Beyond a cutoff `T`, `|E t| ≤ ε' t` with `ε' = ε (τ + 1) / 2`.
  set ε' := ε * (τ + 1) / 2 with hε'
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((isLittleO_iff.mp hE (by positivity : 0 < ε')).and (eventually_ge_atTop (1 : ℝ)))
  have hT1 : 1 ≤ T := (hT T le_rfl).2
  have hbound (t : ℝ) (ht : T ≤ t) : |E t| ≤ ε' * t := by
    have h := (hT t ht).1
    have ht0 : 0 ≤ t := by linarith [(hT t ht).2]
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg ht0] at h
  -- The initial segment `∫ t in 1..T` is a constant, eventually below `ε / 2 * x ^ (τ + 1)`.
  set M := |∫ t in (1 : ℝ)..T, t ^ (τ - 1) * E t|
  filter_upwards [eventually_ge_atTop T,
    (tendsto_rpow_atTop hτ1).eventually_ge_atTop (2 * M / ε)] with x hx hxM
  have hxpow : 0 ≤ x ^ (τ + 1) := Real.rpow_nonneg (by linarith) _
  have hTpow : 0 ≤ T ^ (τ + 1) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hxpow,
    ← intervalIntegral.integral_add_adjacent_intervals (hint le_rfl hT1) (hint hT1 hx)]
  have htail : |∫ t in T..x, t ^ (τ - 1) * E t| ≤
      ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) := by
    calc |∫ t in T..x, t ^ (τ - 1) * E t|
        ≤ ∫ t in T..x, |t ^ (τ - 1) * E t| := intervalIntegral.abs_integral_le_integral_abs hx
      _ ≤ ∫ t in T..x, ε' * t ^ τ := by
          refine intervalIntegral.integral_mono_on hx (hint hT1 hx).abs
            ((intervalIntegral.intervalIntegrable_rpow' hτ).const_mul ε') fun t ht ↦ ?_
          have ht0 : 0 < t := by linarith [ht.1]
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
          calc t ^ (τ - 1) * |E t| ≤ t ^ (τ - 1) * (ε' * t) := by
                gcongr
                exact hbound t ht.1
            _ = ε' * t ^ τ := by
                rw [Real.rpow_sub_one ht0.ne']
                field_simp
      _ = ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hτ)]
  have hM : M ≤ ε / 2 * x ^ (τ + 1) := by
    rw [div_le_iff₀ hε] at hxM
    linarith
  have hε'x : ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) ≤ ε / 2 * x ^ (τ + 1) := by
    have : ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) =
        ε / 2 * (x ^ (τ + 1) - T ^ (τ + 1)) := by
      rw [hε']
      field_simp
    rw [this]
    nlinarith
  calc |(∫ t in (1 : ℝ)..T, t ^ (τ - 1) * E t) + ∫ t in T..x, t ^ (τ - 1) * E t|
      ≤ M + |∫ t in T..x, t ^ (τ - 1) * E t| := abs_add_le _ _
    _ ≤ ε * x ^ (τ + 1) := by linarith

/-- Restricting a sequence to `n ≥ 1` does not change its sums over `Icc 0 m` against a weight,
provided the weight is read from `Icc 1 m`. -/
private lemma sum_Icc_zero_mul_ite (g c : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.Icc 0 m, g k * (if k = 0 then 0 else c k) =
      ∑ n ∈ Finset.Icc 1 m, g n * c n := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
  simp only [↓reduceIte, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  simp [hn0]

/-- The Abel-summation identity `sum_mul_eq_sub_integral_mul₀` for the weight `t ^ τ`:
`∑_{1 ≤ n ≤ x} n ^ τ c n = x ^ τ S(x) - τ ∫ t in 1..x, t ^ (τ - 1) S(t)` for `x ≥ 1`, where
`S(t) = ∑_{1 ≤ n ≤ t} c n`. -/
private lemma sum_Icc_rpow_mul_eq (c : ℕ → ℝ) (τ : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ τ * c n =
      x ^ τ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n -
        τ * ∫ t in (1 : ℝ)..x, t ^ (τ - 1) * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n := by
  have hderiv : deriv (fun u : ℝ ↦ u ^ τ) = fun t ↦ τ * t ^ (τ - 1) :=
    funext fun t ↦ Real.deriv_rpow_const t τ
  have habel := sum_mul_eq_sub_integral_mul₀ (f := fun u : ℝ ↦ u ^ τ)
    (fun n ↦ if n = 0 then 0 else c n) (by simp) x
    (fun t ht ↦ (Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))).differentiableAt)
    (by
      refine ContinuousOn.integrableOn_Icc (fun t ht ↦ ?_)
      rw [hderiv]
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).const_mul
        τ).continuousWithinAt)
  have hsum (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k = 0 then 0 else c k) =
      ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n := by
    simpa using sum_Icc_zero_mul_ite (fun _ ↦ 1) c ⌊t⌋₊
  simp only [sum_Icc_zero_mul_ite, hsum, hderiv] at habel
  rw [habel, intervalIntegral.integral_of_le hx, ← integral_const_mul]
  congr 2
  funext t
  ring

/-- **Partial sums weighted by a power.** If the partial sums of `c` grow like `κ x`, that is
`x⁻¹ ∑_{1 ≤ n ≤ x} c n → κ`, then for every exponent `τ > -1` the partial sums weighted by `n ^ τ`
grow like `κ x ^ (τ + 1) / (τ + 1)`:
`(x ^ (τ + 1))⁻¹ ∑_{1 ≤ n ≤ x} n ^ τ c n → κ / (τ + 1)`. No sign condition on `c` is needed. -/
theorem tendsto_rpow_inv_mul_sum_Icc_rpow_mul {c : ℕ → ℝ} {κ τ : ℝ} (hτ : -1 < τ)
    (h : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n) atTop (𝓝 κ)) :
    Tendsto (fun x : ℝ ↦ (x ^ (τ + 1))⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ τ * c n) atTop
      (𝓝 (κ / (τ + 1))) := by
  have hτ1 : 0 < τ + 1 := by linarith
  set S : ℝ → ℝ := fun t ↦ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n with hS
  set E : ℝ → ℝ := fun t ↦ S t - κ * t with hE
  -- The partial sums are interval integrable above `1`, being a step function.
  have hE_int (x : ℝ) (hx : 1 ≤ x) : IntervalIntegrable E volume 1 x := by
    have hS_int : IntervalIntegrable S volume 1 x := by
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr ?_
      simpa using integrableOn_mul_sum_Icc c (m := 1) zero_le_one
        (continuous_const (y := (1 : ℝ))).integrableOn_Icc
    exact hS_int.sub ((continuous_const.mul continuous_id).intervalIntegrable 1 x)
  -- The hypothesis says `E t = o(t)`.
  have hEo : E =o[atTop] id := by
    refine (isLittleO_iff_tendsto' ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht h0
      exact absurd h0 ht.ne'
    · have h0 : Tendsto (fun t ↦ t⁻¹ * S t - κ) atTop (𝓝 0) := by
        simpa using h.sub_const κ
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp only [hE, id]
      field_simp
  have hI := (isLittleO_integral_rpow_sub_one_mul hτ hE_int hEo).tendsto_div_nhds_zero
  have hpow : Tendsto (fun x : ℝ ↦ (x ^ (τ + 1))⁻¹) atTop (𝓝 0) :=
    (tendsto_rpow_atTop hτ1).inv_tendsto_atTop
  have hlim := ((h.sub (hI.const_mul τ)).sub_const (τ * κ / (τ + 1))).add
    (hpow.const_mul (τ * κ / (τ + 1)))
  have hval : κ - τ * 0 - τ * κ / (τ + 1) + τ * κ / (τ + 1) * 0 = κ / (τ + 1) := by
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  -- In the Abel-summation identity, split `S t = E t + κ t` inside the integral.
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hcont : ContinuousOn (fun t : ℝ ↦ t ^ (τ - 1)) (uIcc 1 x) := fun t ht ↦ by
    rw [uIcc_of_le hx] at ht
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).continuousWithinAt
  have hsplit : ∫ t in (1 : ℝ)..x, t ^ (τ - 1) * S t =
      (∫ t in (1 : ℝ)..x, t ^ (τ - 1) * E t) + κ * ((x ^ (τ + 1) - 1) / (τ + 1)) := by
    have hκ : ∫ t in (1 : ℝ)..x, t ^ τ = (x ^ (τ + 1) - 1) / (τ + 1) := by
      rw [integral_rpow (Or.inl hτ), Real.one_rpow]
    rw [← hκ, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hE_int x hx).continuousOn_mul hcont)
        ((intervalIntegral.intervalIntegrable_rpow' hτ).const_mul κ)]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    simp only [hE]
    rw [Real.rpow_sub_one ht0.ne']
    field_simp
    ring
  rw [sum_Icc_rpow_mul_eq c τ hx, hsplit, Real.rpow_add_one hx0.ne']
  have hxτ : 0 < x ^ τ := Real.rpow_pos_of_pos hx0 τ
  field_simp
  ring

end TauCeti
