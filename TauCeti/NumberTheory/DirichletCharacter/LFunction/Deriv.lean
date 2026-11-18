/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.SpecialFunctions.Integrals.RpowLog
import TauCeti.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.NumberTheory.AbelSummation
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.Harmonic.Bounds

/-!
# Derivative representations and near-one bounds for continued Dirichlet L-functions

For a nonprincipal Dirichlet character `χ` of nonzero level `N`, partial summation represents the
continued L-function on `Re(s) > 0` by `s * ∫_{t > 1} S(t) t^{-(s + 1)}`, where `S(t)` is the sum
of `χ(k)` over `1 ≤ k ≤ t` (`DirichletCharacter.LFunction_eq_mul_integral`). Differentiating this
Mellin-type integral gives an integral formula for `L'(s, χ)` valid across the whole right
half-plane `Re(s) > 0`:

`L'(s, χ) = ∫_{t > 1} S(t) (1 - s log t) t^{-(s + 1)}`.

Splitting the integral at the level `N` and integrating by parts over unit intervals `[m, m + 1]`
for `1 ≤ m < N` — where `S(N) = 0` cancels the boundary term at `N` — decomposes both `L(s, χ)`
and `L'(s, χ)` on `Re(s) > 0` into a finite Dirichlet polynomial of length `N` plus a tail
integral over `(N, ∞)`:

* `L(s, χ) = ∑_{n=1}^N χ(n) n^{-s} + s ∫_{t > N} S(t) t^{-(s + 1)}`,
* `L'(s, χ) = -∑_{n=1}^N χ(n) (log n) n^{-s} + ∫_{t > N} S(t) (1 - s log t) t^{-(s + 1)}`.

Bounding `‖χ(n)‖ ≤ 1` on the initial sum and `‖S(t)‖ ≤ N` on the tail yields explicit level-uniform
derivative bounds on `Re(s) > 0`, and in particular the near-one bound
`‖L'(σ, χ)‖ ≤ 64 (log N)²` for every real `σ ≥ 1 - 1 / log N`. Combined with the mean value
inequality and `‖L(1, χ)‖ ≤ 1 + log N`, any real zero `β` of `L(s, χ)` satisfies
`‖L(1, χ)‖ / (64 (log N)²) ≤ 1 - β`.

## Main results

* `DirichletCharacter.integrableOn_sum_mul_one_sub_mul_log_mul_cpow`,
  `DirichletCharacter.hasDerivAt_LFunction_of_re_pos`,
  `DirichletCharacter.deriv_LFunction_eq_integral`: integral representation of `L'(s, χ)` on
  `Re(s) > 0`.
* `DirichletCharacter.LFunction_eq_sum_Icc_add_mul_integral`,
  `DirichletCharacter.deriv_LFunction_eq_neg_sum_Icc_add_integral`: level-split partial-summation
  formulas for `L(s, χ)` and `L'(s, χ)` on `Re(s) > 0`.
* `DirichletCharacter.norm_deriv_LFunction_le_of_re_pos`,
  `DirichletCharacter.norm_deriv_LFunction_ofReal_le_of_pos`: explicit bounds for `‖L'(s, χ)‖` on
  `Re(s) > 0` and on `(0, ∞)`.
* `DirichletCharacter.norm_deriv_LFunction_le_of_one_sub_one_div_log_le`:
  `‖L'(σ, χ)‖ ≤ 64 (log N)²` for `σ ≥ 1 - 1 / log N`.
* `DirichletCharacter.norm_LFunction_sub_le_of_one_sub_one_div_log_le`: Lipschitz bound for
  `L(σ, χ)` on `[1 - 1 / log N, ∞)`.
* `DirichletCharacter.norm_LFunction_one_div_log_sq_le_one_sub_of_LFunction_eq_zero`: every real
  zero `β` of `L(s, χ)` satisfies `‖L(1, χ)‖ / (64 (log N)²) ≤ 1 - β`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Lemma 11.2 and (12.11).
* H. Davenport, *Multiplicative Number Theory*, Chapters 4 and 14.
-/

public section

open Finset Filter MeasureTheory Complex
open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

omit [NeZero N] in
/-- The integral representing `L'(s, χ)` converges absolutely on the half-plane `Re(s) > 0`. -/
theorem integrableOn_sum_mul_one_sub_mul_log_mul_cpow (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1)))
      (Set.Ioi 1) := by
  have h1 :=
    TauCeti.LSeries.integrableOn_sum_mul_cpow_of_isBigO _ (χ.sum_Icc_isBigO_rpow_zero hχ) hs
  have h2 := (TauCeti.LSeries.integrableOn_sum_mul_log_mul_cpow_of_isBigO _
    (χ.sum_Icc_isBigO_rpow_zero hχ) hs).const_mul s
  refine (h1.sub h2).congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  dsimp only [Pi.sub_apply]
  ring

/-- Partial summation gives the derivative of the continued L-function of a nonprincipal character
on the whole half-plane `Re(s) > 0`. -/
theorem hasDerivAt_LFunction_of_re_pos (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt χ.LFunction
      (∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1))) s := by
  have hderiv :=
    TauCeti.LSeries.hasDerivAt_mul_integral_of_isBigO _ (χ.sum_Icc_isBigO_rpow_zero hχ) hs
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
  exact χ.LFunction_eq_mul_integral hχ hz

/-- Integral representation of `L'(s, χ)` on the half-plane `Re(s) > 0`. -/
theorem deriv_LFunction_eq_integral (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    deriv χ.LFunction s =
      ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1)) :=
  (χ.hasDerivAt_LFunction_of_re_pos hχ hs).deriv

/-! ### Level-split partial summation on `(1, N]` and `(N, ∞)` -/

omit [NeZero N] in
/-- Integrating a continuous derivative `g'` against the partial-sum step function of a
nonprincipal character `χ` over `(1, N]` gives `-∑_{k=1}^N χ(k) g(k)`, since `S(N) = 0` cancels the
boundary term at `N` in Abel's summation formula. -/
private theorem integral_Ioc_one_level_sum_mul_eq (hχ : χ ≠ 1) {g g' : ℝ → ℂ}
    (hg : ∀ t : ℝ, 1 ≤ t → HasDerivAt g (g' t) t) (hcont : ContinuousOn g' (Set.Ici 1)) :
    ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * g' t =
      -∑ k ∈ Icc 1 N, χ k * g (k : ℕ) := by
  let c : ℕ → ℂ := fun k ↦ if k = 0 then 0 else χ k
  have hsum (w : ℕ → ℂ) (m : ℕ) : ∑ k ∈ Icc 0 m, w k * c k = ∑ k ∈ Icc 1 m, χ k * w k := by
    rw [Icc_eq_cons_Ioc (Nat.zero_le m), sum_cons, ← Icc_add_one_left_eq_Ioc]
    simp only [c, ↓reduceIte, mul_zero, zero_add]
    refine sum_congr rfl fun k hk ↦ ?_
    simp [Nat.ne_of_gt (mem_Icc.mp hk).1, mul_comm]
  have hsum1 (m : ℕ) : ∑ k ∈ Icc 0 m, c k = ∑ k ∈ Icc 1 m, χ k := by
    simpa using hsum (fun _ ↦ 1) m
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ g t :=
    fun t ht ↦ (hg t ht.1).differentiableAt
  have hderiv_eq : Set.EqOn (deriv g) g' (Set.Icc (1 : ℝ) N) :=
    fun t ht ↦ (hg t ht.1).deriv
  have hint : IntegrableOn (deriv g) (Set.Icc (1 : ℝ) N) :=
    (hcont.mono Set.Icc_subset_Ici_self).integrableOn_Icc.congr_fun hderiv_eq.symm measurableSet_Icc
  have habel := sum_mul_eq_sub_integral_mul₀' c rfl N hdiff hint
  rw [hsum, hsum1, χ.sum_Icc_one_level_eq_zero hχ, mul_zero, zero_sub] at habel
  refine (setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_).trans
    (neg_eq_iff_eq_neg.mp habel.symm)
  rw [(hg t ht.1.le).deriv, hsum1, mul_comm]

/-- **Level-split partial summation for `L(s, χ)`.** For a nonprincipal character `χ` of level `N`
and `Re(s) > 0`, `L(s, χ)` is the finite Dirichlet polynomial up to `N` plus `s` times the tail
integral over `(N, ∞)`. -/
theorem LFunction_eq_sum_Icc_add_mul_integral (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    χ.LFunction s = (∑ n ∈ Icc 1 N, χ n / (n : ℂ) ^ s) +
      s * ∫ t in Set.Ioi (N : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hN1' : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
  have hint :=
    TauCeti.LSeries.integrableOn_sum_mul_cpow_of_isBigO _ (χ.sum_Icc_isBigO_rpow_zero hχ) hs
  have hcont : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (-(s + 1))) (Set.Ici 1) := fun t ht ↦
    (continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  have hhead := χ.integral_Ioc_one_level_sum_mul_eq hχ
    (g := fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1) + 1) / (-(s + 1) + 1))
    (fun t ht ↦ hasDerivAt_ofReal_cpow_const' (zero_lt_one.trans_le ht).ne'
      (by intro h; exact hs0 (by linear_combination -h))) hcont
  simp only [ofReal_natCast] at hhead
  rw [χ.LFunction_eq_mul_integral hχ hs, ← Set.Ioc_union_Ioi_eq_Ioi hN1',
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hN1')),
    mul_add, hhead, mul_neg, mul_sum, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  rw [show -(s + 1) + 1 = -s by ring, cpow_neg, div_eq_mul_inv]
  field_simp [hs0]

/-- **Level-split partial summation for `L'(s, χ)`.** For a nonprincipal character `χ` of level `N`
and `Re(s) > 0`, `L'(s, χ)` is `-∑_{n=1}^N χ(n) (log n) n^{-s}` plus the tail integral over
`(N, ∞)`. -/
theorem deriv_LFunction_eq_neg_sum_Icc_add_integral (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    deriv χ.LFunction s = -(∑ n ∈ Icc 1 N, χ n * Real.log n / (n : ℂ) ^ s) +
      ∫ t in Set.Ioi (N : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1)) := by
  have hN1' : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
  have hint := χ.integrableOn_sum_mul_one_sub_mul_log_mul_cpow hχ hs
  have hcont : ContinuousOn
      (fun t : ℝ ↦ (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1))) (Set.Ici 1) := by
    refine (continuousOn_const.sub (continuousOn_const.mul (continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun t ht ↦ (zero_lt_one.trans_le ht).ne')))).mul fun t ht ↦ ?_
    exact (continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  have hhead := χ.integral_Ioc_one_level_sum_mul_eq hχ
    (g := fun y : ℝ ↦ (y : ℂ) ^ (-s) * Real.log y)
    (fun t ht ↦ (TauCeti.hasDerivAt_ofReal_cpow_mul_log (-s)
      (zero_lt_one.trans_le ht).ne').congr_deriv (by
        rw [show -s - 1 = -(s + 1) by ring]
        ring)) hcont
  simp only [ofReal_natCast, ← mul_assoc] at hhead
  rw [χ.deriv_LFunction_eq_integral hχ hs, ← Set.Ioc_union_Ioi_eq_Ioi hN1',
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hN1')),
    hhead]
  congr 2
  refine sum_congr rfl fun n _ ↦ ?_
  rw [cpow_neg, div_eq_mul_inv]
  ring

/-! ### Explicit bounds on `Re(s) > 0` and near `s = 1` -/

/-- **Explicit bound for `L'(s, χ)` on `Re(s) > 0`.** For a nonprincipal character `χ` of level `N`
and `Re(s) > 0`, `‖L'(s, χ)‖ ≤ ∑_{n=1}^N (log n) n^{-Re(s)} +
N^{1 - Re(s)} ((1 + ‖s‖ / Re(s)) / Re(s) + ‖s‖ / Re(s) · log N)`. -/
theorem norm_deriv_LFunction_le_of_re_pos (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖deriv χ.LFunction s‖ ≤ (∑ n ∈ Icc 1 N, Real.log n * (n : ℝ) ^ (-s.re)) +
      (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ / s.re) / s.re + ‖s‖ / s.re * Real.log N) := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have ha : -s.re - 1 < -1 := by linarith
  have hrpow_int := integrableOn_Ioi_rpow_of_lt ha hN0
  have hlog_int := TauCeti.integrableOn_Ioi_rpow_mul_log_of_lt ha hN0
  have htail_int :
      IntegrableOn (fun t : ℝ ↦ (1 + ‖s‖ * Real.log t) * t ^ (-s.re - 1)) (Set.Ioi N) := by
    refine (hrpow_int.add (hlog_int.const_mul ‖s‖)).congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    dsimp only [Pi.add_apply]
    ring
  have htail_val :
      ∫ t in Set.Ioi (N : ℝ), (1 + ‖s‖ * Real.log t) * t ^ (-s.re - 1) =
        (N : ℝ) ^ (-s.re) * ((1 + ‖s‖ / s.re) / s.re + ‖s‖ / s.re * Real.log N) := by
    have hsplit :
        ∫ t in Set.Ioi (N : ℝ), (1 + ‖s‖ * Real.log t) * t ^ (-s.re - 1) =
          (∫ t in Set.Ioi (N : ℝ), t ^ (-s.re - 1)) +
            ‖s‖ * ∫ t in Set.Ioi (N : ℝ), t ^ (-s.re - 1) * Real.log t := by
      rw [← integral_const_mul, ← integral_add hrpow_int (hlog_int.const_mul ‖s‖)]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ by ring
    rw [hsplit, integral_Ioi_rpow_of_lt ha hN0,
      TauCeti.integral_Ioi_rpow_mul_log_of_lt ha hN0, show -s.re - 1 + 1 = -s.re by ring]
    field_simp [hs.ne']
    ring
  have hhead : ‖-(∑ n ∈ Icc 1 N, χ n * Real.log n / (n : ℂ) ^ s)‖ ≤
      ∑ n ∈ Icc 1 N, Real.log n * (n : ℝ) ^ (-s.re) := by
    rw [norm_neg]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn ↦ ?_)
    have hn1 : (1 : ℝ) ≤ n := mod_cast (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
    rw [norm_div, norm_mul, norm_real, Real.norm_of_nonneg (Real.log_nonneg hn1),
      ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hn0, div_eq_mul_inv, ← Real.rpow_neg hn0.le]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (Real.log_nonneg hn1) (χ.norm_le_one n)) (by positivity)
  have htail : ‖∫ t in Set.Ioi (N : ℝ),
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1))‖ ≤
      (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ / s.re) / s.re + ‖s‖ / s.re * Real.log N) := by
    calc
      _ ≤ ∫ t in Set.Ioi (N : ℝ), (N : ℝ) * ((1 + ‖s‖ * Real.log t) * t ^ (-s.re - 1)) := by
        refine norm_integral_le_of_norm_le (htail_int.const_mul _) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht1 : 1 ≤ t := hN1.trans ht.le
        have ht0 : 0 < t := zero_lt_one.trans_le ht1
        have h1s : ‖1 - s * Real.log t‖ ≤ 1 + ‖s‖ * Real.log t := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_one, norm_mul, norm_real, Real.norm_of_nonneg (Real.log_nonneg ht1)]
        have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
        rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, hre]
        have hmul := mul_le_mul (χ.norm_sum_Icc_le_level hχ ⌊t⌋₊) h1s (norm_nonneg _)
          (Nat.cast_nonneg N)
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg ht0.le (-s.re - 1))
      _ = (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ / s.re) / s.re + ‖s‖ / s.re * Real.log N) := by
        rw [integral_const_mul, htail_val, ← mul_assoc]
        congr 1
        rw [show (1 - s.re : ℝ) = 1 + -s.re by ring, Real.rpow_add hN0, Real.rpow_one]
  rw [χ.deriv_LFunction_eq_neg_sum_Icc_add_integral hχ hs]
  exact (norm_add_le _ _).trans (add_le_add hhead htail)

/-- **Explicit bound for `L'(σ, χ)` at real `σ > 0`.** For a nonprincipal character `χ` of level `N`
and real `σ > 0`, `‖L'(σ, χ)‖ ≤ ∑_{n=1}^N (log n) n^{-σ} + N^{1 - σ} (log N + 2 / σ)`. -/
theorem norm_deriv_LFunction_ofReal_le_of_pos (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    ‖deriv χ.LFunction σ‖ ≤ (∑ n ∈ Icc 1 N, Real.log n * (n : ℝ) ^ (-σ)) +
      (N : ℝ) ^ (1 - σ) * (Real.log N + 2 / σ) := by
  refine (χ.norm_deriv_LFunction_le_of_re_pos hχ (s := σ) (by simpa using hσ)).trans_eq ?_
  simp only [ofReal_re, norm_real, Real.norm_of_nonneg hσ.le, div_self hσ.ne']
  ring

/-- **Near-one derivative bound for `L(s, χ)`.** For a nonprincipal character `χ` of level `N` and
every real `σ ≥ 1 - 1 / log N`, `‖L'(σ, χ)‖ ≤ 64 (log N)²`. -/
theorem norm_deriv_LFunction_le_of_one_sub_one_div_log_le (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 - 1 / Real.log N ≤ σ) :
    ‖deriv χ.LFunction σ‖ ≤ 64 * Real.log N ^ 2 := by
  have hN3 : 3 ≤ N := χ.three_le_level_of_ne_one hχ
  have hlog : (23 : ℝ) / 21 < Real.log N :=
    calc (23 : ℝ) / 21 < Real.log 3 := by linarith [Real.log_three_gt_d9]
      _ ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN3)
  have hlog_pos : 0 < Real.log N := by linarith
  have hinv : 1 / Real.log N < 21 / 23 := by
    rw [div_lt_div_iff₀ hlog_pos (by norm_num)]
    linarith
  have hσ_lo : (2 : ℝ) / 23 < σ := by linarith
  have hσ_pos : 0 < σ := by linarith
  have hsum := TauCeti.sum_Icc_log_mul_rpow_neg_le_exp_mul_log_sq N zero_le_one hσ
  have htail : (N : ℝ) ^ (1 - σ) * (Real.log N + 2 / σ) ≤ 22 * Real.exp 1 * Real.log N ^ 2 := by
    have h1 : (N : ℝ) ^ (1 - σ) ≤ Real.exp 1 :=
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N))
        (by rw [← one_div]; linarith)).trans Real.rpow_inv_log_le_exp_one
    have h2 : 2 / σ ≤ 23 := by
      rw [div_le_iff₀ hσ_pos]
      linarith
    have h3 : Real.log N + 2 / σ ≤ 22 * Real.log N ^ 2 := by
      nlinarith [sq_nonneg (Real.log N - 1)]
    calc
      (N : ℝ) ^ (1 - σ) * (Real.log N + 2 / σ)
        ≤ Real.exp 1 * (22 * Real.log N ^ 2) :=
          mul_le_mul h1 h3 (by positivity) (Real.exp_nonneg 1)
      _ = 22 * Real.exp 1 * Real.log N ^ 2 := by ring
  refine (χ.norm_deriv_LFunction_ofReal_le_of_pos hχ hσ_pos).trans ?_
  nlinarith [Real.exp_one_lt_d9, sq_nonneg (Real.log N)]

/-- **Lipschitz bound for `L(σ, χ)` near and above `1`.** For a nonprincipal character `χ` of level
`N` and `σ₁, σ₂ ≥ 1 - 1 / log N`, `‖L(σ₂, χ) - L(σ₁, χ)‖ ≤ 64 (log N)² |σ₂ - σ₁|`. -/
theorem norm_LFunction_sub_le_of_one_sub_one_div_log_le (hχ : χ ≠ 1) {σ₁ σ₂ : ℝ}
    (h₁ : 1 - 1 / Real.log N ≤ σ₁) (h₂ : 1 - 1 / Real.log N ≤ σ₂) :
    ‖χ.LFunction σ₂ - χ.LFunction σ₁‖ ≤ 64 * Real.log N ^ 2 * |σ₂ - σ₁| := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ ↦ χ.LFunction t) (deriv χ.LFunction x) x := fun x ↦
    (χ.differentiable_LFunction hχ).differentiableAt.hasDerivAt.comp_ofReal
  have hb : ∀ x ∈ Set.uIcc σ₁ σ₂, ‖deriv (fun t : ℝ ↦ χ.LFunction t) x‖ ≤
      64 * Real.log N ^ 2 := by
    intro x hx
    rw [(hd x).deriv]
    exact χ.norm_deriv_LFunction_le_of_one_sub_one_div_log_le hχ ((le_min h₁ h₂).trans hx.1)
  simpa only [Real.norm_eq_abs] using (convex_uIcc σ₁ σ₂).norm_image_sub_le_of_norm_deriv_le
    (fun x _ ↦ (hd x).differentiableAt) hb Set.left_mem_uIcc Set.right_mem_uIcc

/-- **Zero-separation bound from `L(1, χ)`.** For any nonprincipal character `χ` of level `N` and
any real zero `β` of `L(s, χ)`, `‖L(1, χ)‖ / (64 (log N)²) ≤ 1 - β`. -/
theorem norm_LFunction_one_div_log_sq_le_one_sub_of_LFunction_eq_zero (hχ : χ ≠ 1) {β : ℝ}
    (hβ : χ.LFunction β = 0) :
    ‖χ.LFunction 1‖ / (64 * Real.log N ^ 2) ≤ 1 - β := by
  -- Nonvanishing on `Re(s) ≥ 1` forces `β < 1`; for `β < 1 - 1 / log N` use
  -- `‖L(1, χ)‖ ≤ 1 + log N`.
  have hlog : 1 < Real.log N :=
    calc (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
      _ ≤ Real.log N := Real.log_le_log (by norm_num)
          (by exact_mod_cast χ.three_le_level_of_ne_one hχ)
  have hlog_pos : 0 < Real.log N := by linarith
  have hβ1 : β < 1 := by
    by_contra! h1
    exact LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simpa using h1) hβ
  rcases lt_or_ge β (1 - 1 / Real.log N) with hfar | hnear
  · have hL1 := χ.norm_LFunction_one_le_one_add_log hχ
    have hlt : ‖χ.LFunction 1‖ / (64 * Real.log N ^ 2) < 1 / Real.log N := by
      rw [div_lt_div_iff₀ (by positivity) hlog_pos]
      nlinarith
    linarith
  · have h1_mem : 1 - 1 / Real.log N ≤ 1 := by
      have : 0 ≤ 1 / Real.log N := by positivity
      linarith
    have hlip := χ.norm_LFunction_sub_le_of_one_sub_one_div_log_le hχ hnear h1_mem
    rw [ofReal_one, hβ, sub_zero, abs_of_pos (sub_pos.mpr hβ1)] at hlip
    rw [div_le_iff₀ (by positivity)]
    linarith

end DirichletCharacter
