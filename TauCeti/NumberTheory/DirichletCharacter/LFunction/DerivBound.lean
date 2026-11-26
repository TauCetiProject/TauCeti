/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.NumberTheory.AbelSummation
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.IntervalSum
import TauCeti.NumberTheory.Harmonic.Bounds

/-!
# Derivative representations and near-one bounds for continued Dirichlet L-functions

For a nonprincipal complex Dirichlet character `χ` of nonzero level `N` (not necessarily primitive,
so `N` need not be `χ.conductor`), partial summation represents the continued `L`-function on
`Re(s) > 0` by `s * ∫_{t > 1} S(t) t ^ (-(s + 1))`, where `S(t)` is the sum of `χ(k)` over
`1 ≤ k ≤ t` (`DirichletCharacter.LFunction_eq_mul_integral`). Differentiating this Mellin-type
integral gives an absolutely convergent integral representation for `L'(s, χ)` across the whole
right half-plane `Re(s) > 0`:

`L'(s, χ) = ∫_{t > 1} S(t) (1 - s log t) t ^ (-(s + 1))`.

Splitting the integral at the level `N` and integrating by parts over `[1, N]` — where period
cancellation `S(N) = 0` (`DirichletCharacter.intervalSum_level_eq_zero`) eliminates the boundary
term at `N` — decomposes both `L(s, χ)` and `L'(s, χ)` on `Re(s) > 0` into a finite Dirichlet
polynomial of length `N` plus a tail integral over `(N, ∞)`:

* `L(s, χ) = ∑_{n=1}^N χ(n) n ^ (-s) + s ∫_{t > N} S(t) t ^ (-(s + 1))`,
* `L'(s, χ) = -∑_{n=1}^N χ(n) (log n) n ^ (-s) + ∫_{t > N} S(t) (1 - s log t) t ^ (-(s + 1))`.

Bounding `‖χ(n)‖ ≤ 1` on the initial sum via `TauCeti.sum_Icc_log_mul_rpow_neg_le_exp_mul_log_sq`
and `‖S(t)‖ ≤ N` on the tail yields explicit level-uniform derivative bounds throughout `Re(s) > 0`,
and in particular the half-line bound `‖L'(σ, χ)‖ ≤ 64 (log N) ^ 2` for every real
`σ ≥ 1 - 1 / log N`, the corresponding Lipschitz bound on `[1 - 1 / log N, ∞)`, and unconditional
real-zero separation `‖L(1, χ)‖ / (64 (log N) ^ 2) ≤ 1 - β` for every real zero `β` of `L(s, χ)`.

## Main results

* `DirichletCharacter.hasDerivAt_LFunction_of_re_pos`,
  `DirichletCharacter.deriv_LFunction_eq_integral`, and
  `DirichletCharacter.integrableOn_sum_Icc_mul_one_sub_mul_log_mul_cpow`: integral representation
  and absolute integrability of `L'(s, χ)` on `Re(s) > 0` for `χ ≠ 1`.
* `DirichletCharacter.LFunction_eq_sum_Icc_add_mul_integral` and
  `DirichletCharacter.deriv_LFunction_eq_neg_sum_Icc_add_integral`: level-split partial-summation
  formulas for `L(s, χ)` and `L'(s, χ)` on `Re(s) > 0`.
* `DirichletCharacter.norm_deriv_LFunction_le_of_re_pos` and
  `DirichletCharacter.norm_deriv_LFunction_ofReal_le_of_pos`: explicit right-half-plane and
  positive-real bounds for `‖L'(s, χ)‖`.
* `DirichletCharacter.norm_deriv_LFunction_le_mul_log_sq` and
  `DirichletCharacter.norm_LFunction_sub_le_of_one_sub_one_div_log_le`: uniform derivative bound
  `‖L'(σ, χ)‖ ≤ 64 * (log N) ^ 2` and Lipschitz bound on `[1 - 1 / log N, ∞)`.
* `DirichletCharacter.norm_LFunction_one_div_log_sq_le_one_sub_of_LFunction_eq_zero`:
  unconditional real-zero separation `‖L(1, χ)‖ / (64 (log N) ^ 2) ≤ 1 - β` for any real zero `β`
  of any nonprincipal character `χ` of nonzero level `N`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  American Mathematical Society, 2019, Lemma 11.2, p. 113, and (12.11), p. 124.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Springer, 2000, Chapters 4 and 14.
-/

public section

open Finset Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- For a nonprincipal character `χ` of nonzero level `N` and `Re(s) > 0`, `χ.LFunction` has
complex derivative `∫_1^∞ (∑_{k=1}^{⌊t⌋₊} χ(k)) (1 - s log t) t ^ (-(s + 1)) dt` at `s`. -/
theorem hasDerivAt_LFunction_of_re_pos (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt χ.LFunction
      (∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1))) s := by
  have heq : χ.LFunction =ᶠ[𝓝 s] fun z : ℂ ↦
      z * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(z + 1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact χ.LFunction_eq_mul_integral hχ hz
  exact (TauCeti.LSeries.hasDerivAt_mul_integral_of_isBigO _
    (by simpa only [Real.rpow_zero] using χ.isBigO_sum_Icc_one hχ) hs).congr_of_eventuallyEq heq

/-- Integral formula for the complex derivative of the continued L-function of a nonprincipal
character on `Re(s) > 0`. -/
theorem deriv_LFunction_eq_integral (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    deriv χ.LFunction s =
      ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1)) :=
  (χ.hasDerivAt_LFunction_of_re_pos hχ hs).deriv

/-- For a nonprincipal character `χ` of nonzero level `N` and `Re(s) > 0`, the derivative integrand
`t ↦ (∑_{k=1}^{⌊t⌋₊} χ(k)) (1 - s log t) t ^ (-(s + 1))` appearing in
`deriv_LFunction_eq_integral` is integrable on `(1, ∞)`. -/
theorem integrableOn_sum_Icc_mul_one_sub_mul_log_mul_cpow (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1)))
      (Set.Ioi 1) :=
  TauCeti.LSeries.integrableOn_sum_mul_one_sub_mul_log_mul_cpow_of_isBigO _
    (by simpa only [Real.rpow_zero] using χ.isBigO_sum_Icc_one hχ) hs

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
  rw [hsum, hsum1, ← χ.intervalSum_zero_eq_sum_Icc, χ.intervalSum_level_eq_zero hχ, mul_zero,
    zero_sub] at habel
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
  have hint := TauCeti.LSeries.integrableOn_sum_mul_cpow_of_isBigO _
    (by simpa only [Real.rpow_zero] using χ.isBigO_sum_Icc_one hχ) hs
  have hcont : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (-(s + 1))) (Set.Ici 1) := fun t ht ↦
    (continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  have hexp : -(s + 1) + 1 = -s := by ring
  have hhead := χ.integral_Ioc_one_level_sum_mul_eq hχ
    (g := fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1) + 1) / (-(s + 1) + 1))
    (fun t ht ↦ hasDerivAt_ofReal_cpow_const' (zero_lt_one.trans_le ht).ne'
      (by intro h; exact hs0 (by linear_combination -h))) hcont
  simp only [ofReal_natCast] at hhead
  rw [χ.LFunction_eq_mul_integral hχ hs, ← Set.Ioc_union_Ioi_eq_Ioi hN1',
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hN1')),
    mul_add, hhead, mul_neg, mul_sum, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  rw [hexp, cpow_neg, div_eq_mul_inv]
  field_simp [hs0]

/-- **Level-split partial summation for `L'(s, χ)`.** For a nonprincipal character `χ` of level `N`
and `Re(s) > 0`, `L'(s, χ)` is `-∑_{n=1}^N χ(n) (log n) n ^ (-s)` plus the tail integral over
`(N, ∞)`. -/
theorem deriv_LFunction_eq_neg_sum_Icc_add_integral (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    deriv χ.LFunction s = -(∑ n ∈ Icc 1 N, χ n * Real.log n / (n : ℂ) ^ s) +
      ∫ t in Set.Ioi (N : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1)) := by
  have hN1' : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
  have hint := χ.integrableOn_sum_Icc_mul_one_sub_mul_log_mul_cpow hχ hs
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
        rw [← neg_add']
        ring)) hcont
  simp only [ofReal_natCast, ← mul_assoc] at hhead
  rw [χ.deriv_LFunction_eq_integral hχ hs, ← Set.Ioc_union_Ioi_eq_Ioi hN1',
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hN1')),
    hhead]
  congr 2
  refine sum_congr rfl fun n _ ↦ ?_
  rw [cpow_neg, div_eq_mul_inv]
  ring

/-! ### Explicit bounds on `Re(s) > 0` and near `s = 1` -/

/-- Tail estimate on `(N, ∞)`, using period cancellation `‖∑_{k≤t} χ(k)‖ ≤ N`. -/
private lemma norm_integral_Ioi_le (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (N : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1))‖ ≤
      (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ * Real.log N) / s.re + ‖s‖ / s.re ^ 2) := by
  have hN3 := χ.three_le_level_of_ne_one hχ
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN1
  have ha : -(s.re + 1) < -1 := by linarith
  have h_int₁ := (integrableOn_Ioi_rpow_of_lt ha hN0).const_mul (N : ℝ)
  have h_int₂ := (TauCeti.integrableOn_Ioi_rpow_mul_log_of_lt ha hN0).const_mul ((N : ℝ) * ‖s‖)
  calc
    _ ≤ ∫ t in Set.Ioi (N : ℝ),
        ((N : ℝ) * t ^ (-(s.re + 1)) + (N : ℝ) * ‖s‖ * (t ^ (-(s.re + 1)) * Real.log t)) := by
      refine norm_integral_le_of_norm_le (h_int₁.add h_int₂) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : (N : ℝ) < t)
      have ht1 : 1 < t := hN1.trans ht
      have ht0 : 0 < t := zero_lt_one.trans ht1
      have hlog : ‖(1 : ℂ) - s * Real.log t‖ ≤ 1 + ‖s‖ * Real.log t := by
        calc
          ‖(1 : ℂ) - s * Real.log t‖ ≤ ‖(1 : ℂ)‖ + ‖s * (Real.log t : ℂ)‖ := norm_sub_le _ _
          _ = 1 + ‖s‖ * Real.log t := by
            rw [norm_one, norm_mul, Complex.norm_real,
              Real.norm_of_nonneg (Real.log_nonneg ht1.le)]
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [neg_re, add_re, one_re]
      calc
        ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ k‖ * ‖(1 : ℂ) - s * Real.log t‖ * t ^ (-(s.re + 1))
            ≤ ((N : ℝ) * (1 + ‖s‖ * Real.log t)) * t ^ (-(s.re + 1)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (χ.norm_sum_Icc_le_level hχ _) hlog (norm_nonneg _) hN0.le)
            (Real.rpow_nonneg ht0.le _)
        _ = (N : ℝ) * t ^ (-(s.re + 1)) +
              (N : ℝ) * ‖s‖ * (t ^ (-(s.re + 1)) * Real.log t) := by ring
    _ = (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ * Real.log N) / s.re + ‖s‖ / s.re ^ 2) := by
      rw [integral_add h_int₁ h_int₂, integral_const_mul, integral_const_mul,
        integral_Ioi_rpow_of_lt ha hN0, TauCeti.integral_Ioi_rpow_mul_log_of_lt ha hN0]
      have hN_pow : (N : ℝ) * (N : ℝ) ^ (-(s.re + 1) + 1) = (N : ℝ) ^ (1 - s.re) := by
        calc
          (N : ℝ) * (N : ℝ) ^ (-(s.re + 1) + 1) =
              (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(s.re + 1) + 1) := by rw [Real.rpow_one]
          _ = (N : ℝ) ^ (1 - s.re) := by rw [← Real.rpow_add hN0]; congr 1; ring
      have hre : s.re ≠ 0 := hs.ne'
      have hre' : -(s.re + 1) + 1 = -s.re := by ring
      rw [hre'] at hN_pow ⊢
      calc
        (N : ℝ) * (-(N : ℝ) ^ (-s.re) / -s.re) +
            (N : ℝ) * ‖s‖ * ((N : ℝ) ^ (-s.re) * (1 - -s.re * Real.log N) / (-s.re) ^ 2)
            = ((N : ℝ) * (N : ℝ) ^ (-s.re)) *
                (-1 / -s.re + ‖s‖ * (1 - -s.re * Real.log N) / (-s.re) ^ 2) := by ring
        _ = (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ * Real.log N) / s.re + ‖s‖ / s.re ^ 2) := by
          rw [hN_pow]
          congr 1
          field_simp
          ring

/-- **Right-half-plane bound for `L'(s, χ)`.** For any nonprincipal character `χ` of nonzero level
`N` and any `s` with `Re(s) > 0`,
`‖L'(s, χ)‖ ≤ ∑_{n=1}^N (log n) n ^ (-Re(s)) +
N ^ (1 - Re(s)) * ((1 + ‖s‖ log N) / Re(s) + ‖s‖ / Re(s) ^ 2)`. -/
theorem norm_deriv_LFunction_le_of_re_pos (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖deriv χ.LFunction s‖ ≤ (∑ n ∈ Icc 1 N, Real.log n * (n : ℝ) ^ (-s.re)) +
      (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ * Real.log N) / s.re + ‖s‖ / s.re ^ 2) := by
  have hhead : ‖-(∑ n ∈ Icc 1 N, χ n * Real.log n / (n : ℂ) ^ s)‖ ≤
      ∑ n ∈ Icc 1 N, Real.log n * (n : ℝ) ^ (-s.re) := by
    rw [norm_neg]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn ↦ ?_)
    have hn1 : (1 : ℝ) ≤ n := mod_cast (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hn1),
      ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hn0, div_eq_mul_inv, ← Real.rpow_neg hn0.le]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (Real.log_nonneg hn1) (χ.norm_le_one n)) (by positivity)
  rw [χ.deriv_LFunction_eq_neg_sum_Icc_add_integral hχ hs]
  exact (norm_add_le _ _).trans (add_le_add hhead (χ.norm_integral_Ioi_le hχ hs))

/-- **Explicit bound for `L'(σ, χ)` at real `σ > 0`.** For a nonprincipal character `χ` of nonzero
level `N` and real `σ > 0`, `‖L'(σ, χ)‖ ≤ ∑_{n=1}^N (log n) n ^ (-σ) + N ^ (1 - σ) (log N + 2 / σ)`.
-/
theorem norm_deriv_LFunction_ofReal_le_of_pos (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    ‖deriv χ.LFunction σ‖ ≤ (∑ n ∈ Icc 1 N, Real.log n * (n : ℝ) ^ (-σ)) +
      (N : ℝ) ^ (1 - σ) * (Real.log N + 2 / σ) := by
  refine (χ.norm_deriv_LFunction_le_of_re_pos hχ (s := σ) (by simpa using hσ)).trans_eq ?_
  simp only [ofReal_re, Complex.norm_real, Real.norm_of_nonneg hσ.le]
  field_simp [hσ.ne']
  ring

/-- **Near-one and right-half-line derivative bound for Dirichlet L-functions**
(Koukoulopoulos, Lemma 11.2). Uniformly for any nonprincipal character `χ` of nonzero level `N` and
every real `σ ≥ 1 - 1 / log N`, we have `‖L'(σ, χ)‖ ≤ 64 (log N) ^ 2`. -/
theorem norm_deriv_LFunction_le_mul_log_sq (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 - 1 / Real.log N ≤ σ) :
    ‖deriv χ.LFunction σ‖ ≤ 64 * Real.log N ^ 2 := by
  have hN3 : 3 ≤ N := χ.three_le_level_of_ne_one hχ
  have hN3' : (3 : ℝ) ≤ N := mod_cast hN3
  have hlog_pos : 0 < Real.log N := zero_lt_one.trans (Real.one_lt_log_of_three_le hN3')
  have hlog : (23 : ℝ) / 21 < Real.log N := by
    linarith [Real.log_three_gt_d9, Real.log_le_log (by norm_num) hN3']
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

/-- **Lipschitz bound for `L(σ, χ)` near and above `1`.** For any nonprincipal character `χ` of
nonzero level `N` and `σ₁, σ₂ ≥ 1 - 1 / log N`,
`‖L(σ₂, χ) - L(σ₁, χ)‖ ≤ 64 (log N) ^ 2 |σ₂ - σ₁|`. -/
theorem norm_LFunction_sub_le_of_one_sub_one_div_log_le (hχ : χ ≠ 1) {σ₁ σ₂ : ℝ}
    (h₁ : 1 - 1 / Real.log N ≤ σ₁) (h₂ : 1 - 1 / Real.log N ≤ σ₂) :
    ‖χ.LFunction σ₂ - χ.LFunction σ₁‖ ≤ 64 * Real.log N ^ 2 * |σ₂ - σ₁| := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ ↦ χ.LFunction t) (deriv χ.LFunction x) x := fun x ↦
    (χ.differentiable_LFunction hχ).differentiableAt.hasDerivAt.comp_ofReal
  have hb : ∀ x ∈ Set.uIcc σ₁ σ₂, ‖deriv (fun t : ℝ ↦ χ.LFunction t) x‖ ≤
      64 * Real.log N ^ 2 := by
    intro x hx
    rw [(hd x).deriv]
    exact χ.norm_deriv_LFunction_le_mul_log_sq hχ ((le_min h₁ h₂).trans hx.1)
  simpa only [Real.norm_eq_abs] using (convex_uIcc σ₁ σ₂).norm_image_sub_le_of_norm_deriv_le
    (fun x _ ↦ (hd x).differentiableAt) hb Set.left_mem_uIcc Set.right_mem_uIcc

/-- **Unconditional real-zero separation from `L(1, χ)`** (Koukoulopoulos, (12.11)). For any
nonprincipal character `χ` of nonzero level `N` (not necessarily primitive or quadratic) and any
real zero `β` of `L(s, χ)`, `‖L(1, χ)‖ / (64 (log N) ^ 2) ≤ 1 - β`. -/
theorem norm_LFunction_one_div_log_sq_le_one_sub_of_LFunction_eq_zero (hχ : χ ≠ 1) {β : ℝ}
    (hβ : χ.LFunction β = 0) :
    ‖χ.LFunction 1‖ / (64 * Real.log N ^ 2) ≤ 1 - β := by
  -- Nonvanishing on `Re(s) ≥ 1` forces `β < 1`; for `β < 1 - 1 / log N` use
  -- `‖L(1, χ)‖ ≤ 1 + log N`.
  have hlog : 1 < Real.log N :=
    Real.one_lt_log_of_three_le (mod_cast χ.three_le_level_of_ne_one hχ)
  have hlog_pos : 0 < Real.log N := zero_lt_one.trans hlog
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
