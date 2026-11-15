/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.AbelSummation
import TauCeti.NumberTheory.DirichletCharacter.Basic

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
* `DirichletCharacter.norm_deriv_LFunction_le_of_one_sub_inv_log_le`:
  `‖L'(σ, χ)‖ ≤ 64 (log N)²` for `σ ≥ 1 - 1 / log N`.
* `DirichletCharacter.norm_LFunction_sub_le_of_one_sub_inv_log_le`: Lipschitz bound for `L(σ, χ)`
  on `[1 - 1 / log N, ∞)`.
* `DirichletCharacter.norm_LFunction_one_div_log_sq_le_one_sub_of_LFunction_eq_zero`: every real
  zero `β` of `L(s, χ)` satisfies `‖L(1, χ)‖ / (64 (log N)²) ≤ 1 - β`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Lemma 11.2 and (12.11).
* H. Davenport, *Multiplicative Number Theory*, Chapters 4 and 14.
-/

public section

open Finset Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

omit [NeZero N] in
private theorem sum_isBigO_one' (hχ : χ ≠ 1) :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, χ k) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
  rcases N.eq_zero_or_pos with rfl | hN
  · refine isBigO_iff.mpr ⟨‖χ 1‖, Eventually.of_forall fun n ↦ ?_⟩
    have hsub : ∑ k ∈ Icc 1 n, χ k = if 1 ≤ n then χ 1 else 0 := by
      split_ifs with hn
      · rw [← sum_erase_add (Icc 1 n) _ (left_mem_Icc.mpr hn), sum_eq_zero, zero_add, Nat.cast_one]
        intro k hk
        rw [mem_erase, mem_Icc] at hk
        exact MulChar.map_nonunit χ fun hu ↦ by
          rcases Int.isUnit_iff.mp (show IsUnit (k : ℤ) from hu) with h | h <;> omega
      · rw [Icc_eq_empty hn, sum_empty]
    split_ifs at hsub <;> simp [hsub]
  · have : NeZero N := ⟨hN.ne'⟩
    refine isBigO_iff.mpr ⟨N, Eventually.of_forall fun n ↦ ?_⟩
    simpa using χ.norm_sum_Icc_le_level hχ n

omit [NeZero N] in
/-- The integral representing `L'(s, χ)` converges absolutely on the half-plane `Re(s) > 0`. -/
theorem integrableOn_sum_mul_one_sub_mul_log_mul_cpow (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1)))
      (Set.Ioi 1) := by
  have h1 := TauCeti.LSeries.integrableOn_sum_mul_cpow_of_isBigO _ (χ.sum_isBigO_one' hχ) hs
  have h2 := (TauCeti.LSeries.integrableOn_sum_mul_log_mul_cpow_of_isBigO _
    (χ.sum_isBigO_one' hχ) hs).const_mul s
  refine (h1.sub h2).congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  dsimp only [Pi.sub_apply]
  ring

/-- Partial summation gives the derivative of the continued L-function of a nonprincipal character
on the whole half-plane `Re(s) > 0`. -/
theorem hasDerivAt_LFunction_of_re_pos (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt χ.LFunction
      (∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1))) s := by
  have hderiv := TauCeti.LSeries.hasDerivAt_mul_integral_of_isBigO _ (χ.sum_isBigO_one' hχ) hs
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

omit [NeZero N] χ in
/-- Summation by parts on `1 ≤ k ≤ n`: pairing partial sums against forward differences leaves a
boundary term at `n` minus the weighted sum. -/
private theorem sum_Ico_sum_Icc_mul_sub (a g : ℕ → ℂ) (n : ℕ) :
    ∑ m ∈ Ico 1 n, (∑ k ∈ Icc 1 m, a k) * (g (m + 1) - g m) =
      (∑ k ∈ Icc 1 n, a k) * g n - ∑ k ∈ Icc 1 n, a k * g k := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  clear hn0
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [sum_Ico_succ_top hm, ih, sum_Icc_succ_top (Nat.le_add_right_of_le hm),
      sum_Icc_succ_top (Nat.le_add_right_of_le hm)]
    ring

omit [NeZero N] in
/-- Integrating a smooth derivative `g'` against the partial-sum step function on `(1, n]` gives
the discrete forward-difference sum over `1 ≤ m < n`. -/
private theorem integral_Ioc_one_natCast_sum_mul_eq {g g' : ℝ → ℂ}
    (hg : ∀ t : ℝ, 1 ≤ t → HasDerivAt g (g' t) t) (hcont : ContinuousOn g' (Set.Ici 1))
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ t in Set.Ioc (1 : ℝ) (n : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * g' t =
      ∑ m ∈ Ico 1 n, (∑ k ∈ Icc 1 m, χ k) * (g (m + 1 : ℕ) - g (m : ℕ)) := by
  have hint_step (m : ℕ) :
      IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * g' t) (Set.Ioc 1 (m : ℝ)) := by
    have hloc : IntegrableOn (fun t : ℝ ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, χ k) (Set.Icc 1 (m : ℝ)) :=
      (TauCeti.locallyIntegrableOn_sum_Icc_natFloor (fun k ↦ χ k) 1).integrableOn_compact_subset
        (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr zero_le_one)) isCompact_Icc
    exact (hloc.mul_continuousOn (hcont.mono Set.Icc_subset_Ici_self) isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hm1 : (1 : ℝ) ≤ m := mod_cast hm
    have hunit : ∫ t in Set.Ioc (m : ℝ) (m + 1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * g' t =
        (∑ k ∈ Icc 1 m, χ k) * (g (m + 1 : ℕ) - g (m : ℕ)) := by
      have hcongr : Set.EqOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * g' t)
          (fun t : ℝ ↦ (∑ k ∈ Icc 1 m, χ k) * g' t) (Set.Ioo (m : ℝ) (m + 1 : ℝ)) := by
        intro t ht
        have hfl : ⌊t⌋₊ = m :=
          (Nat.floor_eq_iff (by linarith [ht.1])).mpr ⟨ht.1.le, ht.2⟩
        simp [hfl]
      rw [integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo hcongr,
        ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht ↦ hg t (hm1.trans (by rw [Set.uIcc_of_le (by linarith)] at ht; exact ht.1)))
          ((hcont.mono (by rw [Set.uIcc_of_le (by linarith)]; exact fun t ht ↦ hm1.trans ht.1)
            ).intervalIntegrable), Nat.cast_add, Nat.cast_one]
    rw [Nat.cast_add, Nat.cast_one, ← Set.Ioc_union_Ioc_eq_Ioc hm1 (by linarith),
      setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc (hint_step m)
        ((hint_step (m + 1)).mono_set
          (by rw [Nat.cast_add, Nat.cast_one]; exact Set.Ioc_subset_Ioc_left hm1)),
      ih, hunit, sum_Ico_succ_top hm]

omit [NeZero N] χ in
/-- Antiderivative of `(t : ℂ) ^ (-(s + 1))` on `(0, ∞)` for `s ≠ 0`. -/
private theorem hasDerivAt_neg_cpow_div {s : ℂ} (hs : s ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ ↦ -(y : ℂ) ^ (-s) / s) ((t : ℂ) ^ (-(s + 1))) t := by
  have h1 := ((hasDerivAt_ofReal_cpow_const ht.ne' (neg_ne_zero.mpr hs)).neg).div_const s
  refine h1.congr_deriv ?_
  have hsub : -s - 1 = -(s + 1) := by ring
  rw [hsub]
  field_simp [hs]

omit [NeZero N] χ in
/-- Antiderivative of `(1 - s * log t) * (t : ℂ) ^ (-(s + 1))` on `(0, ∞)`. -/
private theorem hasDerivAt_cpow_mul_log (s : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (-s) * Real.log y)
      ((1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1))) t := by
  have hlog : HasDerivAt (fun y : ℝ ↦ (Real.log y : ℂ)) ((t⁻¹ : ℝ) : ℂ) t :=
    (Real.hasDerivAt_log ht.ne').ofReal_comp
  rcases eq_or_ne s 0 with rfl | hs
  · simpa [cpow_neg_one] using hlog
  · have hpow := hasDerivAt_ofReal_cpow_const ht.ne' (neg_ne_zero.mpr hs)
    refine (hpow.mul hlog).congr_deriv ?_
    have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hinv : (t : ℂ) ^ (-s) * ((t⁻¹ : ℝ) : ℂ) = (t : ℂ) ^ (-s - 1) := by
      rw [ofReal_inv, ← cpow_neg_one, ← cpow_add _ _ htC, ← sub_eq_add_neg]
    have hsub : -s - 1 = -(s + 1) := by ring
    rw [hinv, hsub]
    ring

/-- **Level-split partial summation for `L(s, χ)`.** For a nonprincipal character `χ` of level `N`
and `Re(s) > 0`, `L(s, χ)` is the finite Dirichlet polynomial up to `N` plus `s` times the tail
integral over `(N, ∞)`. -/
theorem LFunction_eq_sum_Icc_add_mul_integral (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    χ.LFunction s = (∑ n ∈ Icc 1 N, χ n / (n : ℂ) ^ s) +
      s * ∫ t in Set.Ioi (N : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hN1 : 1 ≤ N := NeZero.one_le
  have hN1' : (1 : ℝ) ≤ N := mod_cast hN1
  have hint := TauCeti.LSeries.integrableOn_sum_mul_cpow_of_isBigO _ (χ.sum_isBigO_one' hχ) hs
  have hcont : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (-(s + 1))) (Set.Ici 1) := fun t ht ↦
    (continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  have hhead := χ.integral_Ioc_one_natCast_sum_mul_eq
    (g := fun y : ℝ ↦ -(y : ℂ) ^ (-s) / s)
    (fun t ht ↦ hasDerivAt_neg_cpow_div hs0 (zero_lt_one.trans_le ht)) hcont hN1
  simp only [ofReal_natCast] at hhead
  rw [sum_Ico_sum_Icc_mul_sub (g := fun n : ℕ ↦ -(n : ℂ) ^ (-s) / s),
    χ.sum_Icc_one_level_eq_zero hχ, zero_mul, zero_sub] at hhead
  rw [χ.LFunction_eq_mul_integral hχ hs, ← Set.Ioc_union_Ioi_eq_Ioi hN1',
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hN1')),
    mul_add, hhead, mul_neg, mul_sum, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  rw [cpow_neg, div_eq_mul_inv]
  field_simp [hs0]

/-- **Level-split partial summation for `L'(s, χ)`.** For a nonprincipal character `χ` of level `N`
and `Re(s) > 0`, `L'(s, χ)` is `-∑_{n=1}^N χ(n) (log n) n^{-s}` plus the tail integral over
`(N, ∞)`. -/
theorem deriv_LFunction_eq_neg_sum_Icc_add_integral (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    deriv χ.LFunction s = -(∑ n ∈ Icc 1 N, χ n * Real.log n / (n : ℂ) ^ s) +
      ∫ t in Set.Ioi (N : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1)) := by
  have hN1 : 1 ≤ N := NeZero.one_le
  have hN1' : (1 : ℝ) ≤ N := mod_cast hN1
  have hint := χ.integrableOn_sum_mul_one_sub_mul_log_mul_cpow hχ hs
  have hcont : ContinuousOn
      (fun t : ℝ ↦ (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1))) (Set.Ici 1) := by
    refine (continuousOn_const.sub (continuousOn_const.mul (continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun t ht ↦ (zero_lt_one.trans_le ht).ne')))).mul fun t ht ↦ ?_
    exact (continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  have hhead := χ.integral_Ioc_one_natCast_sum_mul_eq
    (g := fun y : ℝ ↦ (y : ℂ) ^ (-s) * Real.log y)
    (fun t ht ↦ hasDerivAt_cpow_mul_log s (zero_lt_one.trans_le ht)) hcont hN1
  simp only [ofReal_natCast, ← mul_assoc] at hhead
  rw [sum_Ico_sum_Icc_mul_sub (g := fun n : ℕ ↦ (n : ℂ) ^ (-s) * Real.log n),
    χ.sum_Icc_one_level_eq_zero hχ, zero_mul, zero_sub] at hhead
  rw [χ.deriv_LFunction_eq_integral hχ hs, ← Set.Ioc_union_Ioi_eq_Ioi hN1',
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hN1')),
    hhead]
  congr 2
  refine sum_congr rfl fun n _ ↦ ?_
  rw [cpow_neg, div_eq_mul_inv]
  ring

/-! ### Explicit bounds on `Re(s) > 0` and near `s = 1` -/

omit [NeZero N] χ in
private noncomputable def tailAntideriv (A σ t : ℝ) : ℝ :=
  -t ^ (-σ) * ((1 + A / σ) / σ + A / σ * Real.log t)

omit [NeZero N] χ in
private theorem hasDerivAt_tailAntideriv (A : ℝ) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    HasDerivAt (tailAntideriv A σ) ((1 + A * Real.log t) * t ^ (-σ - 1)) t := by
  have h1 := (Real.hasDerivAt_rpow_const (p := -σ) (Or.inl ht.ne')).fun_neg
  have h2 := ((Real.hasDerivAt_log ht.ne').const_mul (A / σ)).const_add ((1 + A / σ) / σ)
  refine (h1.fun_mul h2).congr_deriv ?_
  have hinv : t ^ (-σ) * t⁻¹ = t ^ (-σ - 1) := by
    rw [Real.rpow_sub_one ht.ne', div_eq_mul_inv]
  have hmul : -t ^ (-σ) * (A / σ * t⁻¹) = -(A / σ) * (t ^ (-σ) * t⁻¹) := by ring
  rw [hmul, hinv]
  field_simp [hσ.ne']
  ring

omit [NeZero N] χ in
private theorem tendsto_tailAntideriv_atTop (A : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (tailAntideriv A σ) atTop (𝓝 0) := by
  have hpow : Tendsto (fun t : ℝ ↦ t ^ (-σ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hσ
  have hlog : Tendsto (fun t : ℝ ↦ t ^ (-σ) * Real.log t) atTop (𝓝 0) := by
    refine (isLittleO_log_rpow_atTop hσ).tendsto_div_nhds_zero.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.rpow_neg ht.le, div_eq_mul_inv, mul_comm]
  have hlin : Tendsto
      (fun t : ℝ ↦ -(t ^ (-σ) * ((1 + A / σ) / σ) + t ^ (-σ) * Real.log t * (A / σ)))
      atTop (𝓝 0) := by
    simpa using ((hpow.mul_const ((1 + A / σ) / σ)).add (hlog.mul_const (A / σ))).neg
  refine hlin.congr fun t ↦ ?_
  simp only [tailAntideriv]
  ring

omit [NeZero N] χ in
private theorem integrableOn_and_integral_tail {a A σ : ℝ} (ha : 1 ≤ a) (hA : 0 ≤ A)
    (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ ↦ (1 + A * Real.log t) * t ^ (-σ - 1)) (Set.Ioi a) ∧
      ∫ t in Set.Ioi a, (1 + A * Real.log t) * t ^ (-σ - 1) =
        a ^ (-σ) * ((1 + A / σ) / σ + A / σ * Real.log a) := by
  have hd : ∀ t ∈ Set.Ici a,
      HasDerivAt (tailAntideriv A σ) ((1 + A * Real.log t) * t ^ (-σ - 1)) t :=
    fun t ht ↦ hasDerivAt_tailAntideriv A hσ (zero_lt_one.trans_le (ha.trans ht))
  have hpos : ∀ t ∈ Set.Ioi a, 0 ≤ (1 + A * Real.log t) * t ^ (-σ - 1) := by
    intro t ht
    have ht1 : 1 ≤ t := ha.trans ht.le
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
    positivity
  have hlim := tendsto_tailAntideriv_atTop A hσ
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hlim]
  simp [tailAntideriv]

/-- **Explicit bound for `L'(s, χ)` on `Re(s) > 0`.** Splitting at the level `N` bounds `‖L'(s, χ)‖`
by the finite sum `∑_{n=1}^N (log n) n^{-Re(s)}` plus an explicit tail term of size `O(N^{1 - Re(s)}
log N)`. -/
theorem norm_deriv_LFunction_le_of_re_pos (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖deriv χ.LFunction s‖ ≤ (∑ n ∈ Icc 1 N, Real.log n * (n : ℝ) ^ (-s.re)) +
      (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ / s.re) / s.re + ‖s‖ / s.re * Real.log N) := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  obtain ⟨htail_int, htail_val⟩ := integrableOn_and_integral_tail hN1 (norm_nonneg s) hs
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

/-- **Explicit bound for `L'(σ, χ)` at real `σ > 0`.** For real `σ > 0`, `‖s‖ = Re(s) = σ`
simplifies the tail term to `N^{1 - σ} (log N + 2 / σ)`. -/
theorem norm_deriv_LFunction_ofReal_le_of_pos (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    ‖deriv χ.LFunction σ‖ ≤ (∑ n ∈ Icc 1 N, Real.log n * (n : ℝ) ^ (-σ)) +
      (N : ℝ) ^ (1 - σ) * (Real.log N + 2 / σ) := by
  refine (χ.norm_deriv_LFunction_le_of_re_pos hχ (s := σ) (by simpa using hσ)).trans_eq ?_
  simp only [ofReal_re, norm_real, Real.norm_of_nonneg hσ.le, div_self hσ.ne']
  ring

omit [NeZero N] χ in
/-- Using `H_n ≤ 1 + log n`, the finite sum `∑_{k=1}^n (log k) / k` is at most `(log n)²`. -/
private theorem sum_Icc_log_div_le_log_sq {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, Real.log k / (k : ℝ) ≤ Real.log n ^ 2 := by
  have hn' : (1 : ℝ) ≤ n := mod_cast hn
  have hsplit : ∑ k ∈ Icc 1 n, Real.log k / (k : ℝ) =
      ∑ k ∈ Ioc 1 n, Real.log k * (k : ℝ)⁻¹ := by
    rw [← Finset.sum_erase_add (Icc 1 n) _ (left_mem_Icc.mpr hn), Nat.cast_one, Real.log_one,
      zero_div, add_zero, Icc_erase_left]
    refine sum_congr rfl fun k _ ↦ div_eq_mul_inv _ _
  have hharm : ∑ k ∈ Ioc 1 n, (k : ℝ)⁻¹ ≤ Real.log n := by
    have hh := harmonic_le_one_add_log n
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
    rw [← Finset.sum_erase_add (Icc 1 n) _ (left_mem_Icc.mpr hn), Nat.cast_one, inv_one,
      Icc_erase_left] at hh
    linarith
  rw [hsplit]
  calc
    ∑ k ∈ Ioc 1 n, Real.log k * (k : ℝ)⁻¹
      ≤ ∑ k ∈ Ioc 1 n, Real.log n * (k : ℝ)⁻¹ := by
        refine sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hk' := mem_Ioc.mp hk
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k))
          (by exact_mod_cast hk'.2)
    _ = Real.log n * ∑ k ∈ Ioc 1 n, (k : ℝ)⁻¹ := (mul_sum _ _ _).symm
    _ ≤ Real.log n * Real.log n := mul_le_mul_of_nonneg_left hharm (Real.log_nonneg hn')
    _ = Real.log n ^ 2 := (sq _).symm

omit [NeZero N] χ in
/-- Numerical lower bound `23 / 21 < log n` for `3 ≤ n`, deduced from `exp 1 < 2.719` and
`2.719 ^ 23 < 3 ^ 21`. -/
private theorem div_lt_log_of_three_le {n : ℕ} (hn : 3 ≤ n) : (23 : ℝ) / 21 < Real.log n := by
  have hexp : Real.exp 23 < (n : ℝ) ^ (21 : ℕ) := by
    have h1 : Real.exp 1 < 2.719 := Real.exp_one_lt_d9.trans (by norm_num)
    have h23 : Real.exp 23 = Real.exp 1 ^ 23 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h23]
    calc
      Real.exp 1 ^ 23 < (2.719 : ℝ) ^ 23 := pow_lt_pow_left₀ h1 (Real.exp_nonneg _) (by decide)
      _ < (3 : ℝ) ^ 21 := by norm_num
      _ ≤ (n : ℝ) ^ 21 := pow_le_pow_left₀ (by positivity) (mod_cast hn) 21
  have hlog := Real.log_lt_log (Real.exp_pos 23) hexp
  rw [Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  linarith

omit [NeZero N] χ in
/-- On `σ ≥ 1 - 1 / log n` (`3 ≤ n`), `n^{-σ} ≤ exp 1 / n` bounds the initial sum
`∑_{k=1}^n (log k) k^{-σ}` by `e (log n)²`. -/
private theorem sum_Icc_log_mul_rpow_neg_le {n : ℕ} (hn : 3 ≤ n) {σ : ℝ}
    (hσ : 1 - 1 / Real.log n ≤ σ) :
    ∑ k ∈ Icc 1 n, Real.log k * (k : ℝ) ^ (-σ) ≤ Real.exp 1 * Real.log n ^ 2 := by
  have hlog_pos : 0 < Real.log n := lt_trans (by norm_num) (div_lt_log_of_three_le hn)
  have hnpow : (n : ℝ) ^ (1 / Real.log n) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < n)),
      mul_one_div_cancel hlog_pos.ne']
  calc
    ∑ k ∈ Icc 1 n, Real.log k * (k : ℝ) ^ (-σ)
      ≤ ∑ k ∈ Icc 1 n, Real.exp 1 * (Real.log k / k) := by
        refine sum_le_sum fun k hk ↦ ?_
        have hk1 : (1 : ℝ) ≤ k := mod_cast (mem_Icc.mp hk).1
        have hkn : (k : ℝ) ≤ n := mod_cast (mem_Icc.mp hk).2
        have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
        have hrpow : (k : ℝ) ^ (-σ) ≤ Real.exp 1 / k := by
          calc
            (k : ℝ) ^ (-σ) ≤ (k : ℝ) ^ (-1 + 1 / Real.log n) :=
              Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
            _ = (k : ℝ) ^ (-1 : ℝ) * (k : ℝ) ^ (1 / Real.log n) := Real.rpow_add hk0 _ _
            _ ≤ (k : ℝ)⁻¹ * (n : ℝ) ^ (1 / Real.log n) := by
              rw [Real.rpow_neg_one]
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow hk0.le hkn (by positivity)) (by positivity)
            _ = Real.exp 1 / k := by rw [hnpow, div_eq_mul_inv, mul_comm]
        calc
          Real.log k * (k : ℝ) ^ (-σ) ≤ Real.log k * (Real.exp 1 / k) :=
            mul_le_mul_of_nonneg_left hrpow (Real.log_nonneg hk1)
          _ = Real.exp 1 * (Real.log k / k) := by ring
    _ = Real.exp 1 * ∑ k ∈ Icc 1 n, Real.log k / (k : ℝ) := (mul_sum _ _ _).symm
    _ ≤ Real.exp 1 * Real.log n ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_Icc_log_div_le_log_sq (by omega)) (Real.exp_nonneg 1)

/-- **Near-one derivative bound for `L(s, χ)`.** For a nonprincipal character `χ` of level `N` and
every real `σ ≥ 1 - 1 / log N`, `‖L'(σ, χ)‖ ≤ 64 (log N)²`. No upper bound on `σ` and no
primitivity hypothesis are required. -/
theorem norm_deriv_LFunction_le_of_one_sub_inv_log_le (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 - 1 / Real.log N ≤ σ) :
    ‖deriv χ.LFunction σ‖ ≤ 64 * Real.log N ^ 2 := by
  have hN3 : 3 ≤ N := χ.three_le_level_of_ne_one hχ
  have hlog : (23 : ℝ) / 21 < Real.log N := div_lt_log_of_three_le hN3
  have hlog_pos : 0 < Real.log N := by linarith
  have hinv : 1 / Real.log N < 21 / 23 := by
    rw [div_lt_div_iff₀ hlog_pos (by norm_num)]
    linarith
  have hσ_lo : (2 : ℝ) / 23 < σ := by linarith
  have hσ_pos : 0 < σ := by linarith
  have hexp1 : Real.exp 1 < 2.719 := Real.exp_one_lt_d9.trans (by norm_num)
  have hNpow : (N : ℝ) ^ (1 / Real.log N) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < N)),
      mul_one_div_cancel hlog_pos.ne']
  have hsum := sum_Icc_log_mul_rpow_neg_le hN3 hσ
  have htail : (N : ℝ) ^ (1 - σ) * (Real.log N + 2 / σ) ≤ 22 * Real.exp 1 * Real.log N ^ 2 := by
    have h1 : (N : ℝ) ^ (1 - σ) ≤ Real.exp 1 := by
      rw [← hNpow]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by linarith)
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
  nlinarith [sq_nonneg (Real.log N)]

/-- **Lipschitz bound for `L(σ, χ)` near and above `1`.** On `[1 - 1 / log N, ∞)`, the continued
L-function of a nonprincipal character satisfies
`‖L(σ₂, χ) - L(σ₁, χ)‖ ≤ 64 (log N)² |σ₂ - σ₁|`. -/
theorem norm_LFunction_sub_le_of_one_sub_inv_log_le (hχ : χ ≠ 1) {σ₁ σ₂ : ℝ}
    (h₁ : 1 - 1 / Real.log N ≤ σ₁) (h₂ : 1 - 1 / Real.log N ≤ σ₂) :
    ‖χ.LFunction σ₂ - χ.LFunction σ₁‖ ≤ 64 * Real.log N ^ 2 * |σ₂ - σ₁| := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ ↦ χ.LFunction t) (deriv χ.LFunction x) x := fun x ↦
    (χ.differentiable_LFunction hχ).differentiableAt.hasDerivAt.comp_ofReal
  have hb : ∀ x ∈ Set.uIcc σ₁ σ₂, ‖deriv (fun t : ℝ ↦ χ.LFunction t) x‖ ≤
      64 * Real.log N ^ 2 := by
    intro x hx
    rw [(hd x).deriv]
    exact χ.norm_deriv_LFunction_le_of_one_sub_inv_log_le hχ ((le_min h₁ h₂).trans hx.1)
  simpa only [Real.norm_eq_abs] using (convex_uIcc σ₁ σ₂).norm_image_sub_le_of_norm_deriv_le
    (fun x _ ↦ (hd x).differentiableAt) hb Set.left_mem_uIcc Set.right_mem_uIcc

/-- **Zero-separation bound from `L(1, χ)`.** For any nonprincipal character `χ` of level `N` and
any real zero `β` of `L(s, χ)`, `‖L(1, χ)‖ / (64 (log N)²) ≤ 1 - β`. No preliminary interval
assumption on `β` is needed: `L(s, χ) ≠ 0` for `Re(s) ≥ 1` forces `β < 1`, and for
`β < 1 - 1 / log N` the bound `‖L(1, χ)‖ ≤ 1 + log N` already makes the left-hand side smaller than
`1 / log N`. -/
theorem norm_LFunction_one_div_log_sq_le_one_sub_of_LFunction_eq_zero (hχ : χ ≠ 1) {β : ℝ}
    (hβ : χ.LFunction β = 0) :
    ‖χ.LFunction 1‖ / (64 * Real.log N ^ 2) ≤ 1 - β := by
  have hlog : (23 : ℝ) / 21 < Real.log N := div_lt_log_of_three_le (χ.three_le_level_of_ne_one hχ)
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
    have hlip := χ.norm_LFunction_sub_le_of_one_sub_inv_log_le hχ hnear h1_mem
    rw [ofReal_one, hβ, sub_zero, abs_of_pos (sub_pos.mpr hβ1)] at hlip
    rw [div_le_iff₀ (by positivity)]
    linarith

end DirichletCharacter
