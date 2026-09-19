/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Ordinary convergence of a Dirichlet series, and its abscissa

Mathlib measures a Dirichlet series only through `LSeriesSummable`, which in `ℂ` is absolute
convergence, and through the resulting `LSeries.abscissaOfAbsConv`.  A Dirichlet series can
converge without converging absolutely, so the classical theory carries a second abscissa, lying
to the left of the first.

`TauCeti.LSeriesConverges f s` says that the partial sums `∑_{n < N} f n / n ^ s` tend to a limit
as `N → ∞`, the index being summed in its natural order, and `TauCeti.LSeries.abscissaOfConv f` is
the infimum of the real points at which they do.  Abel summation bounds that abscissa by any
exponent controlling the partial sums of the coefficients, and in particular turns ordinary
convergence at one point into ordinary convergence at every point further to the right; so this
infimum is again the edge of a half-plane of convergence, and the two abscissae satisfy
`σ_c ≤ σ_a ≤ σ_c + 1`.

The alternating coefficients `(-1) ^ n` show that the first inequality can be strict: their
partial sums are bounded, so `σ_c ≤ 0`, while `σ_a = 1`.  For nonnegative coefficients, on the
other hand, the two abscissae agree, because at a real point the terms are then nonnegative reals,
for which bounded partial sums and summability are the same condition.  This is the case a
Landau-type singularity argument works in, so for such a series it does not matter which of the
two abscissae is named.

## Main results

* `TauCeti.LSeriesConverges_of_sum_isBigO`: partial sums of the coefficients that are `O(n ^ r)`
  give ordinary convergence on `Re s > r`.
* `TauCeti.LSeriesConverges.of_re_lt_re`: ordinary convergence at `s` gives ordinary convergence
  at every `s'` with `s.re < s'.re`, and
  `TauCeti.LSeriesConverges_of_abscissaOfConv_lt_re`: the series converges on the open half-plane
  to the right of `TauCeti.LSeries.abscissaOfConv`.
* `TauCeti.LSeries.abscissaOfConv_le_of_sum_isBigO`: the same bound read off as an inequality
  between the exponent and the abscissa.
* `TauCeti.LSeries.abscissaOfConv_le_abscissaOfAbsConv` and
  `TauCeti.LSeries.abscissaOfAbsConv_le_abscissaOfConv_add_one`: the classical comparisons
  `σ_c ≤ σ_a ≤ σ_c + 1`.
* `TauCeti.LSeries.abscissaOfConv_lt_abscissaOfAbsConv_neg_one_pow`: the two abscissae are
  different for the alternating coefficients.
* `TauCeti.LSeries.abscissaOfConv_eq_abscissaOfAbsConv_of_nonneg`: for nonnegative coefficients
  they are equal, ordinary convergence at a real point being absolute there
  (`TauCeti.lSeriesConverges_iff_lSeriesSummable_of_nonneg`).

## References

* [G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*][tenenbaum1995],
  Chapter II.1.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §2.

The statements and their proofs are modelled on Mathlib's treatment of the abscissa of absolute
convergence in `Mathlib/NumberTheory/LSeries/Convergence.lean`; the reduction of a coefficient
sequence to one vanishing at `0` is the device used by `LSeriesSummable_of_sum_norm_bigO` in
`Mathlib/NumberTheory/LSeries/SumCoeff.lean`.
-/

public section

namespace TauCeti

open Complex Filter Finset MeasureTheory
open scoped ComplexOrder Topology

variable {f : ℕ → ℂ} {s s' : ℂ}

/-- **Ordinary convergence of a Dirichlet series.**  The partial sums `∑_{n < N} f n / n ^ s`,
taken in the natural order of the index, tend to a limit.

This is weaker than `LSeriesSummable f s`, which in `ℂ` amounts to absolute convergence. -/
def LSeriesConverges (f : ℕ → ℂ) (s : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (fun N ↦ ∑ n ∈ range N, LSeries.term f s n) atTop (𝓝 L)

/-- Ordinary convergence is unchanged when the terms of two Dirichlet series agree pointwise. -/
theorem LSeriesConverges.congr {g : ℕ → ℂ}
    (h : ∀ n, LSeries.term f s n = LSeries.term g s n) :
    LSeriesConverges f s ↔ LSeriesConverges g s := by
  unfold LSeriesConverges
  simp_rw [h]

/-- An absolutely convergent Dirichlet series converges. -/
theorem lSeriesConverges_of_lSeriesSummable (h : LSeriesSummable f s) : LSeriesConverges f s :=
  ⟨_, h.hasSum.tendsto_sum_nat⟩

/-- Ordinary convergence depends only on the terms, so replacing the meaningless value `f 0` by
zero changes nothing.  Abel summation needs the sequence it sums to vanish at `0`. -/
private theorem lSeriesConverges_ite_iff :
    LSeriesConverges (fun n ↦ if n = 0 then 0 else f n) s ↔ LSeriesConverges f s := by
  have h : ∀ n, LSeries.term (fun n ↦ if n = 0 then 0 else f n) s n = LSeries.term f s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn]
  exact LSeriesConverges.congr h

/-- The Abel-summation core of `TauCeti.LSeriesConverges_of_sum_isBigO`, for a sequence already
vanishing at `0`. -/
private theorem lSeriesConverges_of_sum_isBigO_aux (hf : f 0 = 0) {r : ℝ}
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ r)
    (hs : r < s.re) : LSeriesConverges f s := by
  set g : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-s) with hg
  -- The multiplier is differentiable away from the origin, with the expected derivative.
  have hderiv : ∀ t : ℝ, t ≠ 0 → HasDerivAt g (-s * (t : ℂ) ^ (-s - 1)) t := by
    intro t ht
    rcases eq_or_ne s 0 with rfl | hs0
    · simpa [hg] using hasDerivAt_const (x := t) (c := (1 : ℂ))
    · exact hasDerivAt_ofReal_cpow_const ht (neg_ne_zero.mpr hs0)
  have hg_diff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ g t := fun t ht ↦
    (hderiv t (zero_lt_one.trans_le ht).ne').differentiableAt
  have hderiv' : ∀ t : ℝ, t ≠ 0 → deriv g t = -s * (t : ℂ) ^ (-s - 1) := fun t ht ↦
    (hderiv t ht).deriv
  have hg_int : LocallyIntegrableOn (deriv g) (Set.Ici 1) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
    refine ContinuousOn.congr (f := fun t : ℝ ↦ -s * (t : ℂ) ^ (-s - 1)) ?_
      fun t ht ↦ hderiv' t (zero_lt_one.trans_le ht).ne'
    exact fun t ht ↦ (continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const t (-s - 1)
        (Or.inr (zero_lt_one.trans_le ht).ne'))).continuousWithinAt
  have hnorm_g : ∀ t : ℝ, 0 < t → ‖g t‖ = t ^ (-s.re) := fun t ht ↦ by
    rw [hg, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.neg_re]
  -- A nonnegative constant in the hypothesis on the partial sums.
  obtain ⟨C, hC0, hCw⟩ := hO.exists_nonneg
  have hC : ∀ᶠ n : ℕ in atTop, ‖∑ k ∈ Icc 0 n, f k‖ ≤ C * (n : ℝ) ^ r := by
    filter_upwards [hCw.bound] with n hn
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r)] at hn
  -- The boundary term of Abel summation tends to zero, since `Re s > r`.
  have h_lim : Tendsto (fun n : ℕ ↦ g n * ∑ k ∈ Icc 0 n, f k) atTop (𝓝 0) := by
    have hz : Tendsto (fun n : ℕ ↦ C * (n : ℝ) ^ (-(s.re - r))) atTop (𝓝 0) := by
      simpa using (((tendsto_rpow_neg_atTop (by linarith : 0 < s.re - r)).comp
        tendsto_natCast_atTop_atTop).const_mul C)
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [hC, eventually_gt_atTop 0] with n hn hn0
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [norm_mul, hnorm_g n hn0']
    calc (n : ℝ) ^ (-s.re) * ‖∑ k ∈ Icc 0 n, f k‖
        ≤ (n : ℝ) ^ (-s.re) * (C * (n : ℝ) ^ r) := by gcongr
      _ = C * (n : ℝ) ^ (-(s.re - r)) := by
          have hexp : -(s.re - r) = -s.re + r := by ring
          rw [hexp, Real.rpow_add hn0']
          ring
  -- The integrand of Abel summation has an integrable majorant.
  have hg_dom : (fun t ↦ deriv g t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =O[atTop]
      fun t : ℝ ↦ t ^ (r - s.re - 1) := by
    have hderivO : (fun t : ℝ ↦ deriv g t) =O[atTop] fun t : ℝ ↦ t ^ (-s.re - 1) := by
      refine Asymptotics.IsBigO.of_bound ‖s‖ ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [hderiv' t ht.ne', norm_mul, norm_neg,
        Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.neg_re, Complex.one_re,
        Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
    have hsumO : (fun t : ℝ ↦ ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =O[atTop]
        fun t : ℝ ↦ t ^ r := by
      have hfloor : Asymptotics.IsEquivalent atTop (fun t : ℝ ↦ (⌊t⌋₊ : ℝ))
          (fun t ↦ max t 0) :=
        Asymptotics.isEquivalent_nat_floor.congr_right
          ((eventually_ge_atTop (0 : ℝ)).mono fun t ht ↦ (max_eq_left ht).symm)
      refine (hO.comp_tendsto tendsto_nat_floor_atTop).trans
        ((hfloor.rpow fun t ↦ le_max_right t 0).isBigO.congr' EventuallyEq.rfl ?_)
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simp [max_eq_left ht]
    refine (hderivO.mul hsumO).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hg_int' : IntegrableAtFilter (fun t : ℝ ↦ t ^ (r - s.re - 1)) atTop :=
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one⟩
  have key := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ f hf
    hg_diff hg_int h_lim hg_dom hg_int'
  -- Read the conclusion back as the partial sums of the Dirichlet series.
  have hpt : ∀ k : ℕ, g k * f k = LSeries.term f s k := fun k ↦ by
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hf]
    · simp only [hg, Complex.ofReal_natCast, LSeries.term_of_ne_zero hk, Complex.cpow_neg,
        div_eq_inv_mul]
  have final : Tendsto (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, LSeries.term f s k) atTop
      (𝓝 (0 - ∫ t in Set.Ioi 1, deriv g t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k)) :=
    key.congr fun n ↦ Finset.sum_congr rfl fun k _ ↦ hpt k
  exact ⟨_, (tendsto_add_atTop_iff_nat 1).mp
    (by simpa only [Nat.range_succ_eq_Icc_zero] using final)⟩

/-- **Ordinary convergence from a bound on the partial sums of the coefficients.**  If
`∑_{1 ≤ k ≤ n} f k` is `O(n ^ r)`, then the Dirichlet series of `f` converges at
every `s` with `Re s > r`.

This is the criterion that produces a half-plane of ordinary convergence.  Abel summation against
the multiplier `t ↦ t ^ (-s)` turns the partial sums into a boundary term, which tends to `0`
because `Re s > r`, plus an integral whose integrand is dominated by the integrable majorant
`t ^ (r - Re s - 1)`. -/
theorem LSeriesConverges_of_sum_isBigO {r : ℝ}
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ r)
    (hs : r < s.re) : LSeriesConverges f s := by
  rw [← lSeriesConverges_ite_iff]
  have hsum : ∀ n : ℕ,
      ∑ k ∈ Icc 0 n, (if k = 0 then 0 else f k) = ∑ k ∈ Icc 1 n, f k := fun n ↦ by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le n),
      Finset.sum_insert (by simp)]
    simp only [reduceIte, zero_add]
    exact Finset.sum_congr rfl fun k hk ↦
      ite_eq_right (by have := (Finset.mem_Icc.mp hk).1; omega)
  exact lSeriesConverges_of_sum_isBigO_aux (by simp)
    (hO.congr' (.of_forall fun n ↦ (hsum n).symm) EventuallyEq.rfl) hs

/-- Iterating the Dirichlet term: dividing the terms at `s` by `n ^ (s' - s)` gives the terms
at `s'`. -/
@[simp] theorem LSeries.term_term_sub (f : ℕ → ℂ) (s s' : ℂ) (n : ℕ) :
    LSeries.term (LSeries.term f s) (s' - s) n = LSeries.term f s' n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hns : (n : ℂ) ^ s ≠ 0 := fun h ↦ hn' ((Complex.cpow_eq_zero_iff _ _).mp h).1
    have hns' : (n : ℂ) ^ s' ≠ 0 := fun h ↦ hn' ((Complex.cpow_eq_zero_iff _ _).mp h).1
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_sub _ _ hn']
    field_simp

/-- **A Dirichlet series converges on a half-plane.**  Ordinary convergence at `s` forces ordinary
convergence at every point strictly to the right of `s`: the partial sums of the terms at `s` are
bounded, which is `TauCeti.LSeriesConverges_of_sum_isBigO` with exponent `0`. -/
theorem LSeriesConverges.of_re_lt_re (h : LSeriesConverges f s) (hs : s.re < s'.re) :
    LSeriesConverges f s' := by
  obtain ⟨L, hL⟩ := h
  have hIcc : Tendsto (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, LSeries.term f s k) atTop (𝓝 L) := by
    simpa only [Nat.range_succ_eq_Icc_zero] using (tendsto_add_atTop_iff_nat 1).mpr hL
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ n : ℕ, ‖∑ k ∈ Icc 0 n, LSeries.term f s k‖ ≤ M := by
    obtain ⟨M, hM⟩ := hIcc.norm.bddAbove_range
    exact ⟨M, fun n ↦ hM ⟨n, rfl⟩⟩
  have hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, LSeries.term f s k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound M (.of_forall fun n ↦ ?_)
    rw [Real.rpow_zero, norm_one, mul_one]
    have hsum : ∑ k ∈ Icc 1 n, LSeries.term f s k =
        ∑ k ∈ Icc 0 n, LSeries.term f s k := by
      rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le n),
        Finset.sum_insert (by simp), LSeries.term_zero, zero_add]
      simp only [zero_add]
    rw [hsum]
    exact hM n
  obtain ⟨L', hL'⟩ := LSeriesConverges_of_sum_isBigO (s := s' - s) hO
    (by simpa using sub_pos.mpr hs)
  exact ⟨L', by simpa only [LSeries.term_term_sub] using hL'⟩

/-- **The abscissa of ordinary convergence** of the L-series of `f`: the infimum of the real
points at which the partial sums of the series converge.  The series converges at every `s` with
`Re s` above it (`TauCeti.LSeriesConverges_of_abscissaOfConv_lt_re`), and it lies below the
abscissa of absolute convergence. -/
noncomputable def LSeries.abscissaOfConv (f : ℕ → ℂ) : EReal :=
  sInf <| Real.toEReal '' {x : ℝ | LSeriesConverges f x}

namespace LSeries

/-- The abscissa of ordinary convergence depends only on the coefficients away from zero. -/
theorem abscissaOfConv_congr {g : ℕ → ℂ} (h : ∀ {n}, n ≠ 0 → f n = g n) :
    abscissaOfConv f = abscissaOfConv g :=
  congrArg sInf <| congrArg _ <| Set.ext fun _ ↦ LSeriesConverges.congr fun n ↦ by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [LSeries.term_of_ne_zero hn, h hn]

/-- If the series converges at every real point above `x`, its abscissa of ordinary convergence is
at most `x`. -/
theorem abscissaOfConv_le_of_forall_lt_LSeriesConverges {x : ℝ}
    (h : ∀ y : ℝ, x < y → LSeriesConverges f y) : abscissaOfConv f ≤ x := by
  refine sInf_le_iff.mpr fun y hy ↦ le_of_forall_gt_imp_ge_of_dense fun a ↦ ?_
  replace hy : ∀ a : ℝ, LSeriesConverges f a → y ≤ a := by
    simpa [abscissaOfConv, mem_lowerBounds] using hy
  cases a with
  | coe a₀ => exact_mod_cast fun ha ↦ hy a₀ (h a₀ ha)
  | bot => simp
  | top => simp

/-- **The ordinary abscissa lies to the left of the absolute one.** -/
theorem abscissaOfConv_le_abscissaOfAbsConv (f : ℕ → ℂ) :
    abscissaOfConv f ≤ _root_.LSeries.abscissaOfAbsConv f :=
  sInf_le_sInf <| Set.image_mono fun _ hx ↦ lSeriesConverges_of_lSeriesSummable hx

/-- Partial sums of the coefficients that are `O(n ^ r)` bound the abscissa of ordinary
convergence by `r`. -/
theorem abscissaOfConv_le_of_sum_isBigO {r : ℝ}
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ r) :
    abscissaOfConv f ≤ r :=
  abscissaOfConv_le_of_forall_lt_LSeriesConverges fun _ hy ↦
    LSeriesConverges_of_sum_isBigO hO (by simpa using hy)

end LSeries

/-- A Dirichlet series converges at every point strictly to the right of its abscissa of ordinary
convergence. -/
theorem LSeriesConverges_of_abscissaOfConv_lt_re
    (hs : LSeries.abscissaOfConv f < s.re) : LSeriesConverges f s := by
  obtain ⟨y, hy, hys⟩ : ∃ y : ℝ, LSeriesConverges f y ∧ y < s.re := by
    simpa [LSeries.abscissaOfConv, sInf_lt_iff] using hs
  exact hy.of_re_lt_re (by simpa using hys)

/-- Ordinary convergence at `s` bounds the abscissa of ordinary convergence by `Re s`. -/
theorem LSeriesConverges.abscissaOfConv_le (h : LSeriesConverges f s) :
    LSeries.abscissaOfConv f ≤ s.re :=
  LSeries.abscissaOfConv_le_of_forall_lt_LSeriesConverges fun _ hy ↦
    h.of_re_lt_re (by simpa using hy)

namespace LSeries

/-- **The two abscissae differ by at most one.**  Where the series converges its terms are
bounded, so `‖f n‖ = O(n ^ x)` for every real `x` above the ordinary abscissa. -/
theorem abscissaOfAbsConv_le_abscissaOfConv_add_one (f : ℕ → ℂ) :
    _root_.LSeries.abscissaOfAbsConv f ≤ abscissaOfConv f + 1 := by
  refine _root_.LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy ↦ ?_
  obtain ⟨z, hz₁, hz₂⟩ := EReal.exists_between_coe_real hy
  have hz₂' : z < y := by exact_mod_cast hz₂
  -- The series converges ordinarily at `z - 1`, so its terms there are bounded.
  have hlt : abscissaOfConv f < ((z - 1 : ℝ) : EReal) := by
    by_contra hcon
    refine absurd hz₁ (not_lt.mpr ?_)
    have hz_eq : (z : EReal) = ((z - 1 : ℝ) : EReal) + 1 := by
      rw [← EReal.coe_one, ← EReal.coe_add]
      norm_num
    calc (z : EReal) = ((z - 1 : ℝ) : EReal) + 1 := hz_eq
      _ ≤ abscissaOfConv f + 1 := add_le_add (not_lt.mp hcon) le_rfl
  obtain ⟨L, hL⟩ := LSeriesConverges_of_abscissaOfConv_lt_re
    (s := ((z - 1 : ℝ) : ℂ)) (by simpa using hlt)
  have hterm : Tendsto (LSeries.term f ((z - 1 : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h := (hL.comp (tendsto_add_atTop_nat 1)).sub hL
    rw [sub_self] at h
    exact h.congr fun N ↦ by simp [Finset.sum_range_succ]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ n : ℕ, ‖LSeries.term f ((z - 1 : ℝ) : ℂ) n‖ ≤ C := by
    obtain ⟨C, hC⟩ := hterm.norm.bddAbove_range
    exact ⟨C, fun n ↦ hC ⟨n, rfl⟩⟩
  refine LSeriesSummable_of_le_const_mul_rpow (x := z) (by simpa using hz₂')
    ⟨C, fun n hn ↦ ?_⟩
  have hn0 : (0 : ℝ) < n := by positivity
  have hbd := hC n
  rw [LSeries.term_of_ne_zero hn, norm_div, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.ofReal_re,
    div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)] at hbd
  linarith [hbd]

end LSeries

/-! ### Alternating coefficients: the two abscissae can differ -/

namespace LSeries

/-- The alternating coefficients have bounded partial sums, so their Dirichlet series converges
for `Re s > 0`. -/
theorem abscissaOfConv_neg_one_pow_le_zero :
    abscissaOfConv (fun n ↦ (-1 : ℂ) ^ n) ≤ 0 := by
  have hsum : ∀ n : ℕ, ‖∑ k ∈ Icc 1 n, (-1 : ℂ) ^ k‖ ≤ 1 := by
    intro n
    have h : ∑ k ∈ Icc 1 n, (-1 : ℂ) ^ k = (∑ k ∈ range (n + 1), (-1 : ℂ) ^ k) - 1 := by
      rw [Nat.range_succ_eq_Icc_zero,
        ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le n),
        Finset.sum_insert (by simp)]
      simp
    rw [h, neg_one_geom_sum]
    split_ifs <;> simp
  have h := abscissaOfConv_le_of_sum_isBigO (f := fun n ↦ (-1 : ℂ) ^ n) (r := 0)
    (Asymptotics.IsBigO.of_bound 1 (.of_forall fun n ↦ by simpa using hsum n))
  exact_mod_cast h

/-- The alternating coefficients have modulus one, so their Dirichlet series converges absolutely
exactly where the Riemann zeta series does. -/
theorem abscissaOfAbsConv_neg_one_pow :
    _root_.LSeries.abscissaOfAbsConv (fun n ↦ (-1 : ℂ) ^ n) = 1 := by
  have h : ∀ x : ℝ, LSeriesSummable (fun n ↦ (-1 : ℂ) ^ n) (x : ℂ) ↔
      LSeriesSummable (1 : ℕ → ℂ) (x : ℂ) := by
    intro x
    rw [LSeriesSummable, LSeriesSummable, ← summable_norm_iff,
      ← summable_norm_iff (f := LSeries.term (1 : ℕ → ℂ) (x : ℂ))]
    refine summable_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div]
      simp
  have habs : _root_.LSeries.abscissaOfAbsConv (fun n ↦ (-1 : ℂ) ^ n) =
      _root_.LSeries.abscissaOfAbsConv 1 :=
    congrArg sInf (congrArg _ (Set.ext fun x ↦ h x))
  rw [habs, _root_.LSeries.abscissaOfAbsConv_one]

/-- **The two abscissae can be different.**  For the alternating coefficients the ordinary
abscissa is at most `0` while the absolute one is `1`. -/
theorem abscissaOfConv_lt_abscissaOfAbsConv_neg_one_pow :
    abscissaOfConv (fun n ↦ (-1 : ℂ) ^ n) <
      _root_.LSeries.abscissaOfAbsConv (fun n ↦ (-1 : ℂ) ^ n) := by
  rw [abscissaOfAbsConv_neg_one_pow]
  exact abscissaOfConv_neg_one_pow_le_zero.trans_lt (by norm_num)

end LSeries

/-! ### Nonnegative coefficients -/

/-- **For coefficients nonnegative away from the ignored index zero, convergence at a real point
is absolute.**  The terms are then nonnegative reals, so their partial sums converge exactly when
they are bounded. -/
theorem lSeriesConverges_iff_lSeriesSummable_of_nonneg
    (ha : ∀ n, n ≠ 0 → 0 ≤ f n) (x : ℝ) :
    LSeriesConverges f (x : ℂ) ↔ LSeriesSummable f (x : ℂ) := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, lSeriesConverges_of_lSeriesSummable⟩
  set r : ℕ → ℝ := fun n ↦ ‖LSeries.term f (x : ℂ) n‖
  have hterm : ∀ n, ((r n : ℝ) : ℂ) = LSeries.term f (x : ℂ) n := fun n ↦ by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [r]
    · exact Complex.norm_of_nonneg' (LSeries.term_nonneg (ha n hn) x)
  have hsum : ∀ N : ℕ, ((∑ n ∈ range N, r n : ℝ) : ℂ) = ∑ n ∈ range N, LSeries.term f (x : ℂ) n :=
    fun N ↦ by rw [Complex.ofReal_sum]; exact Finset.sum_congr rfl fun n _ ↦ hterm n
  have hre : Tendsto (fun N ↦ ∑ n ∈ range N, r n) atTop (𝓝 L.re) := by
    refine ((Complex.continuous_re.tendsto L).comp hL).congr fun N ↦ ?_
    rw [Function.comp_apply, ← hsum N, Complex.ofReal_re]
  have hmono : Monotone fun N ↦ ∑ n ∈ range N, r n :=
    monotone_nat_of_le_succ fun N ↦ by
      rw [Finset.sum_range_succ]
      exact le_add_of_nonneg_right (norm_nonneg _)
  exact Summable.of_norm
    (summable_of_sum_range_le (fun _ ↦ norm_nonneg _) (hmono.ge_of_tendsto hre))

namespace LSeries

/-- **For coefficients nonnegative away from the ignored index zero the two abscissae agree.**
A Dirichlet series with nonnegative coefficients therefore has a single half-plane of convergence,
and the abscissa appearing in Landau's theorem is the ordinary one as well as the absolute one. -/
theorem abscissaOfConv_eq_abscissaOfAbsConv_of_nonneg (ha : ∀ n, n ≠ 0 → 0 ≤ f n) :
    abscissaOfConv f = _root_.LSeries.abscissaOfAbsConv f :=
  congrArg sInf (congrArg _
    (Set.ext fun x ↦ lSeriesConverges_iff_lSeriesSummable_of_nonneg ha x))

end LSeries

end TauCeti
