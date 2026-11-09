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
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.Asymptotics.Lemmas

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
* `TauCeti.LSeries.norm_sum_Icc_neg_one_pow_add_one_le`: the partial sums of the alternating
  coefficients `(-1) ^ (k + 1)` have norm at most `1`.
* `TauCeti.LSeries.abscissaOfConv_eq_abscissaOfAbsConv_of_nonneg`: for nonnegative coefficients
  they are equal, ordinary convergence at a real point being absolute there
  (`TauCeti.LSeriesConverges_iff_LSeriesSummable_of_nonneg`).

## References

* [G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*][tenenbaum1995],
  Chapter II.1.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §2.

The statements and their proofs are modelled on Mathlib's treatment of the abscissa of absolute
convergence in `Mathlib/NumberTheory/LSeries/Convergence.lean`; the reduction of a coefficient
sequence to one vanishing at `0` is the device used by `LSeriesSummable_of_sum_norm_bigO` in
`Mathlib/NumberTheory/LSeries/SumCoeff.lean`.
The Abel-summation proof of `TauCeti.LSeriesConverges_of_sum_isBigO` adapts the proof of
`LSeries_eq_mul_integral` in `Mathlib/NumberTheory/LSeries/SumCoeff.lean`, extended to arbitrary
real `r`.
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

/-- Ordinary convergence depends only on the coefficients away from the ignored index zero. -/
theorem LSeriesConverges_congr {g : ℕ → ℂ} (s : ℂ) (h : ∀ {n}, n ≠ 0 → f n = g n) :
    LSeriesConverges f s ↔ LSeriesConverges g s := by
  simp_rw [LSeriesConverges, LSeries.term_congr h s]

/-- An absolutely convergent Dirichlet series converges. -/
theorem _root_.LSeriesSummable.LSeriesConverges (h : LSeriesSummable f s) :
    LSeriesConverges f s :=
  ⟨_, h.hasSum.tendsto_sum_nat⟩

/-- The Abel-summation core of `TauCeti.LSeriesConverges_of_sum_isBigO`, for a sequence already
vanishing at `0`. -/
private theorem LSeriesConverges_of_sum_isBigO_aux (hf : f 0 = 0) {r : ℝ}
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ r)
    (hs : r < s.re) : LSeriesConverges f s := by
  set g : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-s) with hg
  -- The multiplier is differentiable away from the origin, with the expected derivative.
  have hderiv : ∀ t : ℝ, t ≠ 0 → HasDerivAt g (-s * (t : ℂ) ^ (-s - 1)) t := by
    intro t ht
    rcases eq_or_ne s 0 with rfl | hs0
    · simpa [hg] using hasDerivAt_const (x := t) (c := (1 : ℂ))
    · exact hasDerivAt_ofReal_cpow_const ht (neg_ne_zero.mpr hs0)
  have hg_int : LocallyIntegrableOn (deriv g) (Set.Ici 1) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
    refine ContinuousOn.congr (f := fun t : ℝ ↦ -s * (t : ℂ) ^ (-s - 1)) ?_
      fun t ht ↦ (hderiv t (zero_lt_one.trans_le ht).ne').deriv
    exact fun t ht ↦ (continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const t (-s - 1)
        (Or.inr (zero_lt_one.trans_le ht).ne'))).continuousWithinAt
  -- The boundary term of Abel summation tends to zero, since `Re s > r`.
  have h_lim : Tendsto (fun n : ℕ ↦ g n * ∑ k ∈ Icc 0 n, f k) atTop (𝓝 0) :=
    (Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-s.re) r _
      (Asymptotics.isBigO_norm_left.mp
        (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop) hO
      (by linarith : -s.re + r ≤ -(s.re - r))).trans_tendsto
      ((tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop)
  -- The partial sums along ⌊t⌋₊ are O(t ^ r), giving a bound for the Abel-summation integrand.
  have key := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ f hf
    (fun t ht ↦ (hderiv t (zero_lt_one.trans_le ht).ne').differentiableAt) hg_int h_lim
    ((isBigO_deriv_ofReal_cpow_const_atTop (-s)).mul_atTop_rpow_of_isBigO_rpow _ r
      (r - s.re - 1) hO.comp_natFloor_rpow (by rw [Complex.neg_re]; linarith))
    (integrableAtFilter_rpow_atTop_iff.mpr (by linarith))
  -- Read the conclusion back as the partial sums of the Dirichlet series.
  refine ⟨_, (tendsto_add_atTop_iff_nat 1).mp (key.congr fun n ↦ ?_)⟩
  rw [Nat.range_succ_eq_Icc_zero]
  exact Finset.sum_congr rfl fun k _ ↦ by simp [hg, LSeries.term_def₀ hf, mul_comm]

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
  -- Abel summation needs the coefficient at the ignored index `0` to vanish.
  have hsum (n : ℕ) : ∑ k ∈ Icc 0 n, (if k = 0 then 0 else f k) = ∑ k ∈ Icc 1 n, f k := by
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by simp)]
    simpa using sum_congr rfl fun k hk ↦ ite_eq_right (by grind)
  exact (LSeriesConverges_congr (f := fun n ↦ if n = 0 then 0 else f n) s
    fun hn ↦ ite_eq_right hn).mp
    (LSeriesConverges_of_sum_isBigO_aux (by simp) (by simpa only [hsum] using hO) hs)

/-- Iterating the Dirichlet term: dividing the terms at `s` by `n ^ t` gives the terms
at `s + t`. -/
@[simp] theorem LSeries.term_term (f : ℕ → ℂ) (s t : ℂ) (n : ℕ) :
    LSeries.term (LSeries.term f s) t n = LSeries.term f (s + t) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn), div_div]

/-- **A Dirichlet series converges on a half-plane.**  Ordinary convergence at `s` forces ordinary
convergence at every point strictly to the right of `s`: the partial sums of the terms at `s` are
bounded, which is `TauCeti.LSeriesConverges_of_sum_isBigO` with exponent `0`. -/
theorem LSeriesConverges.of_re_lt_re (h : LSeriesConverges f s) (hs : s.re < s'.re) :
    LSeriesConverges f s' := by
  obtain ⟨L, hL⟩ := h
  have hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, LSeries.term f s k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ) := by
    simp_rw [Real.rpow_zero]
    refine Tendsto.isBigO_one ℝ (((tendsto_add_atTop_iff_nat 1).mpr hL).congr fun n ↦ ?_)
    rw [Nat.range_succ_eq_Icc_zero, ← insert_Icc_add_one_left_eq_Icc n.zero_le,
      sum_insert (by simp), LSeries.term_zero, zero_add, zero_add]
  obtain ⟨L', hL'⟩ := LSeriesConverges_of_sum_isBigO (s := s' - s) hO (by simpa using hs)
  exact ⟨L', by simpa using hL'⟩

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
  congrArg sInf <| congrArg _ <| Set.ext fun x ↦ LSeriesConverges_congr x h

/-- If the series converges at every real point above `x`, its abscissa of ordinary convergence is
at most `x`. -/
theorem abscissaOfConv_le_of_forall_lt_LSeriesConverges {x : EReal}
    (h : ∀ y : ℝ, x < y → LSeriesConverges f y) : abscissaOfConv f ≤ x :=
  le_of_forall_gt_imp_ge_of_dense fun _ hc ↦ by
    obtain ⟨y, hxy, hyc⟩ := EReal.exists_between_coe_real hc
    exact (sInf_le (Set.mem_image_of_mem _ (h y hxy)) : abscissaOfConv f ≤ y).trans hyc.le

/-- **The ordinary abscissa lies to the left of the absolute one.** -/
theorem abscissaOfConv_le_abscissaOfAbsConv (f : ℕ → ℂ) :
    abscissaOfConv f ≤ _root_.LSeries.abscissaOfAbsConv f :=
  sInf_le_sInf <| Set.image_mono fun _ hx ↦ hx.LSeriesConverges

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
  -- The series converges ordinarily at a real `x` with `x + 1 < y`, so its terms there are bounded.
  obtain ⟨x, hx, hxy⟩ := EReal.exists_between_coe_real
    ((EReal.lt_sub_iff_add_lt (.inl (EReal.coe_ne_bot 1)) (.inl (EReal.coe_ne_top 1))).mpr hy)
  obtain ⟨L, hL⟩ := LSeriesConverges_of_abscissaOfConv_lt_re (s := x) (by simpa using hx)
  have hterm : Tendsto (LSeries.term f x) atTop (𝓝 0) := by
    simpa [Function.comp_def, sum_range_succ] using (hL.comp (tendsto_add_atTop_nat 1)).sub hL
  obtain ⟨C, hC⟩ := hterm.norm.bddAbove_range
  have hxy' : x < y - 1 := by exact_mod_cast hxy
  refine LSeriesSummable_of_le_const_mul_rpow (x := x + 1)
    (by rw [Complex.ofReal_re]; linarith) ⟨C, fun n hn ↦ ?_⟩
  have hbd : ‖LSeries.term f x n‖ ≤ C := hC ⟨n, rfl⟩
  rw [LSeries.norm_term_eq, ite_eq_right hn, div_le_iff₀ (by positivity)] at hbd
  simpa using hbd

end LSeries

/-! ### Alternating coefficients: the two abscissae can differ -/

namespace LSeries

/-- The partial sums `∑_{1 ≤ k ≤ n} (-1) ^ (k + 1)` of the alternating coefficients have norm at
most `1`, being `0` or `1` by `Finset.sum_Icc_neg_one_pow_add_one`. -/
theorem norm_sum_Icc_neg_one_pow_add_one_le {R : Type*} [SeminormedRing R] [NormOneClass R]
    (n : ℕ) : ‖∑ k ∈ Icc 1 n, (-1 : R) ^ (k + 1)‖ ≤ 1 := by
  rw [Finset.sum_Icc_neg_one_pow_add_one]
  split_ifs <;> simp

/-- The alternating coefficients have bounded partial sums, so their Dirichlet series converges
for `Re s > 0`. -/
theorem abscissaOfConv_neg_one_pow_le_zero :
    abscissaOfConv (fun n ↦ (-1 : ℂ) ^ n) ≤ 0 := by
  have hsum (n : ℕ) : ‖∑ k ∈ Icc 1 n, (-1 : ℂ) ^ k‖ ≤ 1 := by
    simpa [pow_succ, sum_neg_distrib] using norm_sum_Icc_neg_one_pow_add_one_le (R := ℂ) n
  exact_mod_cast abscissaOfConv_le_of_sum_isBigO (f := fun n ↦ (-1 : ℂ) ^ n) (r := 0)
    (.of_bound 1 (.of_forall fun n ↦ by simpa using hsum n))

/-- The alternating coefficients have modulus one, so their Dirichlet series converges absolutely
exactly where the Riemann zeta series does. -/
theorem abscissaOfAbsConv_neg_one_pow :
    _root_.LSeries.abscissaOfAbsConv (fun n ↦ (-1 : ℂ) ^ n) = 1 := by
  have h (x : ℝ) : LSeriesSummable (fun n ↦ (-1 : ℂ) ^ n) x ↔ LSeriesSummable 1 x := by
    simp [LSeriesSummable, ← summable_norm_iff (E := ℂ), LSeries.norm_term_eq]
  rw [← _root_.LSeries.abscissaOfAbsConv_one]
  exact congrArg sInf (congrArg _ (Set.ext h))

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
theorem LSeriesConverges_iff_LSeriesSummable_of_nonneg
    (ha : ∀ n, n ≠ 0 → 0 ≤ f n) (x : ℝ) :
    LSeriesConverges f (x : ℂ) ↔ LSeriesSummable f (x : ℂ) := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, LSeriesSummable.LSeriesConverges⟩
  have hre (n : ℕ) : (LSeries.term f x n).re = ‖LSeries.term f x n‖ := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · exact Complex.re_eq_norm.mpr (LSeries.term_nonneg (ha n hn) x)
  refine .of_norm ((hasSum_iff_tendsto_nat_of_nonneg (fun _ ↦ norm_nonneg _) L.re).mpr ?_).summable
  simpa only [Function.comp_def, Complex.re_sum, hre] using
    (Complex.continuous_re.tendsto L).comp hL

namespace LSeries

/-- **For coefficients nonnegative away from the ignored index zero the two abscissae agree.**
A Dirichlet series with nonnegative coefficients therefore has a single half-plane of convergence,
and the abscissa appearing in Landau's theorem is the ordinary one as well as the absolute one. -/
theorem abscissaOfConv_eq_abscissaOfAbsConv_of_nonneg (ha : ∀ n, n ≠ 0 → 0 ≤ f n) :
    abscissaOfConv f = _root_.LSeries.abscissaOfAbsConv f :=
  congrArg sInf (congrArg _
    (Set.ext fun x ↦ LSeriesConverges_iff_LSeriesSummable_of_nonneg ha x))

end LSeries

end TauCeti
