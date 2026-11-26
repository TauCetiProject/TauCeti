/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.Analysis.LaplaceTransform.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Mellin transform of the summatory function of a Dirichlet series

At a point of absolute convergence with positive real part, the upper-tail Mellin integral of
`x ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n` converges absolutely and equals `LSeries a s / s`. This
version of the partial-summation formula needs no convergence at a smaller real part and no
pointwise growth estimate for partial sums. Its absolute-integral estimate controls the
summatory function in applications of Landau's theorem to signed coefficients. With `x = exp u`,
the same formula gives the one-sided Laplace transform of the summatory function in the log
variable.

Unlike Mathlib's `LSeries_eq_mul_integral`, which uses a partial-sum growth bound, the proof here
integrates the contribution of each index on its own ray and sums the resulting integrals.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti.LSeries

/-- The contribution of one positive index to the weighted summatory function. -/
private noncomputable def summatoryMellinTerm (a : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℝ → ℂ :=
  if n = 0 then 0 else (Ici (n : ℝ)).indicator fun x ↦ a n * (x : ℂ) ^ (-(s + 1))

private theorem measurable_summatoryMellinTerm (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    Measurable (summatoryMellinTerm a s n) := by
  by_cases hn : n = 0
  · rw [summatoryMellinTerm, ite_eq_left hn]
    exact measurable_const
  simpa only [summatoryMellinTerm, ite_eq_right hn] using
    ((measurable_ofReal.pow_const (-(s + 1))).const_mul (a n)).indicator measurableSet_Ici

private theorem tsum_summatoryMellinTerm (a : ℕ → ℂ) (s : ℂ) (x : ℝ) :
    ∑' n, summatoryMellinTerm a s n x =
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) * (x : ℂ) ^ (-(s + 1)) := by
  rw [Finset.sum_mul, tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    obtain ⟨hn, hnx⟩ := Finset.mem_Icc.mp hn
    have hn0 := Nat.ne_zero_of_lt hn
    have hx := (Nat.le_floor_iff' hn0).mp hnx
    simp [summatoryMellinTerm, hn0, hx]
  · intro n hn
    by_cases hn0 : n = 0
    · simp [summatoryMellinTerm, hn0]
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    have hnx : ¬ (n : ℝ) ≤ x := fun h ↦ hn <| Finset.mem_Icc.mpr
      ⟨hn1, (Nat.le_floor_iff' hn0).mpr h⟩
    simp [summatoryMellinTerm, hn0, hnx]

-- Work on the closed ray during the termwise calculation so that each indicator's support
-- is contained in the domain, including for `n = 1`.
private theorem integrableOn_summatoryMellinTerm (a : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (summatoryMellinTerm a s n) (Ici 1) := by
  by_cases hn : n = 0
  · rw [summatoryMellinTerm, ite_eq_left hn]
    exact integrable_zero _ _ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [summatoryMellinTerm, ite_eq_right hn, IntegrableOn,
    integrable_indicator_iff measurableSet_Ici, IntegrableOn,
    Measure.restrict_restrict_of_subset (Ici_subset_Ici.mpr hn1)]
  exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    ((integrableOn_Ioi_cpow_of_lt (by simp; linarith) (zero_lt_one.trans_le hn1)).const_mul _)

private theorem integral_summatoryMellinTerm (a : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ∫ x in Ici (1 : ℝ), summatoryMellinTerm a s n x = _root_.LSeries.term a s n / s := by
  by_cases hn : n = 0
  · simp [summatoryMellinTerm, hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [summatoryMellinTerm, ite_eq_right hn, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict_of_subset (Ici_subset_Ici.mpr hn1), integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_Ioi_cpow_of_lt (by simp; linarith) (zero_lt_one.trans_le hn1),
    _root_.LSeries.term_def, ite_eq_right hn, ofReal_natCast]
  have hexp : -(s + 1) + 1 = -s := by ring
  rw [hexp, neg_div_neg_eq, cpow_neg]
  simp only [div_eq_mul_inv, mul_assoc]

private theorem integral_norm_summatoryMellinTerm (a : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re)
    (n : ℕ) : ∫ x in Ici (1 : ℝ), ‖summatoryMellinTerm a s n x‖ =
      ‖_root_.LSeries.term a s n‖ / s.re := by
  by_cases hn : n = 0
  · simp [summatoryMellinTerm, hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have heq : (fun x ↦ ‖summatoryMellinTerm a s n x‖) =
      (Ici (n : ℝ)).indicator fun x ↦ ‖a n‖ * x ^ (-(s.re + 1)) := by
    funext x
    by_cases hx : (n : ℝ) ≤ x
    · simp [summatoryMellinTerm, hn, hx,
        norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le (hn1.trans hx))]
    · simp [summatoryMellinTerm, hn, hx]
  rw [heq, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict_of_subset (Ici_subset_Ici.mpr hn1), integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) (zero_lt_one.trans_le hn1),
    _root_.LSeries.norm_term_eq, ite_eq_right hn]
  have hexp : -(s.re + 1) + 1 = -s.re := by ring
  rw [hexp, neg_div_neg_eq, Real.rpow_neg (zero_le_one.trans hn1)]
  simp only [div_eq_mul_inv, mul_assoc]

private theorem lintegral_eNorm_summatory_le (a : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re) :
    (∫⁻ x in Ici (1 : ℝ), ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) * (x : ℂ) ^ (-(s + 1))‖ₑ) ≤
      ∑' n, ENNReal.ofReal (‖_root_.LSeries.term a s n‖ / s.re) := by
  simp_rw [← tsum_summatoryMellinTerm]
  refine (lintegral_mono fun _ ↦ eNorm_tsum_le_tsum_eNorm).trans_eq ?_
  rw [lintegral_tsum fun n ↦ (measurable_summatoryMellinTerm a s n).eNorm.aemeasurable]
  congr with n
  rw [← ofReal_integral_norm_eq_lintegral_eNorm (integrableOn_summatoryMellinTerm a hs n),
    integral_norm_summatoryMellinTerm a hs n]

/-- Absolute convergence of a Dirichlet series at `s` with `0 < Re s` implies absolute
convergence of the upper Mellin tail of its summatory function at the same parameter. -/
theorem _root_.LSeriesSummable.integrableOn_summatory_mul_cpow {a : ℕ → ℂ} {s : ℂ}
    (ha : LSeriesSummable a s) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) * (x : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
  apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mp
  refine ⟨?_, hasFiniteIntegral_iff_eNorm.mpr
    ((lintegral_eNorm_summatory_le a hs).trans_lt (ha.norm.div_const _).tsum_ofReal_lt_top)⟩
  simp_rw [← tsum_summatoryMellinTerm]
  exact (Measurable.tsum fun n ↦ measurable_summatoryMellinTerm a s n).aestronglyMeasurable

/-- The absolute Mellin integral of the summatory function is at most the absolute Dirichlet
series divided by `Re s`. -/
theorem _root_.LSeriesSummable.integral_norm_summatory_mul_cpow_le {a : ℕ → ℂ} {s : ℂ}
    (ha : LSeriesSummable a s) (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) * (x : ℂ) ^ (-(s + 1))‖) ≤
      (∑' n, ‖_root_.LSeries.term a s n‖) / s.re := by
  have hi := (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    (ha.integrableOn_summatory_mul_cpow hs)
  have h := lintegral_eNorm_summatory_le a hs
  rw [← ofReal_integral_norm_eq_lintegral_eNorm hi,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) (ha.norm.div_const _),
    tsum_div_const] at h
  rw [← integral_Ici_eq_integral_Ioi]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- The Mellin integral of a summatory function at a point of absolute convergence with
positive real part equals the Dirichlet series divided by its parameter. -/
theorem _root_.LSeriesSummable.integral_summatory_mul_cpow {a : ℕ → ℂ} {s : ℂ}
    (ha : LSeriesSummable a s) (hs : 0 < s.re) :
    ∫ x in Ioi (1 : ℝ), (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) * (x : ℂ) ^ (-(s + 1)) =
      LSeries a s / s := by
  rw [← integral_Ici_eq_integral_Ioi]
  simp_rw [← tsum_summatoryMellinTerm]
  rw [← integral_tsum_of_summable_integral_norm (integrableOn_summatoryMellinTerm a hs) (by
    simp_rw [integral_norm_summatoryMellinTerm a hs]
    exact ha.norm.div_const _)]
  simp_rw [integral_summatoryMellinTerm a hs, tsum_div_const, LSeries]

/-- The Laplace transform of the summatory function in the variable `x = exp u` is the
Dirichlet series divided by its parameter. -/
theorem _root_.LSeriesSummable.hasLaplace_summatory_comp_exp {a : ℕ → ℂ} {s : ℂ}
    (ha : LSeriesSummable a s) (hs : 0 < s.re) :
    HasLaplace (fun u : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, a n) s (LSeries a s / s) := by
  let g : ℝ → ℂ := fun x ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) * (x : ℂ) ^ (-(s + 1))
  have h (u : ℝ) : Real.exp u • g (Real.exp u) =
      Complex.exp (-s * u) • (∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, a n) := by
    have hexp : (u : ℂ) + u * -(s + 1) = -s * u := by ring
    dsimp only [g]
    rw [real_smul, ofReal_exp_cpow, ofReal_exp, smul_eq_mul, mul_left_comm,
      ← Complex.exp_add, hexp, mul_comm]
  have hi := integrableOn_comp_exp_Ioi g 0
  have he := integral_comp_exp_Ioi g 0
  simp only [Real.exp_zero, h] at hi he
  exact HasLaplace.intro (hi.mpr (ha.integrableOn_summatory_mul_cpow hs))
    (he.trans (ha.integral_summatory_mul_cpow hs))

end TauCeti.LSeries
