/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Probability.Distributions.Relations

/-!
# The expected maximum of independent Gaussians

Let `g₁, …, gₘ` be independent standard Gaussian random variables. Their largest absolute value
grows like `√(log m)` in expectation. This file proves the lower bound

`√(log m) / 32 ≤ 𝔼 max_j |g_j|`

(`TauCeti.Probability.sqrt_log_card_div_le_integral_sup'_abs`), and in particular the bound
`(1 / 100) √(log m)`. The constant is not optimal.

Lower bounds of this kind measure the average norm on the Euclidean sphere of a finite-dimensional
normed space that has many unit vectors of large norm, which is the input to the logarithmic
dimension bound in Dvoretzky's theorem.

The proof uses a single level `s = √(log m) / 4`. Each `|g_j|` exceeds `s` with probability at
least `p = φ(s + 1)`, where `φ` is the standard Gaussian density
(`TauCeti.Probability.mul_gaussianPDFReal_add_le_measureReal_Ioi_gaussianReal`), and
`m p ≥ 1 / 7` by the choice of `s`. By independence the maximum is at most `s` with probability
`(1 - p) ^ m ≤ exp (-m p) ≤ 7 / 8` (`TauCeti.Probability.measureReal_setOf_max_le_iid`), so
Markov's inequality gives `𝔼 max_j |g_j| ≥ s / 8`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Lemma 13.3.6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Real

namespace TauCeti.Probability

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Fintype ι] [Nonempty ι] {P : Measure Ω}
  {g : ι → Ω → ℝ}

/-- At the level `s = √(log m) / 4`, the standard Gaussian density at `s + 1` is at least
`1 / (7 m)`. -/
private theorem one_div_seven_le_mul_gaussianPDFReal {m : ℝ} (hm : 1 ≤ m) :
    1 / 7 ≤ m * gaussianPDFReal 0 1 (√(Real.log m) / 4 + 1) := by
  set s := √(Real.log m) / 4 with hs
  have hs2 : s ^ 2 = Real.log m / 16 := by
    rw [hs, div_pow, Real.sq_sqrt (Real.log_nonneg hm)]
    norm_num
  -- `(s + 1) ^ 2 / 2 ≤ s ^ 2 + 1 ≤ log m + 1`, so the density is at least `e⁻¹ / (√(2π) m)`.
  have hexp : rexp (-1) / m ≤ rexp (-((s + 1) ^ 2 / 2)) := by
    rw [div_eq_mul_inv, ← Real.exp_log (zero_lt_one.trans_le hm), ← Real.exp_neg,
      ← Real.exp_add, Real.exp_le_exp]
    nlinarith [Real.log_nonneg hm, sq_nonneg (s - 1)]
  have hπ : √(2 * π) ≤ 2.51 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [Real.pi_lt_d2]
  have hc : 1 / 7 ≤ (√(2 * π))⁻¹ * rexp (-1) := by
    rw [Real.exp_neg, ← mul_inv, one_div]
    refine inv_anti₀ (by positivity) ?_
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1, Real.sqrt_nonneg (2 * π)]
  calc 1 / 7 ≤ (√(2 * π))⁻¹ * rexp (-1) := hc
    _ = m * ((√(2 * π))⁻¹ * (rexp (-1) / m)) := by field_simp
    _ ≤ m * gaussianPDFReal 0 1 (s + 1) := by
      rw [gaussianPDFReal_zero_one]
      gcongr

/-- The expected maximum of the absolute values of `m` independent standard Gaussian random
variables is at least `√(log m) / 32`. -/
theorem sqrt_log_card_div_le_integral_sup'_abs (hindep : iIndepFun g P)
    (hlaw : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) :
    √(Real.log (Fintype.card ι)) / 32 ≤
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => |g i ω|) ∂P := by
  have _ : IsProbabilityMeasure P := (hlaw (Classical.arbitrary ι)).isProbabilityMeasure
  set m : ℝ := (Fintype.card ι : ℝ) with hm
  set s : ℝ := √(Real.log m) / 4 with hs
  set M : Ω → ℝ := fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => |g i ω| with hM
  have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast Fintype.card_pos
  have hs0 : 0 ≤ s := by positivity
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => (abs_nonneg _).trans
    (Finset.le_sup' (fun i => |g i ω|) (Finset.mem_univ (Classical.arbitrary ι)))
  -- The absolute values `|g i|` are independent with common law `ν`.
  set ν : Measure ℝ := (gaussianReal 0 1).map fun x => |x|
  have hlawAbs : ∀ i, HasLaw (fun ω => |g i ω|) ν P := fun i =>
    (hasLaw_map measurable_abs.aemeasurable).comp (hlaw i)
  have hindepAbs : iIndepFun (fun i ω => |g i ω|) P :=
    hindep.comp (fun _ => abs) fun _ => measurable_abs
  -- Each `|g i|` exceeds `s` with probability at least `p = φ(s + 1)`, and `m p ≥ 1 / 7`.
  set p : ℝ := gaussianPDFReal 0 1 (s + 1)
  have hp : p ≤ ν.real (Ioi s) := by
    have h := mul_gaussianPDFReal_add_le_measureReal_Ioi_gaussianReal (m := 0) 1 hs0 (t := 1)
    rw [one_mul] at h
    rw [map_measureReal_apply measurable_abs measurableSet_Ioi]
    exact h.trans (measureReal_mono fun x (hx : s < x) => hx.trans_le (le_abs_self x))
  have hmp : 1 / 7 ≤ m * p := one_div_seven_le_mul_gaussianPDFReal hm1
  -- By independence, the maximum is at most `s` with probability at most `7 / 8`.
  have hle : P.real {ω | M ω ≤ s} ≤ 7 / 8 := by
    have hq : cdf ν s ≤ 1 - p := by
      rw [cdf_eq_real, ← compl_Ioi, measureReal_compl measurableSet_Ioi, probReal_univ]
      linarith
    have hp0 : 0 ≤ p := gaussianPDFReal_nonneg 0 1 _
    have h7 : rexp (-(1 / 7)) ≤ 7 / 8 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith [Real.add_one_le_exp (1 / 7 : ℝ)]
    calc P.real {ω | M ω ≤ s} = cdf ν s ^ Fintype.card ι :=
          measureReal_setOf_max_le_iid hindepAbs hlawAbs s
      _ ≤ rexp (-p) ^ Fintype.card ι :=
          pow_le_pow_left₀ (cdf_nonneg ν s) (hq.trans (Real.one_sub_le_exp_neg p)) _
      _ = rexp (-(m * p)) := by rw [← Real.exp_nat_mul, hm, mul_neg]
      _ ≤ 7 / 8 := (Real.exp_le_exp.2 (neg_le_neg hmp)).trans h7
  have hge : 1 / 8 ≤ P.real {ω | s ≤ M ω} := by
    have h := measureReal_union_le (μ := P) {ω | M ω ≤ s} {ω | s ≤ M ω}
    rw [show {ω | M ω ≤ s} ∪ {ω | s ≤ M ω} = univ from
      eq_univ_of_forall fun ω => le_total (M ω) s, probReal_univ] at h
    linarith
  -- Markov's inequality for the integrable, nonnegative maximum.
  have hint : Integrable M P := by
    refine (integrable_finsetSum Finset.univ fun i _ =>
      ((hlaw i).integrable IsGaussian.integrable_id).abs).mono' ?_ (ae_of_all _ fun ω => ?_)
    · have : AEMeasurable M P := by
        simp_rw [hM, Finset.sup'_univ_eq_ciSup]
        exact AEMeasurable.iSup fun i => (hlawAbs i).aemeasurable
      exact this.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hM0 ω)]
      exact Finset.sup'_le _ _ fun i _ =>
        Finset.single_le_sum (f := fun i => |g i ω|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  calc √(Real.log m) / 32 = s * (1 / 8) := by rw [hs]; ring
    _ ≤ s * P.real {ω | s ≤ M ω} := by gcongr
    _ ≤ ∫ ω, M ω ∂P := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hM0) hint s

end TauCeti.Probability
