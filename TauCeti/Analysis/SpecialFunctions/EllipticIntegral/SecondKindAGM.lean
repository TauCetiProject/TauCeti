/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Landen
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Monotonicity
import TauCeti.Analysis.SpecialFunctions.ArithmeticGeometricMean
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# AGM evaluation of the complete elliptic integral of the second kind

Landen's transformation gives a telescoping series of squared differences of the
arithmetic and geometric means. The exponentially weighted remainder tends to zero,
so the series evaluates `legendreEc` using the same AGM iteration as `legendreK`.

Mathlib's `NNReal.agmSequences` starts after one AGM step, with the geometric
mean first and the arithmetic mean second.

The telescoping argument follows Bastiaan J Braams' `Carlson.hasSum_agmA_zero`
and `Carlson.carlsonRE_eq_agm` in `lean-codes`, adapted from Carlson's integrals
to real Legendre integrals and Mathlib's AGM sequence.

## References

* NIST DLMF, §19.8(i), <https://dlmf.nist.gov/19.8>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, §9.5, Exercises 3–4.
* Bastiaan J Braams, `Carlson/Elliptic/AGMSecondKind.lean` in `lean-codes`,
  commit `2b8cba1` (Apache-2.0).
-/

public section

namespace TauCeti.Real

open _root_.Real Filter
open scoped Topology NNReal

private noncomputable def residual (a b : ℝ) : ℝ :=
  a ^ 2 * (legendreEc √(1 - (b / a) ^ 2) / legendreK √(1 - (b / a) ^ 2) - 1)

private lemma residual_step {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    residual a b = 2 * residual ((a + b) / 2) √(a * b) - (a ^ 2 - b ^ 2) / 2 := by
  have ha := hb.trans_le hba
  have hr : 0 < b / a ∧ b / a ≤ 1 := ⟨div_pos hb ha, (div_le_one ha).2 hba⟩
  have hs := sq_sqrt (by nlinarith : 0 ≤ 1 - (b / a) ^ 2)
  have hk : (√(1 - (b / a) ^ 2)) ^ 2 < 1 := by rw [hs]; nlinarith [hr.1]
  have hc : √(1 - (√(1 - (b / a) ^ 2)) ^ 2) = b / a := by
    rw [hs, sub_sub_cancel, sqrt_sq (div_pos hb ha).le]
  have hE := legendreEc_eq_one_add_mul_legendreEc hk
  have hK := legendreK_eq_one_add_mul_legendreK hk
  rw [hc] at hE hK
  have harg : √(1 - (√(a * b) / ((a + b) / 2)) ^ 2) =
      (1 - b / a) / (1 + b / a) := by
    have heq : 1 - (√(a * b) / ((a + b) / 2)) ^ 2 =
        ((1 - b / a) / (1 + b / a)) ^ 2 := by
      rw [div_pow, sq_sqrt (by positivity)]
      field_simp
      ring
    rw [heq, sqrt_sq (div_nonneg (by rw [sub_nonneg, div_le_one ha]; exact hba)
      (by positivity))]
  unfold residual
  rw [harg]
  have hKn := (legendreK_pos hk).ne'
  have hK₁ : legendreK ((1 - b / a) / (1 + b / a)) ≠ 0 := by
    intro h
    simp only [h, mul_zero] at hK
    exact hKn hK
  rw [hE, hK]
  generalize legendreEc ((1 - b / a) / (1 + b / a)) = E at *
  generalize legendreK ((1 - b / a) / (1 + b / a)) = K at *
  field_simp
  ring

private lemma residual_bound {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    |residual a b| ≤ a ^ 2 - b ^ 2 := by
  have ha := hb.trans_le hba
  have hr : 0 < b / a ∧ b / a ≤ 1 := ⟨div_pos hb ha, (div_le_one ha).2 hba⟩
  have hs := sq_sqrt (by nlinarith : 0 ≤ 1 - (b / a) ^ 2)
  have hk : (√(1 - (b / a) ^ 2)) ^ 2 < 1 := by rw [hs]; nlinarith [hr.1]
  have hK := legendreK_pos hk
  have hE : legendreEc √(1 - (b / a) ^ 2) ≤ legendreK √(1 - (b / a) ^ 2) :=
    (legendreEc_le_pi_div_two _).trans (pi_div_two_le_legendreK hk)
  have hlo := one_sub_sq_mul_legendreK_le_legendreEc hk
  rw [hs] at hlo
  have hratio : (b / a) ^ 2 ≤
      legendreEc √(1 - (b / a) ^ 2) / legendreK √(1 - (b / a) ^ 2) := by
    rw [le_div_iff₀ hK]
    linarith
  have hratio₁ := (div_le_one hK).2 hE
  unfold residual
  rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) (by linarith))]
  have heq : a ^ 2 * (b / a) ^ 2 = b ^ 2 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hratio (sq_nonneg a)]

private lemma tendsto_weighted_residual {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun n ↦ (2 : ℝ) ^ (n + 1) *
      residual (NNReal.agmSequences x y n).2 (NNReal.agmSequences x y n).1)
      atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hlim : Tendsto (fun n : ℕ ↦ (dist x y) ^ 2 / 4 * (1 / 2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul ((dist x y) ^ 2 / 4)
  refine squeeze_zero_norm (fun n ↦ ?_) hlim
  have hba : ((NNReal.agmSequences x y (n + 1)).1 : ℝ) ≤
      (NNReal.agmSequences x y (n + 1)).2 := by
    exact_mod_cast NNReal.agmSequences_fst_le_snd (x := x) (y := y) (n + 1) (n + 1)
  have hb := residual_bound (by exact_mod_cast NNReal.agmSequences_fst_pos hx hy (n + 1)) hba
  have hgap := NNReal.dist_agmSequences_fst_snd (x := x) (y := y) n
  have hdist : dist (NNReal.agmSequences x y n).1 (NNReal.agmSequences x y n).2 =
      ((NNReal.agmSequences x y n).2 : ℝ) - (NNReal.agmSequences x y n).1 := by
    rw [dist_comm, NNReal.dist_eq, abs_of_nonneg]
    exact sub_nonneg.2 (by exact_mod_cast NNReal.agmSequences_fst_le_snd (x := x) (y := y) n n)
  rw [hdist] at hgap
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  calc
    _ ≤ 2 ^ (n + 1 + 1) *
        (((NNReal.agmSequences x y (n + 1)).2 : ℝ) ^ 2 -
          ((NNReal.agmSequences x y (n + 1)).1 : ℝ) ^ 2) := by gcongr
    _ = 2 ^ (n + 1 + 1) *
        (((NNReal.agmSequences x y n).2 : ℝ) - (NNReal.agmSequences x y n).1) ^ 2 / 4 := by
      rw [NNReal.agmSequences_succ']
      simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat, coe_sqrt, NNReal.coe_mul]
      rw [sq_sqrt (by positivity)]
      ring
    _ ≤ 2 ^ (n + 1 + 1) * (dist x y / 2 ^ (n + 1)) ^ 2 / 4 := by
      gcongr
      exact sub_nonneg.2 (by exact_mod_cast NNReal.agmSequences_fst_le_snd (x := x) (y := y) n n)
    _ = _ := by rw [one_div_pow, pow_succ]; field_simp; ring

private lemma hasSum_agm_sq_gap {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    HasSum (fun n ↦ (2 : ℝ) ^ n *
      (((NNReal.agmSequences x y n).2 : ℝ) ^ 2 -
        ((NNReal.agmSequences x y n).1 : ℝ) ^ 2))
      (-2 * residual (NNReal.agmSequences x y 0).2 (NNReal.agmSequences x y 0).1) := by
  let R := fun n ↦ (2 : ℝ) ^ (n + 1) *
    residual (NNReal.agmSequences x y n).2 (NNReal.agmSequences x y n).1
  have hstep (n : ℕ) : R (n + 1) - R n = (2 : ℝ) ^ n *
      (((NNReal.agmSequences x y n).2 : ℝ) ^ 2 -
        ((NNReal.agmSequences x y n).1 : ℝ) ^ 2) := by
    have hba : ((NNReal.agmSequences x y n).1 : ℝ) ≤ (NNReal.agmSequences x y n).2 := by
      exact_mod_cast NNReal.agmSequences_fst_le_snd (x := x) (y := y) n n
    have h := residual_step (by exact_mod_cast NNReal.agmSequences_fst_pos hx hy n) hba
    dsimp [R]
    rw [NNReal.agmSequences_succ']
    simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat, coe_sqrt, NNReal.coe_mul]
    rw [add_comm ((NNReal.agmSequences x y n).1 : ℝ),
      mul_comm ((NNReal.agmSequences x y n).1 : ℝ), pow_succ, pow_succ]
    linear_combination -(2 : ℝ) ^ (n + 1) * h
  have hnonneg (n : ℕ) : 0 ≤ (2 : ℝ) ^ n *
      (((NNReal.agmSequences x y n).2 : ℝ) ^ 2 -
        ((NNReal.agmSequences x y n).1 : ℝ) ^ 2) := by
    refine mul_nonneg (by positivity) (sub_nonneg.2 ?_)
    gcongr
    exact_mod_cast NNReal.agmSequences_fst_le_snd (x := x) (y := y) n n
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
  simp_rw [← hstep, Finset.sum_range_sub]
  simpa [R] using (tendsto_weighted_residual hx hy).sub_const (R 0)

/-- The squared AGM corrections form a convergent series evaluating `E(k) / K(k)`.
The sequence starts after one step: its difference of squares is `cₙ₊₁²` in the
classical convention `c₀ = k`, `cₙ₊₁ = (aₙ - gₙ) / 2`. -/
theorem hasSum_legendreEc_agm {k : ℝ} (hk : k ^ 2 < 1) :
    HasSum (fun n ↦ (2 : ℝ) ^ n *
      (((NNReal.agmSequences 1 (NNReal.sqrt (Real.toNNReal (1 - k ^ 2))) n).2 : ℝ) ^ 2 -
        ((NNReal.agmSequences 1 (NNReal.sqrt (Real.toNNReal (1 - k ^ 2))) n).1 : ℝ) ^ 2))
      (1 - k ^ 2 / 2 - legendreEc k / legendreK k) := by
  let b : ℝ≥0 := NNReal.sqrt (Real.toNNReal (1 - k ^ 2))
  have hbval : (b : ℝ) = √(1 - k ^ 2) := by
    simp [b, coe_sqrt, Real.toNNReal_of_nonneg (sub_pos.2 hk).le]
  have hb : 0 < b := by rw [← NNReal.coe_pos, hbval]; positivity
  have hba : (b : ℝ) ≤ 1 := by rw [hbval]; exact sqrt_le_one.2 (by nlinarith)
  have h := hasSum_agm_sq_gap (x := 1) (by norm_num) hb
  have hstep := residual_step (a := 1) (b := b) (by exact_mod_cast hb) hba
  have hres : residual 1 b = legendreEc k / legendreK k - 1 := by
    unfold residual
    rw [hbval, div_one, sq_sqrt (by linarith), sub_sub_cancel, sqrt_sq_eq_abs]
    simp only [one_pow, one_mul]
    rcases abs_choice k with h | h <;> simp only [h, legendreEc_neg, legendreK_neg]
  simp only [NNReal.agmSequences_zero, NNReal.coe_div, NNReal.coe_add,
    NNReal.coe_one, NNReal.coe_ofNat, coe_sqrt, one_mul] at h
  have htotal : -2 * residual ((1 + (b : ℝ)) / 2) √(b : ℝ) =
      1 - k ^ 2 / 2 - legendreEc k / legendreK k := by
    rw [hbval]
    rw [hres, hbval, sq_sqrt (by linarith)] at hstep
    norm_num at hstep
    linarith
  exact htotal ▸ h

/-- **AGM evaluation of the complete second kind** (DLMF 19.8.6).
The initial correction is `k² / 2`; the remaining corrections use Mathlib's
AGM sequence, whose index zero is already one step after `(1, √(1 - k²))`. -/
theorem legendreEc_eq_agm_tsum {k : ℝ} (hk : k ^ 2 < 1) :
    legendreEc k = legendreK k * (1 - k ^ 2 / 2 - ∑' n, (2 : ℝ) ^ n *
      (((NNReal.agmSequences 1 (NNReal.sqrt (Real.toNNReal (1 - k ^ 2))) n).2 : ℝ) ^ 2 -
        ((NNReal.agmSequences 1 (NNReal.sqrt (Real.toNNReal (1 - k ^ 2))) n).1 : ℝ) ^ 2)) := by
  rw [(hasSum_legendreEc_agm hk).tsum_eq]
  field_simp [(legendreK_pos hk).ne']
  ring

end TauCeti.Real
