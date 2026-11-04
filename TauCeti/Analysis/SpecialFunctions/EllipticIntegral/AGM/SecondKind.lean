/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Landen
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Monotonicity
import TauCeti.Analysis.SpecialFunctions.ArithmeticGeometricMean
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# AGM evaluation of the complete elliptic integral of the second kind

Landen's transformation gives a telescoping series for `E / K` along Mathlib's AGM
sequence. The terms are weighted differences of squares of the arithmetic and geometric
means. Since one AGM step turns this difference into a squared gap, Mathlib's geometric
gap bound suffices to show that the remainder tends to zero.

## References

* NIST DLMF §19.8(i), <https://dlmf.nist.gov/19.8>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, §9.5, Exercises 3–4.
* Bastiaan J Braams, `lean-codes`, `Carlson/Elliptic/AGMSecondKind.lean`, commit
  `2b8cba1` (Apache-2.0), for the telescoping proof plan. Here we use the real Legendre
  Landen identities and Mathlib's `NNReal.agmSequences`, not Carlson's general R-function.
-/

public section

namespace TauCeti.Real

open _root_.Real Filter
open scoped Topology NNReal

/-- The normalized second-kind error at an AGM pair. -/
private noncomputable def secondKindError (a b : ℝ) : ℝ :=
  a ^ 2 * (1 - legendreEc √(1 - (b / a) ^ 2) / legendreK √(1 - (b / a) ^ 2))

private theorem secondKindError_bounds {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    0 ≤ secondKindError a b ∧ secondKindError a b ≤ a ^ 2 - b ^ 2 := by
  have ha := hb.trans_le hba
  have hsq := sq_sqrt_one_sub_sq_div hb hba
  have hk := sq_sqrt_one_sub_sq_div_lt_one hb hba
  set k := √(1 - (b / a) ^ 2)
  have hK := legendreK_pos hk
  have hE : legendreEc k ≤ legendreK k :=
    (legendreEc_le_pi_div_two k).trans (pi_div_two_le_legendreK hk)
  have hlower := one_sub_sq_mul_legendreK_le_legendreEc hk
  dsimp only [secondKindError]
  constructor
  · exact mul_nonneg (sq_nonneg _) (sub_nonneg.2 ((div_le_one hK).2 hE))
  · have hr : 1 - k ^ 2 ≤ legendreEc k / legendreK k := (le_div_iff₀ hK).2 hlower
    have heq : a ^ 2 * k ^ 2 = a ^ 2 - b ^ 2 := by
      rw [hsq]
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left hr (sq_nonneg a)]

private theorem secondKindError_step {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    secondKindError a b =
      2 * secondKindError ((a + b) / 2) √(a * b) + (a ^ 2 - b ^ 2) / 2 := by
  have ha := hb.trans_le hba
  have hsq := sq_sqrt_one_sub_sq_div hb hba
  have hk := sq_sqrt_one_sub_sq_div_lt_one hb hba
  have hab : 0 < a + b := by positivity
  have hc : √(1 - (√(1 - (b / a) ^ 2)) ^ 2) = b / a := by
    rw [hsq, sub_sub_cancel, sqrt_sq (div_pos hb ha).le]
  have hq : √(1 - (√(a * b) / ((a + b) / 2)) ^ 2) = (1 - b / a) / (1 + b / a) := by
    have hn : 0 ≤ (1 - b / a) / (1 + b / a) := by
      exact div_nonneg (sub_nonneg.2 ((div_le_one ha).2 hba)) (by positivity)
    have heq : 1 - (√(a * b) / ((a + b) / 2)) ^ 2 =
        ((1 - b / a) / (1 + b / a)) ^ 2 := by
      rw [div_pow, sq_sqrt (mul_pos ha hb).le]
      field_simp
      ring
    rw [heq, sqrt_sq hn]
  have hE := legendreEc_eq_one_add_mul_legendreEc hk
  have hK := legendreK_eq_one_add_mul_legendreK hk
  rw [hc] at hE hK
  have hq₀ : ((1 - b / a) / (1 + b / a)) ^ 2 < 1 := by
    have hp : 0 < b / a := div_pos hb ha
    have hl : b / a ≤ 1 := (div_le_one ha).2 hba
    have hnonneg : 0 ≤ (1 - b / a) / (1 + b / a) := by positivity
    have hlt : (1 - b / a) / (1 + b / a) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    nlinarith
  have hK₁ := (legendreK_pos hq₀).ne'
  dsimp only [secondKindError]
  rw [hq, hE, hK]
  generalize legendreEc ((1 - b / a) / (1 + b / a)) = e at *
  generalize legendreK ((1 - b / a) / (1 + b / a)) = i at *
  field_simp
  ring

private theorem agm_secondKind_bounds {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    0 ≤ secondKindError (NNReal.agmSequences a b n).2 (NNReal.agmSequences a b n).1 ∧
      secondKindError (NNReal.agmSequences a b n).2 (NNReal.agmSequences a b n).1 ≤
        ((NNReal.agmSequences a b n).2 : ℝ) ^ 2 -
          ((NNReal.agmSequences a b n).1 : ℝ) ^ 2 := by
  have hpos : 0 < (NNReal.agmSequences a b 0).1 := by
    simpa only [NNReal.agmSequences_zero] using NNReal.sqrt_pos.2 (mul_pos ha hb)
  exact secondKindError_bounds
    (by exact_mod_cast hpos.trans_le (NNReal.agmSequences_fst_monotone (Nat.zero_le n)))
    (NNReal.coe_le_coe.2 (NNReal.agmSequences_fst_le_snd n n))

private theorem agm_secondKind_step {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    secondKindError (NNReal.agmSequences a b n).2 (NNReal.agmSequences a b n).1 =
      2 * secondKindError (NNReal.agmSequences a b (n + 1)).2
        (NNReal.agmSequences a b (n + 1)).1 +
      (((NNReal.agmSequences a b n).2 : ℝ) ^ 2 -
        ((NNReal.agmSequences a b n).1 : ℝ) ^ 2) / 2 := by
  have hpos : 0 < (NNReal.agmSequences a b 0).1 := by
    simpa only [NNReal.agmSequences_zero] using NNReal.sqrt_pos.2 (mul_pos ha hb)
  have h := secondKindError_step
    (by exact_mod_cast hpos.trans_le (NNReal.agmSequences_fst_monotone (Nat.zero_le n)))
    (NNReal.coe_le_coe.2 (NNReal.agmSequences_fst_le_snd n n))
  simpa only [NNReal.agmSequences_succ', NNReal.coe_div, NNReal.coe_add,
    NNReal.coe_ofNat, Real.coe_sqrt, NNReal.coe_mul, add_comm, mul_comm] using h

/-- The weighted squared differences of the AGM means sum to
`(a² + b²)/2 - a² E(√(1 - (b/a)²))/K(√(1 - (b/a)²))`.
Mathlib's index zero is already one AGM step. In particular, the series is summable. -/
theorem hasSum_agmSequences_secondKind {a b : ℝ≥0} (hb : 0 < b) (hba : b ≤ a) :
    HasSum (fun n ↦ (2 : ℝ) ^ n *
      (((NNReal.agmSequences a b n).2 : ℝ) ^ 2 -
        ((NNReal.agmSequences a b n).1 : ℝ) ^ 2))
      ((((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / 2) -
        (a : ℝ) ^ 2 * legendreEc √(1 - ((b : ℝ) / a) ^ 2) /
          legendreK √(1 - ((b : ℝ) / a) ^ 2)) := by
  have ha := hb.trans_le hba
  let R : ℕ → ℝ := fun n ↦ (2 : ℝ) ^ (n + 1) *
    secondKindError (NNReal.agmSequences a b n).2 (NNReal.agmSequences a b n).1
  have hR : Tendsto R atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ mul_nonneg (by positivity) (agm_secondKind_bounds ha hb n).1)
      (fun n ↦ ?_) (by simpa using
        (NNReal.tendsto_two_pow_mul_agmSequences_snd_sq_sub_fst_sq a b).const_mul 2)
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left (agm_secondKind_bounds ha hb n).2
      (by positivity : (0 : ℝ) ≤ 2 ^ n)]
  have htel (n : ℕ) : (2 : ℝ) ^ n *
      (((NNReal.agmSequences a b n).2 : ℝ) ^ 2 -
        ((NNReal.agmSequences a b n).1 : ℝ) ^ 2) = R n - R (n + 1) := by
    dsimp only [R]
    rw [agm_secondKind_step ha hb n, pow_succ, pow_succ]
    ring
  have hsum : HasSum (fun n ↦ (2 : ℝ) ^ n *
      (((NNReal.agmSequences a b n).2 : ℝ) ^ 2 -
        ((NNReal.agmSequences a b n).1 : ℝ) ^ 2)) (R 0) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ mul_nonneg (by positivity)
      (sub_nonneg.2 (pow_le_pow_left₀ (by positivity)
        (NNReal.coe_le_coe.2 (NNReal.agmSequences_fst_le_snd n n)) 2))) _).2
    simp_rw [htel, Finset.sum_range_sub']
    simpa using hR.const_sub (R 0)
  convert hsum using 1
  have h := secondKindError_step (NNReal.coe_pos.2 hb) (NNReal.coe_le_coe.2 hba)
  simp only [R, NNReal.agmSequences_zero, NNReal.coe_div, NNReal.coe_add,
    NNReal.coe_ofNat, Real.coe_sqrt, NNReal.coe_mul, pow_one, zero_add] at *
  dsimp only [secondKindError] at h ⊢
  linear_combination h

/-- **AGM evaluation of `E`**. Starting from `1` and the complementary modulus, let
`(gₙ₊₁, aₙ₊₁) = agmSequences 1 k' n`. Then
`E(k) = K(k) (1 - k²/2 - ∑ 2ⁿ (aₙ₊₁² - gₙ₊₁²))`.
The differences of squares equal the squared half-gaps from the preceding step. -/
theorem legendreEc_eq_agmSeries {k : ℝ} (hk : k ^ 2 < 1) :
    legendreEc k = legendreK k * (1 - k ^ 2 / 2 - ∑' n,
      (2 : ℝ) ^ n *
        (((NNReal.agmSequences 1 (.mk √(1 - k ^ 2) (sqrt_nonneg _)) n).2 : ℝ) ^ 2 -
          ((NNReal.agmSequences 1 (.mk √(1 - k ^ 2) (sqrt_nonneg _)) n).1 : ℝ) ^ 2)) := by
  have hc : 0 < √(1 - k ^ 2) := sqrt_pos.2 (by linarith)
  have hc₁ : √(1 - k ^ 2) ≤ 1 := sqrt_le_one.2 (by nlinarith)
  have h := hasSum_agmSequences_secondKind (a := 1)
    (b := .mk √(1 - k ^ 2) (sqrt_nonneg _)) (NNReal.coe_pos.1 hc) (NNReal.coe_le_coe.1 hc₁)
  have he : legendreEc √(k ^ 2) = legendreEc k := by
    rw [sqrt_sq_eq_abs]
    rcases abs_choice k with h | h <;> simp [h]
  have hκ : legendreK √(k ^ 2) = legendreK k := by
    rw [sqrt_sq_eq_abs]
    rcases abs_choice k with h | h <;> simp [h]
  simp only [NNReal.coe_one, NNReal.coe_mk, one_pow, div_one, sq_sqrt (by linarith : 0 ≤ 1 - k ^ 2),
    sub_sub_cancel, he, hκ, one_mul] at h
  rw [h.tsum_eq]
  field_simp [(legendreK_pos hk).ne']
  ring

end TauCeti.Real
