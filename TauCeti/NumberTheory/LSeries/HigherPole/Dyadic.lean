/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.Order.Northcott.Basic
import Mathlib.Algebra.Order.Group.Indicator

/-!
# A Dirichlet series supported on powers of two

Give each power of two weight equal to its size. Its Dirichlet series is geometric, with sum
`(1 - exp ((1 - s) * log 2))⁻¹` on `1 < s.re`. This sum has a simple pole at one and another
pole at `1 + 2πi / log 2` (see `TauCeti.NumberTheory.LSeries.HigherPole.PoleBoundary`).

The inclusive count is constant on each dyadic interval `[2^j, 2^(j+1))`. Dividing by the cutoff
gives limits of `2` on the powers of two and `4/3` on three times the powers of two. Thus a local
simple pole with positive residue alone cannot give the counting asymptotic in Delange's theorem.

## References

* H. Delange, *Généralisation du théorème de Ikehara* (1954), §5.3, second remark, p. 242,
  on the weaker conclusion under local hypotheses at the real pole.
-/

public section

open Filter Finset
open scoped Topology

namespace TauCeti.HigherPoleTauberian

/-- Weight each power of two, including one, by its size and all other naturals by zero. -/
noncomputable def dyadicWeight : ℕ → ℝ :=
  (Set.range fun j : ℕ ↦ 2 ^ j).indicator Nat.cast

open Classical in
/-- The dyadic weight is the identity on the powers of two and vanishes elsewhere. -/
theorem dyadicWeight_apply (n : ℕ) :
    dyadicWeight n = if ∃ j : ℕ, 2 ^ j = n then (n : ℝ) else 0 := by
  simp only [dyadicWeight, Set.indicator_apply, Set.mem_range]

/-- At a power of two the weight is the power itself. -/
@[simp]
theorem dyadicWeight_two_pow (j : ℕ) : dyadicWeight (2 ^ j) = (2 : ℝ) ^ j := by
  simp [dyadicWeight_apply]

/-- The index zero contributes no weight. -/
@[simp]
theorem dyadicWeight_zero : dyadicWeight 0 = 0 := by simp [dyadicWeight_apply]

/-- The first Dirichlet coefficient is one. -/
@[simp]
theorem dyadicWeight_one : dyadicWeight 1 = 1 := by simpa using dyadicWeight_two_pow 0

/-- The dyadic weights are nonnegative at every index. -/
theorem dyadicWeight_nonneg (n : ℕ) : 0 ≤ dyadicWeight n :=
  Set.indicator_nonneg (fun k _ ↦ Nat.cast_nonneg k) n

/-- The Dirichlet series of the dyadic weights has geometric ratio `exp ((1 - s) * log 2)`. -/
theorem LSeriesHasSum_dyadicWeight {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (dyadicWeight n : ℂ)) s
      (1 - Complex.exp ((1 - s) * Real.log 2))⁻¹ := by
  have hratio : ‖Complex.exp ((1 - s) * Real.log 2)‖ < 1 := by
    rw [Complex.norm_exp, Complex.re_mul_ofReal]
    simpa using mul_neg_of_neg_of_pos (sub_neg.mpr hs) (Real.log_pos one_lt_two)
  refine ((Nat.pow_right_injective (le_refl 2)).hasSum_iff fun n hn ↦ ?_).mp ?_
  · have hzero := Set.indicator_of_notMem hn (Nat.cast : ℕ → ℝ)
    simp [LSeries.term, dyadicWeight, hzero]
  · refine (hasSum_geometric_of_norm_lt_one hratio).congr_fun fun j ↦ ?_
    rw [Function.comp_apply, LSeries.term_of_ne_zero (pow_ne_zero _ two_ne_zero)]
    simp only [dyadicWeight_two_pow, Complex.ofReal_pow, Complex.ofReal_ofNat, Nat.cast_pow,
      Nat.cast_ofNat]
    have hpow : ((2 : ℂ) ^ j) ^ s = ((2 : ℂ) ^ s) ^ j := by
      simpa only [Nat.cast_ofNat, Complex.cpow_nat_mul] using
        (Complex.natCast_cpow_natCast_mul 2 j s).symm
    rw [hpow, ← div_pow]
    congr 1
    calc
      _ = (2 : ℂ) ^ (1 - s) := by rw [Complex.cpow_sub _ _ two_ne_zero, Complex.cpow_one]
      _ = _ := by
        rw [Complex.cpow_def_of_ne_zero two_ne_zero, Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num [mul_comm]

/-- On the whole half-open interval from `2 ^ j` to `2 ^ (j + 1)`, the inclusive count is
`1 + 2 + ⋯ + 2 ^ j = 2 ^ (j + 1) - 1`. -/
theorem summatory_dyadicWeight_of_mem_Ico {j : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ico ((2 : ℝ) ^ j) (2 ^ (j + 1))) :
    summatory (fun n : ℕ ↦ n) dyadicWeight x = 2 ^ (j + 1) - 1 := by
  let p : ℕ → ℕ := fun i ↦ 2 ^ i
  have hmem (i : ℕ) : p i ∈ normLE (fun n : ℕ ↦ n) x ↔ i < j + 1 := by
    simp only [mem_normLE, p, Nat.cast_pow, Nat.cast_ofNat]
    constructor
    · exact fun hi ↦ (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hi.trans_lt hx.2)
    · exact fun hi ↦ (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ hi)).trans hx.1
  rw [summatory_apply]
  calc
    _ = ∑ n ∈ (range (j + 1)).image p, dyadicWeight n := by
      apply (sum_subset _ _).symm
      · exact image_subset_iff.mpr fun i hi ↦ (hmem i).mpr (mem_range.mp hi)
      · intro n hn hn'
        rw [dyadicWeight_apply, ite_eq_right]
        rintro ⟨i, rfl⟩
        exact hn' (mem_image_of_mem p (mem_range.mpr ((hmem i).mp hn)))
    _ = ∑ i ∈ range (j + 1), (2 : ℝ) ^ i := by
      rw [sum_image (Nat.pow_right_injective (le_refl 2)).injOn]
      simp
    _ = _ := by norm_num [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]

/-- For a fixed multiplier `c ∈ [2^m, 2^(m+1))`, the count divided by its cutoff along
`c * 2^j` tends to `2^(m+1) / c`. -/
theorem tendsto_summatory_dyadicWeight_div_mul_two_pow {m : ℕ} {c : ℝ}
    (hc : c ∈ Set.Ico ((2 : ℝ) ^ m) (2 ^ (m + 1))) :
    Tendsto (fun j : ℕ ↦ summatory (fun n : ℕ ↦ n) dyadicWeight (c * 2 ^ j) / (c * 2 ^ j))
      atTop (𝓝 (2 ^ (m + 1) / c)) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc.1
  have hpow := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hzero := tendsto_inv_atTop_zero.comp (hpow.const_mul_atTop hc0)
  have hsub := (tendsto_const_nhds (x := (2 : ℝ) ^ (m + 1) / c)).sub hzero
  rw [sub_zero] at hsub
  refine hsub.congr fun j ↦ ?_
  have hmem : c * 2 ^ j ∈ Set.Ico ((2 : ℝ) ^ (m + j)) (2 ^ (m + j + 1)) := by
    have hj : 0 < (2 : ℝ) ^ j := by positivity
    simpa [Set.mem_Ico, pow_add, pow_succ, mul_right_comm] using
      And.intro (mul_le_mul_of_nonneg_right hc.1 hj.le) (mul_lt_mul_of_pos_right hc.2 hj)
  rw [summatory_dyadicWeight_of_mem_Ico hmem, Nat.add_right_comm m j 1, pow_add 2 (m + 1) j]
  dsimp
  field_simp

/-- The ratio of the dyadic count to the cutoff has no limit at infinity. -/
theorem not_tendsto_summatory_dyadicWeight_div (L : ℝ) :
    ¬ Tendsto (fun x : ℝ ↦ summatory (fun n : ℕ ↦ n) dyadicWeight x / x) atTop (𝓝 L) := by
  intro h
  have hp := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hlim (c : ℝ) (m : ℕ) (hc : c ∈ Set.Ico ((2 : ℝ) ^ m) (2 ^ (m + 1))) :
      L = 2 ^ (m + 1) / c :=
    tendsto_nhds_unique (h.comp (hp.const_mul_atTop (lt_of_lt_of_le (by positivity) hc.1)))
      (tendsto_summatory_dyadicWeight_div_mul_two_pow hc)
  have h₁ := hlim 1 0 (by norm_num [Set.mem_Ico])
  have h₃ := hlim 3 1 (by norm_num [Set.mem_Ico])
  norm_num at h₁ h₃
  linarith

end TauCeti.HigherPoleTauberian
