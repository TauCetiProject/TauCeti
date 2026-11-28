/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.InvSubOne

/-!
# Discrete exponential moments

A positive-index exponential sum with a power weight is bounded by the corresponding
inverse power of the decay rate, uniformly over all positive rates.
-/

public section

open Real

namespace TauCeti

/-- The positive-index exponential moment of order `a ≥ 0` is summable, with a bound
uniform in the positive scale `u`. -/
theorem exists_summable_and_tsum_rpow_mul_exp_neg_le {a : ℝ} (ha : 0 ≤ a) :
    ∃ C > 0, ∀ u > 0,
      Summable (fun n : ℕ+ ↦ (n : ℝ) ^ a * exp (-(n * u))) ∧
        (∑' n : ℕ+, (n : ℝ) ^ a * exp (-(n * u))) ≤ C * u ^ (-(a + 1)) := by
  obtain ⟨C, _, hmax⟩ := exists_rpow_mul_exp_neg_mul_le ha one_half_pos
  have hC : 0 < C := (exp_pos (-(1 / 2))).trans_le (by simpa using hmax 1 zero_le_one)
  refine ⟨2 * C, by positivity, fun u hu ↦ ?_⟩
  let v := u / 2
  have hv : 0 < v := by positivity
  have hg : HasSum (fun n : ℕ+ ↦ exp (-(n * v))) (1 / (exp v - 1)) := by
    refine (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ ↦ exp (-((n : ℝ) * v)))).2 ?_
    simpa only [Nat.cast_succ, one_div] using Real.hasSum_exp_neg_nat_succ_mul hv
  have hb (n : ℕ+) : (n : ℝ) ^ a * exp (-(n * u)) ≤ (C * u ^ (-a)) * exp (-(n * v)) := by
    have h := hmax ((n : ℝ) * u) (by positivity)
    rw [mul_rpow (by positivity) hu.le] at h
    calc
      _ = (((n : ℝ) ^ a * u ^ a) * exp (-(1 / 2) * (n * u))) *
          u ^ (-a) * exp (-(n * v)) := by
        have he : exp (-(1 / 2) * (n * u)) * exp (-(n * v)) = exp (-(n * u)) := by
          rw [← exp_add]
          congr 1
          dsimp [v]
          ring
        rw [rpow_neg hu.le]
        calc
          _ = (n : ℝ) ^ a * (exp (-(1 / 2) * (n * u)) * exp (-(n * v))) := by rw [he]
          _ = _ := by field_simp [(rpow_pos_of_pos hu a).ne']
      _ ≤ _ := by gcongr; simpa only [neg_mul] using h
  have hs := (hg.mul_left (C * u ^ (-a))).summable
  have hf := Summable.of_nonneg_of_le (fun _ ↦ by positivity) hb hs
  refine ⟨hf, (hf.tsum_le_tsum hb hs).trans ?_⟩
  rw [(hg.mul_left _).tsum_eq]
  have hden : v ≤ exp v - 1 := by linarith [add_one_le_exp v]
  calc
    _ ≤ (C * u ^ (-a)) * (1 / v) := by gcongr
    _ = 2 * C * u ^ (-(a + 1)) := by
      rw [neg_add, rpow_add hu, rpow_neg hu.le, rpow_neg_one]
      dsimp [v]
      ring

end TauCeti
