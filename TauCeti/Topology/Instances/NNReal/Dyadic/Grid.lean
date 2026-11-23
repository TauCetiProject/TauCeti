/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic nonnegative rationals and downward floor approximations

For each level `n : ℕ`, the dyadic nonnegative rationals `k / 2 ^ n : ℚ≥0` form a nested grid of
mesh `2⁻ⁿ` on `ℝ≥0`. Every `t : ℝ≥0` is approximated from below by
`approxDyadicNNRat n t = ⌊(t : ℝ) * 2 ^ n⌋₊ / 2 ^ n`, at distance at most `2⁻ⁿ`, and these
approximants converge to `t` as `n → ∞`.

## Main definitions and results

* `TauCeti.dyadicNNRat`: the `k`-th level-`n` dyadic nonnegative rational `k / 2 ^ n : ℚ≥0`.
* `TauCeti.dyadicNNRat_double` and `TauCeti.dyadicNNRat_scale`: nesting identities across dyadic
  levels.
* `TauCeti.dist_dyadicNNRat_succ` and `TauCeti.edist_dyadicNNRat_succ`: adjacent dyadic grid points
  at level `n` are at distance `2⁻ⁿ`.
* `TauCeti.approxDyadicNNRat`: downward level-`n` dyadic floor approximation of `t : ℝ≥0` in `ℚ≥0`.
* `TauCeti.coe_approxDyadicNNRat_le`, `TauCeti.dist_approxDyadicNNRat_le`,
  `TauCeti.edist_approxDyadicNNRat_le`, `TauCeti.tendsto_approxDyadicNNRat`, and
  `TauCeti.tendsto_approxDyadicNNRat_apply_of_continuousAt`: error bounds and convergence of
  `approxDyadicNNRat n t` to `t` and through functions continuous at `t` on `Iic T`.
-/

public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti

/-- The `k`-th dyadic nonnegative rational `k / 2 ^ n` at scale `2⁻ⁿ`. -/
def dyadicNNRat (n k : ℕ) : ℚ≥0 := (k : ℚ≥0) / 2 ^ n

/-- Definitional unfolding of `dyadicNNRat`. -/
theorem dyadicNNRat_def (n k : ℕ) : dyadicNNRat n k = (k : ℚ≥0) / 2 ^ n := (rfl)

/-- The `0`-th dyadic rational at any level is `0`. -/
@[simp]
theorem dyadicNNRat_zero (n : ℕ) : dyadicNNRat n 0 = 0 := by
  simp [dyadicNNRat_def]

/-- Level-`0` dyadic rationals are the natural numbers. -/
@[simp]
theorem dyadicNNRat_zero_left (k : ℕ) : dyadicNNRat 0 k = k := by
  simp [dyadicNNRat_def]

/-- Coercion of `dyadicNNRat n k` to `ℝ≥0`. -/
@[simp]
theorem coe_dyadicNNRat (n k : ℕ) : (dyadicNNRat n k : ℝ≥0) = (k : ℝ≥0) / 2 ^ n := by
  simp [dyadicNNRat_def]

/-- A level-`n` dyadic rational lies in `[0, N]` if and only if its numerator is at most
`N * 2 ^ n`. -/
theorem coe_dyadicNNRat_le_natCast_iff {N n k : ℕ} :
    (dyadicNNRat n k : ℝ≥0) ≤ N ↔ k ≤ N * 2 ^ n := by
  rw [coe_dyadicNNRat, div_le_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ n)]
  exact_mod_cast Iff.rfl

/-- Doubling the index and increasing the level by one preserves a dyadic rational. -/
theorem dyadicNNRat_double (n k : ℕ) :
    dyadicNNRat (n + 1) (2 * k) = dyadicNNRat n k := by
  rw [dyadicNNRat_def, dyadicNNRat_def]
  push_cast
  rw [pow_succ', mul_div_mul_left _ _ (two_ne_zero' ℚ≥0)]

/-- Refining a dyadic rational by `d` levels multiplies its index by `2 ^ d`. -/
theorem dyadicNNRat_scale (n d k : ℕ) :
    dyadicNNRat (n + d) (k * 2 ^ d) = dyadicNNRat n k := by
  rw [dyadicNNRat_def, dyadicNNRat_def]
  push_cast
  rw [pow_add, mul_div_mul_right _ _ (pow_ne_zero d (two_ne_zero' ℚ≥0))]

/-- Adjacent level-`n` dyadic rationals are at distance `2⁻ⁿ`. -/
theorem dist_dyadicNNRat_succ (n k : ℕ) :
    dist (dyadicNNRat n k : ℝ≥0) (dyadicNNRat n (k + 1) : ℝ≥0) = (2 : ℝ)⁻¹ ^ n := by
  rw [NNReal.dist_eq, coe_dyadicNNRat, coe_dyadicNNRat, inv_pow]
  push_cast
  have hle : (k : ℝ) / 2 ^ n ≤ ((k : ℝ) + 1) / 2 ^ n := by gcongr; linarith
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
  ring

/-- Adjacent level-`n` dyadic rationals are at extended distance `2⁻ⁿ`. -/
theorem edist_dyadicNNRat_succ (n k : ℕ) :
    edist (dyadicNNRat n k : ℝ≥0) (dyadicNNRat n (k + 1) : ℝ≥0) = (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [edist_dist, dist_dyadicNNRat_succ, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]

/-- Downward floor approximation of `t : ℝ≥0` on the level-`n` dyadic grid in `ℚ≥0`. -/
noncomputable def approxDyadicNNRat (n : ℕ) (t : ℝ≥0) : ℚ≥0 :=
  dyadicNNRat n ⌊(t : ℝ) * 2 ^ n⌋₊

/-- Definitional unfolding of `approxDyadicNNRat`. -/
theorem approxDyadicNNRat_def (n : ℕ) (t : ℝ≥0) :
    approxDyadicNNRat n t = dyadicNNRat n ⌊(t : ℝ) * 2 ^ n⌋₊ := (rfl)

/-- The downward dyadic floor approximation of `t` does not exceed `t`. -/
theorem coe_approxDyadicNNRat_le (n : ℕ) (t : ℝ≥0) :
    (approxDyadicNNRat n t : ℝ≥0) ≤ t := by
  rw [← NNReal.coe_le_coe, approxDyadicNNRat_def, coe_dyadicNNRat]
  push_cast
  exact (div_le_iff₀ (by positivity)).2 (Nat.floor_le (by positivity))

/-- The downward level-`n` dyadic floor approximation is within `2⁻ⁿ` of `t`. -/
theorem dist_approxDyadicNNRat_le (n : ℕ) (t : ℝ≥0) :
    dist (approxDyadicNNRat n t : ℝ≥0) t ≤ (2 : ℝ)⁻¹ ^ n := by
  rw [NNReal.dist_eq, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 (coe_approxDyadicNNRat_le n t))),
    approxDyadicNNRat_def, coe_dyadicNNRat, inv_pow]
  push_cast
  have hdiv : (t : ℝ) < ((⌊(t : ℝ) * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n :=
    (lt_div_iff₀ (by positivity)).2 (Nat.lt_floor_add_one _)
  linarith [add_div (⌊(t : ℝ) * 2 ^ n⌋₊ : ℝ) 1 ((2 : ℝ) ^ n), one_div ((2 : ℝ) ^ n)]

/-- The downward level-`n` dyadic floor approximation is within extended distance `2⁻ⁿ` of `t`. -/
theorem edist_approxDyadicNNRat_le (n : ℕ) (t : ℝ≥0) :
    edist (approxDyadicNNRat n t : ℝ≥0) t ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [edist_dist]
  calc ENNReal.ofReal (dist (approxDyadicNNRat n t : ℝ≥0) t)
      ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) := ENNReal.ofReal_le_ofReal (dist_approxDyadicNNRat_le n t)
    _ = (2 : ℝ≥0∞)⁻¹ ^ n := by
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos zero_lt_two,
          ENNReal.ofReal_ofNat]

/-- Downward dyadic floor approximations converge to every `t : ℝ≥0`. -/
theorem tendsto_approxDyadicNNRat (t : ℝ≥0) :
    Tendsto (fun n ↦ (approxDyadicNNRat n t : ℝ≥0)) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  convert (tendsto_nat_floor_mul_div_atTop t.coe_nonneg).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)) using 1
  ext n
  simp [approxDyadicNNRat_def]

/-- If `g : Iic T → E` is continuous at `t` and agrees with `f : ℚ≥0 → E` on dyadic rationals in
`[0, T]`, then `f (approxDyadicNNRat n t.1)` converges to `g t`. -/
theorem tendsto_approxDyadicNNRat_apply_of_continuousAt {E : Type*} [TopologicalSpace E]
    {T : ℝ≥0} {f : ℚ≥0 → E} {g : Iic T → E} {t : Iic T} (hg : ContinuousAt g t)
    (hg_dyad : ∀ n k (hk : (dyadicNNRat n k : ℝ≥0) ≤ T),
      g ⟨(dyadicNNRat n k : ℝ≥0), hk⟩ = f (dyadicNNRat n k)) :
    Tendsto (fun n ↦ f (approxDyadicNNRat n t.val)) atTop (𝓝 (g t)) := by
  have hconv : Tendsto (fun n ↦ (⟨(approxDyadicNNRat n t.val : ℝ≥0),
      (coe_approxDyadicNNRat_le n t.val).trans t.property⟩ : Iic T)) atTop (𝓝 t) :=
    tendsto_subtype_rng.2 (tendsto_approxDyadicNNRat t.val)
  refine (hg.tendsto.comp hconv).congr fun n ↦ ?_
  simp only [Function.comp_apply, approxDyadicNNRat_def]
  exact hg_dyad n ⌊(t.val : ℝ) * 2 ^ n⌋₊ ((coe_approxDyadicNNRat_le n t.val).trans t.property)

end TauCeti
