/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Growth bounds for strongly continuous semigroups

This file contains exponential growth bounds for C₀-semigroups, including the
contraction case and the existence of a finite exponential type.

## References
Ported and adapted (Apache 2.0) from `mrdouglasny/hille-yosida`; references include
Engel--Nagel, Linares, Pazy, Hille, and Yosida.
-/

public section

noncomputable section

open scoped Topology NNReal

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-! ## Exponential growth bounds -/

/-- A C₀-semigroup has exponential growth bound `(ω, M)`, with `M ≥ 1`. -/
def StronglyContinuousSemigroup.HasGrowthBound
    (S : StronglyContinuousSemigroup X) (ω : ℝ) (M : ℝ) : Prop :=
  1 ≤ M ∧ ∀ (t : ℝ), 0 ≤ t → ‖S.realOperator t‖ ≤ M * Real.exp (ω * t)

omit [CompleteSpace X] in
/-- The multiplicative constant in a growth bound is at least one. -/
theorem StronglyContinuousSemigroup.HasGrowthBound.one_le
    {S : StronglyContinuousSemigroup X} {ω M : ℝ} (hb : S.HasGrowthBound ω M) :
    1 ≤ M := by
  unfold StronglyContinuousSemigroup.HasGrowthBound at hb
  exact hb.1

omit [CompleteSpace X] in
/-- The operator-norm estimate supplied by a growth bound. -/
theorem StronglyContinuousSemigroup.HasGrowthBound.bound
    {S : StronglyContinuousSemigroup X} {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (t : ℝ) (ht : 0 ≤ t) : ‖S.realOperator t‖ ≤ M * Real.exp (ω * t) := by
  unfold StronglyContinuousSemigroup.HasGrowthBound at hb
  exact hb.2 t ht

omit [CompleteSpace X] in
/-- A contraction semigroup has growth bound `(0, 1)`. -/
theorem ContractionSemigroup.hasGrowthBound (S : ContractionSemigroup X) :
    S.toStronglyContinuousSemigroup.HasGrowthBound 0 1 :=
  ⟨le_rfl, fun t ht => by simpa using S.contracting_real t ht⟩


/-! ## Growth Bounds and Exponential Type -/

/-- Every C₀-semigroup has a finite exponential growth bound
([EN] Prop. I.5.5, [Linares] Thm. 1). -/
theorem StronglyContinuousSemigroup.existsGrowthBound
    (S : StronglyContinuousSemigroup X) :
    ∃ (ω : ℝ) (M : ℝ), S.HasGrowthBound ω M := by
  obtain ⟨M, hM1, hMbound⟩ := S.normBoundedOnUnitInterval
  have hM_pos : 0 < M := by linarith
  refine ⟨Real.log M, M, hM1, fun t ht => ?_⟩
  -- Integer-time operator norm bound by induction: ‖S(k)‖ ≤ M^k
  have h_int_bound : ∀ (k : ℕ), ‖S.realOperator (↑k : ℝ)‖ ≤ M ^ k := by
    intro k; induction k with
    | zero =>
      simp only [Nat.cast_zero, S.realOperator_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      have : (↑(k + 1) : ℝ) = 1 + ↑k := by push_cast; ring
      rw [this, S.semigroup 1 ↑k (by linarith) (Nat.cast_nonneg k)]
      calc ‖(S.realOperator 1).comp (S.realOperator ↑k)‖
          ≤ ‖S.realOperator 1‖ * ‖S.realOperator ↑k‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * M ^ k :=
            mul_le_mul (hMbound 1 (by linarith) le_rfl) ih (norm_nonneg _) (by linarith)
        _ = M ^ (k + 1) := by ring
  set n := ⌊t⌋₊ with hn_def
  have hn_le : (↑n : ℝ) ≤ t := Nat.floor_le ht
  have hfrac_nn : 0 ≤ t - ↑n := sub_nonneg.mpr hn_le
  have hfrac_le1 : t - ↑n ≤ 1 := by
    have := Nat.lt_floor_add_one t; linarith
  have h_eq : (t - ↑n) + ↑n = t := by ring
  have h_sg := S.semigroup (t - ↑n) ↑n hfrac_nn (Nat.cast_nonneg n)
  rw [h_eq] at h_sg
  rw [h_sg]
  calc ‖(S.realOperator (t - ↑n)).comp (S.realOperator ↑n)‖
      ≤ ‖S.realOperator (t - ↑n)‖ * ‖S.realOperator ↑n‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ M * M ^ n :=
        mul_le_mul (hMbound _ hfrac_nn hfrac_le1) (h_int_bound n) (norm_nonneg _) (by linarith)
    _ ≤ M * Real.exp (Real.log M * t) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        calc (M : ℝ) ^ n
            = Real.exp (↑n * Real.log M) := by
              rw [Real.exp_nat_mul, Real.exp_log hM_pos]
          _ ≤ Real.exp (Real.log M * t) := by
              apply Real.exp_le_exp.mpr
              calc ↑n * Real.log M ≤ t * Real.log M :=
                    mul_le_mul_of_nonneg_right hn_le (Real.log_nonneg hM1)
                _ = Real.log M * t := by ring

end TauCeti.Semigroups

end
