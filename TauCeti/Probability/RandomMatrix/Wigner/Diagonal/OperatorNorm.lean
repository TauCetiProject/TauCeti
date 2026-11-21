/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Probability.RandomMatrix.Wigner.Basic
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Probability.IdentDistrib

/-!
# Operator norm of the Wigner diagonal perturbation

For identically distributed diagonal entries of finite second moment, removing the diagonal
changes the normalized Wigner matrix by an operator-norm error that tends to zero almost surely.
-/

public section

open Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology NNReal Matrix.Norms.L2Operator

namespace TauCeti.Probability

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'}

/-- The operator norm of the difference between a normalized Wigner corner and its
zero-diagonal version tends to zero almost surely for identically distributed diagonal
entries of finite second moment. No independence is required. -/
theorem ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_zero
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}
    {Y : Ω' → ℝ} (hid : ∀ i, IdentDistrib (η i) Y P Q) (hη : MemLp Y 2 Q) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ‖wignerMatrix ξ η (n + 1) ω -
      wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω‖) atTop (𝓝 0) := by
  have hm : ∀ᶠ n : ℕ in atTop, ((n + 1 : ℕ) : ℝ) ≤ Real.sqrt (n + 1 : ℕ) ^ 2 :=
    .of_forall fun n ↦ (Real.sq_sqrt (Nat.cast_nonneg (n + 1))).ge
  filter_upwards [ae_eventually_forall_lt_norm_le_mul_of_identDistrib (p := 2) hid hη
    Real.tendsto_sqrt_natCast_add_one_atTop
    (by simpa only [NNReal.coe_ofNat, Real.rpow_two] using hm)] with ω hω
  refine Metric.tendsto_atTop.2 fun ε hε ↦ eventually_atTop.1 ?_
  filter_upwards [hω (ε / 2) (half_pos hε)] with n hn
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _),
    wignerMatrix_eq_add_diagonal ξ η, add_sub_cancel_left, l2_opNorm_diagonal]
  refine ((pi_norm_le_iff_of_nonneg (half_pos hε).le).2 fun i ↦ ?_).trans_lt (half_lt_self hε)
  rw [Complex.norm_real, norm_div, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_le_iff₀ (Real.sqrt_pos.2 (by positivity))]
  exact hn _ i.isLt

end TauCeti.Probability
