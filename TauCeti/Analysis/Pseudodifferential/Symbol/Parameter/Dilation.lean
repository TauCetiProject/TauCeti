/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Basic

/-!
# Norm bounds for the parameter dilations

The estimates of a strongly parameter-dependent symbol (`TauCeti.ParameterSymbol`) are stated for
the dilated derivatives `TauCeti.parameterIteratedFDeriv`, in which every direction is dilated by
the weight `w = 1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)` under `TauCeti.parameterDilation`: the position direction
is fixed, the frequency direction is scaled by `w` and the spectral parameter direction by `w ^ 2`.
This file bounds these dilations by ordinary norms.

## Main declarations

* `TauCeti.norm_parameterDilation_le`: for `t ≥ 1` the dilation by `t` has norm at most `t ^ 2`.
* `TauCeti.norm_parameterIteratedFDeriv_le`: the dilated derivative of order `k` is at most the
  ordinary one times `w ^ (2 k)`.

## References

* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

noncomputable section

namespace TauCeti

variable {n : ℕ}

/-- For `t ≥ 1`, the dilation by `t` has norm at most `t ^ 2`: it scales the spectral parameter
direction by `t ^ 2`, the frequency direction by `t` and fixes the position direction. -/
theorem norm_parameterDilation_le {t : ℝ} (ht : 1 ≤ t) : ‖parameterDilation n t‖ ≤ t ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have h₁ : ‖v.1.1‖ ≤ ‖v‖ := (norm_fst_le v.1).trans (norm_fst_le v)
  have h₂ : ‖v.1.2‖ ≤ ‖v‖ := (norm_snd_le v.1).trans (norm_fst_le v)
  have h₃ : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  have ht2 : t ≤ t ^ 2 := by nlinarith
  rw [parameterDilation_apply]
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, ?_⟩ <;> dsimp only
  · exact h₁.trans (le_mul_of_one_le_left (norm_nonneg v) (by nlinarith))
  · rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    exact mul_le_mul ht2 h₂ (norm_nonneg _) (sq_nonneg t)
  · rw [norm_smul, Real.norm_of_nonneg (sq_nonneg t)]
    exact mul_le_mul_of_nonneg_left h₃ (sq_nonneg t)

/-- The dilated derivative is at most the ordinary derivative times `w ^ (2 k)`, for the weight
`w = parameterWeight ξ z ≥ 1`: each of the `k` directions is dilated by at most `w ^ 2`. -/
theorem norm_parameterIteratedFDeriv_le {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (k : ℕ) (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A) (x ξ : CoordinateSpace n)
    (z : ℂ) : ‖parameterIteratedFDeriv k f ((x, ξ), z)‖ ≤
      ‖iteratedFDeriv ℝ k f ((x, ξ), z)‖ * (parameterWeight ξ z ^ 2) ^ k := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [parameterIteratedFDeriv_apply]
  calc _ ≤ ‖iteratedFDeriv ℝ k f ((x, ξ), z)‖ *
        ∏ i, ‖parameterDilation n (parameterWeight ξ z) (v i)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ ‖iteratedFDeriv ℝ k f ((x, ξ), z)‖ * ∏ i, (parameterWeight ξ z ^ 2 * ‖v i‖) := by
        gcongr with i
        exact ((parameterDilation n _).le_opNorm (v i)).trans (mul_le_mul_of_nonneg_right
          (norm_parameterDilation_le (one_le_parameterWeight ξ z)) (norm_nonneg _))
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          mul_assoc]

end TauCeti
