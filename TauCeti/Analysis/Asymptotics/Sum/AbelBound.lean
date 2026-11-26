/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.AbelSummation

/-!
# A norm bound by Abel summation

Bounded coefficient partial sums allow an estimate for a weighted series in terms of the
integrated absolute derivative of a smooth weight. Unlike the monotone-weight form, this also
applies to a weight that first increases and then decreases.
-/

public section

open Asymptotics Filter Finset MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- For a weight tending to zero at infinity, a bound on the coefficient partial sums times the
integral of the norm of the weight's derivative bounds the norm of the weighted sum. -/
theorem exists_tendsto_sum_mul_and_norm_le {𝕜 : Type*} [RCLike 𝕜] {c : ℕ → 𝕜} {f : ℝ → 𝕜}
    {B : ℝ} (hc : ∀ n, ‖∑ k ∈ Icc 0 n, c k‖ ≤ B)
    (hf : ∀ t ∈ Set.Ici 0, DifferentiableAt ℝ f t)
    (hdf : IntegrableOn (deriv f) (Set.Ici 0)) (hlim : Tendsto f atTop (𝓝 0)) :
    ∃ L, Tendsto (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, f k * c k) atTop (𝓝 L) ∧
      ‖L‖ ≤ B * ∫ t in Ioi 0, ‖deriv f t‖ := by
  have hzero : Tendsto (fun n : ℕ ↦ f n * ∑ k ∈ Icc 0 n, c k) atTop (𝓝 0) := by
    refine (hlim.comp tendsto_natCast_atTop_atTop).op_zero_isBoundedUnder_le
      (isBoundedUnder_of ⟨B, hc⟩) (· * ·) norm_mul_le
  have hbound (t : ℝ) : ‖deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ B * ‖deriv f t‖ := by
    rw [norm_mul, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hc _) (norm_nonneg _)
  have hbig : (fun t ↦ deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] deriv f :=
    IsBigO.of_bound B (Eventually.of_forall hbound)
  have hsum := tendsto_sum_mul_atTop_nhds_one_sub_integral c hf hdf.locallyIntegrableOn
    hzero hbig (integrableAtFilter_atTop_iff.mpr ⟨0, hdf⟩)
  refine ⟨_, hsum, ?_⟩
  rw [zero_sub, norm_neg, ← integral_const_mul]
  exact norm_integral_le_of_norm_le ((hdf.mono_set Ioi_subset_Ici_self).norm.const_mul B)
    (Eventually.of_forall hbound)

end TauCeti
