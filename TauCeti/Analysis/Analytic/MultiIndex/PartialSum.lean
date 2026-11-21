/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.MultiIndex.Coeff

/-!
# Partial sums of multi-index series

On a finite coordinate space `ι → 𝕜`, each homogeneous term `p k (fun _ ↦ z)` of a formal
multilinear series `p` expands into multi-index monomials of total degree `k`
(`FormalMultilinearSeries.apply_eq_sum_mvCoeff`). Summing over `k < T` expresses the Taylor partial
sum `p.partialSum T z` in terms of `p.mvCoeff`, and the triangle inequality bounds
`‖p k (fun _ ↦ z)‖` on the closed polydisc `‖z‖ ≤ r` by the multi-index majorant
`∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k`.

## Main results

* `FormalMultilinearSeries.partialSum_eq_sum_mvCoeff`: the Taylor partial sum of order `T` written
  degree by degree in terms of `FormalMultilinearSeries.mvCoeff`.
* `FormalMultilinearSeries.norm_apply_le_sum_mvCoeff`: norm bound on a homogeneous term on
  `‖z‖ ≤ r` in terms of `‖p.mvCoeff α‖ * r ^ k`.
-/

public section

open Finset

namespace FormalMultilinearSeries

variable {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The Taylor partial sum `p.partialSum T z` expanded in multi-index monomials of total degree
less than `T`. -/
theorem partialSum_eq_sum_mvCoeff [DecidableEq ι]
    (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (T : ℕ) (z : ι → 𝕜) :
    p.partialSum T z =
      ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, (∏ i, z i ^ α i) • p.mvCoeff α := by
  simp_rw [FormalMultilinearSeries.partialSum, p.apply_eq_sum_mvCoeff]

/-- On the closed polydisc `‖z‖ ≤ r`, the homogeneous term `p k (fun _ ↦ z)` has norm at most
`∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k`. -/
theorem norm_apply_le_sum_mvCoeff [DecidableEq ι]
    (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (k : ℕ) {z : ι → 𝕜} {r : ℝ} (hz : ‖z‖ ≤ r) :
    ‖p k (fun _ ↦ z)‖ ≤ ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k := by
  rw [p.apply_eq_sum_mvCoeff]
  refine (norm_sum_le _ _).trans (sum_le_sum fun α hα ↦ ?_)
  rw [norm_smul, norm_prod, mul_comm, ← (mem_piAntidiag.1 hα).1, ← prod_pow_eq_pow_sum]
  refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ ?_)
    (norm_nonneg _)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm z i).trans hz) _

end FormalMultilinearSeries
