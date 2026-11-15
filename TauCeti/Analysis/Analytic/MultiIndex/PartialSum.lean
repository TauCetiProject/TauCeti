/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import TauCeti.Analysis.Analytic.MultiIndex.Coeff
import Mathlib.Analysis.Analytic.Constructions

/-!
# Partial sums and coordinate reindexing of multi-index series

On a finite coordinate space `ι → 𝕜`, each homogeneous term `p k (fun _ ↦ z)` of a formal
multilinear series `p` expands into multi-index monomials of total degree `k`
(`FormalMultilinearSeries.apply_eq_sum_mvCoeff`). Summing over `k < T` expresses the Taylor partial
sum `p.partialSum T z` in terms of `p.mvCoeff`, and the triangle inequality bounds
`‖p k (fun _ ↦ z)‖` and `‖p.partialSum T z‖` on the closed polydisc `‖z‖ ≤ r` by the multi-index
majorant `∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k`.

This file also records the invariance of `FormalMultilinearSeries.mvCoeff` under reindexing the
coordinates by an equivalence `κ ≃ ι`, used when transporting polydisc integral formulas from
`Fin n → ℂ` to an arbitrary finite index type `ι`.

## Main results

* `FormalMultilinearSeries.partialSum_eq_sum_mvCoeff`: the Taylor partial sum of order `T` written
  degree by degree in terms of `FormalMultilinearSeries.mvCoeff`.
* `FormalMultilinearSeries.norm_apply_le_sum_mvCoeff` and
  `FormalMultilinearSeries.norm_partialSum_le_sum_mvCoeff`: norm bounds on homogeneous terms and
  partial sums on `‖z‖ ≤ r` in terms of `‖p.mvCoeff α‖ * r ^ k`.
* `FormalMultilinearSeries.mvCoeff_compContinuousLinearMap_piCongrLeft`: reindexing coordinates by
  `e : κ ≃ ι` pulls `p.mvCoeff α` back to `α ∘ e`.
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

/-- On the closed polydisc `‖z‖ ≤ r`, the Taylor partial sum `p.partialSum T z` has norm at most
`∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k`. -/
theorem norm_partialSum_le_sum_mvCoeff [DecidableEq ι]
    (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (T : ℕ) {z : ι → 𝕜} {r : ℝ} (hz : ‖z‖ ≤ r) :
    ‖p.partialSum T z‖ ≤
      ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k :=
  (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ p.norm_apply_le_sum_mvCoeff k hz)

/-- Reindexing coordinates along `e : κ ≃ ι` pulls back the multi-index coefficients of `p`: the
coefficient of `p.compContinuousLinearMap (piCongrLeft 𝕜 (fun _ ↦ 𝕜) e)` at `α ∘ e` is
`p.mvCoeff α`. -/
theorem mvCoeff_compContinuousLinearMap_piCongrLeft {κ : Type*} [Fintype κ]
    (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (e : κ ≃ ι) (α : ι → ℕ) :
    (p.compContinuousLinearMap
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : ι ↦ 𝕜) e : (κ → 𝕜) →L[𝕜] (ι → 𝕜))).mvCoeff
        (α ∘ e) = p.mvCoeff α := by
  classical
  set k := ∑ i, α i
  have hk : ∑ j, (α ∘ e) j = k := e.sum_comp α
  rw [mvCoeff_eq_sum _ hk, mvCoeff_eq_sum p rfl]
  refine sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin k)) e) (fun a ↦ ?_) (fun a _ ↦ ?_)
  · simp only [mem_filter, mem_univ, true_and, Function.comp_apply, Equiv.arrowCongr_apply,
      Equiv.refl_symm]
    refine ⟨fun h i ↦ ?_, fun h j ↦ ?_⟩
    · rw [← e.apply_symm_apply i, ← h (e.symm i)]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun r ↦ e.apply_eq_iff_eq)
    · rw [← h (e j)]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun r ↦ e.apply_eq_iff_eq.symm)
  · simp only [compContinuousLinearMap_apply, Equiv.arrowCongr_apply, Equiv.refl_symm,
      Function.comp_apply]
    congr 1
    ext r i
    change Equiv.piCongrLeft (fun _ : ι ↦ 𝕜) e (Pi.single (a r) 1) i =
      Pi.single (M := fun _ : ι ↦ 𝕜) (e (a r)) 1 i
    rw [Equiv.piCongrLeft_apply]
    simp [Pi.single_apply, e.symm_apply_eq]

end FormalMultilinearSeries
