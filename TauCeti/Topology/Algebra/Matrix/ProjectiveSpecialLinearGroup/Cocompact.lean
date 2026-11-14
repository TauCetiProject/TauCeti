/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

import TauCeti.Analysis.Matrix.Normed

/-!
# Escaping sequences in projective special linear groups

A sequence leaving every compact subset of `PSL(n, R)`, with its quotient topology, has lifts to
`SL(n, R)` leaving every compact set of matrices: the closed embedding `SL(n, R) → Matrix n n R`
and the continuous quotient map `SL(n, R) → PSL(n, R)` both pull compact sets back to compact
sets. Over a proper normed field the norms of the lifts therefore tend to infinity, so dividing
each lift by an entry of largest norm gives matrices of norm one with determinants tending to
zero. A subsequence of them converges to a nonzero singular matrix.

## Main results

* `Matrix.ProjectiveSpecialLinearGroup.tendsto_coe_cocompact_of_tendsto_cocompact`: lifts of an
  escaping sequence in `PSL(n, R)` escape every compact set of matrices.
* `Matrix.ProjectiveSpecialLinearGroup.exists_tendsto_inv_smul_of_tendsto_cocompact`: rescaled
  lifts of an escaping sequence in `PSL(n, 𝕜)` subconverge to a nonzero singular matrix.
-/

public section

open Filter Topology

namespace Matrix.ProjectiveSpecialLinearGroup

/-- Lifts to `SL(n, R)` of elements of `PSL(n, R)` escaping to infinity escape to infinity in
`Matrix n n R`. -/
theorem tendsto_coe_cocompact_of_tendsto_cocompact {n R α : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T1Space R] {l : Filter α}
    {g : α → ProjectiveSpecialLinearGroup n R}
    (hg : Tendsto g l (cocompact (ProjectiveSpecialLinearGroup n R)))
    {A : α → SpecialLinearGroup n R} (hA : ∀ a, (A a : ProjectiveSpecialLinearGroup n R) = g a) :
    Tendsto (fun a ↦ (A a : Matrix n n R)) l (cocompact (Matrix n n R)) := by
  have hA' : Tendsto A l (cocompact (SpecialLinearGroup n R)) :=
    (tendsto_comap_iff.2 (hg.congr fun a ↦ (hA a).symm)).mono_right <| comap_cocompact_le
      (f := (QuotientGroup.mk : SpecialLinearGroup n R → ProjectiveSpecialLinearGroup n R))
      QuotientGroup.continuous_mk
  exact SpecialLinearGroup.isClosedEmbedding_val.tendsto_cocompact.comp hA'

open scoped Matrix.Norms.Elementwise in
/-- **Escaping sequences converge projectively to singular matrices.** Lifts `A k` to `SL(n, 𝕜)`
of a sequence of elements of `PSL(n, 𝕜)` escaping to infinity, divided by suitable scalars `m k`,
have a subsequence converging to a nonzero singular matrix. -/
theorem exists_tendsto_inv_smul_of_tendsto_cocompact {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] [NormedField 𝕜] [ProperSpace 𝕜] {g : ℕ → ProjectiveSpecialLinearGroup n 𝕜}
    (hg : Tendsto g atTop (cocompact (ProjectiveSpecialLinearGroup n 𝕜)))
    {A : ℕ → SpecialLinearGroup n 𝕜} (hA : ∀ k, (A k : ProjectiveSpecialLinearGroup n 𝕜) = g k) :
    ∃ (m : ℕ → 𝕜) (φ : ℕ → ℕ) (B : Matrix n n 𝕜), StrictMono φ ∧ B ≠ 0 ∧ B.det = 0 ∧
      Tendsto (fun k ↦ (m (φ k))⁻¹ • (A (φ k) : Matrix n n 𝕜)) atTop (𝓝 B) := by
  have hnorm : Tendsto (fun k ↦ ‖(A k : Matrix n n 𝕜)‖) atTop atTop :=
    tendsto_norm_cocompact_atTop.comp (tendsto_coe_cocompact_of_tendsto_cocompact hg hA)
  -- Divide `A k` by an entry `m k` of largest norm, so that the quotient has norm one and
  -- determinant `(m k)⁻ⁿ`, which tends to zero.
  choose p hp using fun k ↦ Finite.exists_max fun p : n × n ↦
    ‖(A k : Matrix n n 𝕜) p.1 p.2‖
  set m : ℕ → 𝕜 := fun k ↦ (A k : Matrix n n 𝕜) (p k).1 (p k).2
  have hm_norm : ∀ k, ‖m k‖ = ‖(A k : Matrix n n 𝕜)‖ := fun k ↦
    le_antisymm (norm_apply_le_norm _) <|
      (norm_le_iff (norm_nonneg _)).2 fun i j ↦ hp k (i, j)
  have hm0 : ∀ k, m k ≠ 0 := fun k ↦ by
    rw [← norm_ne_zero_iff, hm_norm, norm_ne_zero_iff]
    exact fun h ↦ by simpa [h] using (A k).2
  set C : ℕ → Matrix n n 𝕜 := fun k ↦ (m k)⁻¹ • (A k : Matrix n n 𝕜) with hC
  have hC_norm : ∀ k, ‖C k‖ = 1 := fun k ↦ by
    rw [hC, norm_smul, norm_inv, hm_norm, inv_mul_cancel₀]
    rw [← hm_norm, norm_ne_zero_iff]
    exact hm0 k
  obtain ⟨B, -, φ, hφ, hCB⟩ :=
    (isCompact_closedBall (0 : Matrix n n 𝕜) 1).tendsto_subseq (x := C)
      fun k ↦ by simp [hC_norm]
  refine ⟨m, φ, B, hφ, ?_, ?_, hCB⟩
  · have hB1 : ‖B‖ = 1 := tendsto_nhds_unique ((continuous_norm.tendsto B).comp hCB)
      (by simp [Function.comp_def, hC_norm])
    rintro rfl
    simp at hB1
  · refine tendsto_nhds_unique ((continuous_id.matrix_det.tendsto B).comp hCB) ?_
    have hdetC : ∀ k, (C k).det = (m k)⁻¹ ^ Fintype.card n := fun k ↦ by
      simp [hC, (A k).2]
    simp only [Function.comp_def, id_eq, hdetC]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [hm_norm, Fintype.card_ne_zero] using ((tendsto_inv_atTop_zero.comp
      (hnorm.comp hφ.tendsto_atTop)).pow (Fintype.card n))

end Matrix.ProjectiveSpecialLinearGroup
