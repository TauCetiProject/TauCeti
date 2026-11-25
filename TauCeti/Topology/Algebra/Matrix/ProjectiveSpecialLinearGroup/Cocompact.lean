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
      Tendsto (fun k ↦ (m (φ k))⁻¹ • (A (φ k) : Matrix n n 𝕜)) atTop (𝓝 B) :=
  Matrix.exists_tendsto_inv_smul_of_tendsto_cocompact
    (tendsto_coe_cocompact_of_tendsto_cocompact hg hA)
    (isBoundedUnder_of ⟨1, fun k ↦ by simp [(A k).property]⟩)

end Matrix.ProjectiveSpecialLinearGroup
