/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Graph
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Graph

/-!
# Embedded Lagrangian graphs

The graph of a diffeomorphism is a Lagrangian embedding for the difference of two
nondegenerate forms exactly when the diffeomorphism preserves those forms. In particular,
the diagonal is a Lagrangian embedding. This realizes identity correspondences and graphs of
canonical transformations as actual embedded submanifolds.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Sections 3 and 5.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}

/-- A diffeomorphism has an embedded Lagrangian graph exactly when it preserves the forms. -/
@[simp]
theorem isLagrangianEmbedding_graph_iff (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate)
    (φ : M ≃ₘ⟮I, J⟯ N) :
    (hσ.twistedProd hτ).IsLagrangianEmbedding I (fun x ↦ (x, φ x)) ↔
      SmoothForm.mpullback φ φ.contMDiff τ = σ := by
  rw [isLagrangianEmbedding_iff_of_isSmoothEmbedding
      φ.contMDiff.isSmoothEmbedding_graph,
    hσ.isLagrangianMap_graph_iff hτ φ]

/-- The diagonal is an embedded Lagrangian for the difference form. -/
@[simp]
theorem isLagrangianEmbedding_diagonal (hσ : σ.IsNondegenerate) :
    (hσ.twistedProd hσ).IsLagrangianEmbedding I (fun x : M ↦ (x, x)) := by
  exact (isLagrangianEmbedding_iff_of_isSmoothEmbedding
    contMDiff_id.isSmoothEmbedding_graph).mpr hσ.isLagrangianMap_diagonal

end TauCeti.SmoothTwoForm.IsNondegenerate
