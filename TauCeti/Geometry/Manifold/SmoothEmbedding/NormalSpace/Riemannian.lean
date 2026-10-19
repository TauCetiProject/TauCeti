/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Orthogonal representatives of normal classes

For a smooth embedding into a manifold whose tangent spaces carry a Riemannian metric, every
intrinsic normal class has a unique representative orthogonal to the tangent space of the
embedded submanifold. This identifies the intrinsic normal space with the orthogonal complement
of the embedded tangent space, using Mathlib's `Submodule.quotientEquivOfIsTopCompl`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

noncomputable section

open Bundle Manifold
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti.SmoothEmbedding

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

variable [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

private theorem isTopCompl_tangentRange_orthogonal
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    Submodule.IsTopCompl (f.tangentRange x hn)
      (Submodule.orthogonal (f.tangentRange x hn)) := by
  have hclosed : IsClosed
      (f.tangentRange x hn : Set (TangentSpace J (f x))) :=
    f.isClosed_tangentRange x hn
  let : CompleteSpace (f.tangentRange x hn) := hclosed.completeSpace_coe
  exact (f.tangentRange x hn).isTopCompl_orthogonal

/-- Orthogonal representatives identify an intrinsic normal space with the orthogonal complement
of the embedded tangent space in the ambient tangent space. -/
def normalSpaceOrthogonalComplementEquiv
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    f.NormalSpace x hn ≃L[ℝ] Submodule.orthogonal (f.tangentRange x hn) :=
  (f.tangentRange x hn).quotientEquivOfIsTopCompl _
    (isTopCompl_tangentRange_orthogonal f x hn)

/-- The inverse orthogonal-representative equivalence takes the normal class of the given
orthogonal vector. -/
@[simp]
theorem normalSpaceOrthogonalComplementEquiv_symm_apply
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : Submodule.orthogonal (f.tangentRange x hn)) :
    (f.normalSpaceOrthogonalComplementEquiv x hn).symm v =
      f.normalClass x hn v := by
  rw [normalClass_def]
  exact Submodule.quotientEquivOfIsTopCompl_symm_apply
    (isTopCompl_tangentRange_orthogonal f x hn) v

/-- The orthogonal representative of the class of an ambient tangent vector is its projection
onto the orthogonal complement of the embedded tangent space. -/
@[simp]
theorem normalSpaceOrthogonalComplementEquiv_normalClass
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    f.normalSpaceOrthogonalComplementEquiv x hn (f.normalClass x hn v) =
      (Submodule.orthogonal (f.tangentRange x hn)).orthogonalProjectionOnto v := by
  apply (f.normalSpaceOrthogonalComplementEquiv x hn).symm.injective
  rw [ContinuousLinearEquiv.symm_apply_apply,
    normalSpaceOrthogonalComplementEquiv_symm_apply]
  apply (f.normalClass_eq_iff x hn _ _).mpr
  rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
    sub_sub_cancel]
  exact (f.tangentRange x hn).starProjection_apply_mem v

/-- The unique tangent vector orthogonal to the embedded tangent space which represents an
intrinsic normal class. -/
def normalRepresentative (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    f.NormalSpace x hn →L[ℝ] TangentSpace J (f x) :=
  (Submodule.orthogonal (f.tangentRange x hn)).subtypeL.comp
    (f.normalSpaceOrthogonalComplementEquiv x hn).toContinuousLinearMap

/-- The normal representative is the orthogonal vector given by the orthogonal-representative
equivalence. -/
theorem normalRepresentative_apply
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) (v : f.NormalSpace x hn) :
    f.normalRepresentative x hn v = f.normalSpaceOrthogonalComplementEquiv x hn v := by
  rw [normalRepresentative, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearEquiv.coe_coe]

/-- The representative of an ambient tangent class is its orthogonal projection to the normal
directions. -/
@[simp]
theorem normalRepresentative_normalClass
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    f.normalRepresentative x hn (f.normalClass x hn v) =
      (Submodule.orthogonal (f.tangentRange x hn)).starProjection v := by
  rw [normalRepresentative_apply, normalSpaceOrthogonalComplementEquiv_normalClass,
    Submodule.coe_orthogonalProjectionOnto_apply]

/-- Taking the normal class of its orthogonal representative recovers the original class. -/
@[simp]
theorem normalClass_normalRepresentative
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : f.NormalSpace x hn) :
    f.normalClass x hn (f.normalRepresentative x hn v) = v := by
  rw [normalRepresentative_apply, ← normalSpaceOrthogonalComplementEquiv_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Normal representatives are orthogonal to every tangent vector of the embedded
submanifold. -/
theorem normalRepresentative_mem_orthogonal
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : f.NormalSpace x hn) :
    f.normalRepresentative x hn v ∈ Submodule.orthogonal (f.tangentRange x hn) := by
  rw [normalRepresentative_apply]
  exact (f.normalSpaceOrthogonalComplementEquiv x hn v).property

/-- The normal representative is the unique orthogonal ambient tangent vector in its normal
class. -/
theorem normalRepresentative_eq_iff
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : f.NormalSpace x hn) (w : TangentSpace J (f x)) :
    f.normalRepresentative x hn v = w ↔
      w ∈ Submodule.orthogonal (f.tangentRange x hn) ∧ f.normalClass x hn w = v := by
  constructor
  · rintro rfl
    exact ⟨f.normalRepresentative_mem_orthogonal x hn v,
      f.normalClass_normalRepresentative x hn v⟩
  · rintro ⟨hw, hv⟩
    rw [← hv, normalRepresentative_normalClass,
      Submodule.starProjection_eq_self_iff.mpr hw]

/-- The normal representative is perpendicular to the differential of every tangent vector. -/
theorem inner_normalRepresentative_mfderiv
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : f.NormalSpace x hn) (w : TangentSpace I x) :
    inner ℝ (f.normalRepresentative x hn v) (mfderiv I J f x w) = 0 := by
  exact Submodule.inner_left_of_mem_orthogonal
    ((f.mem_tangentRange_iff x hn _).2 ⟨w, rfl⟩)
    (f.normalRepresentative_mem_orthogonal x hn v)

end TauCeti.SmoothEmbedding
