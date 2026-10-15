/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.IsotypicBlock.Isotypic
public import TauCeti.RepresentationTheory.Compact.Character.IsotypicProjection

/-!
# Strong character averages are the Peter–Weyl projections

Over an algebraically closed `RCLike` field, for any compact group, the orthogonal projection
onto an irreducible Peter–Weyl block is integration of left translations against the conjugate
character multiplied by the model's dimension. The integral is vector-valued in `L²(G)`, so strong
continuity of the regular action suffices, even when the action is not continuous in the operator
norm.

The block is already identified with the algebraic isotypic component of its model. Consequently
membership in that component is equivalent to being fixed by the strong character average.
The kernel is exactly `ContRepresentation.isotypicKernel`, used by the finite-dimensional
bundled isotypic projector.

The convolution identity uses `ContRepresentation.integratedOperatorL1`, which constructs a
bounded operator by integrating individual orbits, and density of continuous functions in `L²`.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, second edition, §5.2.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Chapter III.
-/

public section

open MeasureTheory
open scoped MonoidAlgebra

namespace TauCeti

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Character averaging is the strong integral of left translations against the conjugate
character multiplied by the model's dimension, for any compact group. -/
theorem peterWeylBlockAveraging_apply_eq_integral (model : IrrepModel 𝕜 G)
    (f : Lp 𝕜 2 (haarProb G)) :
    peterWeylBlockAveraging model f =
      ∫ g, ContRepresentation.isotypicKernel model.rep model.continuous_rep g •
        leftRegularLp 𝕜 G g f ∂haarProb G := by
  rw [peterWeylBlockAveraging_def, convolutionOperator_apply_eq_integral_leftRegularLp]
  simp only [ContinuousMap.smul_apply, ContinuousMap.star_apply, smul_eq_mul,
    ContRepresentation.isotypicKernel_apply, finrank_euclideanSpace_fin]

variable [IsAlgClosed 𝕜] {ι : Type*} {models : ι → IrrepModel 𝕜 G}

/-- The orthogonal Peter–Weyl block projection is the strong character average. No finiteness
or discrete topology assumption on the group is needed. -/
theorem starProjection_peterWeylBlock_apply_eq_integral (h : IsIrrepSkeleton models)
    (i : ι) (f : Lp 𝕜 2 (haarProb G)) :
    (peterWeylBlock (models i)).starProjection f =
      ∫ g, ContRepresentation.isotypicKernel (models i).rep (models i).continuous_rep g •
        leftRegularLp 𝕜 G g f ∂haarProb G := by
  rw [← peterWeylBlockAveraging_eq_starProjection h i,
    peterWeylBlockAveraging_apply_eq_integral]

/-- A vector lies in the selected algebraic isotypic component of the left regular
representation exactly when its strong character average fixes it. -/
@[simp]
theorem mem_isotypicComponent_iff_integral_isotypicKernel (h : IsIrrepSkeleton models)
    (i : ι) (f : Lp 𝕜 2 (haarProb G)) :
    f ∈ isotypicComponent 𝕜[G] (leftRegularLp 𝕜 G).toRepresentation.asModule
        (models i).rep.toRepresentation.asModule ↔
      (∫ g, ContRepresentation.isotypicKernel (models i).rep (models i).continuous_rep g •
        leftRegularLp 𝕜 G g f ∂haarProb G) = f := by
  rw [← mem_peterWeylBlock_iff_mem_isotypicComponent h i,
    ← Submodule.starProjection_eq_self_iff,
    starProjection_peterWeylBlock_apply_eq_integral h i]

end TauCeti
