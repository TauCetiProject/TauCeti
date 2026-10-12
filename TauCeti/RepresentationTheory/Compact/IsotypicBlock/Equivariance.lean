/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.IsotypicBlock.Basic

/-!
# Equivariance of Peter-Weyl block averaging

Character averaging on `L²(G)` commutes with both left and right translation, hence with the
biregular action of `G × G`. This makes the orthogonal Peter-Weyl block projections equivariant:
both their images and their kernels are subrepresentations. The argument applies to arbitrary
compact groups, whose regular actions need only be strongly continuous.

The averaging operator is convolution against the central kernel `dim V_π · conj χ_π`.
Equivariance holds over every `RCLike` coefficient field, independently of whether averaging
is a projection. Over an algebraically closed field, the existing
`peterWeylBlockAveraging_eq_starProjection` identifies it with the block projection.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, second edition, §5.2.
* D. Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory

namespace TauCeti

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Character averaging commutes with left translation on an arbitrary compact group. -/
theorem peterWeylBlockAveraging_comp_leftRegularLp (model : IrrepModel 𝕜 G) (g : G) :
    (peterWeylBlockAveraging model).comp (leftRegularLp 𝕜 G g) =
      (leftRegularLp 𝕜 G g).comp (peterWeylBlockAveraging model) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, peterWeylBlockAveraging_def, leftRegularLp_apply]
  apply convolutionOperator_compMeasurePreserving_mul_left
  intro x y
  simp only [ContinuousMap.smul_apply, ContinuousMap.star_apply, smul_eq_mul]
  rw [ContRepresentation.character_mul_comm model.rep model.continuous_rep y x]

/-- Character averaging commutes with right translation on an arbitrary compact group. -/
theorem peterWeylBlockAveraging_comp_rightRegularLp (model : IrrepModel 𝕜 G) (g : G) :
    (peterWeylBlockAveraging model).comp (rightRegularLp 𝕜 G g) =
      (rightRegularLp 𝕜 G g).comp (peterWeylBlockAveraging model) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, peterWeylBlockAveraging_def, rightRegularLp_apply]
  exact convolutionOperator_compMeasurePreserving_mul_right _ f g

/-- The Peter-Weyl character averaging operator is equivariant for the biregular action of
`G × G`. In particular, over an algebraically closed field the orthogonal block projection
is a morphism of biregular representations. -/
theorem peterWeylBlockAveraging_comp_biRegularLp (model : IrrepModel 𝕜 G) (p : G × G) :
    (peterWeylBlockAveraging model).comp (biRegularLp 𝕜 G p) =
      (biRegularLp 𝕜 G p).comp (peterWeylBlockAveraging model) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, biRegularLp_apply_eq_left_right]
  have hleft := DFunLike.congr_fun
    (peterWeylBlockAveraging_comp_leftRegularLp model p.1) (rightRegularLp 𝕜 G p.2 f)
  have hright := DFunLike.congr_fun (peterWeylBlockAveraging_comp_rightRegularLp model p.2) f
  simp only [ContinuousLinearMap.comp_apply] at hleft hright
  rw [hright] at hleft
  exact hleft

end TauCeti
