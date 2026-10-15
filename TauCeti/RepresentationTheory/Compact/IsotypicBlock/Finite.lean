/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Character.IsotypicProjection
public import TauCeti.RepresentationTheory.Compact.Finite
public import TauCeti.RepresentationTheory.Compact.IsotypicBlock.Isotypic

/-!
# For a finite group the Peter-Weyl block projections are the isotypic projectors

The algebraic identification of Peter-Weyl blocks with the isotypic components of the left
regular representation is proved for arbitrary compact groups in
`TauCeti/RepresentationTheory/Compact/IsotypicBlock/Isotypic.lean`. This file additionally
identifies their character averaging operators with the bundled
`ContRepresentation.isotypicProjector` for finite discrete groups.

The bundled projector requires a norm-continuous representation on a finite-dimensional
carrier. Both conditions hold here: every map out of `G` is continuous, and `L²(G)` is the
space `G → 𝕜` of all functions on `G`, of dimension `|G|`
(`TauCeti.finiteDimensional_lp_haarProb`).

The bridge is that **convolution is the integrated operator of the left regular representation**,
`TauCeti.convolutionOperator_eq_integratedOperator_leftRegularLp`. Both operators are group averages
of the translates of their argument; the identity follows from the strong integral formula
`TauCeti.convolutionOperator_apply_eq_integral_leftRegularLp`, valid for arbitrary compact groups.
The *left* regular representation is the
one that appears, and not the right: left translation moves a matrix coefficient
`g ↦ ⟪π g v, w⟫` through its second vector `w`
(`ContRepresentation.matrixCoeff_comp_mulLeft`), on which it depends linearly, so the block
is a sum of copies of `π` itself under left translation, whereas right translation moves the first
vector, on which the coefficient depends conjugate-linearly.
This also matches the convolution computation of the block file, which moves the second vector by
the integrated operator of the kernel on the model's carrier.

Reading the averaging kernel `dim V_π · conj χ_π` as
`ContRepresentation.isotypicKernel` identifies the two operators
(`TauCeti.peterWeylBlockAveraging_eq_isotypicProjector`), and gives the range of the bundled
projector as the Peter-Weyl block (`TauCeti.toSubmodule_range_isotypicProjector_leftRegularLp`).

## Main results

* `TauCeti.convolutionOperator_eq_integratedOperator_leftRegularLp`: **on a finite discrete group,
  convolution against a kernel is the integrated operator of that kernel in the left regular
  representation.**
* `TauCeti.peterWeylBlockAveraging_eq_isotypicProjector`: **the character averaging operator of a
  block is the isotypic projector of the model in the left regular representation.**
* `TauCeti.toSubmodule_range_isotypicProjector_leftRegularLp`: **the range of the bundled
  isotypic projector is the Peter-Weyl block**, for a skeleton of the unitary dual over an
  algebraically closed `𝕜`.

## References

* Daniel Bump, *Lie Groups*, second edition, Chapter 2.

## Tags

Peter-Weyl theorem, isotypic component, finite group, convolution, regular representation
-/

public section

open MeasureTheory
open scoped InnerProductSpace MonoidAlgebra

namespace TauCeti

/-! ### Convolution as the integrated operator of the left regular representation -/

section Convolution

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [Finite G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Convolution is the norm-continuous integrated operator of the left regular representation
for a finite discrete group. The strong integral formula holds for arbitrary compact groups in
`TauCeti.convolutionOperator_apply_eq_integral_leftRegularLp`; finiteness here ensures that the
regular representation is also continuous in the operator norm. -/
theorem convolutionOperator_eq_integratedOperator_leftRegularLp (k : C(G, 𝕜)) :
    convolutionOperator k =
      ContRepresentation.integratedOperator (leftRegularLp 𝕜 G)
        continuous_of_discreteTopology k := by
  ext f
  rw [convolutionOperator_apply_eq_integral_leftRegularLp,
    ContRepresentation.integratedOperator_apply]

end Convolution

/-! ### The block projections are the isotypic projectors -/

section IsotypicProjector

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [Finite G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **The character averaging operator of a block is the isotypic projector of its model**, for a
finite discrete group.

The averaging kernel `dim V_π · conj χ_π` of `TauCeti.peterWeylBlockAveraging` *is*
`ContRepresentation.isotypicKernel` of the model, and convolution against it is the
integrated action of that kernel in the left regular representation by
`TauCeti.convolutionOperator_eq_integratedOperator_leftRegularLp`. -/
theorem peterWeylBlockAveraging_eq_isotypicProjector (model : IrrepModel 𝕜 G) :
    peterWeylBlockAveraging model =
      (ContRepresentation.isotypicProjector (leftRegularLp 𝕜 G) continuous_of_discreteTopology
        model.rep model.continuous_rep).toContinuousLinearMap := by
  rw [ContRepresentation.toContinuousLinearMap_isotypicProjector, peterWeylBlockAveraging_def,
    convolutionOperator_eq_integratedOperator_leftRegularLp]
  congr 1
  refine ContinuousMap.ext fun g => ?_
  rw [ContRepresentation.isotypicKernel_apply]
  simp

section Skeleton

variable [IsAlgClosed 𝕜] {ι : Type*} {models : ι → IrrepModel 𝕜 G}

/-- **The range of the isotypic projector of a model in the left regular representation is the
`π`-block of `L²(G)`**, for a finite discrete group, an algebraically closed `𝕜` and a skeleton of
the unitary dual. -/
theorem toSubmodule_range_isotypicProjector_leftRegularLp (h : IsIrrepSkeleton models) (i : ι) :
    (ContRepresentation.isotypicProjector (leftRegularLp 𝕜 G) continuous_of_discreteTopology
        (models i).rep (models i).continuous_rep).toIntertwiningMap.range.toSubmodule =
      peterWeylBlock (models i) := by
  rw [← range_peterWeylBlockAveraging h i, peterWeylBlockAveraging_eq_isotypicProjector]
  rfl

end Skeleton

end IsotypicProjector

end TauCeti
