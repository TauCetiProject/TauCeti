/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Character.IsotypicProjection
public import TauCeti.RepresentationTheory.Compact.Finite
public import TauCeti.RepresentationTheory.Compact.IsotypicBlock.Basic

/-!
# For a finite group the Peter-Weyl block projections are the isotypic projectors

`TauCeti/RepresentationTheory/Compact/IsotypicBlock/Basic.lean` proves that the character averaging
operator `TauCeti.peterWeylBlockAveraging` of a model `π` is the orthogonal projection of `L²(G)`
onto the `π`-block, and says in its `## What is not proved here` section that this is a statement
about a projection onto a *subspace*, not about a `G`-isotypic decomposition: the block is called
isotypic only because it is spanned by the matrix coefficients of `π` alone. The obstruction named
there is that `ContRepresentation.isotypicProjector` is the integrated operator of a
*norm*-continuous representation on a *finite-dimensional* carrier, while `L²(G)` is in general
infinite-dimensional and its regular representation then only strongly continuous.

Both obstructions disappear for a finite discrete `G`: every map out of `G` is continuous, and
`L²(G)` is the space `G → 𝕜` of all functions on `G`, of dimension `|G|`
(`TauCeti.finiteDimensional_lp_haarProb`). This file closes the gap there.

The bridge is that **convolution is the integrated operator of the left regular representation**,
`TauCeti.convolutionOperator_eq_integratedOperator_leftRegularLp`. Both operators are group averages
of the translates of their argument, and the identity is the substitution `y = g⁻¹x` in the
convolution integral, run as a reindexing of a finite sum. The *left* regular representation is the
one that appears, and not the right: left translation moves a matrix coefficient
`g ↦ ⟪π g v, w⟫` through its second vector `w`
(`ContRepresentation.matrixCoeff_comp_mulLeft`), on which it depends linearly, so the block
is a sum of copies of `π` itself under left translation, whereas right translation moves the first
vector, on which the coefficient depends conjugate-linearly.
This also matches the convolution computation of the block file, which moves the second vector by
the integrated operator of the kernel on the model's carrier.

Reading the averaging kernel `dim V_π · conj χ_π` as
`ContRepresentation.isotypicKernel` then identifies the two operators outright
(`TauCeti.peterWeylBlockAveraging_eq_isotypicProjector`), and the range identification of the
isotypic projector turns the `π`-block into the `π`-isotypic component of the left regular
representation — Mathlib's `isotypicComponent` of the `𝕜[G]`-module `L²(G)` — in
`TauCeti.mem_peterWeylBlock_iff_mem_isotypicComponent` and
`TauCeti.toSubmodule_range_isotypicProjector_leftRegularLp`. That is the `G`-isotypic statement the
block file leaves open, for the groups where the general construction is available.

## Main results

* `TauCeti.convolutionOperator_eq_integratedOperator_leftRegularLp`: **on a finite discrete group,
  convolution against a kernel is the integrated operator of that kernel in the left regular
  representation.**
* `TauCeti.peterWeylBlockAveraging_eq_isotypicProjector`: **the character averaging operator of a
  block is the isotypic projector of the model in the left regular representation.**
* `TauCeti.toSubmodule_range_isotypicProjector_leftRegularLp`,
  `TauCeti.mem_peterWeylBlock_iff_mem_isotypicComponent` and
  `TauCeti.restrictScalars_isotypicComponent_eq_peterWeylBlock`: **the `π`-block of `L²(G)` is the
  `π`-isotypic component of the left regular representation**, for a skeleton of the unitary dual
  over an algebraically closed `𝕜`.

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

/-- On a finite discrete group, left translation on `L²(G)` is left translation of functions, on
the nose: normalized Haar measure has full support, so an `L²` class is its own function. -/
private theorem coeFn_leftRegularLp_eq (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    ⇑(leftRegularLp 𝕜 G g f) = fun x => f (g⁻¹ * x) :=
  eq_of_ae_eq_haarProb G (coeFn_leftRegularLp g f)

/-- On a finite discrete group, the convolution operator is represented by the continuous
convolution of its kernel on the nose, for the same reason. -/
private theorem coeFn_convolutionOperator_eq (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ⇑(convolutionOperator k f) = ⇑(convolutionCLM k f) :=
  eq_of_ae_eq_haarProb G (coeFn_convolutionOperator k f)

section Sum

variable [Fintype G]

/-- The integrated operator of the left regular representation of a finite discrete group is the
group average of the translates. -/
private theorem integratedOperator_leftRegularLp_eq_smul_sum (k : C(G, 𝕜))
    (f : Lp 𝕜 2 (haarProb G)) :
    ContRepresentation.integratedOperator (leftRegularLp 𝕜 G) continuous_of_discreteTopology k f
      = (Nat.card G : 𝕜)⁻¹ • ∑ g : G, k g • leftRegularLp 𝕜 G g f := by
  rw [ContRepresentation.integratedOperator_apply, integral_haarProb,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  norm_num

end Sum

/-- **Convolution is the integrated operator of the left regular representation**, for a finite
discrete group.

Both sides average the translates `x ↦ f (g⁻¹ * x)` of `f` against the kernel: the integrated
operator does so visibly, and for convolution it is the substitution `y = g⁻¹ * x` in
`TauCeti.convolutionCLM_apply_apply`, which on a finite group is a reindexing of the sum along the
bijection `g ↦ g⁻¹ * x`.

Nothing of the sort holds for a general compact group, not because the identity fails but because
its right-hand side is not available: `TauCeti.ContRepresentation.integratedOperator` asks for a
norm-continuous representation, and the regular representation of an infinite compact group on
`L²(G)` is only strongly continuous. -/
theorem convolutionOperator_eq_integratedOperator_leftRegularLp (k : C(G, 𝕜)) :
    convolutionOperator k =
      ContRepresentation.integratedOperator (leftRegularLp 𝕜 G)
        continuous_of_discreteTopology k := by
  have : Fintype G := Fintype.ofFinite G
  refine ContinuousLinearMap.ext fun f => (lpHaarProbEquivFun G 𝕜 2).injective ?_
  rw [integratedOperator_leftRegularLp_eq_smul_sum, map_smul, map_sum]
  refine funext fun x => ?_
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, lpHaarProbEquivFun_apply,
    coeFn_leftRegularLp_eq, map_smul]
  rw [congrFun (coeFn_convolutionOperator_eq k f) x, convolutionCLM_apply_apply,
    integral_haarProb_eq_inv_mul_sum]
  congr 1
  refine (Fintype.sum_bijective (fun g : G => g⁻¹ * x)
    ((Equiv.inv G).trans (Equiv.mulRight x)).bijective _ _ fun g => ?_).symm
  congr 2
  group

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

/-- **The `π`-block of `L²(G)` is the `π`-isotypic component of the left regular
representation.**

This is the `G`-isotypic reading of the Peter-Weyl blocks that
`TauCeti/RepresentationTheory/Compact/IsotypicBlock/Basic.lean` leaves open: the block of a model
`π` is Mathlib's `isotypicComponent` of type `π` in the `𝕜[G]`-module `L²(G)` carried by the left
regular representation, so the decomposition of `L²(G)` into blocks is its isotypic decomposition
as a representation of `G` acting by left translation. -/
theorem mem_peterWeylBlock_iff_mem_isotypicComponent (h : IsIrrepSkeleton models) (i : ι)
    (f : Lp 𝕜 2 (haarProb G)) :
    f ∈ peterWeylBlock (models i) ↔
      f ∈ isotypicComponent 𝕜[G] (leftRegularLp 𝕜 G).toRepresentation.asModule
        (models i).rep.toRepresentation.asModule := by
  rw [ContRepresentation.mem_isotypicComponent_iff_isotypicProjector_apply (leftRegularLp 𝕜 G)
      continuous_of_discreteTopology (isUnitary_leftRegularLp 𝕜 G) (models i).rep
      (models i).continuous_rep (models i).isIrreducible f,
    ← ContIntertwiningMap.toContinuousLinearMap_apply,
    ← peterWeylBlockAveraging_eq_isotypicProjector,
    peterWeylBlockAveraging_eq_starProjection h i, Submodule.starProjection_eq_self_iff]

/-- **The `π`-block is the `π`-isotypic component as a submodule**, the previous lemma read as an
equality of subspaces of `L²(G)` rather than a membership criterion: restricting the scalars of
Mathlib's `isotypicComponent` from `𝕜[G]` to `𝕜` returns the block. -/
theorem restrictScalars_isotypicComponent_eq_peterWeylBlock (h : IsIrrepSkeleton models) (i : ι) :
    (isotypicComponent 𝕜[G] (leftRegularLp 𝕜 G).toRepresentation.asModule
        (models i).rep.toRepresentation.asModule).restrictScalars 𝕜 =
      peterWeylBlock (models i) :=
  SetLike.ext fun f => (mem_peterWeylBlock_iff_mem_isotypicComponent h i f).symm

end Skeleton

end IsotypicProjector

end TauCeti
