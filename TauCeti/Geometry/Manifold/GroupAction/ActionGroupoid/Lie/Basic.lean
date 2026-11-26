/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.GroupAction.ActionGroupoid.Product
public import TauCeti.Geometry.Manifold.Groupoid.Fibers

/-!
# Lie action groupoids

A smooth action of a real Lie group on a manifold gives a Lie groupoid when both models are
finite-dimensional and boundaryless, both spaces are second-countable, and the base is Hausdorff.
Objects retain the charts of the base; total arrows use the product atlas of labels and sources
from `GroupAction/ActionGroupoid/Product.lean`.

Open the scope `TauCeti.ActionGroupoid` to use that atlas and the Lie groupoid instance.
`TauCeti.ActionGroupoid.sourceFiberDiffeomorph` identifies each source fibre, with the canonical
regular-fibre atlas of the Lie groupoid, with the acting group. The construction retains labels
that act trivially.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
* The formal construction follows `TauCeti.PairGroupoid.arrowDiffeomorph` and
  `TauCeti.PairGroupoid.isLieGroupoid` in `Groupoid/Examples.lean`: transport the arrow atlas,
  source submersion, and smooth composition from product coordinates.
-/

public noncomputable section

open CategoryTheory Topology
open CategoryTheory.ActionCategory
open scoped Manifold ContDiff

namespace TauCeti.ActionGroupoid

section LieGroupoid

variable {E H F K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace K]
  (J : ModelWithCorners ℝ F K) (I : ModelWithCorners ℝ E H) [J.Boundaryless] [I.Boundaryless]
  (G X : Type*) [Group G] [MulAction G X]
  [TopologicalSpace G] [ChartedSpace K G] [TopologicalSpace X] [ChartedSpace H X]
  [LieGroup J ∞ G] [IsManifold I ∞ X] [ContMDiffSMul J I ∞ G X]
  [T2Space X] [SecondCountableTopology G] [SecondCountableTopology X]

/-- A smooth action on finite-dimensional boundaryless real models gives a Lie action groupoid
when both spaces are second-countable and the base is Hausdorff. Objects are modelled on `I` and
arrows on `J.prod I`. -/
scoped instance isLieGroupoid : IsLieGroupoid I (J.prod I) (ActionCategory G X) where
  isSubmersion_source := isSubmersion_productSource J I ∞ G X
  contMDiff_unit := contMDiff_productUnit J I ∞ G X
  contMDiff_inverse := contMDiff_productInverse J I ∞ G X (contMDiff_inv J ∞)
  contMDiff_comp := by
    let hs := isSubmersion_productSource J I ∞ G X
    let hi := contMDiff_productInverse J I ∞ G X (contMDiff_inv J ∞)
    let := transverseFiberProductChartedSpace
      (f := (Quiver.Total.right : Quiver.Total (ActionCategory G X) → ActionCategory G X))
      (g := (Quiver.Total.left : Quiver.Total (ActionCategory G X) → ActionCategory G X))
      (n := ∞) (by simp) (hs.contMDiff.comp hi) hs.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right (by simp) hs p)
    have hemb := isSmoothEmbedding_coe_transverseFiberProduct
      (f := (Quiver.Total.right : Quiver.Total (ActionCategory G X) → ActionCategory G X))
      (g := (Quiver.Total.left : Quiver.Total (ActionCategory G X) → ActionCategory G X))
      (n := ∞) (by simp) (hs.contMDiff.comp hi) hs.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right (by simp) hs p)
    exact contMDiff_productComp J I ∞ hemb.contMDiff.fst hemb.contMDiff.snd
      (fun p ↦ p.property)
  t2Space_sourceFiber _ := by
    have := topologicalGroup_of_lieGroup J ∞ (G := G)
    have := J.t1Space G
    exact inferInstance

end LieGroupoid

section SourceFiber

variable {E H F K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace K]
  (J : ModelWithCorners ℝ F K) (I : ModelWithCorners ℝ E H) [J.Boundaryless] [I.Boundaryless]
  (G X : Type*) [Group G] [MulAction G X]
  [TopologicalSpace G] [ChartedSpace K G] [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold J ∞ G] [IsManifold I ∞ X]
  [IsLieGroupoid I (J.prod I) (ActionCategory G X)]

/-- The canonical source fibre is diffeomorphic to the acting group. The fibre carries precisely
the Lie groupoid's preferred regular-fibre atlas. -/
def sourceFiberDiffeomorph (x : ActionCategory G X) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (J.prod I) x
    {a : Quiver.Total (ActionCategory G X) // a.left = x} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (Module.finrank ℝ (F × E) - Module.finrank ℝ E) → ℝ), J⟯ G :=
  RegularFiber.diffeomorphOfProd (by simp)
    (IsLieGroupoid.contMDiff_source I (J.prod I) (ActionCategory G X))
    BoundarylessManifold.isInteriorPoint (IsLieGroupoid.isRegularValue_source I (J.prod I) x)
    (arrowDiffeomorph J I ∞ G X) (objectDiffeomorph I ∞ G X) (by
      funext a
      simp only [Function.comp_apply, objectDiffeomorph_apply, arrowDiffeomorph_apply])

/-- The canonical source-fibre diffeomorphism reads an arrow's label. -/
theorem sourceFiberDiffeomorph_apply (x : ActionCategory G X)
    (a : {a : Quiver.Total (ActionCategory G X) // a.left = x}) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (J.prod I) x
    sourceFiberDiffeomorph J I G X x a = a.val.hom.hom := by
  simp only [sourceFiberDiffeomorph, RegularFiber.diffeomorphOfProd_apply,
    arrowDiffeomorph_apply]

/-- The inverse constructs the arrow with the given label and source. -/
@[simp]
theorem coe_sourceFiberDiffeomorph_symm_apply (x : ActionCategory G X) (g : G) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (J.prod I) x
    ((sourceFiberDiffeomorph J I G X x).symm g).val =
      (arrowDiffeomorph J I ∞ G X).symm (g, x.back) := by
  simp only [sourceFiberDiffeomorph, RegularFiber.coe_diffeomorphOfProd_symm_apply,
    objectDiffeomorph_apply]

end SourceFiber

end TauCeti.ActionGroupoid
