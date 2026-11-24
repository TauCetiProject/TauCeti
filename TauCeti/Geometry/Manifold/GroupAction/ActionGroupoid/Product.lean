/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import TauCeti.Geometry.Manifold.GroupAction.ActionGroupoid.Basic
public import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# The product atlas on an action groupoid

For an action of a monoid `G` on a manifold `X`, total arrows of the native action category
`CategoryTheory.ActionCategory G X` carry the product charts of `G × X` in coordinates
`(label, source)`. Open the scope `TauCeti.ActionGroupoid` to use this atlas.

`arrowDiffeomorph` identifies total arrows with the product. The source and units are `C^n`
without assumptions on the action, the target is `C^n` when the action is, and composition of
`C^n` families is `C^n` when multiplication of labels is. For a group, inversion is `C^n` when
inversion of labels and the action are. The source is a submersion whenever both factors are
`C^n` manifolds.

The product arrow atlas and transport of the source submersion follow the pair-groupoid
construction `TauCeti.PairGroupoid.arrowDiffeomorph` and `TauCeti.PairGroupoid.isLieGroupoid` in
`TauCeti/Geometry/Manifold/Groupoid/Examples.lean`.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
-/

public noncomputable section

open CategoryTheory Topology
open CategoryTheory.ActionCategory
open scoped Manifold ContDiff

namespace TauCeti.ActionGroupoid

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H F K : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace K]
  (J : ModelWithCorners 𝕜 F K) (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  (G X : Type*) [Monoid G] [MulAction G X]
  [TopologicalSpace G] [ChartedSpace K G] [TopologicalSpace X] [ChartedSpace H X]

/-- Product charts on total arrows, transported from label-source pairs `G × X`. -/
scoped instance instChartedSpaceProductArrows :
    ChartedSpace (ModelProd K H) (Quiver.Total (ActionCategory G X)) :=
  (arrowHomeomorph G X).pullbackChartedSpace

/-- Total arrows with the product atlas form a `C^n` manifold. -/
scoped instance instIsManifoldProductArrows [IsManifold J n G] [IsManifold I n X] :
    IsManifold (J.prod I) n (Quiver.Total (ActionCategory G X)) :=
  (arrowHomeomorph G X).pullback_isManifold (J.prod I) n

/-- Total arrows with the product atlas are diffeomorphic to label-source pairs. -/
def arrowDiffeomorph :
    Quiver.Total (ActionCategory G X) ≃ₘ^n⟮J.prod I, J.prod I⟯ G × X :=
  (arrowHomeomorph G X).pullbackDiffeomorph (J.prod I) n

/-- The arrow diffeomorphism reads the label and the underlying source point. -/
theorem arrowDiffeomorph_apply (a : Quiver.Total (ActionCategory G X)) :
    arrowDiffeomorph J I n G X a = (a.hom.hom, a.left.back) := by
  simp [arrowDiffeomorph]

/-- The first coordinate of the arrow diffeomorphism is the label. -/
@[simp]
theorem arrowDiffeomorph_apply_fst (a : Quiver.Total (ActionCategory G X)) :
    (arrowDiffeomorph J I n G X a).1 = a.hom.hom := by
  rw [arrowDiffeomorph_apply]

/-- The second coordinate of the arrow diffeomorphism is the underlying source point. -/
@[simp]
theorem arrowDiffeomorph_apply_snd (a : Quiver.Total (ActionCategory G X)) :
    (arrowDiffeomorph J I n G X a).2 = a.left.back := by
  rw [arrowDiffeomorph_apply]

/-- The inverse of the arrow diffeomorphism uses the native total-arrow equivalence. -/
theorem arrowDiffeomorph_symm_apply (p : G × X) :
    (arrowDiffeomorph J I n G X).symm p = (totalEquiv G X).symm p := by
  simp [arrowDiffeomorph]

/-- The arrow constructed from product coordinates has the prescribed label. -/
@[simp↓]
theorem arrowDiffeomorph_symm_apply_hom_hom (p : G × X) :
    ((arrowDiffeomorph J I n G X).symm p).hom.hom = p.1 := by
  rw [arrowDiffeomorph_symm_apply]
  exact totalEquiv_symm_apply_hom_hom p

/-- The source of the arrow constructed from product coordinates is the prescribed point. -/
@[simp]
theorem arrowDiffeomorph_symm_apply_left (p : G × X) :
    ((arrowDiffeomorph J I n G X).symm p).left = objEquiv G X p.2 := by
  rw [arrowDiffeomorph_symm_apply]
  exact totalEquiv_symm_apply_left p

/-- The target of the arrow constructed from product coordinates is the label acting on the
source point. -/
@[simp]
theorem arrowDiffeomorph_symm_apply_right (p : G × X) :
    ((arrowDiffeomorph J I n G X).symm p).right = objEquiv G X (p.1 • p.2) := by
  rw [arrowDiffeomorph_symm_apply]
  exact totalEquiv_symm_apply_right p

/-- The second arrow's label multiplies on the left of the first arrow's label. -/
theorem arrowDiffeomorph_comp (a b : Quiver.Total (ActionCategory G X)) (h : a.right = b.left) :
    arrowDiffeomorph J I n G X (a.comp b h) = (b.hom.hom * a.hom.hom, a.left.back) := by
  rw [arrowDiffeomorph_apply]
  rw [Quiver.Total.comp_def]
  simp

variable {G X}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

variable (G X)

/-- Source is smooth for the product arrow atlas. -/
theorem contMDiff_productSource :
    ContMDiff (J.prod I) I n
      (Quiver.Total.left : Quiver.Total (ActionCategory G X) → ActionCategory G X) :=
  (contMDiff_objects_iff I n).2
    ((contMDiff_snd.comp (arrowDiffeomorph J I n G X).contMDiff).congr fun _ ↦ by
      simp [arrowDiffeomorph_apply])

/-- The unit at an object has label `1` and source the underlying point. -/
theorem arrowDiffeomorph_unit (x : ActionCategory G X) :
    arrowDiffeomorph J I n G X ⟨x, x, 𝟙 x⟩ = (1, x.back) := by
  simp only [arrowDiffeomorph_apply, ActionCategory.id_hom]

/-- The target of an arrow is its label acting on its source point. -/
theorem right_back_eq_smul (a : Quiver.Total (ActionCategory G X)) :
    a.right.back = (arrowDiffeomorph J I n G X a).1 •
      (arrowDiffeomorph J I n G X a).2 := by
  rw [arrowDiffeomorph_apply]
  exact a.hom.map_val.symm

/-- Units are smooth for the product arrow atlas. -/
theorem contMDiff_productUnit :
    ContMDiff I (J.prod I) n fun x : ActionCategory G X ↦
      (⟨x, x, 𝟙 x⟩ : Quiver.Total (ActionCategory G X)) := by
  rw [← (arrowDiffeomorph J I n G X).contMDiff_diffeomorph_comp_iff le_rfl]
  exact ((contMDiff_const (c := (1 : G))).prodMk
    (objectDiffeomorph I n G X).contMDiff).congr fun _ ↦ by
      simp only [Function.comp_apply, arrowDiffeomorph_unit, objectDiffeomorph_apply]

/-- A jointly `C^n` action makes target smooth for the product arrow atlas. -/
theorem contMDiff_productTarget [ContMDiffSMul J I n G X] :
    ContMDiff (J.prod I) I n
      (Quiver.Total.right : Quiver.Total (ActionCategory G X) → ActionCategory G X) := by
  apply (contMDiff_objects_iff I n).2
  exact ((contMDiff_fst.comp (arrowDiffeomorph J I n G X).contMDiff).smul
    (contMDiff_snd.comp (arrowDiffeomorph J I n G X).contMDiff)).congr
      fun a ↦ right_back_eq_smul J I n G X a

variable {G X}

/-- Composable `C^n` families of arrows have a `C^n` composite when multiplication of labels is
`C^n`. The action itself need not be smooth. -/
theorem contMDiff_productComp [ContMDiffMul J n G]
    {a b : N → Quiver.Total (ActionCategory G X)}
    (ha : ContMDiff I' (J.prod I) n a) (hb : ContMDiff I' (J.prod I) n b)
    (h : ∀ z, (a z).right = (b z).left) :
    ContMDiff I' (J.prod I) n fun z ↦ (a z).comp (b z) (h z) := by
  rw [← (arrowDiffeomorph J I n G X).contMDiff_diffeomorph_comp_iff le_rfl]
  have hda := (arrowDiffeomorph J I n G X).contMDiff.comp ha
  have hdb := (arrowDiffeomorph J I n G X).contMDiff.comp hb
  exact (hdb.fst.mul hda.fst |>.prodMk hda.snd).congr fun z ↦ by
    dsimp only [Function.comp_apply]
    rw [arrowDiffeomorph_comp]
    simp only [arrowDiffeomorph_apply, Pi.mul_apply]

end Smooth

section Inverse

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H F K : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace K]
  (J : ModelWithCorners 𝕜 F K) (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  (G X : Type*) [Group G] [MulAction G X]
  [TopologicalSpace G] [ChartedSpace K G] [TopologicalSpace X] [ChartedSpace H X]

/-- Inversion in label-source coordinates sends `(g, x)` to `(g⁻¹, g • x)`. -/
theorem arrowDiffeomorph_inverse (a : Quiver.Total (ActionCategory G X)) :
    arrowDiffeomorph J I n G X ⟨a.right, a.left, inv a.hom⟩ =
      (a.hom.hom⁻¹, a.hom.hom • a.left.back) := by
  simp only [arrowDiffeomorph_apply, inv_hom]
  exact Prod.ext rfl a.hom.map_val.symm

/-- Inversion in the product arrow atlas is `C^n` when group inversion and the action are. -/
theorem contMDiff_productInverse [ContMDiffSMul J I n G X]
    (hInv : ContMDiff J J n fun g : G ↦ g⁻¹) :
    ContMDiff (J.prod I) (J.prod I) n fun a : Quiver.Total (ActionCategory G X) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (ActionCategory G X)) := by
  rw [← (arrowDiffeomorph J I n G X).contMDiff_diffeomorph_comp_iff le_rfl]
  have ha := (arrowDiffeomorph J I n G X).contMDiff
  exact ((hInv.comp (contMDiff_fst.comp ha)).prodMk
    ((contMDiff_fst.comp ha).smul (contMDiff_snd.comp ha))).congr fun a ↦ by
      have hcoords : arrowDiffeomorph J I n G X ⟨a.right, a.left, inv a.hom⟩ =
          ((arrowDiffeomorph J I n G X a).1⁻¹,
            (arrowDiffeomorph J I n G X a).1 • (arrowDiffeomorph J I n G X a).2) := by
        rw [arrowDiffeomorph_inverse, arrowDiffeomorph_apply]
      exact hcoords

end Inverse

section Submersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H F K : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace K]
  (J : ModelWithCorners 𝕜 F K) (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  (G X : Type*) [Monoid G] [MulAction G X]
  [TopologicalSpace G] [ChartedSpace K G] [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold J n G] [IsManifold I n X]

/-- The source projection for the product arrow atlas is a `C^n` submersion. -/
theorem isSubmersion_productSource :
    Manifold.IsSubmersion (J.prod I) I n
      (Quiver.Total.left : Quiver.Total (ActionCategory G X) → ActionCategory G X) := by
  -- Adapt `Manifold.isSubmersionOfComplement_fst` by swapping the model factors.
  have hsnd : Manifold.IsSubmersion (J.prod I) I n (@Prod.snd G X) := by
    refine Manifold.IsSubmersionOfComplement.isSubmersion (F := F) ?_
    refine Manifold.isSubmersionOfComplement_iff.mpr fun p ↦ ?_
    refine .mk_of_continuousAt continuous_snd.continuousAt
      (ContinuousLinearEquiv.prodComm 𝕜 F E) (chartAt (ModelProd K H) p) (chartAt H p.2)
      (mem_chart_source _ p) (mem_chart_source _ p.2) (IsManifold.chart_mem_maximalAtlas p)
      (IsManifold.chart_mem_maximalAtlas p.2) ?_
    intro y hy
    rw [← extChartAt, ← extChartAt] at *
    rw [extChartAt_prod] at hy ⊢
    exact (extChartAt I p.2).right_inv hy.2
  have h : (Quiver.Total.left : Quiver.Total (ActionCategory G X) → ActionCategory G X) =
      (objectDiffeomorph I n G X).symm ∘ (Prod.snd ∘ arrowDiffeomorph J I n G X) := by
    funext a
    apply back_injective
    simp [arrowDiffeomorph_apply, objEquiv]
  rw [h]
  exact (objectDiffeomorph I n G X).symm.isLocalDiffeomorph.comp_isSubmersion
    ((arrowDiffeomorph J I n G X).isLocalDiffeomorph.isSubmersion_comp hsnd)

end Submersion

end TauCeti.ActionGroupoid
