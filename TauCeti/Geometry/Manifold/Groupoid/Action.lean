/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.GroupAction.ActionGroupoid
public import TauCeti.Geometry.Manifold.Groupoid.Fibers
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Smooth action groupoids

For a smooth action of a Lie group `G` on a manifold `X`, the native action category
`CategoryTheory.ActionCategory G X` is a Lie groupoid. Objects have the existing charts of `X`.
Total arrows have the product charts of `G × X`, with coordinates `(label, source)`.

Open the scope `TauCeti.ActionGroupoid` to use the product arrow atlas and Lie groupoid instance.
The construction allows positive-dimensional acting groups and retains labels acting trivially.

`TauCeti.ActionGroupoid.arrowDiffeomorph` gives the product coordinates. The arrow `(g, x)` has
source `x`, target `g • x` and inverse `(g⁻¹, g • x)`. Units have label `1`.
Following `(g, x)` by `(h, g • x)` gives `(h * g, x)`.
`TauCeti.ActionGroupoid.sourceFiberDiffeomorph` identifies each regular source fibre with `G`.

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

/-- The inverse of the arrow diffeomorphism uses the native total-arrow equivalence. -/
theorem arrowDiffeomorph_symm_apply (p : G × X) :
    (arrowDiffeomorph J I n G X).symm p = (totalEquiv G X).symm p := by
  simp [arrowDiffeomorph]

/-- The arrow constructed from a label-source pair has the prescribed label. -/
@[simp]
theorem arrowDiffeomorph_symm_label (p : G × X) :
    ((arrowDiffeomorph J I n G X).symm p).hom.hom = p.1 :=
  (congrArg (fun a ↦ a.hom.hom) (arrowDiffeomorph_symm_apply J I n G X p)).trans
    (totalEquiv_symm_apply_hom_hom p)

@[simp]
theorem arrowDiffeomorph_toHomeomorph :
    (arrowDiffeomorph J I n G X).toHomeomorph = arrowHomeomorph G X := by
  simp [arrowDiffeomorph]

/-- The second arrow's label multiplies on the left of the first arrow's label. -/
theorem arrowDiffeomorph_comp (a b : Quiver.Total (ActionCategory G X)) (h : a.right = b.left) :
    arrowDiffeomorph J I n G X (a.comp b h) = (b.hom.hom * a.hom.hom, a.left.back) := by
  simp [arrowDiffeomorph_apply, Quiver.Total.comp_def]

variable {G X}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- A map into product-charted arrows is `C^n` exactly when its label and source point are. -/
theorem contMDiff_productArrows_iff {f : N → Quiver.Total (ActionCategory G X)} :
    ContMDiff I' (J.prod I) n f ↔
      ContMDiff I' J n (fun z ↦ (f z).hom.hom) ∧
        ContMDiff I' I n (fun z ↦ (f z).left.back) := by
  rw [← (arrowDiffeomorph J I n G X).contMDiff_diffeomorph_comp_iff le_rfl]
  simp only [Function.comp_def, arrowDiffeomorph_apply, contMDiff_prod_iff]

variable (G X)

/-- Source is smooth for the product arrow atlas. -/
theorem contMDiff_productSource :
    ContMDiff (J.prod I) I n
      (Quiver.Total.left : Quiver.Total (ActionCategory G X) → ActionCategory G X) :=
  (contMDiff_objects_iff I n).2
    ((contMDiff_snd.comp (arrowDiffeomorph J I n G X).contMDiff).congr fun _ ↦ by
      simp [arrowDiffeomorph_apply])

/-- Units are smooth for the product arrow atlas. -/
theorem contMDiff_productUnit :
    ContMDiff I (J.prod I) n fun x : ActionCategory G X ↦
      (⟨x, x, 𝟙 x⟩ : Quiver.Total (ActionCategory G X)) := by
  rw [← (arrowDiffeomorph J I n G X).contMDiff_diffeomorph_comp_iff le_rfl]
  exact ((contMDiff_const (c := (1 : G))).prodMk
    (objectDiffeomorph I n G X).contMDiff).congr fun _ ↦ by simp [arrowDiffeomorph_apply]

/-- A jointly `C^n` action makes target smooth for the product arrow atlas. -/
theorem contMDiff_productTarget [ContMDiffSMul J I n G X] :
    ContMDiff (J.prod I) I n
      (Quiver.Total.right : Quiver.Total (ActionCategory G X) → ActionCategory G X) := by
  apply (contMDiff_objects_iff I n).2
  exact ((contMDiff_fst.comp (arrowDiffeomorph J I n G X).contMDiff).smul
    (contMDiff_snd.comp (arrowDiffeomorph J I n G X).contMDiff)).congr
      fun a ↦ by
        have htarget : a.right.back = (arrowDiffeomorph J I n G X a).1 •
            (arrowDiffeomorph J I n G X a).2 := by
          rw [arrowDiffeomorph_apply]
          exact a.hom.map_val.symm
        exact htarget

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
  -- The same product-chart normal form as `Manifold.isSubmersionOfComplement_fst`,
  -- with the continuous linear swap selecting the second factor.
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

section LieGroupoid

variable {E H F K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace K]
  (J : ModelWithCorners ℝ F K) (I : ModelWithCorners ℝ E H) [J.Boundaryless] [I.Boundaryless]
  (G X : Type*) [Group G] [MulAction G X]
  [TopologicalSpace G] [ChartedSpace K G] [TopologicalSpace X] [ChartedSpace H X]
  [LieGroup J ∞ G] [IsManifold I ∞ X] [ContMDiffSMul J I ∞ G X]
  [T2Space X] [SecondCountableTopology G] [SecondCountableTopology X]

/-- A second-countable real Lie group acting smoothly on a Hausdorff second-countable manifold
has a Lie action groupoid, with objects modelled on `I` and arrows modelled on `J.prod I`. -/
scoped instance isLieGroupoid : IsLieGroupoid I (J.prod I) (ActionCategory G X) where
  isSubmersion_source := isSubmersion_productSource J I ∞ G X
  contMDiff_unit := contMDiff_productUnit J I ∞ G X
  contMDiff_inverse := contMDiff_productInverse J I ∞ G X (contMDiff_inv J ∞)
  contMDiff_comp := by
    have ha := (arrowDiffeomorph J I ∞ G X).contMDiff
    exact contMDiff_composablePairs_comp_of_eq (isSubmersion_productSource J I ∞ G X)
      (contMDiff_productInverse J I ∞ G X (contMDiff_inv J ∞))
      ((arrowDiffeomorph J I ∞ G X).symm.contMDiff.comp
        (((ha.comp contMDiff_snd).fst.mul (ha.comp contMDiff_fst).fst).prodMk
          (ha.comp contMDiff_fst).snd))
      fun p ↦ (arrowDiffeomorph J I ∞ G X).injective (by
        simp only [Diffeomorph.coe_toEquiv, Function.comp_apply]
        rw [arrowDiffeomorph_comp, Diffeomorph.apply_symm_apply]
        simp only [arrowDiffeomorph_apply, Pi.mul_apply])
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

/-- The source fibre over an object is canonically diffeomorphic to the acting Lie group.
The source of the diffeomorphism carries the Lie groupoid's regular-fibre atlas. -/
def sourceFiberDiffeomorph (x : ActionCategory G X) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (J.prod I) x
    {a : Quiver.Total (ActionCategory G X) // a.left = x} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (Module.finrank ℝ (F × E) - Module.finrank ℝ E) → ℝ), J⟯ G :=
  letI := IsLieGroupoid.sourceFiberChartedSpace I (J.prod I) x
  { toFun := fun a ↦ a.val.hom.hom
    invFun := fun g ↦ ⟨(arrowDiffeomorph J I ∞ G X).symm (g, x.back), by
      apply back_injective
      simp [arrowDiffeomorph_symm_apply, objEquiv]⟩
    left_inv := fun a ↦ Subtype.ext <| (arrowHomeomorph G X).injective <| by
      simp only [arrowDiffeomorph_symm_apply, arrowHomeomorph_apply, totalEquiv_symm_apply_hom_hom,
        totalEquiv_symm_apply_left]
      exact Prod.ext rfl (congrArg ActionCategory.back a.property).symm
    right_inv := fun g ↦ by
      simpa only [arrowDiffeomorph_apply] using congrArg Prod.fst
        ((arrowDiffeomorph J I ∞ G X).apply_symm_apply (g, x.back))
    contMDiff_toFun := by
      exact ((arrowDiffeomorph J I ∞ G X).contMDiff.comp
        (IsLieGroupoid.isSmoothEmbedding_coe_sourceFiber I (J.prod I) x).contMDiff).fst.congr
          fun _ ↦ by simp [arrowDiffeomorph_apply]
    contMDiff_invFun := by
      exact ((IsLieGroupoid.isSmoothEmbedding_coe_sourceFiber I (J.prod I) x).contMDiff_iff_comp
        (f := fun g ↦ ⟨(arrowDiffeomorph J I ∞ G X).symm (g, x.back), by
          apply back_injective
          simp [arrowDiffeomorph_symm_apply, objEquiv]⟩)).2
        ((arrowDiffeomorph J I ∞ G X).symm.contMDiff.comp
          (contMDiff_id.prodMk contMDiff_const)) }

/-- The canonical source-fibre diffeomorphism reads an arrow's label. -/
theorem sourceFiberDiffeomorph_apply (x : ActionCategory G X)
    (a : {a : Quiver.Total (ActionCategory G X) // a.left = x}) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (J.prod I) x
    sourceFiberDiffeomorph J I G X x a = a.val.hom.hom := by
  rfl

/-- The inverse source-fibre diffeomorphism constructs the arrow with the given label and source. -/
@[simp]
theorem sourceFiberDiffeomorph_symm_apply (x : ActionCategory G X) (g : G) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (J.prod I) x
    ((sourceFiberDiffeomorph J I G X x).symm g).val =
      (arrowDiffeomorph J I ∞ G X).symm (g, x.back) := by
  rfl

end SourceFiber

end TauCeti.ActionGroupoid
