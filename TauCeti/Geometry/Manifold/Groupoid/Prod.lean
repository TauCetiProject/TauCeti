/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Groupoid.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Prod
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Products of Lie groupoids

Let `C` and `D` be categories whose total arrows carry charted-space structures. A total arrow of
the product category `C × D` is a pair of total arrows of `C` and `D`, and
`TauCeti.totalProdHomeomorph` identifies `Quiver.Total (C × D)` with
`Quiver.Total C × Quiver.Total D`. Pulling the product charts back along this homeomorphism makes
`Quiver.Total (C × D)` a `C^n` manifold diffeomorphic to the product of the arrow manifolds
(`TauCeti.totalProdDiffeomorph`). A map into it is `C^n` exactly when both of its components are
(`TauCeti.contMDiff_totalProd_iff`).

With the product charts on objects, the product of two Lie groupoids is a Lie groupoid
(`TauCeti.IsLieGroupoid.prod`): its source, target, units, inversion and composition are computed
componentwise. Every arrow of both factors is retained, so isotropy groups of the product are
products of the isotropy groups of the factors.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Section 1.1.
* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
-/

public section

noncomputable section

open CategoryTheory Module Topology
open scoped Manifold ContDiff

namespace TauCeti

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {C D : Type*} [Category C] [Category D]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H (Quiver.Total C)]
  [TopologicalSpace (Quiver.Total D)] [ChartedSpace G (Quiver.Total D)]

/-- The total arrows of a product category carry the product charts of the pairs of total arrows
of the factors, pulled back along `TauCeti.totalProdHomeomorph`. -/
instance instChartedSpaceTotalProd : ChartedSpace (ModelProd H G) (Quiver.Total (C × D)) :=
  (totalProdHomeomorph C D).pullbackChartedSpace

/-- The total arrows of a product of categories with `C^n` arrow manifolds form a `C^n` manifold.
-/
instance instIsManifoldTotalProd (J : ModelWithCorners 𝕜 E H) (K : ModelWithCorners 𝕜 F G)
    (n : ℕ∞ω) [IsManifold J n (Quiver.Total C)] [IsManifold K n (Quiver.Total D)] :
    IsManifold (J.prod K) n (Quiver.Total (C × D)) :=
  (totalProdHomeomorph C D).pullback_isManifold (J.prod K) n

variable (C D) in
/-- The total arrows of a product category are `C^n` diffeomorphic to pairs of total arrows of the
factors. -/
def totalProdDiffeomorph (J : ModelWithCorners 𝕜 E H) (K : ModelWithCorners 𝕜 F G) (n : ℕ∞ω) :
    Quiver.Total (C × D) ≃ₘ^n⟮J.prod K, J.prod K⟯ Quiver.Total C × Quiver.Total D :=
  (totalProdHomeomorph C D).pullbackDiffeomorph (J.prod K) n

variable {J : ModelWithCorners 𝕜 E H} {K : ModelWithCorners 𝕜 F G} {n : ℕ∞ω}

/-- The diffeomorphism reads off the components of a total arrow of a product category. -/
@[simp]
theorem coe_totalProdDiffeomorph :
    ⇑(totalProdDiffeomorph C D J K n) = totalProdHomeomorph C D :=
  Homeomorph.coe_pullbackDiffeomorph _ _ _

/-- The inverse diffeomorphism pairs a total arrow of each factor. -/
@[simp]
theorem coe_totalProdDiffeomorph_symm :
    ⇑(totalProdDiffeomorph C D J K n).symm = (totalProdHomeomorph C D).symm :=
  Homeomorph.coe_pullbackDiffeomorph_symm _ _ _

/-- A map into the total arrows of a product category is `C^n` exactly when both of its components
are. -/
theorem contMDiff_totalProd_iff {I : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H' M] {f : M → Quiver.Total (C × D)} :
    ContMDiff I (J.prod K) n f ↔
      ContMDiff I J n (fun z ↦ (⟨(f z).left.1, (f z).right.1, (f z).hom.1⟩ : Quiver.Total C)) ∧
        ContMDiff I K n
          (fun z ↦ (⟨(f z).left.2, (f z).right.2, (f z).hom.2⟩ : Quiver.Total D)) := by
  rw [← (totalProdDiffeomorph C D J K n).contMDiff_diffeomorph_comp_iff le_rfl,
    contMDiff_prod_iff]
  simp only [Function.comp_def, coe_totalProdDiffeomorph, totalProdHomeomorph_apply]

end Smooth

namespace IsLieGroupoid

variable {E H E' H' F G F' G' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {I' : ModelWithCorners ℝ F G} [I'.Boundaryless]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] [TopologicalSpace G']
  {J' : ModelWithCorners ℝ F' G'} [J'.Boundaryless]
  {C : Type*} [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsLieGroupoid I J C]
  {D : Type*} [Category D] [IsGroupoid D]
  [TopologicalSpace D] [ChartedSpace G D] [IsManifold I' ∞ D]
  [TopologicalSpace (Quiver.Total D)] [ChartedSpace G' (Quiver.Total D)]
  [IsManifold J' ∞ (Quiver.Total D)] [IsLieGroupoid I' J' D]

include I J I' J' in
/-- The source map of a product of Lie groupoids is a smooth submersion. -/
private theorem isSubmersion_source_prod :
    Manifold.IsSubmersion (J.prod J') (I.prod I') ∞
      (Quiver.Total.left : Quiver.Total (C × D) → C × D) := by
  -- The source of a product is `Prod.map` of the sources, read through `totalProdDiffeomorph`.
  have h : (Quiver.Total.left : Quiver.Total (C × D) → C × D) =
      Prod.map Quiver.Total.left Quiver.Total.left ∘ totalProdDiffeomorph C D J J' ∞ :=
    funext fun _ ↦ by simp
  rw [h]
  exact (totalProdDiffeomorph C D J J' ∞).isLocalDiffeomorph.isSubmersion_comp
    ((isSubmersion_source (I := I) (J := J) (C := C)).prodMap
      (isSubmersion_source (I := I') (J := J') (C := D)))

include I J I' J' in
/-- Inversion in a product of Lie groupoids is smooth. -/
private theorem contMDiff_inverse_prod :
    ContMDiff (J.prod J') (J.prod J') ∞ fun a : Quiver.Total (C × D) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (C × D)) := by
  -- The components of the inverse of a pair of arrows are the inverses of its components.
  have h := contMDiff_totalProd_iff.1 (contMDiff_id (I := J.prod J') (n := ∞)
    (M := Quiver.Total (C × D)))
  exact contMDiff_totalProd_iff.2
    ⟨((contMDiff_inverse (I := I) (J := J) (C := C)).comp h.1).congr fun a ↦
      congrArg (Quiver.Total.mk _ _) (IsIso.eq_inv_of_hom_inv_id
        (congrArg Prod.fst (IsIso.hom_inv_id a.hom))),
      ((contMDiff_inverse (I := I') (J := J') (C := D)).comp h.2).congr fun a ↦
        congrArg (Quiver.Total.mk _ _) (IsIso.eq_inv_of_hom_inv_id
          (congrArg Prod.snd (IsIso.hom_inv_id a.hom)))⟩

include I J I' J' in
/-- Composition in a product of Lie groupoids is smooth on the transverse fibre product of target
and source: each component of a composite is the composite of the components, and the components
of a composable pair of the product are composable pairs of the factors depending smoothly on it.
-/
private theorem contMDiff_comp_prod
    (hs : Manifold.IsSubmersion (J.prod J') (I.prod I') ∞
      (Quiver.Total.left : Quiver.Total (C × D) → C × D))
    (hi : ContMDiff (J.prod J') (J.prod J') ∞ fun a : Quiver.Total (C × D) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (C × D))) :
    letI := transverseFiberProductChartedSpace
      (f := (Quiver.Total.right : Quiver.Total (C × D) → C × D))
      (g := (Quiver.Total.left : Quiver.Total (C × D) → C × D)) (n := ∞) (by simp)
      (hs.contMDiff.comp hi) hs.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right (by simp) hs p)
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ (E' × F') + finrank ℝ (E' × F') - finrank ℝ (E × F)) → ℝ)
      (J.prod J') ∞
      fun p : {p : Quiver.Total (C × D) × Quiver.Total (C × D) // p.1.right = p.2.left} ↦
        p.val.1.comp p.val.2 p.property := by
  let := transverseFiberProductChartedSpace
    (f := (Quiver.Total.right : Quiver.Total (C × D) → C × D))
    (g := (Quiver.Total.left : Quiver.Total (C × D) → C × D)) (n := ∞) (by simp)
    (hs.contMDiff.comp hi) hs.contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_right (by simp) hs p)
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct
    (f := (Quiver.Total.right : Quiver.Total (C × D) → C × D))
    (g := (Quiver.Total.left : Quiver.Total (C × D) → C × D)) (n := ∞) (by simp)
    (hs.contMDiff.comp hi) hs.contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_right (by simp) hs p)
  have h₁ := contMDiff_totalProd_iff.1 (contMDiff_fst.comp hemb.contMDiff)
  have h₂ := contMDiff_totalProd_iff.1 (contMDiff_snd.comp hemb.contMDiff)
  let := composablePairsChartedSpace I J C
  let := composablePairsChartedSpace I' J' D
  have hC := (contMDiff_comp_composablePairs I J C).comp
    ((contMDiff_composablePairs_iff I J C le_rfl
      (f := fun p : {p : Quiver.Total (C × D) × Quiver.Total (C × D) // p.1.right = p.2.left} ↦
        ⟨(⟨p.val.1.left.1, p.val.1.right.1, p.val.1.hom.1⟩,
          ⟨p.val.2.left.1, p.val.2.right.1, p.val.2.hom.1⟩), congrArg Prod.fst p.property⟩)).2
      ⟨h₁.1, h₂.1⟩)
  have hD := (contMDiff_comp_composablePairs I' J' D).comp
    ((contMDiff_composablePairs_iff I' J' D le_rfl
      (f := fun p : {p : Quiver.Total (C × D) × Quiver.Total (C × D) // p.1.right = p.2.left} ↦
        ⟨(⟨p.val.1.left.2, p.val.1.right.2, p.val.1.hom.2⟩,
          ⟨p.val.2.left.2, p.val.2.right.2, p.val.2.hom.2⟩), congrArg Prod.snd p.property⟩)).2
      ⟨h₁.2, h₂.2⟩)
  refine contMDiff_totalProd_iff.2 ⟨hC.congr fun p ↦ ?_, hD.congr fun p ↦ ?_⟩ <;>
  · obtain ⟨⟨⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩, f⟩, ⟨⟨y₁', y₂'⟩, ⟨z₁, z₂⟩, f'⟩⟩, h⟩ := p
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Function.comp_apply]
    rw [Quiver.Total.comp_def, Quiver.Total.comp_def]
    simp

include I J I' J' in
/-- Every source fibre of a product of Lie groupoids is Hausdorff: it embeds in the product of the
source fibres of the factors. -/
private theorem t2Space_sourceFiber_prod (x : C × D) :
    T2Space {a : Quiver.Total (C × D) // a.left = x} := by
  have := t2Space_sourceFiber (I := I) (J := J) (C := C) x.1
  have := t2Space_sourceFiber (I := I') (J := J') (C := D) x.2
  refine .of_injective_continuous
    (f := fun a : {a : Quiver.Total (C × D) // a.left = x} ↦
      ((⟨⟨a.val.left.1, a.val.right.1, a.val.hom.1⟩, congrArg Prod.fst a.property⟩ :
          {b : Quiver.Total C // b.left = x.1}),
        (⟨⟨a.val.left.2, a.val.right.2, a.val.hom.2⟩, congrArg Prod.snd a.property⟩ :
          {b : Quiver.Total D // b.left = x.2}))) ?_ ?_
  · intro a b hab
    refine Subtype.ext ((totalProdHomeomorph C D).injective ?_)
    simpa only [totalProdHomeomorph_apply, Prod.ext_iff, Subtype.ext_iff] using hab
  · have he := (totalProdHomeomorph C D).continuous.comp
      (continuous_subtypeVal (p := fun a : Quiver.Total (C × D) ↦ a.left = x))
    simp only [Function.comp_def, totalProdHomeomorph_apply] at he
    exact ((continuous_fst.comp he).subtype_mk _).prodMk ((continuous_snd.comp he).subtype_mk _)

/-- **The product of two Lie groupoids is a Lie groupoid**, with the product charts on objects and
on total arrows, and source, target, units, inversion and composition computed componentwise. -/
instance prod : IsLieGroupoid (I.prod I') (J.prod J') (C × D) where
  t2Space_objects :=
    have := t2Space_objects (I := I) (J := J) (C := C)
    have := t2Space_objects (I := I') (J := J') (C := D)
    inferInstance
  secondCountableTopology_arrows :=
    have := secondCountableTopology_arrows (I := I) (J := J) (C := C)
    have := secondCountableTopology_arrows (I := I') (J := J') (C := D)
    inferInstance
  isSubmersion_source := isSubmersion_source_prod
  contMDiff_unit :=
    -- Units of a product are pairs of units.
    contMDiff_totalProd_iff.2
      ⟨((contMDiff_unit (I := I) (J := J) (C := C)).comp contMDiff_fst).congr fun _ ↦ by simp,
        ((contMDiff_unit (I := I') (J := J') (C := D)).comp contMDiff_snd).congr fun _ ↦ by simp⟩
  contMDiff_inverse := contMDiff_inverse_prod (I := I) (I' := I')
  contMDiff_comp := contMDiff_comp_prod isSubmersion_source_prod
    (contMDiff_inverse_prod (I := I) (I' := I'))
  t2Space_sourceFiber := t2Space_sourceFiber_prod (I := I) (J := J) (I' := I') (J' := J')

end IsLieGroupoid

end TauCeti
