/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic

/-!
# Mapping-cone triangles of bounded complexes

The mapping cone of a morphism `φ : K ⟶ L` of bounded cochain complexes is bounded, so Mathlib's
mapping-cone triangle `K ⟶ L ⟶ cone φ ⟶ K⟦1⟧` is a triangle of bounded complexes,
`CochainComplex.Bounded.mappingConeTriangle φ`. Its image in the bounded homotopy category is
distinguished, and every distinguished triangle there is isomorphic to such an image
(`TauCeti.HomotopyCategory.Bounded.mem_distTriang_iff`). This is the bounded counterpart of the
definition of the distinguished triangles of Mathlib's `HomotopyCategory C (.up ℤ)`.

Consequently a functor out of the bounded homotopy category which commutes with the shift is a
triangle functor as soon as it sends the images of bounded mapping-cone triangles to
distinguished triangles (`TauCeti.HomotopyCategory.Bounded.isTriangulated_of_mappingConeTriangle`).
-/

public section

open CategoryTheory Limits Pretriangulated

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

namespace CochainComplex.Bounded

variable {K L : CochainComplex.Bounded C} (φ : K ⟶ L)

/-- The mapping cone of a morphism of bounded cochain complexes, as a bounded complex. -/
noncomputable abbrev mappingCone : CochainComplex.Bounded C :=
  ⟨CochainComplex.mappingCone φ.hom,
    CochainComplex.bounded_mappingCone φ.hom K.property L.property⟩

/-- The mapping-cone triangle `K ⟶ L ⟶ cone φ ⟶ K⟦1⟧` of a morphism of bounded cochain
complexes. Its third morphism is induced by the cocycle `-mappingCone.fst φ`, as in Mathlib's
`CochainComplex.mappingCone.triangle`, which is its image in all cochain complexes
(`CochainComplex.Bounded.ιMapTriangleMappingConeTriangleIso`). -/
-- The morphisms are typed by the vertices, so the vertices must compute for consumers.
@[expose, implicit_reducible, simps! obj₁ obj₂ obj₃ mor₁ mor₂ mor₃]
noncomputable def mappingConeTriangle : Triangle (CochainComplex.Bounded C) :=
  Triangle.mk φ (ObjectProperty.homMk (CochainComplex.mappingCone.inr φ.hom) :
      L ⟶ mappingCone φ)
    (ObjectProperty.homMk (CochainComplex.HomComplex.Cocycle.homOf
        ((-CochainComplex.mappingCone.fst φ.hom).rightShift 1 0 (zero_add 1)) ≫
      ((ι C).commShiftIso (1 : ℤ)).inv.app K))

/-- The mapping-cone triangle of a morphism of bounded complexes is Mathlib's mapping-cone
triangle of the underlying morphism of cochain complexes. -/
@[expose, simps! hom_hom₁ hom_hom₂ hom_hom₃ inv_hom₁ inv_hom₂ inv_hom₃]
noncomputable def ιMapTriangleMappingConeTriangleIso :
    (ι C).mapTriangle.obj (mappingConeTriangle φ) ≅
      CochainComplex.mappingCone.triangle φ.hom :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [mappingConeTriangle, CochainComplex.mappingCone.triangle])
    (by simp [mappingConeTriangle, CochainComplex.mappingCone.triangle])
    (by simp [mappingConeTriangle, CochainComplex.mappingCone.triangle])

end CochainComplex.Bounded

namespace TauCeti.HomotopyCategory.Bounded

open CochainComplex.Bounded (mappingConeTriangle ιMapTriangleMappingConeTriangleIso)

variable [HasZeroObject C]

/-- The image in the bounded homotopy category of the mapping-cone triangle of a morphism of
bounded complexes is distinguished. -/
theorem quotient_mapTriangle_mappingConeTriangle_mem_distTriang
    {K L : CochainComplex.Bounded C} (φ : K ⟶ L) :
    (quotient C).mapTriangle.obj (mappingConeTriangle φ) ∈
      distTriang (HomotopyCategory.Bounded C) :=
  isomorphic_distinguished _
    (_root_.HomotopyCategory.mappingCone_triangleh_distinguished φ.hom) _
    ((Functor.mapTriangleCompIso (quotient C) (ι C)).symm.app _ ≪≫
      (Functor.mapTriangleIso (quotientCompιIso C)).app _ ≪≫
      (Functor.mapTriangleCompIso (CochainComplex.Bounded.ι C)
        (_root_.HomotopyCategory.quotient C (.up ℤ))).app _ ≪≫
      (_root_.HomotopyCategory.quotient C (.up ℤ)).mapTriangle.mapIso
        (ιMapTriangleMappingConeTriangleIso φ))

/-- A triangle in the bounded homotopy category is distinguished exactly when it is isomorphic to
the image of the mapping-cone triangle of a morphism of bounded complexes. -/
theorem mem_distTriang_iff (T : Triangle (HomotopyCategory.Bounded C)) :
    T ∈ distTriang (HomotopyCategory.Bounded C) ↔
      ∃ (K L : CochainComplex.Bounded C) (φ : K ⟶ L),
        Nonempty (T ≅ (quotient C).mapTriangle.obj (mappingConeTriangle φ)) := by
  refine ⟨fun hT ↦ ?_, fun ⟨K, L, φ, ⟨e⟩⟩ ↦ isomorphic_distinguished _
    (quotient_mapTriangle_mappingConeTriangle_mem_distTriang φ) _ e⟩
  let e₁ := (quotient C).objObjPreimageIso T.obj₁
  let e₂ := (quotient C).objObjPreimageIso T.obj₂
  obtain ⟨φ, hφ⟩ := (quotient C).map_surjective (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
  obtain ⟨e, -, -⟩ := exists_iso_of_arrow_iso _ _ hT
    (quotient_mapTriangle_mappingConeTriangle_mem_distTriang φ)
    (Arrow.isoMk e₁.symm e₂.symm (by simp [mappingConeTriangle, hφ]))
  exact ⟨_, _, φ, ⟨e⟩⟩

/-- A functor out of the bounded homotopy category which commutes with the shift is a triangle
functor when it sends the image of the mapping-cone triangle of every morphism of bounded
complexes to a distinguished triangle. -/
theorem isTriangulated_of_mappingConeTriangle {D : Type u'} [Category.{v'} D] [HasZeroObject D]
    [Preadditive D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : HomotopyCategory.Bounded C ⥤ D) [F.CommShift ℤ]
    (hF : ∀ {K L : CochainComplex.Bounded C} (φ : K ⟶ L),
      F.mapTriangle.obj ((quotient C).mapTriangle.obj (mappingConeTriangle φ)) ∈ distTriang D) :
    F.IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨K, L, φ, ⟨e⟩⟩ := (mem_distTriang_iff T).1 hT
    exact isomorphic_distinguished _ (hF φ) _ (F.mapTriangle.mapIso e)

end TauCeti.HomotopyCategory.Bounded
