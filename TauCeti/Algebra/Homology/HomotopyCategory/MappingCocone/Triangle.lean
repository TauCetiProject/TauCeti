/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Basic

/-!
# Functorial mapping cocone triangles

For a natural transformation of cochain-complex-valued functors, the mapping cocone
triangles form a functor. The induced maps on the first vertex are the shifted mapping
cone maps of Mathlib's `CochainComplex.mappingCone.triangleMap`.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CochainComplex

namespace CategoryTheory.NatTrans

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {D : Type*} [Category* D] {F G : D ⥤ CochainComplex C ℤ} (τ : F ⟶ G)

/-- The functor taking a natural transformation to its objectwise mapping cocone triangles.
Its vertices compute to the mapping cocone, source and target functors, respectively. -/
@[expose]
noncomputable def mappingCoconeTriangleFunctor : D ⥤ Triangle (CochainComplex C ℤ) where
  obj X := mappingCocone.triangle (τ.app X)
  map {X Y} f :=
    { hom₁ := (mappingCoconeFunctor τ).map f
      hom₂ := F.map f
      hom₃ := G.map f
      comm₁ := ((mappingCoconeFunctorFst τ).naturality f).symm
      comm₂ := (τ.naturality f).symm
      comm₃ := by
        -- The third map is the cone inclusion followed by the inverse shift cancellation.
        have h := (mappingCone.triangleMap (τ.app X) (τ.app Y) (F.map f) (G.map f)
          (τ.naturality f).symm).comm₂
        simp only [mappingCone.triangleMap_hom₂, mappingCone.triangleMap_hom₃] at h
        let η := (shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)).inv
        let m := mappingCone.map (τ.app X) (τ.app Y) (F.map f) (G.map f) (τ.naturality f).symm
        -- Use the shifted cone hom types explicitly across the `mappingCocone` wrapper.
        change ((mappingCone.triangle (τ.app X)).mor₂ ≫ η.app _) ≫ m⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧' =
          G.map f ≫ (mappingCone.triangle (τ.app Y)).mor₂ ≫ η.app _
        have hm : η.app _ ≫ m⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧' = m ≫ η.app _ :=
          (η.naturality m).symm
        simpa only [Category.assoc] using
          (congrArg ((mappingCone.triangle (τ.app X)).mor₂ ≫ ·) hm).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ η.app _) h).trans (Category.assoc _ _ _))) }
  map_id X := by
    apply Triangle.hom_ext
    · exact (mappingCoconeFunctor τ).map_id X
    · exact F.map_id X
    · exact G.map_id X
  map_comp f g := by
    apply Triangle.hom_ext
    · exact (mappingCoconeFunctor τ).map_comp f g
    · exact F.map_comp f g
    · exact G.map_comp f g

@[simp]
theorem mappingCoconeTriangleFunctor_obj (X : D) :
    (mappingCoconeTriangleFunctor τ).obj X = mappingCocone.triangle (τ.app X) := (rfl)

@[simp]
theorem mappingCoconeTriangleFunctor_comp_π₁ :
    mappingCoconeTriangleFunctor τ ⋙ Triangle.π₁ = mappingCoconeFunctor τ := (rfl)

@[simp]
theorem mappingCoconeTriangleFunctor_comp_π₂ :
    mappingCoconeTriangleFunctor τ ⋙ Triangle.π₂ = F := (rfl)

@[simp]
theorem mappingCoconeTriangleFunctor_comp_π₃ :
    mappingCoconeTriangleFunctor τ ⋙ Triangle.π₃ = G := (rfl)

end CategoryTheory.NatTrans
