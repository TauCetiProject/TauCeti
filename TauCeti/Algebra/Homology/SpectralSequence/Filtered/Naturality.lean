/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject

/-!
# Naturality of the spectral object of a filtered complex

A natural transformation `α : F ⟶ G` of functors `ι ⥤ CochainComplex C ℤ` (for instance a
morphism of filtered cochain complexes, see `CochainComplex.filtrationFunctor`) induces a
morphism of spectral objects `CochainComplex.spectralObjectMap α :
spectralObject F ⟶ spectralObject G`. It is functorial in `α`, and on `H^n(f)` it is the map in
cohomology induced by the morphism of mapping cones of `F.map f` and `G.map f`
(`CochainComplex.spectralObjectMap_hom_app_hIso`), or by the morphism of cokernels when `F.map f`
and `G.map f` are monomorphisms (`CochainComplex.spectralObjectMap_hom_app_hIsoCokernel`).

## Main definitions

* `CochainComplex.spectralObjectMap α`: the morphism of spectral objects induced by `α : F ⟶ G`.
* `CochainComplex.spectralObjectFunctor C ι`: the spectral object as a functor of `F`.
-/

public section

open CategoryTheory Limits ComposableArrows HomotopyCategory

namespace CochainComplex

section Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {ι : Type*} [Category* ι] {F G H : ι ⥤ CochainComplex C ℤ}

omit [HasZeroObject C] in
/-- The third morphisms of the distinguished triangles of mapping cones in the homotopy category
are natural in the pair of composable morphisms. -/
lemma quotient_mappingConeCompTriangle_mor₃_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CochainComplex C ℤ}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (f' : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) (c : X₃ ⟶ Y₃)
    (h₁ : f ≫ b = a ≫ f') (h₂ : g ≫ c = b ≫ g') :
    ((quotient C (ComplexShape.up ℤ)).map (mappingConeCompTriangle f g).mor₃ ≫
        ((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app (mappingCone f)) ≫
        ((quotient C (ComplexShape.up ℤ)).map (mappingCone.map f f' a b h₁))⟦(1 : ℤ)⟧' =
      (quotient C (ComplexShape.up ℤ)).map (mappingCone.map g g' b c h₂) ≫
        (quotient C (ComplexShape.up ℤ)).map (mappingConeCompTriangle f' g').mor₃ ≫
          ((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app (mappingCone f') := by
  have eq := mappingConeCompTriangle_mor₃_naturality f g f' g' (homMk₂ a b c h₁ h₂)
  dsimp at eq
  let Q := quotient C (ComplexShape.up ℤ)
  exact (Category.assoc _ _ _).trans <|
    (congrArg (fun t => Q.map (mappingConeCompTriangle f g).mor₃ ≫ t)
      (Q.commShiftIso_hom_naturality (mappingCone.map f f' a b h₁) (1 : ℤ)).symm).trans <|
    (Q.map_comp_assoc _ _ _).symm.trans <|
    (congrArg (fun t => Q.map t ≫ (Q.commShiftIso (1 : ℤ)).hom.app (mappingCone f'))
      eq.symm).trans (Q.map_comp_assoc _ _ _)

/-- The morphism of triangulated spectral objects in the homotopy category induced by a natural
transformation `α : F ⟶ G`: on `f : i ⟶ j`, the morphism of mapping cones of `F.map f` and
`G.map f` given by `α.app i` and `α.app j`. -/
noncomputable def triangulatedSpectralObjectMap (α : F ⟶ G) :
    (spectralObjectMappingCone C).precomp F ⟶ (spectralObjectMappingCone C).precomp G where
  hom := Functor.whiskerRight ((Functor.whiskeringRight _ _ _).map α)
    (spectralObjectMappingCone C).ω₁
  comm {i j k} f g := by
    rw [precomp_spectralObjectMappingCone_δ, precomp_spectralObjectMappingCone_δ]
    exact quotient_mappingConeCompTriangle_mor₃_naturality (F.map f) (F.map g) (G.map f)
      (G.map g) (α.app i) (α.app j) (α.app k) (α.naturality f) (α.naturality g)

@[simp]
lemma triangulatedSpectralObjectMap_id (F : ι ⥤ CochainComplex C ℤ) :
    triangulatedSpectralObjectMap (𝟙 F) = 𝟙 _ := by
  ext : 1
  simp [triangulatedSpectralObjectMap]
  rfl

@[simp]
lemma triangulatedSpectralObjectMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    triangulatedSpectralObjectMap (α ≫ β) =
      triangulatedSpectralObjectMap α ≫ triangulatedSpectralObjectMap β := by
  ext : 1
  simp [triangulatedSpectralObjectMap]
  rfl

end Triangulated

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} [Category* ι]
  {F G H : ι ⥤ CochainComplex C ℤ}

/-- The morphism of spectral objects `spectralObject F ⟶ spectralObject G` induced by a natural
transformation `α : F ⟶ G`. -/
noncomputable def spectralObjectMap (α : F ⟶ G) : spectralObject F ⟶ spectralObject G :=
  (Triangulated.SpectralObject.mapHomologicalFunctorFunctor
    (homologyFunctor C (ComplexShape.up ℤ) 0) ι).map (triangulatedSpectralObjectMap α)

@[simp]
lemma spectralObjectMap_id (F : ι ⥤ CochainComplex C ℤ) :
    spectralObjectMap (𝟙 F) = 𝟙 _ := by
  simp [spectralObjectMap]
  rfl

@[simp]
lemma spectralObjectMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    spectralObjectMap (α ≫ β) = spectralObjectMap α ≫ spectralObjectMap β := by
  simp [spectralObjectMap]
  rfl

variable (C ι) in
/-- The spectral object of a functor `ι ⥤ CochainComplex C ℤ`, as a functor. -/
@[expose, simps]
noncomputable def spectralObjectFunctor :
    (ι ⥤ CochainComplex C ℤ) ⥤ Abelian.SpectralObject C ι where
  obj := spectralObject
  map := spectralObjectMap

/-- On `H^n(f)`, the morphism of spectral objects induced by `α` is the map in cohomology of the
morphism of mapping cones of `F.map f` and `G.map f`. -/
lemma spectralObjectMap_hom_app_hIso (α : F ⟶ G) {i j : ι} (f : i ⟶ j) (n : ℤ) :
    ((spectralObjectMap α).hom n).app (mk₁ f) ≫ (spectralObjectHIso G f n).hom =
      (spectralObjectHIso F f n).hom ≫
        HomologicalComplex.homologyMap
          (mappingCone.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f)) n := by
  rw [spectralObjectHIso_hom, spectralObjectHIso_hom]
  dsimp [spectralObjectMap, triangulatedSpectralObjectMap]
  convert ((homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.naturality
    (mappingCone.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f))) using 2
  all_goals rfl

/-- On `H^n(f)`, for monomorphisms `F.map f` and `G.map f`, the morphism of spectral objects
induced by `α` is the map in cohomology of the induced morphism of cokernels. -/
lemma spectralObjectMap_hom_app_hIsoCokernel (α : F ⟶ G) {i j : ι} (f : i ⟶ j)
    [Mono (F.map f)] [Mono (G.map f)] (n : ℤ) :
    ((spectralObjectMap α).hom n).app (mk₁ f) ≫ (spectralObjectHIsoCokernel G f n).hom =
      (spectralObjectHIsoCokernel F f n).hom ≫
        HomologicalComplex.homologyMap
          (cokernel.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f)) n := by
  rw [spectralObjectHIsoCokernel_hom, spectralObjectHIsoCokernel_hom]
  erw [reassoc_of% spectralObjectMap_hom_app_hIso]
  have key := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (mappingCone.map_descShortComplex (ShortComplex.cokernelSequence (F.map f))
      (ShortComplex.cokernelSequence (G.map f))
      { τ₁ := α.app i
        τ₂ := α.app j
        τ₃ := cokernel.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f)
        comm₁₂ := (α.naturality f).symm
        comm₂₃ := (cokernel.π_desc _ _ _).symm })
  dsimp only at key
  rw [HomologicalComplex.homologyMap_comp] at key
  erw [HomologicalComplex.homologyMap_comp] at key
  exact (congrArg ((spectralObjectHIso F f n).hom ≫ ·) key).trans (Category.assoc _ _ _).symm

end CochainComplex
