/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject

/-!
# Naturality of the spectral object of a filtered complex on graded pieces

A natural transformation `α : F ⟶ G` of functors `ι ⥤ CochainComplex C ℤ` induces a morphism of
spectral objects `CochainComplex.spectralObjectMap α` (in
`TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject`), which on `H^n(f)` is the map
in cohomology of the induced morphism of mapping cones. When `F.map f` and `G.map f` are
monomorphisms, for instance for a morphism of filtrations, it is the map in cohomology of the
induced morphism of cokernels, that is, of graded pieces
(`CochainComplex.spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom`).
-/

public section

open CategoryTheory Limits ComposableArrows

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} [Category* ι]
  {F G : ι ⥤ CochainComplex C ℤ}

/-- On `H^n(f)`, for monomorphisms `F.map f` and `G.map f`, the morphism of spectral objects
induced by `α` is the map in cohomology of the induced morphism of cokernels. -/
lemma spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom (α : F ⟶ G) {i j : ι}
    (f : i ⟶ j) [Mono (F.map f)] [Mono (G.map f)] (n : ℤ) :
    ((spectralObjectMap α).hom n).app (mk₁ f) ≫ (spectralObjectHIsoCokernel G f n).hom =
      (spectralObjectHIsoCokernel F f n).hom ≫
        HomologicalComplex.homologyMap
          (cokernel.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f)) n := by
  -- The square of mapping cones and cokernels, from `mappingCone.map_descShortComplex`.
  have key₀ := mappingCone.map_descShortComplex (ShortComplex.cokernelSequence (F.map f))
    (ShortComplex.cokernelSequence (G.map f))
    { τ₁ := α.app i
      τ₂ := α.app j
      τ₃ := cokernel.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f)
      comm₁₂ := (α.naturality f).symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }
  have key := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · n) key₀).trans
      (HomologicalComplex.homologyMap_comp _ _ n))
  rw [spectralObjectHIsoCokernel_hom, spectralObjectHIsoCokernel_hom]
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (spectralObjectMap_hom_app_hIso α f n)).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((spectralObjectHIso F f n).hom ≫ ·) key).trans (Category.assoc _ _ _).symm

end CochainComplex
