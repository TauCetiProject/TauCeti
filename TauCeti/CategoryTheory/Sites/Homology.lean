/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Sites.Abelian
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Homology of complexes of sheaves

With only zero morphisms in the coefficient category, `J.complexToPresheaf A c`
regards a complex of sheaves of any shape as its presheaf of section complexes.
The abbreviation `HomologicalComplex.sheafPresheaf` and its characteristic equations
retain the caller's section functors and degreewise sheaves.

Let `A` be an abelian category and `(C, J)` a site on which `A`-valued presheaves can be
sheafified. Homology in the abelian category of `A`-valued sheaves is not computed objectwise:
the inclusion of sheaves into presheaves preserves kernels but not cokernels. It is computed by
sheafifying the objectwise homology of the underlying complex of presheaves
(`CategoryTheory.GrothendieckTopology.homologyFunctorIsoSheafify`), because sheafification is exact
and a sheaf is the sheafification of its underlying presheaf.

This is how the cohomology sheaves of a complex of sheaves, for instance the higher direct images
of a morphism of sites, are compared with presheaves defined object by object.

In the same way, the last term of a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of sheaves is the
sheafification of the presheaf cokernel of `F₁ ⟶ F₂`
(`CategoryTheory.ShortComplex.ShortExact.isIso_presheafToSheaf_map_cokernelDesc`), although
`F₂ ⟶ F₃` need not be surjective on sections.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology

section SectionComplexes

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (A : Type*) [Category* A] [HasZeroMorphisms A] {ι : Type*} (c : ComplexShape ι)

/-- Complexes of sheaves give presheaves of section complexes, functorially in the complex.
This composes the existing forgetful and complex-of-functors functors. -/
@[expose]
def complexToPresheaf : HomologicalComplex (Sheaf J A) c ⥤
    Cᵒᵖ ⥤ HomologicalComplex A c :=
  (sheafToPresheaf J A).mapHomologicalComplex c ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex

/-- The induced map on section complexes evaluates the original sheaf map in each degree. -/
lemma complexToPresheaf_map_app_f {K L : HomologicalComplex (Sheaf J A) c}
    (f : K ⟶ L) (U : Cᵒᵖ) (q : ι) :
    (((J.complexToPresheaf A c).map f).app U).f q = (f.f q).hom.app U := rfl

end SectionComplexes

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (A : Type*) [Category* A] [Abelian A] [HasSheafify J A] {ι : Type*} (c : ComplexShape ι) (i : ι)

/-- The homology of a complex of sheaves is the sheafification of the homology of the underlying
complex of presheaves. -/
noncomputable def homologyFunctorIsoSheafify :
    HomologicalComplex.homologyFunctor (Sheaf J A) c i ≅
      (sheafToPresheaf J A).mapHomologicalComplex c ⋙
        HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ A) c i ⋙ presheafToSheaf J A :=
  -- a sheaf is the sheafification of its underlying presheaf, and sheafification is exact
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.mapHomologicalComplexIdIso _ c).symm ≪≫
      NatIso.mapHomologicalComplex (asIso (sheafificationAdjunction J A).counit).symm c ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) c).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((presheafToSheaf J A).mapHomologicalComplexCompHomologyFunctorIso c i)

end CategoryTheory.GrothendieckTopology

namespace HomologicalComplex

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {A : Type*} [Category* A] [HasZeroMorphisms A] {ι : Type*} {c : ComplexShape ι}

/-- The presheaf of section complexes of a complex of sheaves on an arbitrary site. -/
abbrev sheafPresheaf (K : HomologicalComplex (Sheaf J A) c) :
    Cᵒᵖ ⥤ HomologicalComplex A c :=
  (J.complexToPresheaf A c).obj K

/-- The section complex is obtained by applying the native sheaf-sections functor. -/
@[simp]
lemma sheafPresheaf_obj (K : HomologicalComplex (Sheaf J A) c) (U : Cᵒᵖ) :
    (sheafPresheaf K).obj U = (((sheafSections J A).obj U).mapHomologicalComplex c).obj K := by
  rw [sheafPresheaf, GrothendieckTopology.complexToPresheaf]
  rfl

/-- Evaluation in one degree recovers precisely the caller's sheaf in that degree. -/
@[simp]
lemma sheafPresheaf_comp_eval (K : HomologicalComplex (Sheaf J A) c) (q : ι) :
    sheafPresheaf K ⋙ HomologicalComplex.eval A c q = (K.X q).obj := by
  rw [sheafPresheaf, GrothendieckTopology.complexToPresheaf]
  rfl

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {A : Type*} [Category* A] [Abelian A] [HasSheafify J A] {S : ShortComplex (Sheaf J A)}

/-- **A short exact sequence of sheaves ends with a sheafified cokernel.** For a short exact
sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of sheaves, the map from the presheaf cokernel of `F₁ ⟶ F₂` to
`F₃` induced by `F₂ ⟶ F₃` becomes an isomorphism after sheafification. -/
theorem isIso_presheafToSheaf_map_cokernelDesc (hS : S.ShortExact) :
    IsIso ((presheafToSheaf J A).map
      (cokernel.desc S.f.hom S.g.hom (S.map (sheafToPresheaf J A)).zero)) := by
  let a := presheafToSheaf J A
  let ε := (sheafificationAdjunction J A).counit
  have := hS.epi_g
  -- `τ` identifies the sheafified cokernel with `F₃`; its inverse is induced by the universal
  -- property of `F₃` as the cokernel of `F₁ ⟶ F₂`
  let c := cokernel.desc S.f.hom S.g.hom (S.map (sheafToPresheaf J A)).zero
  let τ := a.map c ≫ ε.app S.X₃
  have hτ : a.map (cokernel.π S.f.hom) ≫ τ = ε.app S.X₂ ≫ S.g := by
    simp only [τ, c, ← a.map_comp_assoc, cokernel.π_desc]
    exact ε.naturality S.g
  have hψ : S.f ≫ inv (ε.app S.X₂) ≫ a.map (cokernel.π S.f.hom) = 0 := by
    have hn : ε.app S.X₁ ≫ S.f = a.map S.f.hom ≫ ε.app S.X₂ := (ε.naturality S.f).symm
    rw [← cancel_epi (ε.app S.X₁), comp_zero, reassoc_of% hn, IsIso.hom_inv_id_assoc,
      ← a.map_comp, cokernel.condition, a.map_zero]
  let ψ := hS.gIsCokernel.desc (CokernelCofork.ofπ _ hψ)
  have hgψ : S.g ≫ ψ = inv (ε.app S.X₂) ≫ a.map (cokernel.π S.f.hom) :=
    hS.gIsCokernel.fac (CokernelCofork.ofπ _ hψ) WalkingParallelPair.one
  have : IsIso τ := ⟨ψ, by
    rw [← cancel_epi (a.map (cokernel.π S.f.hom)), reassoc_of% hτ, hgψ,
      IsIso.hom_inv_id_assoc, Category.comp_id], by
    rw [← cancel_epi S.g, reassoc_of% hgψ, hτ, IsIso.inv_hom_id_assoc]
    exact (Category.comp_id _).symm⟩
  exact IsIso.of_isIso_comp_right (a.map c) (ε.app S.X₃)

end CategoryTheory.ShortComplex.ShortExact
