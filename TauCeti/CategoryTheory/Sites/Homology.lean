/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Abelian
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Homology of complexes of sheaves

Let `A` be an abelian category and `(C, J)` a site on which `A`-valued presheaves can be
sheafified. Homology in the abelian category of `A`-valued sheaves is not computed objectwise:
the inclusion of sheaves into presheaves preserves kernels but not cokernels. It is computed by
sheafifying the objectwise homology of the underlying complex of presheaves
(`CategoryTheory.GrothendieckTopology.homologyFunctorIsoSheafify`), because sheafification is exact
and a sheaf is the sheafification of its underlying presheaf.

This is how the cohomology sheaves of a complex of sheaves, for instance the higher direct images
of a morphism of sites, are compared with presheaves defined object by object.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology

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
