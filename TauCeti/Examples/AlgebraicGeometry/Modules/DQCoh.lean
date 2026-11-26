/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Derived.DQCoh
public import TauCeti.Examples.AlgebraicGeometry.Modules.PseudoCoherent

import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# Tests for the derived category of complexes with quasi-coherent cohomology

For any model of the derived category of `𝒪_X`-modules, the structure sheaf placed in degree zero
lies in `D_QCoh(𝒪_X)`, and so do its shifts and the coproducts of copies of it. On the spectrum of
a discrete valuation ring there is a sheaf of modules which is not quasi-coherent, and it gives an
object placed in degree zero outside `D_QCoh`.

Under the equivalence `D(ℤ) ≌ D_QCoh(𝒪_{Spec ℤ})`, `ℤ[0]` goes to `𝒪[0]` and `(ℤ/2)[0]` to
`(ℤ/2)~[0]`, whose derived global sections are `(ℤ/2)[0]` again: `(ℤ/2)~` has no higher
cohomology. Its support is the closed point `(2)`: its derived restriction to `D(2)` vanishes, as
the examples for derived restriction check.
-/

open CategoryTheory Limits DerivedCategory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Coherent

universe w w' u

variable (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]

/-- `𝒪_X[0] ∈ D_QCoh(𝒪_X)`. -/
example : DQCoh X ((singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  (DQCoh.singleFunctor_obj_mem_iff _ 0).2 inferInstance

/-- The shifts `𝒪_X[n]` lie in `D_QCoh(𝒪_X)`. -/
example (n : ℤ) :
    DQCoh X (((singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))⟦n⟧) :=
  (DQCoh X).le_shift n _ ((DQCoh.singleFunctor_obj_mem_iff _ 0).2 inferInstance)

/-- A coproduct of copies of `𝒪_X[0]`, indexed by a `u`-small type, lies in `D_QCoh(𝒪_X)`. -/
example (J : Type u) :
    DQCoh X (∐ fun _ : J ↦ (singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  (DQCoh X).prop_of_isColimit (colimit.isColimit _)
    (fun _ ↦ (DQCoh.singleFunctor_obj_mem_iff _ 0).2 inferInstance)

/-- Over the spectrum of a discrete valuation ring, some sheaf of modules placed in degree zero
does not lie in `D_QCoh`. -/
example (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HasDerivedCategory.{w} (Spec (.of R)).Modules] :
    ∃ F : (Spec (.of R)).Modules, ¬ DQCoh _ ((singleFunctor _ 0).obj F) := by
  obtain ⟨F, -, hF, -⟩ :=
    exists_isPseudoCoherentOver_and_not_isQuasicoherent_of_isDiscreteValuationRing R
  exact ⟨F, fun h ↦ hF ((DQCoh.singleFunctor_obj_mem_iff F 0).1 h)⟩

section SpecInt

variable [HasDerivedCategory.{w} (Spec (.of ℤ)).Modules]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (CommRingCat.of ℤ))]

/-- Under `D(ℤ) ≌ D_QCoh(𝒪_{Spec ℤ})`, `ℤ[0]` goes to `𝒪_{Spec ℤ}[0]`. -/
example : Nonempty (((DQCoh.affineEquiv (.of ℤ)).functor.obj
      ((singleFunctor _ 0).obj (ModuleCat.of (CommRingCat.of ℤ) ℤ))).obj ≅
    (singleFunctor _ 0).obj (SheafOfModules.unit (Spec (.of ℤ)).ringCatSheaf)) :=
  ⟨eqToIso (DQCoh.affineEquiv_functor_obj_obj ..) ≪≫
    ((tilde.functor _).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (singleFunctor _ 0).mapIso tildeSelf⟩

/-- Under `D(ℤ) ≌ D_QCoh(𝒪_{Spec ℤ})`, `(ℤ/2)[0]` goes to `(ℤ/2)~[0]`. -/
example : Nonempty (((DQCoh.affineEquiv (.of ℤ)).functor.obj
      ((singleFunctor _ 0).obj (ModuleCat.of (CommRingCat.of ℤ) (ZMod 2)))).obj ≅
    (singleFunctor _ 0).obj ((tilde.functor (.of ℤ)).obj (.of _ (ZMod 2)))) :=
  ⟨eqToIso (DQCoh.affineEquiv_functor_obj_obj ..) ≪≫
    ((tilde.functor _).mapDerivedCategorySingleFunctor 0).app _⟩

/-- The derived global sections of `(ℤ/2)~[0]` are `(ℤ/2)[0]`: `(ℤ/2)~` has no higher
cohomology on `Spec ℤ`. -/
example : Nonempty ((derivedModuleSpecΓFunctor (.of ℤ)).obj
      ((singleFunctor _ 0).obj ((tilde.functor (.of ℤ)).obj (.of _ (ZMod 2)))) ≅
    (singleFunctor _ 0).obj (ModuleCat.of (CommRingCat.of ℤ) (ZMod 2))) :=
  ⟨(derivedModuleSpecΓFunctor _).mapIso
      (((tilde.functor _).mapDerivedCategorySingleFunctor 0).app _).symm ≪≫
    (asIso ((tildeDerivedAdjunction _).unit.app _)).symm⟩

/-- The equivalence `D(ℤ) ≌ D_QCoh(𝒪_{Spec ℤ})` sends the non-zero object `(ℤ/2)[0]` to a non-zero
object. -/
example : ¬ IsZero ((DQCoh.affineEquiv (.of ℤ)).functor.obj
    ((singleFunctor _ 0).obj (ModuleCat.of (CommRingCat.of ℤ) (ZMod 2)))) := fun h ↦ by
  have := ModuleCat.subsingleton_of_isZero (IsZero.of_full_of_faithful_of_isZero
    (singleFunctor _ 0) _ (IsZero.of_full_of_faithful_of_isZero (DQCoh.affineEquiv (.of ℤ)).functor
      _ h))
  exact zero_ne_one (Subsingleton.elim (0 : ZMod 2) 1)

end SpecInt

end TauCeti.AlgebraicGeometry.Coherent
