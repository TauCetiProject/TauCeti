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
-/

open CategoryTheory Limits DerivedCategory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Coherent

universe w u

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

end TauCeti.AlgebraicGeometry.Coherent
