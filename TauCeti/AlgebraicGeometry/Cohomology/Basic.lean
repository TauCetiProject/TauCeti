/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Cohomology of sheaves of modules on a scheme

Mathlib defines the cohomology `CategoryTheory.Sheaf.H` of an abelian sheaf on a site as an
`Ext` group from the constant sheaf `ℤ`. This file applies that construction to the underlying
abelian sheaf of an `𝒪_X`-module and packages the result in the scheme-module API.

For a scheme `X` and `M : X.Modules`, the main declarations are:

* `Scheme.Modules.Cohomology M i`, the group `Hⁱ(X, M)`;
* `Scheme.Modules.cohomologyFunctor X i`, functoriality in the coefficient sheaf;
* `Scheme.Modules.cohomologyZeroEquiv`, the canonical equivalence
  `H⁰(X, M) ≃+ Γ(M, ⊤)` with global sections;
* `Scheme.Modules.cohomologyOn M n U`, the cohomology `Hⁿ(U, M)` of an open subset,
  `Scheme.Modules.cohomologyOnRes` its restriction maps,
  `Scheme.Modules.cohomologyOnMap` its functoriality in the coefficient sheaf,
  `Scheme.Modules.cohomologyOnZeroEquiv` the identification of `H⁰(U, M)` with `Γ(M, U)`, and
  `Scheme.Modules.cohomologyOnTopIso` the identification of `Hⁿ(⊤, M)` with `Hⁿ(X, M)`.

The construction is stated for every sheaf of modules, which is the natural generality of sheaf
cohomology. In particular it applies to finitely presented sheaves through their underlying
objects, and hence supplies the `Hⁱ(X, ℱ)` used for coherent sheaves in
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer B. Finite-dimensionality for proper schemes,
vanishing on curves, and the comparison with Čech cohomology remain later Layer B work.

No formalization is vendored. The definitions reuse Mathlib's `Sheaf.H`, `Sheaf.functorH`,
`Sheaf.H.equiv₀` and `Sheaf.H'`, and the comparison at the terminal open subset is
`TauCeti/CategoryTheory/Sites/SheafCohomology/Terminal.lean`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- The `i`th cohomology group `Hⁱ(X, M)` of a sheaf of modules on a scheme.

This is sheaf cohomology on the small Zariski site of `X`, obtained by forgetting the
`𝒪_X`-module structure and applying Mathlib's `CategoryTheory.Sheaf.H`. -/
abbrev Cohomology (M : X.Modules) (i : ℕ) : Type u :=
  CategoryTheory.Sheaf.H.{u}
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) i

/-- Degree-`i` cohomology as an additive functor from sheaves of modules to abelian groups. -/
abbrev cohomologyFunctor (X : Scheme.{u}) (i : ℕ) : X.Modules ⥤ AddCommGrpCat.{u} :=
  _root_.SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH.{u} _ i

/-- Degreewise scheme-module cohomology preserves addition and zero morphisms. -/
instance (X : Scheme.{u}) (i : ℕ) : (cohomologyFunctor X i).Additive :=
  inferInstanceAs ((_root_.SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH.{u} _ i).Additive)

/-- Zeroth cohomology is canonically equivalent to the group of global sections.

Naturality in the coefficient sheaf follows from `CategoryTheory.Sheaf.H.equiv₀_naturality`
and `CategoryTheory.Sheaf.H.equiv₀_symm_naturality`, applied to `isTerminalTop` and the
underlying sheaf morphism. -/
def cohomologyZeroEquiv (M : X.Modules) :
    Cohomology M 0 ≃+ Γ(M, ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) isTerminalTop

/-- The identification of zeroth cohomology with global sections is Mathlib's
`CategoryTheory.Sheaf.H.equiv₀` at the terminal open. -/
lemma cohomologyZeroEquiv_apply {M : X.Modules} (x : Cohomology M 0) :
    cohomologyZeroEquiv M x = CategoryTheory.Sheaf.H.equiv₀
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) isTerminalTop x :=
  (rfl)

/-- The degree-zero cohomology equivalence is natural in the coefficient sheaf. -/
lemma cohomologyZeroEquiv_naturality {M N : X.Modules} (f : M ⟶ N) (x : Cohomology M 0) :
    cohomologyZeroEquiv N ((cohomologyFunctor X 0).map f x) =
      f.app ⊤ (cohomologyZeroEquiv M x) :=
  (CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f) x).symm

section Opens

variable (M : X.Modules)

/-- The cohomology `Hⁿ(U, M)` of an open subset `U` of a scheme `X` with coefficients in a sheaf
of modules `M`, as an abelian group.

This is `CategoryTheory.Sheaf.H'` applied to the underlying abelian sheaf of `M`. At `U = ⊤` it
agrees with `Scheme.Modules.Cohomology`, by `Scheme.Modules.cohomologyOnTopIso`. -/
abbrev cohomologyOn (n : ℕ) (U : Opens X) : AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.H'.{u} ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n U

/-- Restriction in cohomology along an inclusion of open subsets. -/
abbrev cohomologyOnRes (n : ℕ) {U V : Opens X} (h : U ≤ V) :
    cohomologyOn M n V ⟶ cohomologyOn M n U :=
  (CategoryTheory.Sheaf.cohomologyPresheaf.{u}
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n).map (homOfLE h).op

@[simp]
lemma cohomologyOnRes_refl (n : ℕ) (U : Opens X) :
    cohomologyOnRes M n (le_refl U) = 𝟙 _ := by
  dsimp only [cohomologyOnRes]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]

@[simp, reassoc]
lemma cohomologyOnRes_comp (n : ℕ) {U V W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W) :
    cohomologyOnRes M n hVW ≫ cohomologyOnRes M n hUV =
      cohomologyOnRes M n (hUV.trans hVW) := by
  dsimp only [cohomologyOnRes]
  rw [← CategoryTheory.Functor.map_comp, ← op_comp, homOfLE_comp]

/-- Restricting twice in cohomology is restricting along the composite inclusion. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnRes_comp_apply (n : ℕ)
    {U V W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W) (x : cohomologyOn M n W) :
    cohomologyOnRes M n hUV (cohomologyOnRes M n hVW x) =
      cohomologyOnRes M n (hUV.trans hVW) x := by
  rw [← ConcreteCategory.comp_apply, cohomologyOnRes_comp]

/-- Degree-zero cohomology over an open subset `U` is the group of sections of `M` over `U`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnZeroEquiv (U : Opens X) :
    cohomologyOn M 0 U ≃+ Γ(M, U) :=
  TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) U

/-- The identification of degree-zero cohomology with sections commutes with restriction. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnZeroEquiv_cohomologyOnRes
    {U V : Opens X} (h : U ≤ V) (x : cohomologyOn M 0 V) :
    M.cohomologyOnZeroEquiv U (cohomologyOnRes M 0 h x) =
      M.presheaf.map (homOfLE h).op (M.cohomologyOnZeroEquiv V x) :=
  TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv_naturality_left _ (homOfLE h) x

/-- The map `Hⁿ(U, M) ⟶ Hⁿ(U, N)` induced by a morphism `f : M ⟶ N` of sheaves of modules. -/
abbrev _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnMap {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) (U : Opens X) : cohomologyOn M n U ⟶ cohomologyOn N n U :=
  ((CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n).map
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f)).app (Opposite.op U)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnMap_id (n : ℕ) (U : Opens X) :
    Scheme.Modules.cohomologyOnMap (𝟙 M) n U = 𝟙 _ :=
  NatTrans.congr_app ((_root_.SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n : X.Modules ⥤ _).map_id M) (Opposite.op U)

@[simp, reassoc]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnMap_comp {N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) (U : Opens X) :
    Scheme.Modules.cohomologyOnMap (f ≫ g) n U =
      Scheme.Modules.cohomologyOnMap f n U ≫ Scheme.Modules.cohomologyOnMap g n U :=
  NatTrans.congr_app ((_root_.SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n : X.Modules ⥤ _).map_comp f g)
      (Opposite.op U)

/-- The identification of degree-zero cohomology with sections is natural in the coefficient
sheaf. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnZeroEquiv_naturality {N : X.Modules}
    (f : M ⟶ N) (U : Opens X) (x : cohomologyOn M 0 U) :
    N.cohomologyOnZeroEquiv U (Scheme.Modules.cohomologyOnMap f 0 U x) =
      f.app U (M.cohomologyOnZeroEquiv U x) :=
  TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv_naturality_right _ U x

/-- The cohomology of the whole space is the cohomology of the scheme. -/
noncomputable abbrev cohomologyOnTopIso (n : ℕ) :
    cohomologyOn M n ⊤ ≅ AddCommGrpCat.of (Cohomology M n) :=
  ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M).cohomologyPresheafObjIsoH
    n isTerminalTop

/-- The identification of `Hⁿ(⊤, M)` with `Hⁿ(X, M)` is natural in the coefficient sheaf. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnTopIso_hom_cohomologyOnMap
    {N : X.Modules} (f : M ⟶ N) (n : ℕ) (x : cohomologyOn M n ⊤) :
    (cohomologyOnTopIso N n).hom (Scheme.Modules.cohomologyOnMap f n ⊤ x) =
      (cohomologyFunctor X n).map f ((cohomologyOnTopIso M n).hom x) :=
  ConcreteCategory.congr_hom ((CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH _ n
    isTerminalTop).hom.naturality ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f)) x

end Opens

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
