/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients

/-!
# Čech cohomology of quasi-coherent sheaves as modules over the base ring

Let `X` be a scheme over a commutative ring `S` and let `M` be a sheaf of modules on `X`. Its
sections over every open are `S`-modules, through the global functions `Γ(X, ⊤)`, and the
restriction maps are `S`-linear; this is the presheaf of `S`-modules
`(Scheme.Modules.sectionsBasePresheafFunctor S).obj M` of
`TauCeti.AlgebraicGeometry.Modules.Sections`. Its Čech complex for a family of opens is
therefore a complex of `S`-modules, and so is its cohomology.

Let `X` be locally Noetherian, `M` quasi-coherent and `U` a finite family of opens covering `X`
whose nonempty finite intersections are affine. Leray's theorem identifies the Čech cohomology of
`M` for `U` with the cohomology `Hⁿ(X, M)` as abelian groups
(`Scheme.Modules.homologyCechComplexIsoCohomology`). This file shows that the identification is
`S`-linear (`Scheme.Modules.homologyCechComplexLinearEquiv`): the Čech complex of the presheaf of
`S`-modules computes `Hⁿ(X, M)` as an `S`-module. Linear-algebraic operations on the Čech complex,
such as extension of scalars along a flat ring map, thus become available for cohomology.

The underlying complex of abelian groups of the Čech complex of a presheaf of modules is the Čech
complex of the underlying presheaf of abelian groups
(`TauCeti.CategoryTheory.cechComplexFunctorMapIso`), and forgetting the module structure preserves
homology. The action of `s : S` on the Čech cohomology is induced by multiplication by `s` on the
presheaf, which is the endomorphism of `M` given by multiplication by the global function `s`, and
Leray's comparison is natural in the coefficient sheaf.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.homologyCechComplexLinearEquiv`: the `S`-linear equivalence
  between the Čech cohomology of this presheaf for a finite cover with affine intersections and
  `Hⁿ(X, M)`.

## Main statements

* `AlgebraicGeometry.Scheme.Modules.homologyCechComplexLinearEquiv_apply`: its underlying map is
  Leray's comparison `homologyCechComplexIsoCohomology`.
* `AlgebraicGeometry.Scheme.Modules.homologyCechComplexLinearEquiv_naturality`: it is natural in
  the quasi-coherent sheaf.

## References

* R. Hartshorne, *Algebraic Geometry*, Theorem III.4.5.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite
open TauCeti TauCeti.CategoryTheory TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Type u} [CommRing S] {X : Scheme.{u}} [X.Over (Spec (.of S))]
  [IsLocallyNoetherian X] {ι : Type u} [Finite ι] (U : ι → X.Opens)
  (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) (hcover : ⨆ i, U i = ⊤)

/-- Forgetting the module structure commutes with taking cohomology. -/
private def homologyCechIso₁ (M : X.Modules) (n : ℕ) :
    (forget₂ (ModuleCat.{u} S) Ab).obj
        (((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M)).homology n) ≅
      (((forget₂ (ModuleCat.{u} S) Ab).mapHomologicalComplex _).obj
        ((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M))).homology n :=
  ((((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M)).sc n).mapHomologyIso
    (forget₂ (ModuleCat.{u} S) Ab)).symm

/-- Forgetting the module structure commutes with forming Čech complexes. -/
private def homologyCechIso₂ (M : X.Modules) (n : ℕ) :
    (((forget₂ (ModuleCat.{u} S) Ab).mapHomologicalComplex _).obj
        ((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M))).homology n ≅
      ((cechComplexFunctor U).obj M.presheaf).homology n :=
  HomologicalComplex.homologyMapIso
    ((cechComplexFunctorMapIso U (forget₂ (ModuleCat.{u} S) Ab)).app _ ≪≫
      (cechComplexFunctor U).mapIso (sectionsBasePresheafCompForget₂Iso S M)) n

omit [IsLocallyNoetherian X] [Finite ι] in
/-- `homologyCechIso₁` is natural. -/
@[reassoc]
private lemma homologyCechIso₁_hom_naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (forget₂ (ModuleCat.{u} S) Ab).map (HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map f)) n) ≫
        (homologyCechIso₁ U N n).hom =
      (homologyCechIso₁ U M n).hom ≫ HomologicalComplex.homologyMap
        (((forget₂ (ModuleCat.{u} S) Ab).mapHomologicalComplex _).map
          ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map f))) n :=
  ShortComplex.mapHomologyIso_inv_naturality _ _

omit [IsLocallyNoetherian X] in
/-- `homologyCechIso₂` is natural. -/
@[reassoc]
private lemma homologyCechIso₂_hom_naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((forget₂ (ModuleCat.{u} S) Ab).mapHomologicalComplex _).map
          ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map f))) n ≫
        (homologyCechIso₂ U N n).hom =
      (homologyCechIso₂ U M n).hom ≫ HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map f.mapPresheaf) n := by
  have h : ((forget₂ (ModuleCat.{u} S) Ab).mapHomologicalComplex _).map
        ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map f)) ≫
        ((cechComplexFunctorMapIso U (forget₂ (ModuleCat.{u} S) Ab)).app _ ≪≫
          (cechComplexFunctor U).mapIso (sectionsBasePresheafCompForget₂Iso S N)).hom =
      ((cechComplexFunctorMapIso U (forget₂ (ModuleCat.{u} S) Ab)).app _ ≪≫
          (cechComplexFunctor U).mapIso (sectionsBasePresheafCompForget₂Iso S M)).hom ≫
        (cechComplexFunctor U).map f.mapPresheaf := by
    rw [Iso.trans_hom, Iso.trans_hom, Iso.app_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.mapIso_hom, ← Category.assoc,
      ← Functor.comp_map (cechComplexFunctor U) (Functor.mapHomologicalComplex _ _),
      (cechComplexFunctorMapIso U (forget₂ (ModuleCat.{u} S) Ab)).hom.naturality,
      Category.assoc, Functor.comp_map]
    have h' : ((Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u} S) Ab)).map
          ((sectionsBasePresheafFunctor S).map f) ≫ (sectionsBasePresheafCompForget₂Iso S N).hom =
        (sectionsBasePresheafCompForget₂Iso S M).hom ≫ f.mapPresheaf :=
      sectionsBasePresheafCompForget₂Iso_hom_naturality S f
    rw [← Functor.map_comp (cechComplexFunctor U), h', Functor.map_comp]
    simp only [Category.assoc]
  simp only [homologyCechIso₂, HomologicalComplex.homologyMapIso_hom]
  rw [← HomologicalComplex.homologyMap_comp, h, HomologicalComplex.homologyMap_comp]

/-- Leray's comparison of the Čech cohomology of the presheaf of `S`-modules of sections with the
cohomology of `M`, as abelian groups: forget the module structure, which commutes with taking
homology and with forming Čech complexes, and apply `homologyCechComplexIsoCohomology`. -/
private def homologyCechComplexAddIso (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (forget₂ (ModuleCat.{u} S) Ab).obj
        (((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M)).homology n) ≅
      AddCommGrpCat.of (Cohomology M n) :=
  homologyCechIso₁ U M n ≪≫ homologyCechIso₂ U M n ≪≫
    homologyCechComplexIsoCohomology U hU hcover M n

/-- `homologyCechComplexAddIso` is the composite of its three steps. -/
private lemma homologyCechComplexAddIso_hom (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (homologyCechComplexAddIso (S := S) U hU hcover M n).hom =
      (homologyCechIso₁ (S := S) U M n).hom ≫ (homologyCechIso₂ (S := S) U M n).hom ≫
        (homologyCechComplexIsoCohomology U hU hcover M n).hom :=
  rfl

/-- `homologyCechComplexAddIso` is natural in the quasi-coherent sheaf. -/
private lemma homologyCechComplexAddIso_hom_naturality {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (f : M ⟶ N) (n : ℕ) :
    (forget₂ (ModuleCat.{u} S) Ab).map (HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map f)) n) ≫
        (homologyCechComplexAddIso U hU hcover N n).hom =
      (homologyCechComplexAddIso U hU hcover M n).hom ≫ (cohomologyFunctor X n).map f := by
  rw [homologyCechComplexAddIso_hom, homologyCechComplexAddIso_hom]
  -- The goal mentions the abelian sheaf of `M` through two defeq presentations of the ring
  -- sheaf, so the naturality squares are composed as terms rather than by rewriting.
  exact ((homologyCechIso₁_hom_naturality_assoc U f n _).trans (congrArg (_ ≫ ·)
    ((homologyCechIso₂_hom_naturality_assoc U f n _).trans (congrArg (_ ≫ ·)
      (homologyMap_comp_homologyCechComplexIsoCohomology_hom U hU hcover f n))))).trans
    ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)

/-- **Čech cohomology computes cohomology, linearly over the base ring.** Let `X` be a locally
Noetherian scheme over `S`, `M` a quasi-coherent sheaf of modules on `X` and `U` a finite family of
opens covering `X` whose nonempty finite intersections are affine. Then the cohomology of the Čech
complex of the presheaf of `S`-modules of sections of `M` for `U` is `S`-linearly equivalent to
`Hⁿ(X, M)`, for every `n`. The underlying additive equivalence is Leray's comparison
`homologyCechComplexIsoCohomology`. -/
def homologyCechComplexLinearEquiv (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M)).homology n ≃ₗ[S]
      Cohomology M n where
  toAddEquiv := (homologyCechComplexAddIso U hU hcover M n).addCommGroupIsoToAddEquiv
  map_smul' s x := by
    have h := ConcreteCategory.congr_hom (homologyCechComplexAddIso_hom_naturality U hU hcover
      (M.globalSectionsSmul (baseRingToGlobalSections S X s)) n) x
    have hx : (forget₂ (ModuleCat.{u} S) Ab).map (HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map
          (M.globalSectionsSmul (baseRingToGlobalSections S X s)))) n) x = s • x := by
      rw [sectionsBasePresheafFunctor_map_globalSectionsSmul, Functor.map_smul,
        CategoryTheory.Functor.map_id,
        HomologicalComplex.homologyMap_smul, HomologicalComplex.homologyMap_id]
      rfl
    -- The additive equivalence applies the homomorphism of the isomorphism.
    change (homologyCechComplexAddIso U hU hcover M n).hom (s • x) =
      s • (homologyCechComplexAddIso U hU hcover M n).hom x
    rw [base_smul_cohomology, cohomology_smul, ← hx]
    exact h

/-- The underlying map of `homologyCechComplexLinearEquiv` is Leray's comparison
`homologyCechComplexIsoCohomology`, after forgetting the module structure, which commutes with
taking homology and with forming Čech complexes. -/
lemma homologyCechComplexLinearEquiv_apply (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : ((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M)).homology n) :
    homologyCechComplexLinearEquiv U hU hcover M n x =
      (homologyCechComplexIsoCohomology U hU hcover M n).hom
        (HomologicalComplex.homologyMap
          ((cechComplexFunctorMapIso U (forget₂ (ModuleCat.{u} S) Ab)).app _ ≪≫
            (cechComplexFunctor U).mapIso (sectionsBasePresheafCompForget₂Iso S M)).hom n
          (((((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M)).sc
              n).mapHomologyIso (forget₂ (ModuleCat.{u} S) Ab)).inv x)) := by
  unfold homologyCechComplexLinearEquiv
  rfl

/-- `homologyCechComplexLinearEquiv` is natural in the quasi-coherent sheaf. -/
lemma homologyCechComplexLinearEquiv_naturality {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (f : M ⟶ N) (n : ℕ)
    (x : ((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M)).homology n) :
    homologyCechComplexLinearEquiv U hU hcover N n
        (HomologicalComplex.homologyMap
          ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map f)) n x) =
      (cohomologyFunctor X n).map f (homologyCechComplexLinearEquiv U hU hcover M n x) :=
  ConcreteCategory.congr_hom (homologyCechComplexAddIso_hom_naturality U hU hcover f n) x

end AlgebraicGeometry.Scheme.Modules
