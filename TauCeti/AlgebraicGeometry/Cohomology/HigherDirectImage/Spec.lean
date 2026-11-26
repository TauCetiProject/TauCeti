/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Higher direct images over `Spec R`

For a scheme `X` quasi-compact and quasi-separated over `Spec R` and a quasi-coherent `𝒪_X`-module
`M`, combining `AlgebraicGeometry.Scheme.Hom.cohomologyHigherDirectImageGlobalSectionsLinearEquiv`
with the tilde equivalence on `Spec R` identifies:
1. `Hⁿ(X, M)` `R`-linearly with `(moduleSpecΓFunctor (R := .of R)).obj (Rⁿ (X ↘ Spec R)_* M)`
   (`AlgebraicGeometry.Scheme.Modules.cohomologyHigherDirectImageSpecΓLinearEquiv`, Stacks Tag
   01XK), naturally in `M` (`cohomologyHigherDirectImageSpecΓLinearEquiv_naturality`).
2. `(Hⁿ(X, M))~` with `Rⁿ (X ↘ Spec R)_* M` in `(Spec R).Modules`
   (`AlgebraicGeometry.Scheme.Modules.tildeCohomologyIsoHigherDirectImage`), naturally in `M`
   (`tildeCohomologyIsoHigherDirectImage_naturality`).
3. Finite type and finite presentation of `Rⁿ (X ↘ Spec R)_* M` with `Module.Finite R` and
   `Module.FinitePresentation R` on `Cohomology M n`
   (`AlgebraicGeometry.Scheme.Modules.isFiniteType_higherDirectImage_Spec_iff` and
   `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_Spec_iff`).

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.5.
* [The Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK).
-/

public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

section SpecBase

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
  (R : Type u) [CommRing R] [X.Over (Spec (.of R))]
  [QuasiCompact (X ↘ Spec (.of R))] [QuasiSeparated (X ↘ Spec (.of R))] (n : ℕ)

/-- **Global sections of higher direct images over `Spec R`** (Stacks Tag 01XK): for `X`
quasi-compact and quasi-separated over `Spec R` and quasi-coherent `M`, `Hⁿ(X, M)` is canonically
`R`-linearly equivalent to `(moduleSpecΓFunctor (R := .of R)).obj (Rⁿ (X ↘ Spec R)_* M)`. -/
def cohomologyHigherDirectImageSpecΓLinearEquiv :
    Cohomology M n ≃ₗ[R]
      (moduleSpecΓFunctor (R := .of R)).obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M) :=
  ((X ↘ Spec (.of R)).cohomologyHigherDirectImageGlobalSectionsLinearEquiv M n R).trans
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).globalSectionsModuleSpecΓLinearEquiv

/-- Evaluation of `cohomologyHigherDirectImageSpecΓLinearEquiv` via
`higherDirectImageSectionsAddEquiv` on `⊤` and `globalSectionsModuleSpecΓLinearEquiv`. -/
@[simp]
theorem cohomologyHigherDirectImageSpecΓLinearEquiv_apply (x : Cohomology M n) :
    M.cohomologyHigherDirectImageSpecΓLinearEquiv R n x =
      (((X ↘ Spec (.of R)).higherDirectImage n).obj M).globalSectionsModuleSpecΓLinearEquiv
        ((X ↘ Spec (.of R)).higherDirectImageSectionsAddEquiv M n
          (isAffineOpen_top (Spec (.of R))) ((cohomologyOnTopBaseLinearEquiv M R n).symm x)) :=
  congrArg (((X ↘ Spec (.of R)).higherDirectImage n).obj M).globalSectionsModuleSpecΓLinearEquiv
    ((X ↘ Spec (.of R)).cohomologyHigherDirectImageGlobalSectionsLinearEquiv_apply M n R x)

/-- Evaluation of `(cohomologyHigherDirectImageSpecΓLinearEquiv).symm`. -/
@[simp]
theorem cohomologyHigherDirectImageSpecΓLinearEquiv_symm_apply
    (y : (moduleSpecΓFunctor (R := .of R)).obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M)) :
    (M.cohomologyHigherDirectImageSpecΓLinearEquiv R n).symm y =
      cohomologyOnTopBaseLinearEquiv M R n
        (((X ↘ Spec (.of R)).higherDirectImageSectionsAddEquiv M n
          (isAffineOpen_top (Spec (.of R)))).symm
          ((((X ↘ Spec (.of R)).higherDirectImage n).obj
            M).globalSectionsModuleSpecΓLinearEquiv.symm y)) :=
  (X ↘ Spec (.of R)).cohomologyHigherDirectImageGlobalSectionsLinearEquiv_symm_apply M n R _

/-- For `X` quasi-compact and quasi-separated over `Spec R` and quasi-coherent `M`, the higher
direct image `Rⁿ (X ↘ Spec R)_* M` is canonically isomorphic to `(Hⁿ(X, M))~`. -/
def tildeCohomologyIsoHigherDirectImage :
    tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n)) ≅
      ((X ↘ Spec (.of R)).higherDirectImage n).obj M :=
  (tilde.functor (.of R)).mapIso
      (M.cohomologyHigherDirectImageSpecΓLinearEquiv R n :
        Cohomology M n ≃ₗ[CommRingCat.of R] _).toModuleIso ≪≫
    @asIso _ _ _ _ (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _)

/-- Forward morphism of `tildeCohomologyIsoHigherDirectImage`. -/
@[simp]
theorem tildeCohomologyIsoHigherDirectImage_hom :
    (M.tildeCohomologyIsoHigherDirectImage R n).hom =
      (tilde.functor (.of R)).map
        (M.cohomologyHigherDirectImageSpecΓLinearEquiv R n :
          Cohomology M n ≃ₗ[CommRingCat.of R] _).toModuleIso.hom ≫
        (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ :=
  (rfl)

/-- Inverse morphism of `tildeCohomologyIsoHigherDirectImage`. -/
@[simp]
theorem tildeCohomologyIsoHigherDirectImage_inv :
    (M.tildeCohomologyIsoHigherDirectImage R n).inv =
      haveI : IsIso (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ :=
        Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _
      CategoryTheory.inv (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ ≫
        (tilde.functor (.of R)).map
          (M.cohomologyHigherDirectImageSpecΓLinearEquiv R n :
            Cohomology M n ≃ₗ[CommRingCat.of R] _).toModuleIso.inv :=
  (rfl)

/-- For `X` quasi-compact and quasi-separated over `Spec R`, `Rⁿ (X ↘ Spec R)_* M` is of finite type
if and only if `Hⁿ(X, M)` is a finitely generated `R`-module. -/
@[simp]
theorem isFiniteType_higherDirectImage_Spec_iff :
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFiniteType ↔
      Module.Finite R (Cohomology M n) := by
  let e := M.tildeCohomologyIsoHigherDirectImage R n
  let C := ModuleCat.of (CommRingCat.of R) (Cohomology M n)
  exact ⟨fun _ ↦ (ModuleCat.isFiniteType_tilde_iff C).mp (isFiniteType_of_epi e.inv), fun h ↦
    have := (ModuleCat.isFiniteType_tilde_iff C).mpr h
    isFiniteType_of_epi e.hom⟩

/-- For `X` quasi-compact and quasi-separated over `Spec R`, `Rⁿ (X ↘ Spec R)_* M` is finitely
presented if and only if `Hⁿ(X, M)` is a finitely presented `R`-module. -/
@[simp]
theorem isFinitePresentation_higherDirectImage_Spec_iff :
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFinitePresentation ↔
      Module.FinitePresentation R (Cohomology M n) :=
  ((SheafOfModules.isFinitePresentation (Spec (.of R)).ringCatSheaf).prop_iff_of_iso
    (M.tildeCohomologyIsoHigherDirectImage R n).symm).trans
    (ModuleCat.isFinitePresentation_tilde_iff (ModuleCat.of (CommRingCat.of R) (Cohomology M n)))

end SpecBase

section Naturality

variable {X : Scheme.{u}} {M₁ M₂ : X.Modules} [M₁.IsQuasicoherent] [M₂.IsQuasicoherent]
  (φ : M₁ ⟶ M₂) (R : Type u) [CommRing R] [X.Over (Spec (.of R))]
  [QuasiCompact (X ↘ Spec (.of R))] [QuasiSeparated (X ↘ Spec (.of R))] (n : ℕ)

/-- Naturality of `cohomologyHigherDirectImageSpecΓLinearEquiv` in `φ : M₁ ⟶ M₂`. -/
theorem cohomologyHigherDirectImageSpecΓLinearEquiv_naturality (x : Cohomology M₁ n) :
    M₂.cohomologyHigherDirectImageSpecΓLinearEquiv R n (cohomologyMapBaseLinear R X φ n x) =
      (moduleSpecΓFunctor (R := .of R)).map (((X ↘ Spec (.of R)).higherDirectImage n).map φ)
        (M₁.cohomologyHigherDirectImageSpecΓLinearEquiv R n x) :=
  let f := X ↘ Spec (.of R)
  (congrArg ((f.higherDirectImage n).obj M₂).globalSectionsModuleSpecΓLinearEquiv
    (f.cohomologyHigherDirectImageGlobalSectionsLinearEquiv_naturality φ n R x)).trans
    (((f.higherDirectImage n).map φ).globalSectionsModuleSpecΓLinearEquiv_naturality _)

/-- Naturality of `tildeCohomologyIsoHigherDirectImage` in `φ : M₁ ⟶ M₂`. -/
@[reassoc]
theorem tildeCohomologyIsoHigherDirectImage_naturality :
    (tilde.functor (.of R)).map
        (ModuleCat.ofHom (cohomologyMapBaseLinear R X φ n :
          Cohomology M₁ n →ₗ[CommRingCat.of R] Cohomology M₂ n)) ≫
      (M₂.tildeCohomologyIsoHigherDirectImage R n).hom =
    (M₁.tildeCohomologyIsoHigherDirectImage R n).hom ≫
      ((X ↘ Spec (.of R)).higherDirectImage n).map φ := by
  have hmod :
      ModuleCat.ofHom (cohomologyMapBaseLinear R X φ n :
          Cohomology M₁ n →ₗ[CommRingCat.of R] Cohomology M₂ n) ≫
        (M₂.cohomologyHigherDirectImageSpecΓLinearEquiv R n :
          Cohomology M₂ n ≃ₗ[CommRingCat.of R] _).toModuleIso.hom =
      (M₁.cohomologyHigherDirectImageSpecΓLinearEquiv R n :
          Cohomology M₁ n ≃ₗ[CommRingCat.of R] _).toModuleIso.hom ≫
        (moduleSpecΓFunctor (R := .of R)).map (((X ↘ Spec (.of R)).higherDirectImage n).map φ) :=
    ModuleCat.hom_ext (LinearMap.ext (cohomologyHigherDirectImageSpecΓLinearEquiv_naturality φ R n))
  exact (((CommSq.mk hmod).map (tilde.functor (.of R))).vert_comp
    ⟨(Scheme.Modules.fromTildeΓNatTrans (R := .of R)).naturality _⟩).w

end Naturality

end AlgebraicGeometry.Scheme.Modules

end
