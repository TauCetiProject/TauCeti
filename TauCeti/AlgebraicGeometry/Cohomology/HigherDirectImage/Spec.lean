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

/-!
# Higher direct images over `Spec R`

Let `X` be a scheme whose structure morphism `X ↘ Spec R` to the spectrum of a commutative ring `R`
is quasi-compact and quasi-separated, and let `M` be a quasi-coherent `𝒪_X`-module. Combining the
affine-base global-sections comparison
(`AlgebraicGeometry.Scheme.Hom.cohomologyHigherDirectImageGlobalSectionsLinearEquiv`) with the
tilde equivalence on `Spec R` identifies:

1. `Hⁿ(X, M)` `R`-linearly with `(moduleSpecΓFunctor (R := .of R)).obj (Rⁿ (X ↘ Spec R)_* M)`
   (`AlgebraicGeometry.Scheme.Modules.cohomologyHigherDirectImageSpecΓLinearEquiv`, Stacks Tag
   01XK), naturally in `M`.
2. `(Hⁿ(X, M))~` canonically with `Rⁿ (X ↘ Spec R)_* M` in `(Spec R).Modules`
   (`AlgebraicGeometry.Scheme.Modules.tildeCohomologyIsoHigherDirectImage`), naturally in `M`.
3. Finite type and finite presentation of `Rⁿ (X ↘ Spec R)_* M` with
   `Module.Finite R (Cohomology M n)` and `Module.FinitePresentation R (Cohomology M n)`
   (`AlgebraicGeometry.Scheme.Modules.isFiniteType_higherDirectImage_Spec_iff` and
   `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_Spec_iff`), without
   Noetherian hypotheses.

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

/-- **Global sections of higher direct images over `Spec R`** (Stacks Tag 01XK): for a quasi-compact
quasi-separated scheme `X` over `Spec R` and a quasi-coherent `𝒪_X`-module `M`, the cohomology
`Hⁿ(X, M)` is canonically `R`-linearly equivalent to the global sections
`Γ(Spec R, Rⁿ (X ↘ Spec R)_* M)` viewed via `moduleSpecΓFunctor`. -/
def cohomologyHigherDirectImageSpecΓLinearEquiv :
    Cohomology M n ≃ₗ[R]
      (moduleSpecΓFunctor (R := .of R)).obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M) :=
  have hid : ((Spec (.of R)) ↘ Spec (.of R)) = 𝟙 _ := by simp [specOverSpec_over]
  have : (X ↘ Spec (.of R)).IsOver (Spec (.of R)) := ⟨by rw [hid, Category.comp_id]⟩
  ((X ↘ Spec (.of R)).cohomologyHigherDirectImageGlobalSectionsLinearEquiv M n R).trans
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).globalSectionsModuleSpecΓLinearEquiv

/-- Evaluation of `cohomologyHigherDirectImageSpecΓLinearEquiv` via
`higherDirectImageBasicOpenSectionsAddEquiv` on `D(1) = ⊤` and
`globalSectionsModuleSpecΓLinearEquiv`. -/
@[simp]
theorem cohomologyHigherDirectImageSpecΓLinearEquiv_apply (x : Cohomology M n) :
    M.cohomologyHigherDirectImageSpecΓLinearEquiv R n x =
      (((X ↘ Spec (.of R)).higherDirectImage n).obj M).globalSectionsModuleSpecΓLinearEquiv
        ((X ↘ Spec (.of R)).higherDirectImageBasicOpenSectionsAddEquiv M n
          ⟨1, (Spec (.of R)).basicOpen_one⟩ ((cohomologyOnTopBaseLinearEquiv M R n).symm x)) := by
  have hid : ((Spec (.of R)) ↘ Spec (.of R)) = 𝟙 _ := by simp [specOverSpec_over]
  have : (X ↘ Spec (.of R)).IsOver (Spec (.of R)) := ⟨by rw [hid, Category.comp_id]⟩
  exact congrArg
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).globalSectionsModuleSpecΓLinearEquiv
    ((X ↘ Spec (.of R)).cohomologyHigherDirectImageGlobalSectionsLinearEquiv_apply M n R x)

/-- Evaluation of the inverse of `cohomologyHigherDirectImageSpecΓLinearEquiv` via the inverses of
`globalSectionsModuleSpecΓLinearEquiv` and `higherDirectImageBasicOpenSectionsAddEquiv`. -/
@[simp]
theorem cohomologyHigherDirectImageSpecΓLinearEquiv_symm_apply
    (y : (moduleSpecΓFunctor (R := .of R)).obj
      (((X ↘ Spec (.of R)).higherDirectImage n).obj M)) :
    (M.cohomologyHigherDirectImageSpecΓLinearEquiv R n).symm y =
      cohomologyOnTopBaseLinearEquiv M R n
        (((X ↘ Spec (.of R)).higherDirectImageBasicOpenSectionsAddEquiv M n
          ⟨1, (Spec (.of R)).basicOpen_one⟩).symm
          ((((X ↘ Spec (.of R)).higherDirectImage n).obj
            M).globalSectionsModuleSpecΓLinearEquiv.symm y)) := by
  have hid : ((Spec (.of R)) ↘ Spec (.of R)) = 𝟙 _ := by simp [specOverSpec_over]
  have : (X ↘ Spec (.of R)).IsOver (Spec (.of R)) := ⟨by rw [hid, Category.comp_id]⟩
  exact (X ↘ Spec (.of R)).cohomologyHigherDirectImageGlobalSectionsLinearEquiv_symm_apply M n R
    ((((X ↘ Spec (.of R)).higherDirectImage n).obj M).globalSectionsModuleSpecΓLinearEquiv.symm y)

/-- For a quasi-compact quasi-separated scheme `X` over `Spec R` and a quasi-coherent `𝒪_X`-module
`M`, the higher direct image `Rⁿ (X ↘ Spec R)_* M` is canonically isomorphic to the quasi-coherent
sheaf `(Hⁿ(X, M))~` associated to the `R`-module `Hⁿ(X, M)`. -/
def tildeCohomologyIsoHigherDirectImage :
    tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n)) ≅
      ((X ↘ Spec (.of R)).higherDirectImage n).obj M :=
  let e : Cohomology M n ≃ₗ[CommRingCat.of R]
      (moduleSpecΓFunctor (R := .of R)).obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M) :=
    M.cohomologyHigherDirectImageSpecΓLinearEquiv R n
  (tilde.functor (.of R)).mapIso e.toModuleIso ≪≫
    @asIso _ _ _ _ (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _)

/-- The forward morphism of `tildeCohomologyIsoHigherDirectImage` applies `tilde.functor` to
`cohomologyHigherDirectImageSpecΓLinearEquiv` and composes with `fromTildeΓ`. -/
@[simp]
theorem tildeCohomologyIsoHigherDirectImage_hom :
    (M.tildeCohomologyIsoHigherDirectImage R n).hom =
      (tilde.functor (.of R)).map
        (M.cohomologyHigherDirectImageSpecΓLinearEquiv R n :
          Cohomology M n ≃ₗ[CommRingCat.of R] _).toModuleIso.hom ≫
        (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ :=
  (rfl)

/-- The inverse morphism of `tildeCohomologyIsoHigherDirectImage` applies the inverse of
`fromTildeΓ` followed by `tilde.functor` on the inverse of
`cohomologyHigherDirectImageSpecΓLinearEquiv`. -/
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

/-- Over `Spec R`, the higher direct image `Rⁿ (X ↘ Spec R)_* M` of a quasi-coherent `𝒪_X`-module
`M` is of finite type if and only if `Hⁿ(X, M)` is a finitely generated `R`-module. -/
@[simp]
theorem isFiniteType_higherDirectImage_Spec_iff :
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFiniteType ↔
      Module.Finite R (Cohomology M n) := by
  let e := M.tildeCohomologyIsoHigherDirectImage R n
  exact ⟨fun _ ↦ (ModuleCat.isFiniteType_tilde_iff
      (ModuleCat.of (CommRingCat.of R) (Cohomology M n))).mp (isFiniteType_of_epi e.inv),
    fun h ↦
      have : (tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n))).IsFiniteType :=
        (ModuleCat.isFiniteType_tilde_iff
          (ModuleCat.of (CommRingCat.of R) (Cohomology M n))).mpr h
      isFiniteType_of_epi e.hom⟩

/-- Over `Spec R`, the higher direct image `Rⁿ (X ↘ Spec R)_* M` of a quasi-coherent `𝒪_X`-module
`M` is finitely presented if and only if `Hⁿ(X, M)` is a finitely presented `R`-module. -/
@[simp]
theorem isFinitePresentation_higherDirectImage_Spec_iff :
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFinitePresentation ↔
      Module.FinitePresentation R (Cohomology M n) :=
  ((SheafOfModules.isFinitePresentation (Spec (.of R)).ringCatSheaf).prop_iff_of_iso
    (M.tildeCohomologyIsoHigherDirectImage R n).symm).trans
    (ModuleCat.isFinitePresentation_tilde_iff
      (ModuleCat.of (CommRingCat.of R) (Cohomology M n)))

end SpecBase

section Naturality

variable {X : Scheme.{u}} {M₁ M₂ : X.Modules} [M₁.IsQuasicoherent] [M₂.IsQuasicoherent]
  (φ : M₁ ⟶ M₂) (R : Type u) [CommRing R] [X.Over (Spec (.of R))]
  [QuasiCompact (X ↘ Spec (.of R))] [QuasiSeparated (X ↘ Spec (.of R))] (n : ℕ)

/-- `cohomologyHigherDirectImageSpecΓLinearEquiv` is natural in morphisms `φ : M₁ ⟶ M₂` of
quasi-coherent `𝒪_X`-modules, intertwining `cohomologyMapBaseLinear` with the map induced by
`Rⁿ (X ↘ Spec R)_* φ` under `moduleSpecΓFunctor`. -/
theorem cohomologyHigherDirectImageSpecΓLinearEquiv_naturality (x : Cohomology M₁ n) :
    M₂.cohomologyHigherDirectImageSpecΓLinearEquiv R n (cohomologyMapBaseLinear R X φ n x) =
      (moduleSpecΓFunctor (R := .of R)).map (((X ↘ Spec (.of R)).higherDirectImage n).map φ)
        (M₁.cohomologyHigherDirectImageSpecΓLinearEquiv R n x) := by
  have hid : ((Spec (.of R)) ↘ Spec (.of R)) = 𝟙 _ := by simp [specOverSpec_over]
  have : (X ↘ Spec (.of R)).IsOver (Spec (.of R)) := ⟨by rw [hid, Category.comp_id]⟩
  have h₁ :=
    (X ↘ Spec (.of R)).cohomologyHigherDirectImageGlobalSectionsLinearEquiv_naturality φ n R x
  let ψ := ((X ↘ Spec (.of R)).higherDirectImage n).map φ
  exact (congrArg
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M₂).globalSectionsModuleSpecΓLinearEquiv h₁).trans
    (ψ.globalSectionsModuleSpecΓLinearEquiv_naturality _)

/-- `tildeCohomologyIsoHigherDirectImage` is natural in morphisms `φ : M₁ ⟶ M₂` of quasi-coherent
`𝒪_X`-modules. -/
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
        (moduleSpecΓFunctor (R := .of R)).map
          (((X ↘ Spec (.of R)).higherDirectImage n).map φ) :=
    ModuleCat.hom_ext (LinearMap.ext fun x ↦
      cohomologyHigherDirectImageSpecΓLinearEquiv_naturality φ R n x)
  have htilde := ((tilde.functor (.of R)).map_comp _ _).symm.trans
    ((congrArg (tilde.functor (.of R)).map hmod).trans ((tilde.functor (.of R)).map_comp _ _))
  have hcounit :=
    (Scheme.Modules.fromTildeΓNatTrans (R := .of R)).naturality
      (((X ↘ Spec (.of R)).higherDirectImage n).map φ)
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker htilde _).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ hcounit).trans (Category.assoc _ _ _).symm)))

end Naturality

end AlgebraicGeometry.Scheme.Modules

end
