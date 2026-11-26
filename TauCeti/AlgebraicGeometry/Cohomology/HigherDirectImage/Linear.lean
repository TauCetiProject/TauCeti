/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic

/-!
# Linear identification of higher direct images over an affine base

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated morphism of schemes and `M` a quasi-coherent
`𝒪_X`-module. The file `Cohomology/HigherDirectImage/Quasicoherent.lean` constructs an additive
equivalence `higherDirectImageSectionsAddEquiv : Hⁿ(f⁻¹ V, M) ≃+ Γ(Rⁿ f_* M, V)` for every affine
open `V` of `Y`. Here we show that this equivalence is semilinear with respect to the pullback of
global functions (`Scheme.Hom.higherDirectImageSectionsAddEquiv_smul`): a global function
`r : Γ(Y, ⊤)` acts on `Hⁿ(f⁻¹ V, M)` through `f^* r` and on `Γ(Rⁿ f_* M, V)` through its
restriction to `V`.

When `Y` is affine, evaluating at `V = ⊤` yields the additive equivalence
`Scheme.Hom.higherDirectImageGlobalSectionsAddEquiv : Hⁿ(X, M) ≃+ Γ(Rⁿ f_* M, ⊤)` respecting global
functions (`Scheme.Hom.higherDirectImageGlobalSectionsAddEquiv_smul`). When `Y = Spec R` and `X` is
a quasi-compact, quasi-separated scheme over `Spec R`, restricting scalars along `R ≃ Γ(Spec R, ⊤)`
upgrades it to an `R`-linear equivalence
`Scheme.Modules.higherDirectImageBaseLinearEquiv : Hⁿ(X, M) ≃ₗ[R] Γ(Spec R, Rⁿ f_* M)`.
Since `Rⁿ f_* M` is quasi-coherent (`isQuasicoherent_higherDirectImage`), Mathlib's counit
`fromTildeΓ` identifies it with the associated sheaf `(Hⁿ(X, M))~`
(`Scheme.Modules.tildeCohomologyIsoHigherDirectImage`, Stacks Tag 01XK). Consequently, `Rⁿ f_* M` is
of finite type if and only if `Hⁿ(X, M)` is a finite `R`-module
(`isFiniteType_higherDirectImage_iff`), and finitely presented if and only if `Hⁿ(X, M)` is finitely
presented (`isFinitePresentation_higherDirectImage_iff`), which over a Noetherian ring `R` reduces
to finiteness (`isFinitePresentation_higherDirectImage_iff_finite`).

No diamond `Module Γ(Y, ⊤) (Cohomology M n)` instance is introduced.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsAddEquiv_smul`:
  scalar compatibility of `higherDirectImageSectionsAddEquiv` on affine opens of the target.
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageGlobalSectionsAddEquiv`:
  `Hⁿ(X, M) ≃+ Γ(Rⁿ f_* M, ⊤)` over an affine base, with scalar compatibility
  `higherDirectImageGlobalSectionsAddEquiv_smul`.
* `AlgebraicGeometry.Scheme.Modules.higherDirectImageBaseLinearEquiv`:
  `Hⁿ(X, M) ≃ₗ[R] moduleSpecΓFunctor.obj (Rⁿ (X ↘ Spec R)_* M)`.
* `AlgebraicGeometry.Scheme.Modules.tildeCohomologyIsoHigherDirectImage`:
  `tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n)) ≅ Rⁿ (X ↘ Spec R)_* M`.
* `AlgebraicGeometry.Scheme.Modules.isFiniteType_higherDirectImage_iff`:
  `(Rⁿ (X ↘ Spec R)_* M).IsFiniteType ↔ Module.Finite R (Cohomology M n)`.
* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_iff`:
  `(Rⁿ (X ↘ Spec R)_* M).IsFinitePresentation ↔ Module.FinitePresentation R (Cohomology M n)`.
* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_iff_finite`:
  over a Noetherian ring `R`,
  `(Rⁿ (X ↘ Spec R)_* M).IsFinitePresentation ↔ Module.Finite R (Cohomology M n)`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.5.
* [Stacks, Lemma 30.4.6 (01XK)](https://stacks.math.columbia.edu/tag/01XK).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Identifying `cohomologyOn M n ⊤` with `cohomologyOn M n (f ⁻¹ᵁ ⊤)` via restriction maps avoids
forcing the kernel to unfold `CategoryTheory.Sheaf.H'` during typeclass unification. -/
private def cohomologyOnTopEquivPreimageTop (M : X.Modules) (n : ℕ) :
    cohomologyOn M n ⊤ ≃ₗ[Γ(X, ⊤)] cohomologyOn M n (f ⁻¹ᵁ ⊤) :=
  have h {U V : X.Opens} (hUV : U ≤ V) (hVU : V ≤ U) :
      cohomologyOnResLinear M n hVU ∘ₗ cohomologyOnResLinear M n hUV = .id := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, cohomologyOnResLinear_apply,
      cohomologyOnRes_comp_apply]
    exact (ConcreteCategory.congr_hom (cohomologyOnRes_refl M n V) x).trans
      (ConcreteCategory.id_apply x)
  LinearEquiv.ofLinearMap
    (cohomologyOnResLinear M n (le_of_eq f.preimage_top))
    (cohomologyOnResLinear M n (le_of_eq f.preimage_top.symm))
    (h _ _) (h _ _)

section QuasiCompactQuasiSeparated

variable [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)

/-- Scalar compatibility of `higherDirectImageSectionsAddEquiv`: for an affine open `V` of `Y`,
pulling back a global function `r : Γ(Y, ⊤)` along `f` corresponds to multiplying by its
restriction to `V` in `Γ(Rⁿ f_* M, V)`. -/
lemma higherDirectImageSectionsAddEquiv_smul {V : Y.Opens} (hV : IsAffineOpen V)
    (r : Γ(Y, ⊤)) (x : cohomologyOn M n (f ⁻¹ᵁ V)) :
    f.higherDirectImageSectionsAddEquiv M n hV (f.appTop r • x) =
      (Y.presheaf.map V.leTop.op r : Γ(Y, V)) •
        f.higherDirectImageSectionsAddEquiv M n hV x := by
  let e := f.higherDirectImagePresheafToPresheafIso M n
  let y : ((f.higherDirectImagePresheaf n).obj M).obj (.op V) := (e.inv.app (.op V)) x
  have hy : e.hom.app (.op V) y = x := Iso.inv_hom_id_apply (e.app (.op V)) x
  let rV : Y.ringCatSheaf.obj.obj (.op V) := Y.presheaf.map V.leTop.op r
  have hsmul : f.appTop r • x = e.hom.app (.op V) (rV • y) := by
    rw [← hy]
    exact (f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r V y).symm
  rw [hsmul, ← hy,
    higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app,
    higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app]
  -- `higherDirectImagePresheafSectionsLinearEquiv` is linear over `Γ(Y, V)`, which is
  -- definitionally `Y.ringCatSheaf.obj.obj (.op V)`.
  exact (f.higherDirectImagePresheafSectionsLinearEquiv M n hV).map_smul rV y

end QuasiCompactQuasiSeparated

section Affine

variable [IsAffine Y] [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)

/-- **Global sections of higher direct images over an affine base.** For a quasi-compact
quasi-separated morphism `f : X ⟶ Y` to an affine scheme `Y` and a quasi-coherent `M`, the global
sections of `Rⁿ f_* M` are canonically identified as an abelian group with `Hⁿ(X, M)`. -/
def higherDirectImageGlobalSectionsAddEquiv :
    Cohomology M n ≃+ Γ((f.higherDirectImage n).obj M, ⊤) :=
  ((cohomologyOnTopLinearEquiv M n).symm.trans
      (f.cohomologyOnTopEquivPreimageTop M n)).toAddEquiv.trans
    (f.higherDirectImageSectionsAddEquiv M n (isAffineOpen_top Y))

/-- `higherDirectImageGlobalSectionsAddEquiv` transports a class in `Hⁿ(X, M)` to `Hⁿ(f⁻¹ ⊤, M)`
and applies `higherDirectImageSectionsAddEquiv` on `⊤`. -/
lemma higherDirectImageGlobalSectionsAddEquiv_apply (x : Cohomology M n) :
    f.higherDirectImageGlobalSectionsAddEquiv M n x =
      f.higherDirectImageSectionsAddEquiv M n (isAffineOpen_top Y)
        (cohomologyOnResLinear M n (le_of_eq f.preimage_top)
          ((cohomologyOnTopLinearEquiv M n).symm x)) :=
  (rfl)

/-- The inverse of `higherDirectImageGlobalSectionsAddEquiv` pulls back a global section of
`Rⁿ f_* M` via `higherDirectImageSectionsAddEquiv` on `⊤` and identifies `Hⁿ(f⁻¹ ⊤, M)` with
`Hⁿ(X, M)`. -/
lemma higherDirectImageGlobalSectionsAddEquiv_symm_apply
    (x : Γ((f.higherDirectImage n).obj M, ⊤)) :
    (f.higherDirectImageGlobalSectionsAddEquiv M n).symm x =
      cohomologyOnTopLinearEquiv M n
        (cohomologyOnResLinear M n (le_of_eq f.preimage_top.symm)
          ((f.higherDirectImageSectionsAddEquiv M n (isAffineOpen_top Y)).symm x)) :=
  (rfl)

/-- `higherDirectImageGlobalSectionsAddEquiv` respects the action of global functions on `Y`:
pulling back `r : Γ(Y, ⊤)` along `f` corresponds to scalar multiplication by `r` on
`Γ(Rⁿ f_* M, ⊤)`. -/
lemma higherDirectImageGlobalSectionsAddEquiv_smul (r : Γ(Y, ⊤)) (x : Cohomology M n) :
    f.higherDirectImageGlobalSectionsAddEquiv M n (f.appTop r • x) =
      r • f.higherDirectImageGlobalSectionsAddEquiv M n x := by
  have htop : (Y.presheaf.map (⊤ : Y.Opens).leTop.op r : Γ(Y, ⊤)) = r := by
    simp [TopologicalSpace.Opens.leTop]
  rw [higherDirectImageGlobalSectionsAddEquiv_apply, higherDirectImageGlobalSectionsAddEquiv_apply]
  have h1 := (cohomologyOnTopLinearEquiv M n).symm.map_smul (f.appTop r) x
  have h2 := (cohomologyOnResLinear M n (le_of_eq f.preimage_top)).map_smul (f.appTop r)
    ((cohomologyOnTopLinearEquiv M n).symm x)
  refine (congrArg (f.higherDirectImageSectionsAddEquiv M n (isAffineOpen_top Y))
    ((congrArg (cohomologyOnResLinear M n (le_of_eq f.preimage_top)) h1).trans h2)).trans ?_
  simpa only [htop] using f.higherDirectImageSectionsAddEquiv_smul M n (isAffineOpen_top Y) r _

end Affine

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

section OverSpec

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  [QuasiCompact (X ↘ Spec (.of R))] [QuasiSeparated (X ↘ Spec (.of R))]
  (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)

/-- **Linear identification over `Spec R`.** For a quasi-compact quasi-separated scheme `X` over
`Spec R` and a quasi-coherent `𝒪_X`-module `M`, the `n`-th cohomology `Hⁿ(X, M)` is `R`-linearly
equivalent to the global sections `moduleSpecΓFunctor.obj (Rⁿ (X ↘ Spec R)_* M)`. -/
def higherDirectImageBaseLinearEquiv :
    Cohomology M n ≃ₗ[R]
      moduleSpecΓFunctor.obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M) where
  __ := (X ↘ Spec (.of R)).higherDirectImageGlobalSectionsAddEquiv M n
  map_smul' r x := by
    -- Both sides have the underlying additive map `higherDirectImageGlobalSectionsAddEquiv`,
    -- with `r : R` acting on the left via `baseRingToGlobalSections` and on the right via
    -- `ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom`.
    change (X ↘ Spec (.of R)).higherDirectImageGlobalSectionsAddEquiv M n
        (baseRingToGlobalSections R X r • x) =
      ((Scheme.ΓSpecIso (.of R)).inv r) •
        (X ↘ Spec (.of R)).higherDirectImageGlobalSectionsAddEquiv M n x
    rw [baseRingToGlobalSections_apply]
    exact (X ↘ Spec (.of R)).higherDirectImageGlobalSectionsAddEquiv_smul M n
      ((Scheme.ΓSpecIso (.of R)).inv r) x

/-- The forward map of `higherDirectImageBaseLinearEquiv` is
`higherDirectImageGlobalSectionsAddEquiv`. -/
@[simp]
lemma higherDirectImageBaseLinearEquiv_apply (x : Cohomology M n) :
    higherDirectImageBaseLinearEquiv R M n x =
      (X ↘ Spec (.of R)).higherDirectImageGlobalSectionsAddEquiv M n x :=
  (rfl)

/-- The inverse map of `higherDirectImageBaseLinearEquiv` is the inverse of
`higherDirectImageGlobalSectionsAddEquiv`. -/
@[simp]
lemma higherDirectImageBaseLinearEquiv_symm_apply
    (x : moduleSpecΓFunctor.obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M)) :
    (higherDirectImageBaseLinearEquiv R M n).symm x =
      ((X ↘ Spec (.of R)).higherDirectImageGlobalSectionsAddEquiv M n).symm x :=
  (rfl)

/-- **Higher direct images over `Spec R` are associated to cohomology** (Hartshorne, Proposition
III.8.5; Stacks, Tag 01XK). For a quasi-compact quasi-separated scheme `X` over `Spec R` and a
quasi-coherent `M`, the quasi-coherent sheaf `Rⁿ (X ↘ Spec R)_* M` is canonically isomorphic to
`tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n))`. -/
def tildeCohomologyIsoHigherDirectImage :
    tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n)) ≅
      ((X ↘ Spec (.of R)).higherDirectImage n).obj M :=
  (tilde.functor (.of R)).mapIso
      (higherDirectImageBaseLinearEquiv R M n).toModuleIso ≪≫
    @asIso _ _ _ _ (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of R) _)

/-- The forward map of `tildeCohomologyIsoHigherDirectImage` is `tilde` of
`higherDirectImageBaseLinearEquiv` followed by the counit `fromTildeΓ`. -/
lemma tildeCohomologyIsoHigherDirectImage_hom :
    (tildeCohomologyIsoHigherDirectImage R M n).hom =
      (tilde.functor (.of R)).map (higherDirectImageBaseLinearEquiv R M n).toModuleIso.hom ≫
        (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ :=
  (rfl)

/-- For a quasi-compact quasi-separated scheme `X` over `Spec R` and a quasi-coherent `M`,
`Rⁿ (X ↘ Spec R)_* M` is of finite type if and only if `Hⁿ(X, M)` is a finitely generated
`R`-module. No Noetherian hypothesis on `R` is needed. -/
theorem isFiniteType_higherDirectImage_iff :
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFiniteType ↔
      Module.Finite R (Cohomology M n) := by
  let e := tildeCohomologyIsoHigherDirectImage R M n
  have h : (tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n))).IsFiniteType ↔
      (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFiniteType :=
    ⟨fun _ ↦ isFiniteType_of_epi e.hom, fun _ ↦ isFiniteType_of_epi e.inv⟩
  exact h.symm.trans
    (ModuleCat.isFiniteType_tilde_iff (R := .of R)
      (ModuleCat.of (CommRingCat.of R) (Cohomology M n)))

/-- For a quasi-compact quasi-separated scheme `X` over `Spec R` and a quasi-coherent `M`,
`Rⁿ (X ↘ Spec R)_* M` is finitely presented if and only if `Hⁿ(X, M)` is a finitely presented
`R`-module. No Noetherian hypothesis on `R` is needed. -/
theorem isFinitePresentation_higherDirectImage_iff :
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFinitePresentation ↔
      Module.FinitePresentation R (Cohomology M n) := by
  have h : (tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n))).IsFinitePresentation ↔
      (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec (.of R)).ringCatSheaf).prop_iff_of_iso
      (tildeCohomologyIsoHigherDirectImage R M n)
  exact h.symm.trans
    (ModuleCat.isFinitePresentation_tilde_iff (R := .of R)
      (ModuleCat.of (CommRingCat.of R) (Cohomology M n)))

/-- For a quasi-compact quasi-separated scheme `X` over `Spec R` of a Noetherian ring `R` and a
quasi-coherent `M`, `Rⁿ (X ↘ Spec R)_* M` is finitely presented if and only if `Hⁿ(X, M)` is a
finitely generated `R`-module. -/
theorem isFinitePresentation_higherDirectImage_iff_finite [IsNoetherianRing R] :
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFinitePresentation ↔
      Module.Finite R (Cohomology M n) :=
  (isFinitePresentation_higherDirectImage_iff R M n).trans
    (Module.finitePresentation_iff_finite R (Cohomology M n))

end OverSpec

end AlgebraicGeometry.Scheme.Modules
