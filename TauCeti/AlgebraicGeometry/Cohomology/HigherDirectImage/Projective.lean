/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Coherent
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic

/-!
# Higher direct images over an affine base and along projective morphisms

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism to an affine scheme `Y`, and `M` a
quasi-coherent `𝒪_X`-module. By
`AlgebraicGeometry.Scheme.Hom.higherDirectImageBasicOpenSectionsAddEquiv`, the sections of the
higher direct image `Rⁿ f_* M` over a basic open `V = D(g)` of `Y` are additively identified with
`Hⁿ(f⁻¹ V, M)`. This file shows that the identification respects scalar multiplication by global
functions on `Y` (`AlgebraicGeometry.Scheme.Hom.higherDirectImageBasicOpenSectionsAddEquiv_smul`),
yielding:

1. Over any affine scheme `Y` with `f : X ⟶ Y` a morphism over `Spec R`, an `R`-linear equivalence
   `Hⁿ(X, M) ≃ₗ[R] Γ(Rⁿ f_* M, ⊤)`
   (`AlgebraicGeometry.Scheme.Hom.cohomologyHigherDirectImageGlobalSectionsLinearEquiv`).
2. When `Y = Spec R` and `f = (X ↘ Spec R)`, the `R`-linear comparison
   `Hⁿ(X, M) ≃ₗ[R] Γ(Spec R, Rⁿ f_* M)`
   (`AlgebraicGeometry.Scheme.cohomologyHigherDirectImageSpecΓLinearEquiv`, Stacks Tag 01XK) and the
   canonical `𝒪_{Spec R}`-module isomorphism `(Hⁿ(X, M))~ ≅ Rⁿ f_* M`
   (`AlgebraicGeometry.Scheme.tildeCohomologyIsoHigherDirectImage`), characterizing finite type and
   finite presentation of `Rⁿ f_* M` in terms of `Module.Finite R (Cohomology M n)` and
   `Module.FinitePresentation R (Cohomology M n)` without Noetherian hypotheses.
3. **Coherence of higher direct images for projective schemes over a Noetherian ring**
   (`AlgebraicGeometry.Scheme.IsProjectiveOver.isFinitePresentation_higherDirectImage`, Stacks Tag
   02O5): if `R` is Noetherian, `X` is projective over `R`, and `M` is a quasi-coherent `𝒪_X`-module
   of finite type, then `Rⁿ (X ↘ Spec R)_* M` is finitely presented (hence coherent) for every
   `n : ℕ`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.5 and Theorem
  III.8.8(b).
* [The Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK) and
  [Tag 02O5](https://stacks.math.columbia.edu/tag/02O5).
-/

public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section Affine

variable [IsAffine Y] [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent]
  (n : ℕ)

/-- Over an affine base `Y`, the additive identification of `Hⁿ(f⁻¹ V, M)` with the sections of
`Rⁿ f_* M` over a basic open `V` intertwines the action of a global function `r ∈ Γ(Y, ⊤)` via
`f^* r` on cohomology with multiplication by `r|_V` on sections. -/
theorem higherDirectImageBasicOpenSectionsAddEquiv_smul {V : Y.Opens}
    (hV : ∃ g : Γ(Y, ⊤), Y.basicOpen g = V) (r : Γ(Y, ⊤)) (x : cohomologyOn M n (f ⁻¹ᵁ V)) :
    f.higherDirectImageBasicOpenSectionsAddEquiv M n hV (f.appTop r • x) =
      Y.presheaf.map V.leTop.op r • f.higherDirectImageBasicOpenSectionsAddEquiv M n hV x := by
  let e := f.higherDirectImagePresheafToPresheafIso M n
  let y : ((f.higherDirectImagePresheaf n).obj M).obj (.op V) := (e.app (.op V)).inv x
  have hy : e.hom.app (.op V) y = x := Iso.inv_hom_id_apply (e.app (.op V)) x
  let rV : Y.ringCatSheaf.obj.obj (.op V) := Y.presheaf.map V.leTop.op r
  have hsmul : e.hom.app (.op V) (rV • y) = f.appTop r • x :=
    (f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r V y).trans
      (congrArg (f.appTop r • ·) hy)
  rw [← hsmul, ← hy,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app]
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
    ((f.higherDirectImagePresheaf n).obj M)).app (.op V)
  let φ := ((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app (.op V)
  exact (congrArg φ (η.hom.map_smul rV y)).trans (φ.hom.map_smul rV (η y))

/-- At `V = ⊤ = D(1)`, the global-sections identification `Hⁿ(f⁻¹ ⊤, M) ≃+ Γ(Rⁿ f_* M, ⊤)` carries
the action of `f^* r` on cohomology to multiplication by `r` on global sections. -/
theorem higherDirectImageBasicOpenSectionsAddEquiv_top_smul (r : Γ(Y, ⊤))
    (x : cohomologyOn M n (f ⁻¹ᵁ ⊤)) :
    f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩ (f.appTop r • x) =
      r • f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩ x := by
  refine (f.higherDirectImageBasicOpenSectionsAddEquiv_smul M n ⟨1, Y.basicOpen_one⟩ r x).trans ?_
  -- the inclusion of `⊤` into itself is the identity
  rw [show (⊤ : Y.Opens).leTop = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- For a quasi-compact quasi-separated morphism `f : X ⟶ Y` over `Spec R` with affine target `Y`
and a quasi-coherent `𝒪_X`-module `M`, the cohomology `Hⁿ(X, M)` is `R`-linearly equivalent to the
global sections `Γ(Rⁿ f_* M, ⊤)`. -/
def cohomologyHigherDirectImageGlobalSectionsLinearEquiv (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))] :
    Cohomology M n ≃ₗ[R] Γ((f.higherDirectImage n).obj M, ⊤) :=
  let e := f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩
  (cohomologyOnTopBaseLinearEquiv M R n).symm.trans
    (show cohomologyOn M n (f ⁻¹ᵁ ⊤) ≃ₗ[R] Γ((f.higherDirectImage n).obj M, ⊤) from
      { toFun := fun x ↦ e x
        invFun := fun y ↦ e.symm y
        left_inv := e.left_inv
        right_inv := e.right_inv
        map_add' := e.map_add
        map_smul' := fun r x ↦ by
          have hr : f.appTop (baseRingToGlobalSections R Y r) = baseRingToGlobalSections R X r := by
            rw [baseRingToGlobalSections_apply, baseRingToGlobalSections_apply,
              ← CommRingCat.comp_apply, ← comp_appTop, HomIsOver.comp_over]
          rw [RingHom.id_apply, base_smul_cohomologyOn, ← hr,
            f.higherDirectImageBasicOpenSectionsAddEquiv_top_smul, base_smul_globalSections] })

/-- Evaluation of `cohomologyHigherDirectImageGlobalSectionsLinearEquiv` via
`higherDirectImageBasicOpenSectionsAddEquiv` on `D(1) = ⊤`. -/
@[simp]
theorem cohomologyHigherDirectImageGlobalSectionsLinearEquiv_apply (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))]
    (x : Cohomology M n) :
    f.cohomologyHigherDirectImageGlobalSectionsLinearEquiv M n R x =
      f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩
        ((cohomologyOnTopBaseLinearEquiv M R n).symm x) :=
  (rfl)

end Affine

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

private lemma moduleSpecΓ_smul_aux (A : CommRingCat.{u}) (N : (Spec A).Modules) (r : A)
    (x : Γ(N, ⊤)) :
    @HSMul.hSMul A ((moduleSpecΓFunctor (R := A)).obj N)
        ((moduleSpecΓFunctor (R := A)).obj N) instHSMul r x =
      (Scheme.ΓSpecIso A).inv r • x := by
  -- `moduleSpecΓFunctor.obj N` and `Γ(N, ⊤)` share `Tilde`'s `A`-module structure.
  change r • x = (Scheme.ΓSpecIso A).inv r • x
  rw [Scheme.Modules.smul_Spec_def, show (⊤ : (Spec A).Opens).leTop = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

section SpecBase

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  [QuasiCompact (X ↘ Spec (.of R))] [QuasiSeparated (X ↘ Spec (.of R))]
  (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)

/-- **Global sections of higher direct images over `Spec R`** (Stacks Tag 01XK): for a quasi-compact
quasi-separated scheme `X` over `Spec R` and a quasi-coherent `𝒪_X`-module `M`, the cohomology
`Hⁿ(X, M)` is canonically `R`-linearly equivalent to the global sections
`Γ(Spec R, Rⁿ (X ↘ Spec R)_* M)` viewed via `moduleSpecΓFunctor`. -/
def cohomologyHigherDirectImageSpecΓLinearEquiv :
    Cohomology M n ≃ₗ[R]
      (moduleSpecΓFunctor (R := .of R)).obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M) :=
  let e := (X ↘ Spec (.of R)).higherDirectImageBasicOpenSectionsAddEquiv M n
    ⟨1, (Spec (.of R)).basicOpen_one⟩
  (cohomologyOnTopBaseLinearEquiv M R n).symm.trans
    (show cohomologyOn M n ((X ↘ Spec (.of R)) ⁻¹ᵁ ⊤) ≃ₗ[R]
        (moduleSpecΓFunctor (R := .of R)).obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M) from
      { toFun := fun x ↦ e x
        invFun := fun y ↦ e.symm y
        left_inv := e.left_inv
        right_inv := e.right_inv
        map_add' := e.map_add
        map_smul' := fun r x ↦ by
          rw [RingHom.id_apply, base_smul_cohomologyOn, baseRingToGlobalSections_apply]
          exact ((X ↘ Spec (.of R)).higherDirectImageBasicOpenSectionsAddEquiv_top_smul M n
            ((Scheme.ΓSpecIso (.of R)).inv r) x).trans
            (moduleSpecΓ_smul_aux (.of R)
              (((X ↘ Spec (.of R)).higherDirectImage n).obj M) r (e x)).symm })

/-- Evaluation of `cohomologyHigherDirectImageSpecΓLinearEquiv` via
`higherDirectImageBasicOpenSectionsAddEquiv` on `D(1) = ⊤`. -/
@[simp]
theorem cohomologyHigherDirectImageSpecΓLinearEquiv_apply (x : Cohomology M n) :
    cohomologyHigherDirectImageSpecΓLinearEquiv R M n x =
      (X ↘ Spec (.of R)).higherDirectImageBasicOpenSectionsAddEquiv M n
        ⟨1, (Spec (.of R)).basicOpen_one⟩ ((cohomologyOnTopBaseLinearEquiv M R n).symm x) :=
  (rfl)

/-- For a quasi-compact quasi-separated scheme `X` over `Spec R` and a quasi-coherent `𝒪_X`-module
`M`, the higher direct image `Rⁿ (X ↘ Spec R)_* M` is canonically isomorphic to the quasi-coherent
sheaf `(Hⁿ(X, M))~` associated to the `R`-module `Hⁿ(X, M)`. -/
def tildeCohomologyIsoHigherDirectImage :
    tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n)) ≅
      ((X ↘ Spec (.of R)).higherDirectImage n).obj M :=
  let e : Cohomology M n ≃ₗ[CommRingCat.of R]
      (moduleSpecΓFunctor (R := .of R)).obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M) :=
    cohomologyHigherDirectImageSpecΓLinearEquiv R M n
  (tilde.functor (.of R)).mapIso e.toModuleIso ≪≫
    @asIso _ _ _ _ (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _)

/-- Over `Spec R`, the higher direct image `Rⁿ (X ↘ Spec R)_* M` of a quasi-coherent `𝒪_X`-module
`M` is of finite type if and only if `Hⁿ(X, M)` is a finitely generated `R`-module. -/
@[simp]
theorem isFiniteType_higherDirectImage_spec_iff :
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFiniteType ↔
      Module.Finite R (Cohomology M n) := by
  let e := tildeCohomologyIsoHigherDirectImage R M n
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
theorem isFinitePresentation_higherDirectImage_spec_iff :
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFinitePresentation ↔
      Module.FinitePresentation R (Cohomology M n) :=
  ((SheafOfModules.isFinitePresentation (Spec (.of R)).ringCatSheaf).prop_iff_of_iso
    (tildeCohomologyIsoHigherDirectImage R M n).symm).trans
    (ModuleCat.isFinitePresentation_tilde_iff
      (ModuleCat.of (CommRingCat.of R) (Cohomology M n)))

end SpecBase

/-- **Coherence of higher direct images for projective schemes over a Noetherian ring** (Hartshorne,
Theorem III.8.8(b); Stacks Tag 02O5): if `X` is projective over a Noetherian ring `R` and `M` is a
quasi-coherent `𝒪_X`-module of finite type, then every higher direct image
`Rⁿ (X ↘ Spec R)_* M` is finitely presented (hence coherent). -/
instance IsProjectiveOver.isFinitePresentation_higherDirectImage (R : Type u) [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFinitePresentation :=
  have := IsProjectiveOver.finite_cohomology R M n
  (isFinitePresentation_higherDirectImage_spec_iff R M n).mpr
    (Module.finitePresentation_of_finite R (Cohomology M n))

end AlgebraicGeometry.Scheme

namespace TauCeti.SymmetricAlgebra

/-- Over a Noetherian ring `R`, for any finite `R`-module `P` and any quasi-coherent module `M` of
finite type on `Proj (Sym_R P)`, every higher direct image `Rⁿ (projToSpec R P)_* M` is finitely
presented. -/
instance isFinitePresentation_higherDirectImage_projToSpec (R P : Type u) [CommRing R]
    [IsNoetherianRing R] [AddCommMonoid P] [Module R P] [Module.Finite R P]
    (M : (Proj (homogeneousSubmodule R P)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    (((projToSpec R P).higherDirectImage n).obj M).IsFinitePresentation :=
  Scheme.IsProjectiveOver.isFinitePresentation_higherDirectImage R M n

end TauCeti.SymmetricAlgebra

end
