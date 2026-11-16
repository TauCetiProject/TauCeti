/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Serre
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent

/-!
# Higher direct images on projective schemes over a Noetherian affine base

This file identifies the higher direct images of a quasi-coherent module along a quasi-compact,
quasi-separated morphism to an affine scheme with the associated sheaves of its cohomology
modules, and deduces coherence and positive-twist vanishing of higher direct images for
projective schemes over a Noetherian ring.

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated morphism to an affine scheme `Y` and `M` a
quasi-coherent `𝒪_X`-module. The global sections of `Rⁿ f_* M` are identified with `Hⁿ(X, M)`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageGlobalSectionsAddEquiv`), compatibly with the
action of global functions (`higherDirectImageGlobalSectionsAddEquiv_smul`). When `Y = Spec R`,
this promotes to an `R`-linear equivalence `Hⁿ(X, M) ≃ₗ[R] Γ(Rⁿ f_* M, ⊤)`
(`AlgebraicGeometry.Scheme.Modules.cohomologyEquivHigherDirectImageSections`), and because
`Rⁿ f_* M` is quasi-coherent, the tilde–global-sections counit yields an isomorphism of
`𝒪_{Spec R}`-modules `Hⁿ(X, M)~ ≅ Rⁿ f_* M`
(`AlgebraicGeometry.Scheme.Modules.tildeCohomologyIsoHigherDirectImage`).

Combined with Serre's finiteness and vanishing theorems
(`TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Serre`), this yields:
* coherence (finite presentation) of `R^q f_* F` for every projective scheme `X` over a Noetherian
  ring `R`, every quasi-coherent `𝒪_X`-module `F` of finite type, and every `q : ℕ`;
* vanishing of `R^q f_* (i^* 𝒪(n) ⊗ F)` for every closed subscheme `i : X ⟶ Proj (Sym_R M)` over
  `Spec R` (with `R` Noetherian and `M` finite), every `q > 0`, and all sufficiently large `n : ℤ`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.higherDirectImageGlobalSectionsAddEquiv`: additive equivalence
  `Hⁿ(X, M) ≃+ Γ(Rⁿ f_* M, ⊤)` over an affine base.
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageGlobalSectionsAddEquiv_smul`: scalar compatibility
  for `higherDirectImageGlobalSectionsAddEquiv`.
* `AlgebraicGeometry.Scheme.Modules.cohomologyEquivHigherDirectImageSections`: `R`-linear
  equivalence `Hⁿ(X, M) ≃ₗ[R] moduleSpecΓFunctor.obj (Rⁿ f_* M)` for `X` quasi-compact and
  quasi-separated over `Spec R`.
* `AlgebraicGeometry.Scheme.Modules.tildeCohomologyIsoHigherDirectImage`: isomorphism
  `Hⁿ(X, M)~ ≅ Rⁿ f_* M` of `𝒪_{Spec R}`-modules.
* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_of_isProjectiveOver`:
  higher direct images of quasi-coherent modules of finite type on a projective scheme over a
  Noetherian ring are finitely presented.
* `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_pullback_twistingSheaf_tensor`:
  higher direct images of sufficiently positive twists vanish in positive degrees.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Propositions III.8.5 and III.5.2.
* [The Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK) (higher direct images
  over an affine base) and [Tag 02O5](https://stacks.math.columbia.edu/tag/02O5) (coherence of
  higher direct images).
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restriction along the equality `f ⁻¹ᵁ ⊤ = ⊤` identifies `Hⁿ(X, M)` with `Hⁿ(f⁻¹ ⊤, M)`
linearly over global functions without unfolding `cohomologyOn`. -/
private def cohomologyEquivPreimageTop (M : X.Modules) (n : ℕ) :
    Cohomology M n ≃ₗ[Γ(X, ⊤)] cohomologyOn M n (f ⁻¹ᵁ ⊤) :=
  let res : cohomologyOn M n ⊤ ≃ₗ[Γ(X, ⊤)] cohomologyOn M n (f ⁻¹ᵁ ⊤) :=
    LinearEquiv.ofLinearMap (cohomologyOnResLinear M n (le_of_eq f.preimage_top))
      (cohomologyOnResLinear M n (le_of_eq f.preimage_top.symm))
      (LinearMap.ext fun x ↦ by
        simp only [LinearMap.comp_apply, cohomologyOnResLinear_apply, LinearMap.id_apply,
          cohomologyOnRes_comp_apply, cohomologyOnRes_refl]
        rfl)
      (LinearMap.ext fun x ↦ by
        simp only [LinearMap.comp_apply, cohomologyOnResLinear_apply, LinearMap.id_apply,
          cohomologyOnRes_comp_apply, cohomologyOnRes_refl]
        rfl)
  (cohomologyOnTopLinearEquiv M n).symm.trans res

variable [IsAffine Y] [QuasiCompact f] [QuasiSeparated f]

/-- **Global sections of a higher direct image over an affine base.** For a quasi-compact,
quasi-separated morphism `f : X ⟶ Y` to an affine scheme `Y` and a quasi-coherent `𝒪_X`-module
`M`, the cohomology `Hⁿ(X, M)` is additively equivalent to the global sections of `Rⁿ f_* M`. -/
def higherDirectImageGlobalSectionsAddEquiv (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Cohomology M n ≃+ Γ((f.higherDirectImage n).obj M, ⊤) :=
  (cohomologyEquivPreimageTop f M n).toAddEquiv.trans
    (f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩)

/-- The identification `Hⁿ(X, M) ≃+ Γ(Rⁿ f_* M, ⊤)` carries the action of a pulled-back global
function `f^* r` on cohomology to scalar multiplication by `r` on global sections of `Rⁿ f_* M`. -/
theorem higherDirectImageGlobalSectionsAddEquiv_smul (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (r : Γ(Y, ⊤)) (x : Cohomology M n) :
    f.higherDirectImageGlobalSectionsAddEquiv M n (f.appTop r • x) =
      r • f.higherDirectImageGlobalSectionsAddEquiv M n x := by
  let e := f.higherDirectImagePresheafToPresheafIso M n
  have hbij := ConcreteCategory.bijective_of_isIso (e.hom.app (.op ⊤))
  obtain ⟨y₀, hy₀⟩ := hbij.2 (cohomologyEquivPreimageTop f M n x)
  let y : ((f.higherDirectImagePresheaf n).obj M).obj (.op ⊤) := y₀
  have hy : (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤) y =
      cohomologyEquivPreimageTop f M n x := hy₀
  have htop : (show Y.ringCatSheaf.obj.obj (.op ⊤) from Y.presheaf.map (⊤ : Y.Opens).leTop.op r) =
      (show Y.ringCatSheaf.obj.obj (.op ⊤) from r) := by
    rw [show (⊤ : Y.Opens).leTop = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  have hsmul : cohomologyEquivPreimageTop f M n (f.appTop r • x) =
      (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤)
        ((show Y.ringCatSheaf.obj.obj (.op ⊤) from r) • y) := by
    rw [LinearEquiv.map_smul, ← hy]
    exact ((congrArg (fun s ↦ e.hom.app (.op ⊤) (s • y)) htop).symm.trans
      (f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r ⊤ y)).symm
  -- Apply the basic-open comparison at `⊤ = D(1)` and use linearity of sheafification.
  change f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩
      (cohomologyEquivPreimageTop f M n (f.appTop r • x)) =
    r • f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩
      (cohomologyEquivPreimageTop f M n x)
  rw [hsmul, ← hy,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app]
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
    ((f.higherDirectImagePresheaf n).obj M)).app (.op ⊤)
  let i := ((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app (.op ⊤)
  exact (congrArg i (η.hom.map_smul _ y)).trans (i.hom.map_smul _ (η y))

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

/-- **Cohomology as global sections of the higher direct image over `Spec R`.** For a
quasi-compact, quasi-separated scheme `X` over `Spec R` and a quasi-coherent `𝒪_X`-module `M`,
`Hⁿ(X, M)` is `R`-linearly equivalent to the global sections of `Rⁿ (X ↘ Spec R)_* M`. -/
def cohomologyEquivHigherDirectImageSections (R : Type u) [CommRing R] {X : Scheme.{u}}
    [X.Over (Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [QuasiSeparated (X ↘ Spec (.of R))] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Cohomology M n ≃ₗ[R]
      moduleSpecΓFunctor.obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M) where
  __ := (X ↘ Spec (.of R)).higherDirectImageGlobalSectionsAddEquiv M n
  map_smul' r x := by
    let f := X ↘ Spec (.of R)
    -- On `Cohomology M n`, `r` acts through `baseRingToGlobalSections`; on `moduleSpecΓFunctor`,
    -- `r` acts through `(ΓSpecIso R).inv` followed by restriction along the identity of `⊤`.
    have htop : ((Spec (.of R)).ringCatSheaf.obj.map
        ((initialOpOfTerminal isTerminalTop).to (.op ⊤))).hom = RingHom.id _ := by
      rw [IsInitial.to_self, CategoryTheory.Functor.map_id]
      rfl
    have hrhs :
        (r : R) • (show moduleSpecΓFunctor.obj ((f.higherDirectImage n).obj M) from
          f.higherDirectImageGlobalSectionsAddEquiv M n x) =
        (Scheme.ΓSpecIso (.of R)).inv r • f.higherDirectImageGlobalSectionsAddEquiv M n x :=
      congrArg (fun g : _ →+* _ ↦ g ((Scheme.ΓSpecIso (.of R)).inv.hom r) •
        (show ((f.higherDirectImage n).obj M).val.obj (.op ⊤) from
          f.higherDirectImageGlobalSectionsAddEquiv M n x)) htop
    change f.higherDirectImageGlobalSectionsAddEquiv M n (r • x) =
      r • (show moduleSpecΓFunctor.obj ((f.higherDirectImage n).obj M) from
        f.higherDirectImageGlobalSectionsAddEquiv M n x)
    rw [hrhs, base_smul_cohomology, baseRingToGlobalSections_apply]
    exact f.higherDirectImageGlobalSectionsAddEquiv_smul M n ((Scheme.ΓSpecIso (.of R)).inv r) x

/-- `cohomologyEquivHigherDirectImageSections` agrees on elements with
`higherDirectImageGlobalSectionsAddEquiv`. -/
@[simp]
theorem cohomologyEquivHigherDirectImageSections_apply (R : Type u) [CommRing R] {X : Scheme.{u}}
    [X.Over (Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [QuasiSeparated (X ↘ Spec (.of R))] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Cohomology M n) :
    (cohomologyEquivHigherDirectImageSections R M n x :
        Γ(((X ↘ Spec (.of R)).higherDirectImage n).obj M, ⊤)) =
      (X ↘ Spec (.of R)).higherDirectImageGlobalSectionsAddEquiv M n x := by
  rfl

/-- **Higher direct images over an affine base are associated to cohomology.** For a
quasi-compact, quasi-separated scheme `X` over `Spec R` and a quasi-coherent `𝒪_X`-module `M`,
the higher direct image `Rⁿ (X ↘ Spec R)_* M` is isomorphic as an `𝒪_{Spec R}`-module to the
quasi-coherent sheaf `Hⁿ(X, M)~`. -/
def tildeCohomologyIsoHigherDirectImage (R : Type u) [CommRing R] {X : Scheme.{u}}
    [X.Over (Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [QuasiSeparated (X ↘ Spec (.of R))] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n)) ≅
      ((X ↘ Spec (.of R)).higherDirectImage n).obj M :=
  (tilde.functor (.of R)).mapIso (cohomologyEquivHigherDirectImageSections R M n).toModuleIso ≪≫
    @asIso _ _ _ _ (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ
      (isIso_fromTildeΓ_of_isQuasicoherent _)

/-- **Coherence of projective higher direct images over a Noetherian affine base.** Let `X` be a
projective scheme over a Noetherian commutative ring `R` and `F` a quasi-coherent `𝒪_X`-module of
finite type. Then every higher direct image `R^q (X ↘ Spec R)_* F` is finitely presented. -/
theorem isFinitePresentation_higherDirectImage_of_isProjectiveOver (R : Type u) [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    (((X ↘ Spec (.of R)).higherDirectImage q).obj F).IsFinitePresentation := by
  let M : ModuleCat.{u} (CommRingCat.of R) := ModuleCat.of (CommRingCat.of R) (Cohomology F q)
  have : Module.Finite (CommRingCat.of R) M :=
    finite_cohomology_of_isProjectiveOver R F q
  have : Module.FinitePresentation (CommRingCat.of R) M :=
    Module.finitePresentation_of_finite (CommRingCat.of R) M
  let e : @Iso (SheafOfModules (Spec (.of R)).ringCatSheaf) _ (tilde M)
      (((X ↘ Spec (.of R)).higherDirectImage q).obj F) :=
    let i := tildeCohomologyIsoHigherDirectImage R F q
    { hom := i.hom, inv := i.inv, hom_inv_id := i.hom_inv_id, inv_hom_id := i.inv_hom_id }
  exact (SheafOfModules.isFinitePresentation (Spec (.of R)).ringCatSheaf).prop_of_iso e
    (isFinitePresentation_tilde M)

/-- **Serre vanishing for higher direct images.** Let `R` be a Noetherian commutative ring, `M` a
finite `R`-module, `i : X ⟶ Proj (Sym_R M)` a closed immersion over `Spec R`, and `F` a
quasi-coherent `𝒪_X`-module of finite type. Then there exists `n₀ : ℤ` such that
`R^q (X ↘ Spec R)_* (i^* 𝒪(n) ⊗ F) = 0` for every `n ≥ n₀` and every `q > 0`. -/
theorem exists_isZero_higherDirectImage_pullback_twistingSheaf_tensor
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] {X : Scheme.{u}} [X.Over (Spec (.of R))]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M))
    [IsClosedImmersion i] [i.IsOver (Spec (.of R))] :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ q > 0,
      IsZero (((X ↘ Spec (.of R)).higherDirectImage q).obj
        ((pullback i).obj (Proj.twistingSheaf
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) n) ⊗ F)) := by
  have : X.IsProjectiveOver R :=
    Scheme.IsProjectiveOver.of_isClosedImmersion R i
  obtain ⟨n₀, hn₀⟩ := F.exists_subsingleton_cohomology_pullback_twistingSheaf_tensor i
  refine ⟨n₀, fun n hn q hq ↦ ?_⟩
  let G : X.Modules := (pullback i).obj
    (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) n) ⊗ F
  have : G.IsQuasicoherent := isQuasicoherent_tensorObj X _ F
  have : Subsingleton (Cohomology G q) := hn₀ n hn q hq
  let N : ModuleCat.{u} (CommRingCat.of R) := ModuleCat.of (CommRingCat.of R) (Cohomology G q)
  have hzero : IsZero N := ModuleCat.isZero_of_subsingleton N
  have htilde : IsZero (tilde N) :=
    (IsZero.iff_id_eq_zero _).mpr (by
      change 𝟙 ((tilde.functor (.of R)).obj N) = 0
      rw [← (tilde.functor (.of R)).map_id, hzero.eq_of_src (𝟙 N) 0]
      exact tilde.map_zero)
  exact htilde.of_iso (tildeCohomologyIsoHigherDirectImage R G q).symm

end AlgebraicGeometry.Scheme.Modules

end
