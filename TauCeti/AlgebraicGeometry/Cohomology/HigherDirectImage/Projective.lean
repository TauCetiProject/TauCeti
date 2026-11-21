/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Serre
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Ample
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality

/-!
# Coherent higher direct images for projective schemes

This file connects sheaf cohomology with higher direct images over affine bases and deduces the
coherence and asymptotic vanishing of higher direct images for projective schemes over Noetherian
affine bases.

## Main results

* `AlgebraicGeometry.Scheme.Hom.higherDirectImageTopAddEquiv` and
  `AlgebraicGeometry.Scheme.Hom.higherDirectImageTopAddEquiv_smul`: for a quasi-compact
  quasi-separated morphism `f : X ⟶ Y` to an affine scheme and a quasi-coherent `𝒪_X`-module `M`,
  the global sections of `R^q f_* M` are identified with `H^q(X, M)`, compatibly with pullback of
  global functions on `Y`.
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageTopBaseLinearEquiv`: for a morphism `f : X ⟶ Y`
  over `Spec R` to an affine scheme `Y`, this identification is an `R`-linear equivalence
  `H^q(X, M) ≃ₗ[R] Γ(R^q f_* M, ⊤)`.
* `AlgebraicGeometry.Scheme.Hom.isFiniteType_higherDirectImage_of_finite_cohomology` and
  `AlgebraicGeometry.Scheme.Hom.isFinitePresentation_higherDirectImage_of_finite_cohomology`:
  finiteness of `H^q(X, M)` over `R` implies that `R^q f_* M` is of finite type (and finitely
  presented when `Y` is locally Noetherian).
* `AlgebraicGeometry.Scheme.Hom.isZero_higherDirectImage_of_subsingleton_cohomology`: if
  `H^q(X, M)` vanishes over an affine base, then `R^q f_* M` is zero.
* `AlgebraicGeometry.Scheme.IsProjectiveOver.finite_cohomology`: **Serre's finiteness theorem**
  for any scheme `X` projective over a Noetherian ring `R`.
* `AlgebraicGeometry.Scheme.IsProjectiveOver.isFinitePresentation_higherDirectImage`: **coherence
  of higher direct images** for any scheme `X` projective over a Noetherian ring `R`.
* `AlgebraicGeometry.Scheme.Hom.exists_isZero_higherDirectImage_tensor_pullback_twistingSheaf`:
  asymptotic vanishing of `R^q (i ≫ projToSpec R M)_* (F ⊗ i^* 𝒪(m))` for closed immersions
  `i : X ⟶ Proj (Sym_R M)` over a Noetherian ring `R`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2 and
  Proposition III.8.5.
* [The Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT).
-/

public section

open CategoryTheory Limits Opposite MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry
  TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

section AffineBase

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- On an affine scheme, a quasi-coherent module with subsingleton global sections is zero. -/
private theorem isZero_of_subsingleton_top [IsAffine Y] (N : Y.Modules) [N.IsQuasicoherent]
    [hsub : Subsingleton Γ(N, ⊤)] : IsZero N := by
  have : Subsingleton ((sectionsFunctor ⊤).obj N) := hsub
  have : IsIso (0 : N ⟶ N) := isIso_of_bijective_sectionsFunctor_map_top (0 : N ⟶ N)
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : N ⟶ N), zero_comp]

/-- The cohomology of `f⁻¹ ⊤` is identified with the cohomology of `⊤` compatibly with global
functions on `X`. -/
private lemma eqToIso_cohomologyOn_inv_smul (M : X.Modules) (q : ℕ) {U : X.Opens} (hU : U = ⊤)
    (s : Γ(X, ⊤)) (c : cohomologyOn M q ⊤) :
    (eqToIso (congrArg (cohomologyOn M q) hU)).inv (s • c) =
      s • (eqToIso (congrArg (cohomologyOn M q) hU)).inv c := by
  subst hU
  rfl

/-- For a quasi-compact quasi-separated morphism `f : X ⟶ Y` to an affine scheme and a
quasi-coherent `𝒪_X`-module `M`, the global sections of the higher direct image `R^q f_* M` are
additively equivalent to the cohomology `H^q(X, M)`. -/
def higherDirectImageTopAddEquiv [IsAffine Y] [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Cohomology M q ≃+ Γ((f.higherDirectImage q).obj M, ⊤) :=
  (cohomologyOnTopIso M q).symm.addCommGroupIsoToAddEquiv.trans <|
    ((eqToIso (congrArg (cohomologyOn M q) f.preimage_top)).symm.addCommGroupIsoToAddEquiv).trans <|
      f.higherDirectImageBasicOpenSectionsAddEquiv M q ⟨1, Y.basicOpen_one⟩

/-- The identification `H^q(X, M) ≃+ Γ(R^q f_* M, ⊤)` carries multiplication by the pullback
`f^* r` of a global function `r` on `Y` to multiplication by `r`. -/
lemma higherDirectImageTopAddEquiv_smul [IsAffine Y] [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) (r : Γ(Y, ⊤)) (x : Cohomology M q) :
    f.higherDirectImageTopAddEquiv M q (f.appTop r • x) =
      r • f.higherDirectImageTopAddEquiv M q x := by
  let c : cohomologyOn M q ⊤ := (cohomologyOnTopIso M q).inv x
  have hc : (cohomologyOnTopIso M q).inv (f.appTop r • x) = f.appTop r • c := by
    apply (cohomologyOnTopIso M q).addCommGroupIsoToAddEquiv.injective
    change (cohomologyOnTopIso M q).hom ((cohomologyOnTopIso M q).inv (f.appTop r • x)) =
      (cohomologyOnTopIso M q).hom (f.appTop r • c)
    rw [Iso.inv_hom_id_apply, ← cohomologyOnTopLinearEquiv_apply,
      (cohomologyOnTopLinearEquiv M q).map_smul, cohomologyOnTopLinearEquiv_apply,
      Iso.inv_hom_id_apply]
  let c' : cohomologyOn M q (f ⁻¹ᵁ ⊤) :=
    (eqToIso (congrArg (cohomologyOn M q) f.preimage_top)).inv c
  have hc' : (eqToIso (congrArg (cohomologyOn M q) f.preimage_top)).inv (f.appTop r • c) =
      f.appTop r • c' :=
    eqToIso_cohomologyOn_inv_smul M q f.preimage_top (f.appTop r) c
  let e := f.higherDirectImagePresheafToPresheafIso M q
  let y : ((f.higherDirectImagePresheaf q).obj M).obj (.op ⊤) := e.inv.app (.op ⊤) c'
  have hy : e.hom.app (.op ⊤) y = c' := Iso.inv_hom_id_apply (e.app (.op ⊤)) c'
  let r' : Y.ringCatSheaf.obj.obj (.op ⊤) := Y.presheaf.map (⊤ : Y.Opens).leTop.op r
  have hsmul : f.appTop r • c' = e.hom.app (.op ⊤) (r' • y) := by
    rw [← hy, ← f.higherDirectImagePresheafToPresheafIso_hom_app_smul M q r ⊤ y]
  change f.higherDirectImageBasicOpenSectionsAddEquiv M q ⟨1, Y.basicOpen_one⟩
      ((eqToIso (congrArg (cohomologyOn M q) f.preimage_top)).inv
        ((cohomologyOnTopIso M q).inv (f.appTop r • x))) =
    r • f.higherDirectImageBasicOpenSectionsAddEquiv M q ⟨1, Y.basicOpen_one⟩ c'
  rw [hc, hc', hsmul, ← hy,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app]
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
    ((f.higherDirectImagePresheaf q).obj M)).app (.op ⊤)
  let i := ((f.higherDirectImagePresheafSheafificationIso q).app M).hom.val.app (.op ⊤)
  have hlin : i (η (r' • y)) = r' • i (η y) :=
    (congrArg i (η.hom.map_smul r' y)).trans (i.hom.map_smul r' (η y))
  have hr' : Y.presheaf.map (⊤ : Y.Opens).leTop.op r = r :=
    ConcreteCategory.congr_hom (Y.presheaf.map_id (.op ⊤)) r
  exact hlin.trans (congrArg (· • i (η y)) hr')

/-- For a quasi-compact quasi-separated morphism `f : X ⟶ Y` to an affine scheme and a
quasi-coherent `𝒪_X`-module `M`, if `H^q(X, M)` is subsingleton then `R^q f_* M` is zero. -/
theorem isZero_higherDirectImage_of_subsingleton_cohomology [IsAffine Y]
    [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
    [Subsingleton (Cohomology M q)] :
    IsZero ((f.higherDirectImage q).obj M) := by
  have : Subsingleton Γ((f.higherDirectImage q).obj M, ⊤) :=
    (f.higherDirectImageTopAddEquiv M q).symm.injective.subsingleton
  exact isZero_of_subsingleton_top ((f.higherDirectImage q).obj M)

section BaseRing

variable (R : Type u) [CommRing R] [IsAffine Y]
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))]

/-- For a quasi-compact quasi-separated morphism `f : X ⟶ Y` over `Spec R` to an affine scheme
`Y`, the cohomology `H^q(X, M)` of a quasi-coherent `𝒪_X`-module `M` is `R`-linearly equivalent to
the global sections of `R^q f_* M`. -/
def higherDirectImageTopBaseLinearEquiv [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Cohomology M q ≃ₗ[R] Γ((f.higherDirectImage q).obj M, ⊤) where
  __ := f.higherDirectImageTopAddEquiv M q
  map_smul' r x := by
    have hr : f.appTop (baseRingToGlobalSections R Y r) = baseRingToGlobalSections R X r := by
      rw [baseRingToGlobalSections_apply, baseRingToGlobalSections_apply,
        ← CommRingCat.comp_apply, ← comp_appTop, HomIsOver.comp_over]
    rw [RingHom.id_apply]
    change f.higherDirectImageTopAddEquiv M q (r • x) =
      r • f.higherDirectImageTopAddEquiv M q x
    rw [base_smul_cohomology, base_smul_globalSections, ← hr,
      f.higherDirectImageTopAddEquiv_smul]

/-- The forward map of `higherDirectImageTopBaseLinearEquiv` is `higherDirectImageTopAddEquiv`. -/
@[simp]
lemma higherDirectImageTopBaseLinearEquiv_apply [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) (x : Cohomology M q) :
    f.higherDirectImageTopBaseLinearEquiv R M q x = f.higherDirectImageTopAddEquiv M q x :=
  (rfl)

/-- For a quasi-compact quasi-separated morphism `f : X ⟶ Y` over `Spec R` to an affine scheme
`Y`, if `H^q(X, M)` is a finitely generated `R`-module for a quasi-coherent `𝒪_X`-module `M`, then
`R^q f_* M` is of finite type. -/
theorem isFiniteType_higherDirectImage_of_finite_cohomology [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) [Module.Finite R (Cohomology M q)] :
    ((f.higherDirectImage q).obj M).IsFiniteType := by
  let N := (f.higherDirectImage q).obj M
  have : Module.Finite R Γ(N, ⊤) :=
    Module.Finite.equiv (f.higherDirectImageTopBaseLinearEquiv R M q)
  let : Algebra R Γ(Y, ⊤) := (baseRingToGlobalSections R Y).toAlgebra
  have : IsScalarTower R Γ(Y, ⊤) Γ(N, ⊤) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Finite Γ(Y, ⊤) Γ(N, ⊤) := Module.Finite.of_restrictScalars_finite R _ _
  obtain ⟨I, _, π, hπ⟩ := exists_epi_free_of_finite N
  exact @isFiniteType_of_epi _ _ _ π hπ _

/-- For a quasi-compact quasi-separated morphism `f : X ⟶ Y` over `Spec R` to a locally Noetherian
affine scheme `Y`, if `H^q(X, M)` is a finitely generated `R`-module for a quasi-coherent
`𝒪_X`-module `M`, then `R^q f_* M` is finitely presented. -/
theorem isFinitePresentation_higherDirectImage_of_finite_cohomology [IsLocallyNoetherian Y]
    [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
    [Module.Finite R (Cohomology M q)] :
    ((f.higherDirectImage q).obj M).IsFinitePresentation := by
  let N := (f.higherDirectImage q).obj M
  have : N.IsQuasicoherent := isQuasicoherent_higherDirectImage f M q
  have : N.IsFiniteType := f.isFiniteType_higherDirectImage_of_finite_cohomology R M q
  exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
    ((pushforwardId Y).app N) (isFinitePresentation_pushforward_of_isFinite (𝟙 Y) N)

end BaseRing

end AffineBase

/-- **Higher direct image vanishing for twists on projective schemes.** Let `R` be a Noetherian
ring, `M` a finitely generated `R`-module, and `i : X ⟶ Proj (Sym_R M)` a closed immersion. For
every quasi-coherent `𝒪_X`-module `F` of finite type, there exists `m₀ : ℤ` such that
`R^q (i ≫ projToSpec R M)_* (F ⊗ i^* 𝒪(m)) = 0` for all `m ≥ m₀` and all `q > 0`. -/
theorem exists_isZero_higherDirectImage_tensor_pullback_twistingSheaf {R M : Type u} [CommRing R]
    [IsNoetherianRing R] [AddCommMonoid M] [Module R M] [Module.Finite R M] {X : Scheme.{u}}
    (i : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M)) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      IsZero (((i ≫ TauCeti.SymmetricAlgebra.projToSpec R M).higherDirectImage q).obj
        (F ⊗ (Scheme.Modules.pullback i).obj
          (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m))) := by
  obtain ⟨m₀, hm₀⟩ := i.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf F
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  let Om := Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m
  have : Om.IsFinitePresentation :=
    TauCeti.SheafOfModules.IsInvertible.isFinitePresentation (M := Om)
  have : Om.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation Om
  have : ((Scheme.Modules.pullback i).obj Om).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback i Om
  have : Subsingleton (Cohomology (F ⊗ (Scheme.Modules.pullback i).obj Om) q) := hm₀ m hm q hq
  exact isZero_higherDirectImage_of_subsingleton_cohomology
    (i ≫ TauCeti.SymmetricAlgebra.projToSpec R M) (F ⊗ (Scheme.Modules.pullback i).obj Om) q

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.IsProjectiveOver

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]

/-- **Serre's finiteness theorem for projective schemes.** For a scheme `X` projective over a
Noetherian ring `R`, a quasi-coherent `𝒪_X`-module `F` of finite type, and every `q : ℕ`, the
cohomology `H^q(X, F)` is a finitely generated `R`-module. -/
theorem finite_cohomology [IsNoetherianRing R] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨M, _, _, _, i, hi, hiR⟩ := exists_isClosedImmersion (R := R) (X := X)
  have : IsLocallyNoetherian (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M)) :=
    LocallyOfFiniteType.isLocallyNoetherian (TauCeti.SymmetricAlgebra.projToSpec R M)
  have : ((pushforward i).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite i F
  have : ((pushforward i).obj F).IsQuasicoherent := isQuasicoherent_of_isFinitePresentation _
  have : ((pushforward i).obj F).IsFiniteType := isFiniteType_of_isFinitePresentation _
  have hfin : Module.Finite R (Cohomology ((pushforward i).obj F) q) :=
    TauCeti.SymmetricAlgebra.finite_cohomology_proj ((pushforward i).obj F) q
  exact (i.moduleFinite_cohomology_pushforward_iff R F q).mp hfin

/-- **Coherence of higher direct images for projective schemes over Noetherian affine bases.**
For a scheme `X` projective over a Noetherian ring `R`, a quasi-coherent `𝒪_X`-module `F` of
finite type, and every `q : ℕ`, the higher direct image `R^q (X ↘ Spec R)_* F` is finitely
presented. -/
theorem isFinitePresentation_higherDirectImage [IsNoetherianRing R] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    (((X ↘ Spec (.of R)).higherDirectImage q).obj F).IsFinitePresentation := by
  have : Module.Finite R (Cohomology F q) := finite_cohomology R F q
  let : (Spec (.of R)).Over (Spec (.of R)) := ⟨𝟙 _⟩
  have : (X ↘ Spec (.of R)).IsOver (Spec (.of R)) := ⟨Category.comp_id _⟩
  exact Scheme.Hom.isFinitePresentation_higherDirectImage_of_finite_cohomology
    (X ↘ Spec (.of R)) R F q

end AlgebraicGeometry.Scheme.IsProjectiveOver

end
