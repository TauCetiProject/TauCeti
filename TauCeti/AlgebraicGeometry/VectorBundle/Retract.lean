/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Retract closure and local characterizations of finite locally free sheaves

A retract `r : Retract M N` of an object in a preadditive category is the kernel of the idempotent
`𝟙 N - r.r ≫ r.i` (via `CategoryTheory.Limits.isSplitMonoEqualizes` and
`CategoryTheory.Preadditive.isLimitKernelForkOfFork`). Since quasi-coherent `𝒪_X`-modules are closed
under ambient kernels (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderKernels`),
every retract of a quasi-coherent `𝒪_X`-module is quasi-coherent.

Combined with the affine dictionary (`TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde_iff`),
retract closure passes to finite locally free sheaves: on an affine open `Spec R`, a retract of a
finite locally free sheaf is quasi-coherent and its module of global sections is a retract of a
finitely generated projective `R`-module, hence again finitely generated and projective. Checking on
an affine open cover extends retract closure to an arbitrary scheme
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_retract`).

This yields the two pointwise local characterizations of finite local freeness on a scheme `X`:
* `isFiniteLocallyFree_iff_forall_exists_iso_free`: `M` is finite locally free if and only if every
  point of `X` has an open neighborhood on which `M` is isomorphic to a finite free sheaf;
* `isFiniteLocallyFree_iff_forall_exists_retract_free`: `M` is finite locally free if and only if
  every point of `X` has an open neighborhood on which `M` is a retract (direct summand) of a
  finite free sheaf, matching Thomason–Trobaugh's Definition 2.2.2.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isStableUnderRetracts_isQuasicoherent` and
  `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_retract`: quasi-coherence is closed under
  retracts;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_isLocallyFree_and_isFiniteType`:
  finite local freeness agrees with being locally free of finite type;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_free`,
  `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pullback`, and
  `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_restrict`: finite free sheaves are finite
  locally free, and pullback and open-immersion restriction preserve finite local freeness;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_retract` and
  `AlgebraicGeometry.Scheme.Modules.isStableUnderRetracts_isFiniteLocallyFree`: finite local
  freeness is closed under retracts;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_exists_iso_free` and
  `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_exists_retract_free`: pointwise
  local characterizations by finite free sheaves and their retracts.

## References

* [The Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* R. W. Thomason and T. Trobaugh, *Higher algebraic K-theory of schemes and of derived categories*,
  Definition 2.2.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

/-- Quasi-coherence of `𝒪_X`-modules is stable under retracts: a retract `M` of `N` is the kernel
of the idempotent endomorphism `𝟙 N - r.r ≫ r.i`, and quasi-coherent sheaves are closed under
ambient kernels. -/
instance isStableUnderRetracts_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsStableUnderRetracts where
  of_retract r hN :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit_kernelFork
      (Preadditive.isLimitKernelForkOfFork (isSplitMonoEqualizes r.i)) hN hN

/-- A retract of a quasi-coherent `𝒪_X`-module is quasi-coherent. -/
theorem isQuasicoherent_of_retract {X : Scheme.{u}} {M N : X.Modules} (r : Retract M N)
    [N.IsQuasicoherent] : M.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_retract r inferInstance

/-- An `𝒪_X`-module is finite locally free (locally free and finitely presented) if and only if it
is locally free and of finite type. -/
theorem isFiniteLocallyFree_iff_isLocallyFree_and_isFiniteType {X : Scheme.{u}} (M : X.Modules) :
    isFiniteLocallyFree X M ↔ M.IsLocallyFree ∧ M.IsFiniteType := by
  constructor
  · rintro ⟨h1, h2⟩
    let F : SheafOfModules X.ringCatSheaf := M
    have : F.IsFinitePresentation := h2
    exact ⟨h1, inferInstanceAs F.IsFiniteType⟩
  · rintro ⟨h1, h2⟩
    exact (SheafOfModules.isFiniteLocallyFree_iff_exists_isLocallyFreeData_isFiniteType
      (R := X.sheaf) M).mpr
        (SheafOfModules.IsLocallyFree.exists_isLocallyFreeData_isFiniteType (R := X.sheaf) M)

/-- The free `𝒪_X`-module on a finite index type is finite locally free. -/
theorem isFiniteLocallyFree_free (X : Scheme.{u}) (I : Type u) [Finite I] :
    isFiniteLocallyFree X (SheafOfModules.free I) :=
  ⟨inferInstance, TauCeti.SheafOfModules.isFinitePresentation_free I⟩

/-- Pulling back a finite locally free `𝒪_X`-module along an arbitrary morphism of schemes produces
a finite locally free sheaf. -/
theorem isFiniteLocallyFree_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    (hM : isFiniteLocallyFree X M) : isFiniteLocallyFree Y ((pullback f).obj M) :=
  have := hM.1
  have := hM.2
  ⟨isLocallyFree_pullback f M, isFinitePresentation_pullback f M⟩

/-- Restricting a finite locally free `𝒪_X`-module along an open immersion produces a finite
locally free sheaf. -/
theorem isFiniteLocallyFree_restrict {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} (hM : isFiniteLocallyFree X M) : isFiniteLocallyFree U (M.restrict j) :=
  (isFiniteLocallyFree U).prop_of_iso ((restrictFunctorIsoPullback j).app M).symm
    (isFiniteLocallyFree_pullback j hM)

/-- On an affine scheme `Spec R`, a retract of a finite locally free sheaf is finite locally
free. -/
private theorem isFiniteLocallyFree_of_retract_spec {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (r : Retract M N) (hN : isFiniteLocallyFree (Spec R) N) :
    isFiniteLocallyFree (Spec R) M := by
  have hNq : N.IsQuasicoherent :=
    let F : SheafOfModules (Spec R).ringCatSheaf := N
    have : F.IsLocallyFree := hN.1
    inferInstanceAs F.IsQuasicoherent
  have hMq : M.IsQuasicoherent := isQuasicoherent_of_retract r
  obtain ⟨_, _⟩ := TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ
    ⟨N, hN⟩
  let rΓ := r.map moduleSpecΓFunctor
  have hcomp : rΓ.r.hom.comp rΓ.i.hom = LinearMap.id := by
    ext x
    exact congrArg (fun φ : moduleSpecΓFunctor.obj M ⟶ _ ↦ φ x) rΓ.retract
  have : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    Module.Finite.of_surjective rΓ.r.hom fun x ↦ ⟨rΓ.i.hom x, by
      simpa using LinearMap.congr_fun hcomp x⟩
  have : Module.Projective R (moduleSpecΓFunctor.obj M) :=
    Module.Projective.of_split rΓ.i.hom rΓ.r.hom hcomp
  have htilde : isFiniteLocallyFree (Spec R) (tilde (moduleSpecΓFunctor.obj M)) :=
    (TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde_iff _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso (fromTildeΓ M) := isIso_fromTildeΓ_of_isQuasicoherent M
  exact (isFiniteLocallyFree (Spec R)).prop_of_iso (asIso (fromTildeΓ M)) htilde

/-- A retract (direct summand) of a finite locally free `𝒪_X`-module is finite locally free. -/
theorem isFiniteLocallyFree_of_retract {X : Scheme.{u}} {M N : X.Modules} (r : Retract M N)
    (hN : isFiniteLocallyFree X N) : isFiniteLocallyFree X M := by
  refine (isFiniteLocallyFree_iff_forall_pullback X.affineCover M).mpr fun i ↦ ?_
  exact isFiniteLocallyFree_of_retract_spec (r.map (pullback (X.affineCover.f i)))
    (isFiniteLocallyFree_pullback (X.affineCover.f i) hN)

/-- Finite local freeness of `𝒪_X`-modules is stable under retracts. -/
instance isStableUnderRetracts_isFiniteLocallyFree (X : Scheme.{u}) :
    (isFiniteLocallyFree X).IsStableUnderRetracts where
  of_retract r hN := isFiniteLocallyFree_of_retract r hN

/-- An `𝒪_X`-module is finite locally free if and only if every point of `X` has an open
neighborhood over which it is isomorphic to a finite free sheaf. -/
theorem isFiniteLocallyFree_iff_forall_exists_iso_free {X : Scheme.{u}} (M : X.Modules) :
    isFiniteLocallyFree X M ↔
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        ∃ I : Type u, Finite I ∧ Nonempty (M.restrict U.ι ≅ SheafOfModules.free I) := by
  constructor
  · intro hM x
    obtain ⟨𝒰, h𝒰⟩ := (isFiniteLocallyFree_iff_exists_openCover M).mp hM
    let i := 𝒰.idx x
    obtain ⟨I, hI, ⟨e⟩⟩ := h𝒰 i
    refine ⟨(𝒰.f i).opensRange, ?_, I, hI, ⟨restrictOpensRangeIsoFree M (𝒰.f i) e⟩⟩
    obtain ⟨y, hy⟩ := 𝒰.covers x
    exact ⟨y, hy⟩
  · intro h
    choose U hxU I hI he using h
    refine (isFiniteLocallyFree_iff_forall_pullback
      (X.openCoverOfIsOpenCover U
        (top_unique fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩)) M).mpr fun x ↦ ?_
    have := hI x
    exact (isFiniteLocallyFree (U x).toScheme).prop_of_iso
      (((restrictFunctorIsoPullback (U x).ι).app M).symm ≪≫ (he x).some).symm
      (isFiniteLocallyFree_free (U x).toScheme (I x))

/-- **Thomason–Trobaugh local summand characterization** (TT 2.2.2): an `𝒪_X`-module is finite
locally free if and only if every point of `X` has an open neighborhood over which it is a retract
(direct summand) of a finite free sheaf. -/
theorem isFiniteLocallyFree_iff_forall_exists_retract_free {X : Scheme.{u}} (M : X.Modules) :
    isFiniteLocallyFree X M ↔
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        ∃ I : Type u, Finite I ∧ Nonempty (Retract (M.restrict U.ι) (SheafOfModules.free I)) := by
  constructor
  · intro hM x
    obtain ⟨U, hxU, I, hI, ⟨e⟩⟩ := (isFiniteLocallyFree_iff_forall_exists_iso_free M).mp hM x
    exact ⟨U, hxU, I, hI, ⟨Retract.ofIso e⟩⟩
  · intro h
    choose U hxU I hI hr using h
    refine (isFiniteLocallyFree_iff_forall_pullback
      (X.openCoverOfIsOpenCover U
        (top_unique fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩)) M).mpr fun x ↦ ?_
    have := hI x
    have hrest : isFiniteLocallyFree (U x).toScheme (M.restrict (U x).ι) :=
      isFiniteLocallyFree_of_retract (hr x).some (isFiniteLocallyFree_free (U x).toScheme (I x))
    exact (isFiniteLocallyFree (U x).toScheme).prop_of_iso
      ((restrictFunctorIsoPullback (U x).ι).app M) hrest

end

end AlgebraicGeometry.Scheme.Modules
