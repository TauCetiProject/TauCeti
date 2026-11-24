/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Affine.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# The Picard group of an affine scheme

For a commutative ring `R`, passing to isomorphism classes across the monoidal equivalence
`InvertibleSheaf.invertibleModuleEquiv` identifies the Picard group `LineBundleClass (Spec (.of R))`
of line bundles on `Spec R` with Mathlib's algebraic Picard group `CommRing.Pic R` by a
multiplicative equivalence `LineBundleClass.specEquivPic`. It sends the class of an invertible sheaf
`L` to `CommRing.Pic.mk R (Γ L)`, and sends a Picard class `P` to the class of `P~`, so
`specEquivPic R (mk L) = P` holds precisely when `L ≅ P~`
(`LineBundleClass.specEquivPic_mk_eq_iff`).

Pullback of line-bundle classes along `Spec φ : Spec S ⟶ Spec R` corresponds under
`LineBundleClass.specEquivPic` to extension of scalars `CommRing.Pic.mapRingHom φ`
(`LineBundleClass.specEquivPic_pullback`). For an arbitrary affine scheme `X`, composing with
pullback along `X.isoSpec : X ≅ Spec Γ(X, ⊤)` yields a canonical group isomorphism
`LineBundleClass.equivPicOfIsAffine : LineBundleClass X ≃* CommRing.Pic Γ(X, ⊤)` natural in
morphisms of affine schemes (`LineBundleClass.equivPicOfIsAffine_pullback`).

As consequences, `LineBundleClass X` is `Small.{u}` for any affine scheme `X : Scheme.{u}`, and
`LineBundleClass X` is trivial whenever `CommRing.Pic Γ(X, ⊤)` is a subsingleton (in particular over
local rings, semilocal rings, and GCD/factorial domains).

## Main declarations

* `TauCeti.AlgebraicGeometry.LineBundleClass.specEquivPic`: the multiplicative equivalence
  `LineBundleClass (Spec (.of R)) ≃* CommRing.Pic R`;
* `TauCeti.AlgebraicGeometry.LineBundleClass.specEquivPic_mk`,
  `TauCeti.AlgebraicGeometry.LineBundleClass.specEquivPic_tilde`,
  `TauCeti.AlgebraicGeometry.LineBundleClass.specEquivPic_symm_mk`,
  `TauCeti.AlgebraicGeometry.LineBundleClass.specEquivPic_mk_eq_iff`, and
  `TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_one_iff_free`: action of `specEquivPic` and its
  inverse on line bundles and invertible modules, and characterization of trivial line-bundle
  classes;
* `TauCeti.AlgebraicGeometry.LineBundleClass.skeletonMulEquiv_trans_specEquivPic`: agreement of
  `specEquivPic` with the categorical equivalence `Skeleton.mulEquiv` applied to
  `InvertibleSheaf.invertibleModuleEquiv`;
* `TauCeti.AlgebraicGeometry.LineBundleClass.specEquivPic_pullback` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.specEquivPic_comp_pullbackHom`: compatibility of
  `specEquivPic` with pullback along `Spec.map` and `CommRing.Pic.mapRingHom`;
* `TauCeti.AlgebraicGeometry.LineBundleClass.equivPicOfIsAffine` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.equivPicOfIsAffine_pullback`: the isomorphism
  `LineBundleClass X ≃* CommRing.Pic Γ(X, ⊤)` for any affine scheme `X` and its naturality;
* `TauCeti.AlgebraicGeometry.LineBundleClass.small_spec`,
  `TauCeti.AlgebraicGeometry.LineBundleClass.small_of_isAffine`,
  `TauCeti.AlgebraicGeometry.LineBundleClass.subsingleton_spec`, and
  `TauCeti.AlgebraicGeometry.LineBundleClass.subsingleton_of_isAffine`: smallness and vanishing of
  Picard groups of affine schemes.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 6.2 and Exercise 6.2
* [The Stacks Project, Tag 0AFW](https://stacks.math.columbia.edu/tag/0AFW)
* [The Stacks Project, Tag 0B8I](https://stacks.math.columbia.edu/tag/0B8I)
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace LineBundleClass

section Spec

variable (R : Type u) [CommRing R]

/-- **The Picard group of `Spec R` is canonically isomorphic to `CommRing.Pic R`.** It sends the
class of a line bundle `L` on `Spec R` to the Picard class of its invertible `R`-module of global
sections, with inverse `P ↦ [P~]`. -/
def specEquivPic : LineBundleClass (Spec (.of R)) ≃* CommRing.Pic R :=
  ((skeletonMulEquiv (Spec (.of R))).symm.trans
    (Skeleton.mulEquiv (InvertibleSheaf.invertibleModuleEquiv (.of R))).symm).trans
    (InvertibleModules.skeletonEquivPic R)

/-- `specEquivPic R` sends the class of a line bundle `L` on `Spec R` to the Picard class of its
module of global sections. -/
@[simp]
theorem specEquivPic_mk (L : InvertibleSheaf (Spec (.of R))) :
    specEquivPic R (mk L) = CommRing.Pic.mk R ((moduleSpecΓFunctor (R := .of R)).obj L.obj) := by
  -- `(Skeleton.mulEquiv e).symm` acts on objects as `e.inverse.mapSkeleton.obj`.
  have hinv : (Skeleton.mulEquiv (InvertibleSheaf.invertibleModuleEquiv (.of R))).symm
      (toSkeleton L) =
      toSkeleton ((InvertibleSheaf.invertibleModuleEquiv (.of R)).inverse.obj L) :=
    (InvertibleSheaf.invertibleModuleEquiv (.of R)).inverse.mapSkeleton_obj_toSkeleton L
  simp only [specEquivPic, MulEquiv.trans_apply, skeletonMulEquiv_symm_mk, hinv,
    InvertibleModules.skeletonEquivPic_toSkeleton]
  -- `((invertibleModuleEquiv (.of R)).inverse.obj L).obj` reduces definitionally to
  -- `moduleSpecΓFunctor.obj L.obj` (see `invertibleModuleEquiv_inverse_obj_obj`).
  rfl

/-- `specEquivPic R` sends the class of `M~` for an invertible `R`-module `M` to
`CommRing.Pic.mk R M`. -/
theorem specEquivPic_tilde (M : ModuleCat.{u} R) [Module.Invertible R M] :
    specEquivPic R (mk ⟨tilde (R := .of R) M, isInvertible_tilde (R := .of R) M⟩) =
      CommRing.Pic.mk R M := by
  let L : InvertibleSheaf (Spec (.of R)) :=
    ⟨tilde (R := .of R) M, isInvertible_tilde (R := .of R) M⟩
  have : Module.Invertible R ((moduleSpecΓFunctor (R := .of R)).obj (tilde (R := .of R) M)) :=
    InvertibleSheaf.invertible_moduleSpecΓ_of L
  rw [specEquivPic_mk]
  exact CommRing.Pic.mk_eq_mk_iff.mpr
    ⟨((tilde.toTildeΓNatIso (R := .of R)).app M).symm.toLinearEquiv⟩

/-- The inverse of `specEquivPic R` sends `P : CommRing.Pic R` to the class of `(ofPic R P)~`. -/
theorem specEquivPic_symm_apply (P : CommRing.Pic R) :
    (specEquivPic R).symm P =
      mk ((InvertibleSheaf.invertibleModuleEquiv (.of R)).functor.obj
        (InvertibleModules.ofPic R P)) := by
  -- `Skeleton.mulEquiv e` acts on objects as `e.functor.mapSkeleton.obj`.
  have hfwd : (Skeleton.mulEquiv (InvertibleSheaf.invertibleModuleEquiv (.of R)))
      (toSkeleton (InvertibleModules.ofPic R P)) =
      toSkeleton ((InvertibleSheaf.invertibleModuleEquiv (.of R)).functor.obj
        (InvertibleModules.ofPic R P)) :=
    (InvertibleSheaf.invertibleModuleEquiv (.of R)).functor.mapSkeleton_obj_toSkeleton
      (InvertibleModules.ofPic R P)
  simp only [specEquivPic, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    InvertibleModules.skeletonEquivPic_symm_apply, hfwd, skeletonMulEquiv_toSkeleton]

/-- The inverse of `specEquivPic R` sends `CommRing.Pic.mk R M` to the class of `M~`. -/
@[simp]
theorem specEquivPic_symm_mk (M : Type u) [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    (specEquivPic R).symm (CommRing.Pic.mk R M) =
      mk ⟨tilde (R := .of R) (ModuleCat.of R M),
        isInvertible_tilde (R := .of R) (ModuleCat.of R M)⟩ :=
  (specEquivPic R).symm_apply_eq.mpr (specEquivPic_tilde R (ModuleCat.of R M)).symm

/-- `specEquivPic R` sends the class of `L` to `P` if and only if `L` is isomorphic to `P~`. -/
theorem specEquivPic_mk_eq_iff (L : InvertibleSheaf (Spec (.of R))) (P : CommRing.Pic R) :
    specEquivPic R (mk L) = P ↔
      Nonempty (L.obj ≅ tilde (R := .of R) (ModuleCat.of R P)) := by
  rw [← (specEquivPic R).eq_symm_apply, specEquivPic_symm_apply, mk_eq_mk_iff]
  have hP : (InvertibleModules.ofPic R P).obj = ModuleCat.of R P :=
    InvertibleModules.ofPic_obj R P
  exact ⟨fun ⟨e⟩ ↦ ⟨e ≪≫ (tilde.functor (.of R)).mapIso (eqToIso hP)⟩,
    fun ⟨e⟩ ↦ ⟨e ≪≫ (tilde.functor (.of R)).mapIso (eqToIso hP.symm)⟩⟩

/-- The class of a line bundle `L` on `Spec (.of R)` is trivial in `LineBundleClass (Spec (.of R))`
if and only if its `R`-module of global sections is free. -/
theorem mk_eq_one_iff_free (L : InvertibleSheaf (Spec (.of R))) :
    mk L = 1 ↔ Module.Free R ((moduleSpecΓFunctor (R := .of R)).obj L.obj) := by
  rw [← (specEquivPic R).map_eq_one_iff, specEquivPic_mk, CommRing.Pic.mk_eq_one_iff_free]

/-- Composing `LineBundleClass.skeletonMulEquiv` with `specEquivPic R` agrees with the categorical
monoid equivalence `Skeleton.mulEquiv` induced by `InvertibleSheaf.invertibleModuleEquiv` followed
by `InvertibleModules.skeletonEquivPic R`. -/
theorem skeletonMulEquiv_trans_specEquivPic :
    (skeletonMulEquiv (Spec (.of R))).trans (specEquivPic R) =
      (Skeleton.mulEquiv (InvertibleSheaf.invertibleModuleEquiv (.of R))).symm.trans
        (InvertibleModules.skeletonEquivPic R) := by
  ext x
  simp only [specEquivPic, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- Pullback of line-bundle classes along `Spec f` corresponds under `specEquivPic` to
`CommRing.Pic.mapRingHom f`. -/
@[simp]
theorem specEquivPic_pullback {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (a : LineBundleClass (Spec (.of R))) :
    specEquivPic S (pullback (Spec.map (CommRingCat.ofHom f)) a) =
      CommRing.Pic.mapRingHom f (specEquivPic R a) := by
  obtain ⟨P, rfl⟩ := (specEquivPic R).symm.surjective a
  rw [MulEquiv.apply_symm_apply, specEquivPic_symm_apply, pullback_mk]
  let M := InvertibleModules.ofPic R P
  let MS := (InvertibleModules.extendScalars f).obj M
  have : Module.Invertible S MS.obj := InvertibleModules.invertible_obj MS
  have hiso : mk ((InvertibleSheaf.pullback (Spec.map (CommRingCat.ofHom f))).obj
      ((InvertibleSheaf.invertibleModuleEquiv (.of R)).functor.obj M)) =
      mk ((InvertibleSheaf.invertibleModuleEquiv (.of S)).functor.obj MS) :=
    mk_eq_mk_iff.mpr ⟨(SheafOfModules.isInvertible (Spec (.of S))).ι.mapIso
      ((InvertibleSheaf.invertibleModuleEquivCompPullbackIso (CommRingCat.ofHom f)).app M)⟩
  rw [hiso]
  have htilde : specEquivPic S
      (mk ((InvertibleSheaf.invertibleModuleEquiv (.of S)).functor.obj MS)) =
      InvertibleModules.skeletonEquivPic S
        ((InvertibleModules.extendScalars f).mapSkeleton.obj (toSkeleton M)) := by
    rw [Functor.mapSkeleton_obj_toSkeleton, InvertibleModules.skeletonEquivPic_toSkeleton]
    exact specEquivPic_tilde S MS.obj
  rw [htilde, InvertibleModules.skeletonEquivPic_extendScalars_mapSkeleton,
    ← InvertibleModules.skeletonEquivPic_symm_apply, MulEquiv.apply_symm_apply]

/-- As group homomorphisms, `specEquivPic` intertwines `pullbackHom (Spec.map (ofHom f))` with
`CommRing.Pic.mapRingHom f`. -/
theorem specEquivPic_comp_pullbackHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (specEquivPic S : LineBundleClass (Spec (.of S)) →* CommRing.Pic S).comp
      (pullbackHom (Spec.map (CommRingCat.ofHom f))) =
      (CommRing.Pic.mapRingHom f).comp (specEquivPic R) := by
  ext a
  simp [specEquivPic_pullback]

/-- `LineBundleClass (Spec (.of R))` is `u`-small, since `specEquivPic R` embeds it into
`CommRing.Pic R : Type u`. -/
instance small_spec : Small.{u} (LineBundleClass (Spec (.of R))) :=
  small_of_injective (specEquivPic R).injective

/-- If `CommRing.Pic R` is trivial (for instance when `R` is local, semilocal, or a GCD domain),
then every line bundle on `Spec R` is trivial up to isomorphism. -/
instance subsingleton_spec [Subsingleton (CommRing.Pic R)] :
    Subsingleton (LineBundleClass (Spec (.of R))) :=
  (specEquivPic R).toEquiv.subsingleton

end Spec

section IsAffine

variable (X : Scheme.{u}) [IsAffine X]

/-- **The Picard group of an affine scheme `X` is canonically isomorphic to
`CommRing.Pic Γ(X, ⊤)`.** It pulls back line-bundle classes along `X.isoSpec.inv : Spec Γ(X, ⊤) ⟶ X`
and applies `specEquivPic Γ(X, ⊤)`. -/
def equivPicOfIsAffine : LineBundleClass X ≃* CommRing.Pic Γ(X, ⊤) :=
  (pullbackEquiv X.isoSpec.symm).trans (specEquivPic Γ(X, ⊤))

/-- `equivPicOfIsAffine X` pulls back along `X.isoSpec.inv` and applies `specEquivPic Γ(X, ⊤)`. -/
theorem equivPicOfIsAffine_apply (a : LineBundleClass X) :
    equivPicOfIsAffine X a = specEquivPic Γ(X, ⊤) (pullback X.isoSpec.inv a) := by
  simp [equivPicOfIsAffine]

/-- The inverse of `equivPicOfIsAffine X` pulls back the class on `Spec Γ(X, ⊤)` along
`X.isoSpec.hom`. -/
theorem equivPicOfIsAffine_symm_apply (P : CommRing.Pic Γ(X, ⊤)) :
    (equivPicOfIsAffine X).symm P = pullback X.isoSpec.hom ((specEquivPic Γ(X, ⊤)).symm P) := by
  simp only [equivPicOfIsAffine, MulEquiv.symm_trans_apply, pullbackEquiv_symm, Iso.symm_symm_eq,
    pullbackEquiv_apply]

/-- On `Spec (.of R)`, `equivPicOfIsAffine` differs from `specEquivPic R` by the canonical ring
isomorphism `(Scheme.ΓSpecIso (.of R)).inv : R ⟶ Γ(Spec (.of R), ⊤)`. -/
theorem equivPicOfIsAffine_spec (R : Type u) [CommRing R]
    (a : LineBundleClass (Spec (.of R))) :
    equivPicOfIsAffine (Spec (.of R)) a =
      CommRing.Pic.mapRingHom (Scheme.ΓSpecIso (.of R)).inv.hom (specEquivPic R a) := by
  rw [equivPicOfIsAffine_apply, Scheme.isoSpec_Spec_inv]
  exact specEquivPic_pullback (Scheme.ΓSpecIso (.of R)).inv.hom a

/-- `equivPicOfIsAffine` is natural with respect to morphisms between affine schemes: pullback along
`f : X ⟶ Y` corresponds to extension of scalars along `f.appTop : Γ(Y, ⊤) ⟶ Γ(X, ⊤)`. -/
@[simp]
theorem equivPicOfIsAffine_pullback {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (a : LineBundleClass Y) :
    equivPicOfIsAffine X (pullback f a) =
      CommRing.Pic.mapRingHom f.appTop.hom (equivPicOfIsAffine Y a) := by
  rw [equivPicOfIsAffine_apply, equivPicOfIsAffine_apply, pullback_comp,
    ← Scheme.isoSpec_inv_naturality f, ← pullback_comp]
  exact specEquivPic_pullback f.appTop.hom (pullback Y.isoSpec.inv a)

/-- `LineBundleClass X` is `u`-small for any affine scheme `X : Scheme.{u}`. -/
instance small_of_isAffine : Small.{u} (LineBundleClass X) :=
  small_of_injective (equivPicOfIsAffine X).injective

/-- For an affine scheme `X` whose coordinate ring has trivial Picard group, `LineBundleClass X` is
trivial. -/
instance subsingleton_of_isAffine [Subsingleton (CommRing.Pic Γ(X, ⊤))] :
    Subsingleton (LineBundleClass X) :=
  (equivPicOfIsAffine X).toEquiv.subsingleton

end IsAffine

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
