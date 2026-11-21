/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Condensed.Discrete.Colimit
public import Mathlib.Condensed.Discrete.Module
public import Mathlib.Condensed.Solid
public import TauCeti.Topology.LocallyConstant.FinsuppDual

/-!
# Free solid modules on profinite sets as duals of locally constant functions

For a profinite set `S` and a commutative ring `R`, Mathlib defines the condensed `R`-module
`R[S]^solid` (`Condensed.profiniteSolid R`) as the right Kan extension of the free condensed
modules `R[T]` on finite sets `T` along `FintypeCat.toProfinite`, so that informally
`R[S]^solid = lim R[S_i]` over the finite quotients `S_i` of `S`. This file identifies it with
the condensed `R`-module `Condensed.locallyConstantDual R S` whose sections over a compact
Hausdorff space `X` are the `R`-linear maps `LocallyConstant S R → LocallyConstant X R`, the
condensed dual of the locally constant functions on `S`
(`Condensed.profiniteSolidIsoLocallyConstantDual`, natural in `S`).

The proof shows that `locallyConstantDual R` is a right Kan extension of `finFree R` along
`FintypeCat.toProfinite`:
* on a finite set `T`, the free condensed module `R[T]` is the discrete condensed module on
  the free module `T →₀ R` (`Condensed.freeCompLocallyConstantIso`, by uniqueness of left
  adjoints), whose sections are identified with the dual of `LocallyConstant T R` by
  `LocallyConstant.finsuppLinearEquiv`;
* the dual sends the presentation of `S` as the limit of its finite quotients to a limit
  (`Condensed.isLimitLocallyConstantDual`), because `LocallyConstant S R` is the colimit of the
  `LocallyConstant S_i R` (`Condensed.isColimitLocallyConstantModulePresheafDiagram`).

A basis of `LocallyConstant S R` exhibits the dual, hence `R[S]^solid`, as a product of copies of
the discrete condensed module `R` (`Condensed.profiniteSolidObjIsoPi`). By Nöbeling's theorem
(`LocallyConstant.freeOfProfinite`) such a basis exists over the integers, so that `ℤ[S]^solid` is
a product of copies of `ℤ`.

## References

* D. Clausen, P. Scholze, *Lectures on condensed mathematics*, Lecture V: Definition 5.1,
  Theorem 5.4 and Corollary 5.5.
-/

public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor

noncomputable section

namespace Condensed

/-- For a finite set `T`, the condensed set represented by the finite profinite set `T` is the
discrete condensed set on `T`: a continuous map from a compact Hausdorff space to the finite
discrete space `T` is the same as a locally constant one. -/
def toProfiniteCompProfiniteToCondensedIso :
    FintypeCat.toProfinite.{u} ⋙ profiniteToCondensed ≅
      FintypeCat.incl ⋙ uliftFunctor.{u + 1} ⋙ CondensedSet.LocallyConstant.functor :=
  NatIso.ofComponents (fun T ↦ ObjectProperty.isoMk _ <| NatIso.ofComponents (fun X ↦ Equiv.toIso
    { toFun (g : ULift.{u + 1} (X.unop ⟶ profiniteToCompHaus.obj (FintypeCat.toProfinite.obj T))) :=
        ⟨ULift.up ∘ g.down.hom.hom, by
        have : DiscreteTopology (profiniteToCompHaus.obj (FintypeCat.toProfinite.obj T)) := ⟨rfl⟩
        exact ((IsLocallyConstant.iff_continuous _).2 g.down.hom.hom.continuous).comp _⟩
      invFun (f : LocallyConstant X.unop (ULift.{u + 1} T)) :=
        ⟨CompHausLike.ofHom _ ⟨ULift.down ∘ f, (f.isLocallyConstant.comp _).continuous⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }) fun _ ↦ rfl) fun _ ↦ rfl

variable (R : Type (u + 1)) [Ring R]

/-- The free condensed `R`-module on a discrete condensed set is the discrete condensed module on
the free `R`-module, by uniqueness of left adjoints. -/
def freeCompLocallyConstantIso :
    CondensedSet.LocallyConstant.functor.{u} ⋙ free R ≅
      ModuleCat.free R ⋙ CondensedMod.LocallyConstant.functor R :=
  ((CompHausLike.LocallyConstant.adjunction _ _).comp (freeForgetAdjunction R)).leftAdjointUniq
    (((ModuleCat.adj R).comp (CondensedMod.LocallyConstant.adjunction R)).ofNatIsoRight
      (Iso.refl _))

/-- The presheaf of `R`-modules `S ↦ LocallyConstant S M` on profinite sets turns the
presentation of `S` as the limit of its finite quotients into a colimit. This is the
module-valued version of `Condensed.isColimitLocallyConstantPresheafDiagram`. -/
def isColimitLocallyConstantModulePresheafDiagram (M : ModuleCat.{u + 1} R) (S : Profinite.{u}) :
    IsColimit (((CompHausLike.LocallyConstantModule.functorToPresheaves.{u + 1, u} R).obj
      M).mapCocone S.asLimitCone.op) :=
  let : ReflectsFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    reflectsFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  isColimitOfReflects (CategoryTheory.forget (ModuleCat.{u + 1} R))
    (isColimitLocallyConstantPresheafDiagram M S)

variable (R : Type (u + 1)) [CommRing R]

/-- The functor sending a profinite set `S` to the condensed `R`-module whose sections over a
compact Hausdorff space `X` are the `R`-linear maps `LocallyConstant S R → LocallyConstant X R`,
with restriction along `X` given by composition. It is the internal hom, in condensed
`R`-modules, from the discrete module `LocallyConstant S R` to the discrete module `R`, and it is
isomorphic to `Condensed.profiniteSolid R` (`Condensed.profiniteSolidIsoLocallyConstantDual`). -/
@[expose]
def locallyConstantDual : Profinite.{u} ⥤ CondensedMod.{u} R :=
  ObjectProperty.lift _
    (((CompHausLike.LocallyConstantModule.functorToPresheaves.{u + 1, u} R).obj
      (ModuleCat.of R R)).rightOp ⋙ MonoidalClosed.internalHom ⋙
      (whiskeringLeft _ _ _).obj
        ((CondensedMod.LocallyConstant.functor R).obj (ModuleCat.of R R)).obj)
    (fun _ ↦ GrothendieckTopology.HasSheafCompose.isSheaf _
      ((CondensedMod.LocallyConstant.functor R).obj _).property)

/-- On sections over `X`, the map `(locallyConstantDual R).map f` for `f : S ⟶ S'` precomposes
with the pullback of locally constant functions along `f`. -/
@[simp]
lemma locallyConstantDual_map_hom_app {S S' : Profinite.{u}} (f : S ⟶ S') (X : CompHaus.{u}ᵒᵖ)
    (L : ModuleCat.of R (LocallyConstant S R) ⟶ ModuleCat.of R (LocallyConstant X.unop R)) :
    ((locallyConstantDual R).map f).hom.app X L =
      ModuleCat.ofHom (LocallyConstant.comapₗ R f.hom.hom) ≫ L :=
  rfl

/-- On sections, the restriction maps of `(locallyConstantDual R).obj S` along `g : X ⟶ Y`
postcompose with the pullback of locally constant functions along `g`. -/
@[simp]
lemma locallyConstantDual_obj_obj_map {S : Profinite.{u}} {X Y : CompHaus.{u}ᵒᵖ} (g : X ⟶ Y)
    (L : ModuleCat.of R (LocallyConstant S R) ⟶ ModuleCat.of R (LocallyConstant X.unop R)) :
    ((locallyConstantDual R).obj S).obj.map g L =
      L ≫ ModuleCat.ofHom (LocallyConstant.comapₗ R g.unop.hom.hom) :=
  rfl

/-- `locallyConstantDual R` sends the presentation of a profinite set `S` as the limit of its
finite quotients to a limit, since `LocallyConstant S R` is the colimit of the locally constant
functions on the finite quotients. -/
def isLimitLocallyConstantDual (S : Profinite.{u}) :
    IsLimit ((locallyConstantDual R).mapCone S.asLimitCone) := by
  -- Limits of sheaves, and of presheaves, are detected sectionwise.
  refine @isLimitOfReflects _ _ _ _ _ _ _
    (sheafToPresheaf (coherentTopology CompHaus.{u}) (ModuleCat.{u + 1} R)) _ ?_
    ((fullyFaithful_reflectsLimits.{u, u} _).reflectsLimitsOfShape.reflectsLimit)
  apply evaluationJointlyReflectsLimits
  intro X
  refine @isLimitOfReflects _ _ _ _ _ _ _ (CategoryTheory.forget (ModuleCat.{u + 1} R)) _ ?_
    (reflectsLimit_of_reflectsIsomorphisms _ _)
  -- On sections over `X` this is `Hom(colim LocallyConstant S_i R, -) = lim Hom(-, -)`.
  exact (isLimitOfPreserves (yoneda.obj _)
    (isColimitLocallyConstantModulePresheafDiagram R _ S).op).whiskerEquivalence
      (opOpEquivalence _).symm

/-- On sections over `X`, the discrete condensed module `R[T]` on a finite set `T` is the dual of
the locally constant functions on `T`. -/
private def locallyConstantFreeIsoApp (T : FintypeCat.{u}) (X : CompHaus.{u}) :
    ModuleCat.of R (LocallyConstant X (ULift.{u + 1} T →₀ R)) ≅
      ModuleCat.of R (ModuleCat.of R (LocallyConstant (FintypeCat.toProfinite.obj T) R) ⟶
        ModuleCat.of R (LocallyConstant X R)) :=
  have : DiscreteTopology (FintypeCat.toProfinite.obj T) := ⟨rfl⟩
  have : Finite (FintypeCat.incl.obj T) := T.property
  (LocallyConstant.finsuppLinearEquiv R X (ι := FintypeCat.toProfinite.obj T)
    (κ := ULift.{u + 1} (FintypeCat.incl.obj T)) Equiv.ulift ≪≫ₗ
    (ModuleCat.homLinearEquiv (S := R)
      (M := ModuleCat.of R (LocallyConstant (FintypeCat.toProfinite.obj T) R))
      (N := ModuleCat.of R (LocallyConstant X R))).symm).toModuleIso

private lemma locallyConstantFreeIsoApp_hom_apply (T : FintypeCat.{u}) (X : CompHaus.{u})
    (φ : LocallyConstant X (ULift.{u + 1} T →₀ R))
    (f : LocallyConstant (FintypeCat.toProfinite.obj T) R) :
    ((locallyConstantFreeIsoApp R T X).hom φ).hom f =
      φ.map (Finsupp.linearCombination R (f ∘ Equiv.ulift)) :=
  LocallyConstant.finsuppLinearEquiv_apply_apply R X _ φ f

private lemma locallyConstantFreeIsoApp_naturality_left (T : FintypeCat.{u}) {X Y : CompHaus.{u}}
    (g : X ⟶ Y) (φ : LocallyConstant Y (ULift.{u + 1} T →₀ R))
    (f : LocallyConstant (FintypeCat.toProfinite.obj T) R) :
    ((locallyConstantFreeIsoApp R T X).hom (φ.comap g.hom.hom)).hom f =
      (((locallyConstantFreeIsoApp R T Y).hom φ).hom f).comap g.hom.hom := by
  rw [locallyConstantFreeIsoApp_hom_apply, locallyConstantFreeIsoApp_hom_apply]
  -- Postcomposition (`map`) and precomposition (`comap`) of locally constant functions commute;
  -- Mathlib has no lemma for this, and both sides unfold to the same composite function.
  rfl

private lemma locallyConstantFreeIsoApp_naturality {T T' : FintypeCat.{u}} (h : T ⟶ T')
    (X : CompHaus.{u}) (φ : LocallyConstant X (ULift.{u + 1} T →₀ R))
    (f : LocallyConstant (FintypeCat.toProfinite.obj T') R) :
    ((locallyConstantFreeIsoApp R T' X).hom
        (φ.map (Finsupp.mapDomain (ULift.map h)))).hom f =
      ((locallyConstantFreeIsoApp R T X).hom φ).hom
        (f.comap (FintypeCat.toProfinite.map h).hom.hom) := by
  ext x
  rw [locallyConstantFreeIsoApp_hom_apply, locallyConstantFreeIsoApp_hom_apply]
  exact Finsupp.linearCombination_mapDomain R _ (φ x)

/-- On finite sets, the discrete condensed module `R[T]` is the dual of the locally constant
functions on `T`, naturally in `T`. -/
private def locallyConstantFreeIso :
    (FintypeCat.incl ⋙ uliftFunctor.{u + 1}) ⋙ ModuleCat.free R ⋙
      CondensedMod.LocallyConstant.functor R ≅ FintypeCat.toProfinite ⋙ locallyConstantDual R :=
  NatIso.ofComponents (fun T ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun X ↦ locallyConstantFreeIsoApp R T X.unop) fun g ↦ by
      ext φ
      apply ModuleCat.hom_ext
      ext f
      exact locallyConstantFreeIsoApp_naturality_left R T g.unop φ f)) fun h ↦ by
    ext X φ
    apply ModuleCat.hom_ext
    ext f
    exact locallyConstantFreeIsoApp_naturality R h X.unop φ f

/-- On finite sets, `locallyConstantDual R` agrees with the free condensed module functor: for a
finite set `T`, the free condensed module `R[T]` is the dual of `LocallyConstant T R`. -/
def toProfiniteCompLocallyConstantDualIso :
    FintypeCat.toProfinite ⋙ locallyConstantDual R ≅ finFree R :=
  (locallyConstantFreeIso R).symm ≪≫
    isoWhiskerLeft (FintypeCat.incl ⋙ uliftFunctor.{u + 1}) (freeCompLocallyConstantIso R).symm ≪≫
    isoWhiskerRight toProfiniteCompProfiniteToCondensedIso.symm (free R)

/-- `locallyConstantDual R` is the right Kan extension of the free condensed modules on finite
sets along `FintypeCat.toProfinite`. -/
instance : (locallyConstantDual R).IsRightKanExtension
    (toProfiniteCompLocallyConstantDualIso R).hom :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (E := RightExtension.mk _ (toProfiniteCompLocallyConstantDualIso R).hom) fun S ↦
      (IsLimit.postcomposeHomEquiv (isoWhiskerLeft (StructuredArrow.proj S FintypeCat.toProfinite)
        (toProfiniteCompLocallyConstantDualIso R)) _).symm
        (Profinite.Extend.isLimitCone S.asLimitCone (locallyConstantDual R) S.asLimit
          (isLimitLocallyConstantDual R S))

/-- The free solid `R`-module `R[S]^solid` on a profinite set `S` is the condensed dual of
`LocallyConstant S R`: its sections over `X` are the `R`-linear maps
`LocallyConstant S R → LocallyConstant X R`. The isomorphism is natural in `S`. -/
def profiniteSolidIsoLocallyConstantDual : profiniteSolid R ≅ locallyConstantDual R :=
  Functor.rightKanExtensionUnique _ (profiniteSolidCounit R) _
    (toProfiniteCompLocallyConstantDualIso R).hom

/-- `profiniteSolidIsoLocallyConstantDual R` is compatible with the identifications of both
functors with the free condensed modules on finite sets. This is the property by which the
universal property of right Kan extensions characterises it. -/
@[reassoc (attr := simp)]
lemma profiniteSolidIsoLocallyConstantDual_hom_app_comp (T : FintypeCat.{u}) :
    (profiniteSolidIsoLocallyConstantDual R).hom.app (FintypeCat.toProfinite.obj T) ≫
      (toProfiniteCompLocallyConstantDualIso R).hom.app T = (profiniteSolidCounit R).app T := by
  simp [profiniteSolidIsoLocallyConstantDual]

/-- Evaluation of the dual at a locally constant function `f : LocallyConstant S R`, as a map to
the discrete condensed module `R`: on sections over `X` it sends `L` to `L f`. -/
@[expose]
def locallyConstantDualEval {S : Profinite.{u}} (f : LocallyConstant S R) :
    (locallyConstantDual R).obj S ⟶
      (CondensedMod.LocallyConstant.functor R).obj (ModuleCat.of R R) :=
  ObjectProperty.homMk
    { app _ := ModuleCat.ofHom
        { toFun L := L.hom f
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      naturality _ _ _ := rfl }

@[simp]
lemma locallyConstantDualEval_hom_app_apply {S : Profinite.{u}} (f : LocallyConstant S R)
    (X : CompHaus.{u}ᵒᵖ)
    (L : ModuleCat.of R (LocallyConstant S R) ⟶ ModuleCat.of R (LocallyConstant X.unop R)) :
    (locallyConstantDualEval R f).hom.app X L = L.hom f :=
  rfl

/-- If `b` is a basis of `LocallyConstant S R`, evaluation at the basis vectors exhibits
`(locallyConstantDual R).obj S` as a product of copies of the discrete condensed module `R`. -/
def isLimitLocallyConstantDualFan {I : Type (u + 1)} {S : Profinite.{u}}
    (b : Module.Basis I R (LocallyConstant S R)) :
    IsLimit (Fan.mk ((locallyConstantDual R).obj S) fun i ↦ locallyConstantDualEval R (b i)) := by
  -- Limits of sheaves, and of presheaves, are detected sectionwise.
  refine @isLimitOfReflects _ _ _ _ _ _ _
    (sheafToPresheaf (coherentTopology CompHaus.{u}) (ModuleCat.{u + 1} R)) _ ?_
    ((fullyFaithful_reflectsLimits.{u + 1, u + 1} _).reflectsLimitsOfShape.reflectsLimit)
  apply evaluationJointlyReflectsLimits
  intro X
  -- On sections, a linear map out of `LocallyConstant S R` is determined freely by its values
  -- on the basis.
  exact
    { lift s := ModuleCat.ofHom (ModuleCat.homLinearEquiv.symm.toLinearMap ∘ₗ
        (b.constr R).toLinearMap ∘ₗ LinearMap.pi fun i ↦ (s.π.app ⟨i⟩).hom)
      fac s := by
        rintro ⟨i⟩
        ext p
        exact b.constr_basis R _ i
      uniq s m hm := by
        ext p : 2
        apply ModuleCat.hom_ext
        refine b.ext fun i ↦ ?_
        exact (ConcreteCategory.congr_hom (hm ⟨i⟩) p).trans
          (b.constr_basis R (fun j ↦ (s.π.app ⟨j⟩).hom p) i).symm }

/-- If `b` is a basis of `LocallyConstant S R` indexed by `I`, then `R[S]^solid` is the product of
`I` copies of the discrete condensed module `R`. -/
def profiniteSolidObjIsoPi {I : Type (u + 1)} {S : Profinite.{u}}
    (b : Module.Basis I R (LocallyConstant S R)) :
    (profiniteSolid R).obj S ≅
      ∏ᶜ fun _ : I ↦ (CondensedMod.LocallyConstant.functor R).obj (ModuleCat.of R R) :=
  (profiniteSolidIsoLocallyConstantDual R).app S ≪≫
    (isLimitLocallyConstantDualFan R b).conePointUniqueUpToIso (limit.isLimit _)

/-- The `i`-th coordinate of `profiniteSolidObjIsoPi R b` is evaluation at the basis vector
`b i`. -/
@[reassoc (attr := simp)]
lemma profiniteSolidObjIsoPi_hom_π {I : Type (u + 1)} {S : Profinite.{u}}
    (b : Module.Basis I R (LocallyConstant S R)) (i : I) :
    (profiniteSolidObjIsoPi R b).hom ≫ Pi.π _ i =
      (profiniteSolidIsoLocallyConstantDual R).hom.app S ≫ locallyConstantDualEval R (b i) := by
  simp [profiniteSolidObjIsoPi]

end Condensed
