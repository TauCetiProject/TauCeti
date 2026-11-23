/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Condensed.Solid
public import TauCeti.Condensed.Discrete.Colimit
public import TauCeti.Condensed.Discrete.LocallyConstant
public import TauCeti.Condensed.Discrete.Module
public import TauCeti.Topology.LocallyConstant.FinsuppDual

/-!
# `R[S]^solid` on profinite sets as the dual of locally constant functions

For a profinite set `S` and a commutative ring `R`, Mathlib defines the condensed `R`-module
`R[S]^solid` (`Condensed.profiniteSolid R`) as the right Kan extension of the free condensed
modules `R[T]` on finite sets `T` along `FintypeCat.toProfinite`, so that informally
`R[S]^solid = lim R[S_i]` over the finite quotients `S_i` of `S`. This file identifies it,
naturally in `S` (`TauCeti.profiniteSolidIsoLocallyConstantDual`), with the condensed
`R`-module `TauCeti.locallyConstantDual R S` whose sections over a compact Hausdorff space `X`
are the `R`-linear maps `LocallyConstant S R → LocallyConstant X R`
(`TauCeti.locallyConstantDualSectionsEquiv`), with restriction by composition.

The proof shows that `locallyConstantDual R` is a right Kan extension of `finFree R` along
`FintypeCat.toProfinite`:
* on a finite set `T`, the free condensed module `R[T]` is the discrete condensed module on
  the free module `T →₀ R` (`TauCeti.locallyConstantCompFreeIso`, by uniqueness of left
  adjoints), whose sections are identified with the dual of `LocallyConstant T R` by
  `TauCeti.locallyConstantFinsuppLinearEquiv`;
* the dual sends a presentation of `S` as a cofiltered limit of finite sets, such as the limit of
  its finite quotients, to a limit (`TauCeti.isLimitLocallyConstantDual`), because
  `LocallyConstant S R` is the corresponding colimit of the `LocallyConstant S_i R`
  (`TauCeti.isColimitLocallyConstantModulePresheaf`).

A basis of `LocallyConstant S R` exhibits the dual, hence `R[S]^solid`, as a product of copies of
the discrete condensed module `R` (`TauCeti.profiniteSolidObjIsoPi`). This file proves only this
basis-dependent decomposition. Over the integers, Nöbeling's theorem
(`LocallyConstant.freeOfProfinite`) says that `LocallyConstant S ℤ` is free, so that `ℤ[S]^solid`
is a product of copies of `ℤ`; applying `TauCeti.profiniteSolidObjIsoPi` to this requires
transporting a basis to the universe-lifted coefficient ring `ULift ℤ`, since the coefficient
ring of condensed modules lives in `Type (u + 1)`.

This file computes `Condensed.profiniteSolid R`; it does not prove that `R[S]^solid` is solid
(`CondensedMod.IsSolid`), nor that it is free among solid modules.

## References

* D. Clausen, P. Scholze, *Lectures on condensed mathematics*, Lecture V: Definition 5.1,
  Theorem 5.4 and Corollary 5.5.
-/

public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor

noncomputable section

namespace TauCeti

open Condensed

variable (R : Type (u + 1)) [CommRing R]

/-- The functor sending a profinite set `S` to the condensed `R`-module whose sections over a
compact Hausdorff space `X` are the `R`-linear maps `LocallyConstant S R → LocallyConstant X R`
(`TauCeti.locallyConstantDualSectionsEquiv`), with restriction along `X` given by
postcomposition with the pullback of locally constant functions. It is built sectionwise from the
internal hom of `R`-modules. One may interpret it as the internal hom, in condensed `R`-modules,
from the discrete module `LocallyConstant S R` to the discrete module `R`, but this file does not
prove that identification; it proves that the functor is isomorphic to `Condensed.profiniteSolid R`
(`TauCeti.profiniteSolidIsoLocallyConstantDual`). -/
def locallyConstantDual : Profinite.{u} ⥤ CondensedMod.{u} R :=
  ObjectProperty.lift _
    (((CompHausLike.LocallyConstantModule.functorToPresheaves.{u + 1, u} R).obj
      (ModuleCat.of R R)).rightOp ⋙ MonoidalClosed.internalHom ⋙
      (whiskeringLeft _ _ _).obj
        ((CondensedMod.LocallyConstant.functor R).obj (ModuleCat.of R R)).obj)
    (fun _ ↦ GrothendieckTopology.HasSheafCompose.isSheaf _
      ((CondensedMod.LocallyConstant.functor R).obj _).property)

/-- The sections of `(locallyConstantDual R).obj S` over `X` are the `R`-linear maps
`LocallyConstant S R → LocallyConstant X R`. -/
def locallyConstantDualSectionsEquiv (S : Profinite.{u}) (X : CompHaus.{u}ᵒᵖ) :
    ((locallyConstantDual R).obj S).obj.obj X ≃ₗ[R]
      (LocallyConstant S R →ₗ[R] LocallyConstant X.unop R) :=
  ModuleCat.homLinearEquiv

/-- On sections over `X`, the map `(locallyConstantDual R).map f` for `f : S ⟶ S'` precomposes
with the pullback of locally constant functions along `f`. -/
@[simp]
lemma locallyConstantDual_map_hom_app_apply {S S' : Profinite.{u}} (f : S ⟶ S')
    (X : CompHaus.{u}ᵒᵖ) (L : ((locallyConstantDual R).obj S).obj.obj X) :
    locallyConstantDualSectionsEquiv R S' X (((locallyConstantDual R).map f).hom.app X L) =
      locallyConstantDualSectionsEquiv R S X L ∘ₗ LocallyConstant.comapₗ R f.hom.hom :=
  (rfl)

/-- On sections, the restriction maps of `(locallyConstantDual R).obj S` along `g : X ⟶ Y`
postcompose with the pullback of locally constant functions along `g`. -/
@[simp]
lemma locallyConstantDual_obj_obj_map_apply {S : Profinite.{u}} {X Y : CompHaus.{u}ᵒᵖ}
    (g : X ⟶ Y) (L : ((locallyConstantDual R).obj S).obj.obj X) :
    locallyConstantDualSectionsEquiv R S Y (((locallyConstantDual R).obj S).obj.map g L) =
      LocallyConstant.comapₗ R g.unop.hom.hom ∘ₗ locallyConstantDualSectionsEquiv R S X L :=
  (rfl)

/-- A cone of condensed `R`-modules is a limit cone if its cone of sections over every compact
Hausdorff space `X` is: limits of sheaves, and of presheaves, are detected sectionwise. -/
private def isLimitOfIsLimitSections {J : Type*} [Category* J] {K : J ⥤ CondensedMod.{u} R}
    (c : Cone K)
    (h : ∀ X : CompHaus.{u}ᵒᵖ, IsLimit
      ((sheafToPresheaf (coherentTopology CompHaus.{u}) (ModuleCat.{u + 1} R) ⋙
        (evaluation _ _).obj X).mapCone c)) :
    IsLimit c :=
  have : ReflectsLimit K (sheafToPresheaf (coherentTopology CompHaus.{u}) (ModuleCat.{u + 1} R)) :=
    (fullyFaithful_reflectsLimits _).reflectsLimitsOfShape.reflectsLimit
  isLimitOfReflects _ <| evaluationJointlyReflectsLimits _ fun X ↦
    (h X).ofIsoLimit (Functor.mapConeMapCone _).symm

/-- On sections over `X`, `locallyConstantDual R` is the internal hom from the module of locally
constant functions on `S` into `N = LocallyConstant X R`: on both sides, `f : S ⟶ S'` acts by
precomposition with the pullback along `f` (`locallyConstantDual_map_hom_app_apply`). -/
private def locallyConstantDualSectionsIso (X : CompHaus.{u}ᵒᵖ) :
    locallyConstantDual R ⋙ sheafToPresheaf (coherentTopology CompHaus.{u}) (ModuleCat.{u + 1} R) ⋙
        (evaluation _ _).obj X ≅
      ((CompHausLike.LocallyConstantModule.functorToPresheaves.{u + 1, u} R).obj
        (ModuleCat.of R R)).rightOp ⋙ MonoidalClosed.internalHom.flip.obj
          (((CondensedMod.LocallyConstant.functor R).obj (ModuleCat.of R R)).obj.obj X) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by
    refine ModuleCat.hom_ext (LinearMap.ext fun L ↦ ?_)
    exact (locallyConstantDualSectionsEquiv R _ X).injective
      (locallyConstantDual_map_hom_app_apply R f X L)

section Limit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}
  (c : Cone (F ⋙ FintypeCat.toProfinite))

/-- `locallyConstantDual R` sends a cofiltered limit of finite sets with surjective projections,
such as the presentation of a profinite set as the limit of its finite quotients, to a limit,
since `LocallyConstant c.pt R` is the colimit of the locally constant functions on the finite
sets. -/
def isLimitLocallyConstantDual (hc : IsLimit c) [∀ i, Epi (c.π.app i)] :
    IsLimit ((locallyConstantDual R).mapCone c) :=
  isLimitOfIsLimitSections R _ fun X ↦
    -- On sections over `X` this is `Hom(colim LocallyConstant c_i R, N) = lim Hom(-, N)` for the
    -- internal hom into `N = LocallyConstant X R`, which turns colimits into limits.
    -- The cone `coneRightOpOfCocone` built from the image of `c.op` is the image of `c`.
    have h : IsLimit (((CompHausLike.LocallyConstantModule.functorToPresheaves.{u + 1, u} R).obj
        (ModuleCat.of R R)).rightOp.mapCone c) :=
      isLimitConeRightOpOfCocone _ (isColimitLocallyConstantModulePresheaf c (ModuleCat.of R R) hc)
    IsLimit.mapConeEquiv (locallyConstantDualSectionsIso R X).symm <|
      (isLimitOfPreserves (MonoidalClosed.internalHom.flip.obj _) h).ofIsoLimit
        (Functor.mapConeMapCone _)

end Limit

/-- On sections over `X`, the discrete condensed module `R[T]` on a finite set `T` is the dual of
the locally constant functions on `T`. -/
private def locallyConstantFreeIsoApp (T : FintypeCat.{u}) (X : CompHaus.{u}) :
    ModuleCat.of R (LocallyConstant X (ULift.{u + 1} T →₀ R)) ≅
      ModuleCat.of R (ModuleCat.of R (LocallyConstant (FintypeCat.toProfinite.obj T) R) ⟶
        ModuleCat.of R (LocallyConstant X R)) :=
  (TauCeti.locallyConstantFinsuppLinearEquiv R X (ι := FintypeCat.toProfinite.obj T)
    (κ := ULift.{u + 1} T) Equiv.ulift ≪≫ₗ
    (ModuleCat.homLinearEquiv (S := R)
      (M := ModuleCat.of R (LocallyConstant (FintypeCat.toProfinite.obj T) R))
      (N := ModuleCat.of R (LocallyConstant X R))).symm).toModuleIso

private lemma locallyConstantFreeIsoApp_hom_apply (T : FintypeCat.{u}) (X : CompHaus.{u})
    (φ : LocallyConstant X (ULift.{u + 1} T →₀ R))
    (f : LocallyConstant (FintypeCat.toProfinite.obj T) R) :
    ((locallyConstantFreeIsoApp R T X).hom φ).hom f =
      TauCeti.locallyConstantFinsuppLinearEquiv R X (ι := FintypeCat.toProfinite.obj T)
        Equiv.ulift φ f :=
  (rfl)

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
      exact (locallyConstantFreeIsoApp_hom_apply R T _ _ f).trans
        (TauCeti.locallyConstantFinsuppLinearEquiv_comap R _
          (ι := FintypeCat.toProfinite.obj T) Equiv.ulift g.unop.hom.hom φ f))) fun h ↦ by
    ext X φ
    apply ModuleCat.hom_ext
    ext f
    exact (locallyConstantFreeIsoApp_hom_apply R _ _ _ f).trans
      (TauCeti.locallyConstantFinsuppLinearEquiv_map_mapDomain R _
        (ι := FintypeCat.toProfinite.obj _) (ι' := FintypeCat.toProfinite.obj _) Equiv.ulift
        Equiv.ulift (ULift.map h) (FintypeCat.toProfinite.map h).hom.hom (fun _ ↦ rfl) φ f)

/-- On finite sets, `locallyConstantDual R` agrees with the free condensed module functor: for a
finite set `T`, the free condensed module `R[T]` is the dual of `LocallyConstant T R`. -/
def toProfiniteCompLocallyConstantDualIso :
    FintypeCat.toProfinite ⋙ locallyConstantDual R ≅ finFree R :=
  (locallyConstantFreeIso R).symm ≪≫
    isoWhiskerLeft (FintypeCat.incl ⋙ uliftFunctor.{u + 1}) (locallyConstantCompFreeIso R).symm ≪≫
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
          (isLimitLocallyConstantDual R S.asLimitCone S.asLimit))

/-- The condensed `R`-module `R[S]^solid = (Condensed.profiniteSolid R).obj S` on a profinite set
`S` is the condensed dual of `LocallyConstant S R`: its sections over `X` are the `R`-linear maps
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
def locallyConstantDualEval {S : Profinite.{u}} (f : LocallyConstant S R) :
    (locallyConstantDual R).obj S ⟶
      (CondensedMod.LocallyConstant.functor R).obj (ModuleCat.of R R) :=
  ObjectProperty.homMk
    { app X := ModuleCat.ofHom
        (LinearMap.applyₗ f ∘ₗ (locallyConstantDualSectionsEquiv R S X).toLinearMap)
      naturality _ _ _ := rfl }

@[simp]
lemma locallyConstantDualEval_hom_app_apply {S : Profinite.{u}} (f : LocallyConstant S R)
    (X : CompHaus.{u}ᵒᵖ) (L : ((locallyConstantDual R).obj S).obj.obj X) :
    (locallyConstantDualEval R f).hom.app X L = locallyConstantDualSectionsEquiv R S X L f :=
  (rfl)

/-- If `b` is a basis of `LocallyConstant S R`, evaluation at the basis vectors exhibits
`(locallyConstantDual R).obj S` as a product of copies of the discrete condensed module `R`. -/
def isLimitLocallyConstantDualFan {I : Type (u + 1)} {S : Profinite.{u}}
    (b : Module.Basis I R (LocallyConstant S R)) :
    IsLimit (Fan.mk ((locallyConstantDual R).obj S) fun i ↦ locallyConstantDualEval R (b i)) :=
  isLimitOfIsLimitSections R _ fun X ↦
    -- Rewrite the evaluated diagram as the discrete diagram on the evaluated factors.
    IsLimit.postcomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) _ <|
    -- On sections, a linear map out of `LocallyConstant S R` is determined freely by its values
    -- on the basis (`Module.Basis.constr`), so the cone of sections is the concrete product cone:
    -- its `i`-th leg evaluates `b.constr R L` at `b i`, which is `L i`.
    (ModuleCat.productConeIsLimit.{u + 1, u + 1, u + 1}
      fun _ : I ↦ ModuleCat.of R (LocallyConstant X.unop R)).ofIsoLimit
      (Cone.ext ((locallyConstantDualSectionsEquiv R S X ≪≫ₗ (b.constr R).symm).toModuleIso.symm)
        fun ⟨i⟩ ↦ by ext L; exact (b.constr_basis R L i).symm)

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

end TauCeti
