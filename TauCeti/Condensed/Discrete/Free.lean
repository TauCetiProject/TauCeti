/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Discrete.Module
public import Mathlib.Condensed.Functors

/-!
# Free condensed modules on discrete condensed sets

A finite set `F`, viewed as a profinite space, represents the condensed set whose sections over a
compact Hausdorff space `T` are the continuous maps `T → F`, that is, the locally constant maps.
So the represented condensed set is the discrete condensed set of locally constant maps into `F`
(`TauCeti.fintypeToCondensedIso`).

The free condensed module on a discrete condensed set is discrete: both
`CondensedSet.LocallyConstant.functor ⋙ Condensed.free R` and
`ModuleCat.free R ⋙ CondensedMod.LocallyConstant.functor R` are left adjoint to taking the
underlying set of the sections over a point, so they are isomorphic
(`TauCeti.freeLocallyConstantIso`), compatibly with the units of the two adjunctions
(`TauCeti.unit_app_comp_map_freeLocallyConstantIso_hom_app`). Together, the free condensed
`R`-module on a finite set `F` has sections `LocallyConstant T (F →₀ R)` over `T`; this is the
input for the computation of the free solid module `R[S]^solid` on a profinite set `S`, defined
in Mathlib as a limit of free condensed modules on finite sets.
-/

public section

universe u

open CategoryTheory Opposite Condensed

namespace TauCeti

/-- The continuous maps from a compact Hausdorff space `T` to a finite discrete space `F` are its
locally constant maps. -/
private def homFintypeEquiv (F : FintypeCat.{u}) (T : CompHaus.{u}) :
    ULift.{u + 1} (T ⟶ profiniteToCompHaus.obj (FintypeCat.toProfinite.obj F)) ≃
      LocallyConstant T (ULift.{u + 1} F) where
  toFun f := ⟨fun t ↦ ULift.up (f.down t),
    letI : DiscreteTopology (profiniteToCompHaus.obj (FintypeCat.toProfinite.obj F)) :=
      FintypeCat.discreteTopology F
    ((IsLocallyConstant.iff_continuous _).mpr (ConcreteCategory.hom f.down).continuous).comp _⟩
  invFun g := ULift.up
    (CompHausLike.ofHom _ ⟨fun t ↦ (g t).down, (g.isLocallyConstant.comp _).continuous⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A finite set, viewed as a profinite space, represents the discrete condensed set of locally
constant maps into it. On sections over `T`, the isomorphism sends a continuous map `T → F` to
itself, viewed as a locally constant map. -/
noncomputable def fintypeToCondensedIso :
    FintypeCat.toProfinite ⋙ profiniteToCondensed.{u} ≅
      FintypeCat.incl ⋙ uliftFunctor.{u + 1} ⋙ CondensedSet.LocallyConstant.functor :=
  NatIso.ofComponents (fun F ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
    -- Both naturality squares hold by definition: on sections, both sides act by precomposition
    -- (with `g : T' ⟶ T`) and postcomposition (with `k : F ⟶ F'`) of the same underlying function,
    -- and `homFintypeEquiv` does not change that function.
    (NatIso.ofComponents (fun T ↦ (homFintypeEquiv F T.unop).toIso) fun _ ↦ rfl)) fun _ ↦ by
      apply (fullyFaithfulSheafToPresheaf _ _).map_injective
      ext T f
      rfl

theorem fintypeToCondensedIso_hom_app_hom_app_apply (F : FintypeCat.{u}) (T : CompHaus.{u})
    (f : ULift.{u + 1} (T ⟶ profiniteToCompHaus.obj (FintypeCat.toProfinite.obj F))) (t : T) :
    -- The section is an element of the sections of a discrete condensed set, which elaboration
    -- does not unfold to `LocallyConstant T (ULift F)`; the explicit `F` lets it be applied to `t`.
    DFunLike.coe (F := LocallyConstant T (ULift.{u + 1} F))
      ((fintypeToCondensedIso.hom.app F).hom.app (op T) f) t =
      ULift.up (f.down t) :=
  (rfl)

variable (R : Type (u + 1)) [Ring R]

/-- The free condensed `R`-module on the discrete condensed set of a set `X` is the discrete
condensed module on the free `R`-module `X →₀ R`: both functors are left adjoint to taking the
underlying set of the sections over a point. -/
noncomputable def freeLocallyConstantIso :
    CondensedSet.LocallyConstant.functor ⋙ free R ≅
      ModuleCat.free R ⋙ CondensedMod.LocallyConstant.functor R :=
  ((CompHausLike.LocallyConstant.adjunction _ _).comp (freeForgetAdjunction R)).leftAdjointUniq
    (((ModuleCat.adj R).comp (CondensedMod.LocallyConstant.adjunction R)).ofNatIsoRight
      (NatIso.ofComponents fun _ ↦ Iso.refl _))

/-- `freeLocallyConstantIso` is compatible with the units of the two adjunctions it compares: the
unit of `CondensedSet.LocallyConstant.functor ⋙ free R`, followed by the underlying map of
`freeLocallyConstantIso`, is the unit of
`ModuleCat.free R ⋙ CondensedMod.LocallyConstant.functor R`. -/
@[reassoc]
theorem unit_app_comp_map_freeLocallyConstantIso_hom_app (X : Type (u + 1)) :
    ((CompHausLike.LocallyConstant.adjunction.{u, u + 1} _ _).comp
        (freeForgetAdjunction R)).unit.app X ≫
      (forget R ⋙ (sheafSections _ _).obj _).map ((freeLocallyConstantIso R).hom.app X) =
    ((ModuleCat.adj R).comp (CondensedMod.LocallyConstant.adjunction R)).unit.app X := by
  refine (Adjunction.unit_leftAdjointUniq_hom_app _ _ X).trans ?_
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
  exact Category.comp_id _

end TauCeti
