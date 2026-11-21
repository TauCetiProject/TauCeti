/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Sheaf
public import TauCeti.AlgebraicGeometry.Sites.Etale.Pullback
import TauCeti.AlgebraicGeometry.Sites.EtaleSepClosed

/-!
# Trivial finite étale covers and sheaf restriction

This file relates finite étale schemes over `S` to sheaf restriction on the small étale site
(`TauCeti.AlgebraicGeometry.Sites.Etale.Pullback`).

For a finite type `M`, the trivial finite étale cover `TauCeti.FiniteEtaleScheme.trivialCover S M`
is the coproduct of `M` copies of `S`. Its sheaf of sections is the constant étale sheaf with value
`M` (`TauCeti.FiniteEtaleScheme.toSheafTrivialCoverIso`).

For an étale morphism `p : T ⟶ S`, restricting the sheaf of sections of a finite étale `S`-scheme
`X` along `p` yields the sheaf of sections of its base change `(pullback p).obj X`
(`TauCeti.FiniteEtaleScheme.toSheafCompSmallEtaleMapPushforwardIso`,
`TauCeti.FiniteEtaleScheme.toSheafCompSmallEtalePullbackIso`), via the canonical bijection on
sections `TauCeti.FiniteEtaleScheme.restrictSectionEquiv`.

## Main definitions

* `TauCeti.FiniteEtaleScheme.trivialCover`: the finite étale cover of `S` given by a finite
  coproduct of copies of `S`.
* `TauCeti.FiniteEtaleScheme.restrictSectionEquiv`: bijection between sections of `X` over
  `p.smallEtaleMap.obj V` and sections of `(pullback p).obj X` over `V`.
* `TauCeti.FiniteEtaleScheme.toSheafCompSmallEtaleMapPushforwardIso`: natural isomorphism
  `toSheaf S ⋙ p.smallEtaleMap.sheafPushforwardContinuous (Type u) _ _ ≅ pullback p ⋙ toSheaf T`.
* `TauCeti.FiniteEtaleScheme.toSheafCompSmallEtalePullbackIso`: natural isomorphism
  `toSheaf S ⋙ p.smallEtalePullback (Type u) ≅ pullback p ⋙ toSheaf T`.

## Main results

* `TauCeti.FiniteEtaleScheme.toSheafOfHomIdIso`: the sheaf of sections of `ofHom (𝟙 S)` is the
  constant sheaf on `PUnit`.
* `TauCeti.FiniteEtaleScheme.toSheafTrivialCoverIso`: the sheaf of sections of `trivialCover S M`
  is the constant étale sheaf with value `M`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, [Tag 03Q4](https://stacks.math.columbia.edu/tag/03Q4).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

section TrivialCover

variable (S : Scheme.{u})

/-- The trivial finite étale cover of `S` indexed by a finite type `M`: the coproduct of `M`
copies of the identity `S ⟶ S`. -/
noncomputable def trivialCover (M : Type u) [Finite M] : FiniteEtaleScheme S :=
  ∐ fun _ : M ↦ ofHom (𝟙 S)

/-- The sheaf of sections of the base `S` itself is the constant sheaf on a singleton. -/
noncomputable def toSheafOfHomIdIso :
    (toSheaf S).obj (ofHom (𝟙 S)) ≅
      (constantSheaf (Scheme.smallEtaleTopology S) (Type u)).obj PUnit.{u + 1} :=
  let hT : IsTerminal ((toEtale S).obj (ofHom (𝟙 S))) :=
    (Scheme.Etale.mkIdTerminal S).ofIso
      ((Scheme.Etale.forgetFullyFaithful S).preimageIso (eqToIso (by simp)))
  let e : (Functor.const S.Etaleᵒᵖ).obj PUnit.{u + 1} ≅
      (sheafToPresheaf (Scheme.smallEtaleTopology S) (Type u)).obj
        ((toSheaf S).obj (ofHom (𝟙 S))) :=
    NatIso.ofComponents (fun U ↦ Equiv.toIso
      { toFun _ := hT.from U.unop
        invFun _ := PUnit.unit
        left_inv _ := rfl
        right_inv _ := hT.hom_ext _ _ }) (fun _ ↦ by
      ext _
      exact hT.hom_ext _ _)
  ((presheafToSheaf (Scheme.smallEtaleTopology S) (Type u)).mapIso e ≪≫
    (asIso (sheafificationAdjunction (Scheme.smallEtaleTopology S) (Type u)).counit).app
      ((toSheaf S).obj (ofHom (𝟙 S)))).symm

/-- The sheaf of sections of `trivialCover S M` is the constant étale sheaf with value `M`. -/
noncomputable def toSheafTrivialCoverIso (M : Type u) [Finite M] :
    (toSheaf S).obj (trivialCover S M) ≅
      (constantSheaf (Scheme.smallEtaleTopology S) (Type u)).obj M :=
  haveI : Fintype M := Fintype.ofFinite M
  have := hasColimitsOfShape_of_hasFiniteColimits
    (C := Sheaf (Scheme.smallEtaleTopology S) (Type u)) (Discrete M)
  have : (constantSheaf (Scheme.smallEtaleTopology S) (Type u)).IsLeftAdjoint :=
    (constantSheafAdj (Scheme.smallEtaleTopology S) (Type u) (Scheme.Etale.mkIdTerminal S))
      |>.isLeftAdjoint
  PreservesCoproduct.iso (toSheaf S) _ ≪≫
    Sigma.mapIso (fun _ ↦ toSheafOfHomIdIso S) ≪≫
    (PreservesCoproduct.iso (constantSheaf (Scheme.smallEtaleTopology S) (Type u)) _).symm ≪≫
    (constantSheaf (Scheme.smallEtaleTopology S) (Type u)).mapIso
      (Types.coproductIso _ ≪≫ Equiv.toIso (Equiv.sigmaPUnit M))

end TrivialCover

section RestrictSheaf

variable {S T : Scheme.{u}}

/-- Bijection between sections of `X` over `p.smallEtaleMap.obj V` and sections of
`(pullback p).obj X` over `V`. -/
noncomputable def restrictSectionEquiv (p : T ⟶ S) [Etale p]
    (X : FiniteEtaleScheme S) (V : T.Etale) :
    (p.smallEtaleMap.obj V ⟶ (toEtale S).obj X) ≃
      (V ⟶ (toEtale T).obj ((pullback p).obj X)) where
  toFun g := MorphismProperty.Over.homMk
    (Limits.pullback.lift g.left V.hom (MorphismProperty.Over.w g))
    (Limits.pullback.lift_snd _ _ _)
  invFun h := MorphismProperty.Over.homMk
    (h.left ≫ Limits.pullback.fst X.obj.hom p)
    (((Category.assoc h.left (Limits.pullback.fst X.obj.hom p) X.obj.hom).trans
      (congrArg (h.left ≫ ·) Limits.pullback.condition)).trans
      (MorphismProperty.Over.w_assoc h p))
  left_inv g := by
    apply MorphismProperty.Over.Hom.ext
    exact Limits.pullback.lift_fst _ _ _
  right_inv h := by
    apply MorphismProperty.Over.Hom.ext
    refine Limits.pullback.hom_ext ?_ ?_
    · exact Limits.pullback.lift_fst _ _ _
    · exact (Limits.pullback.lift_snd _ _ _).trans (MorphismProperty.Over.w h).symm

/-- Underlying scheme morphism of `restrictSectionEquiv p X V g`. -/
@[simp]
lemma restrictSectionEquiv_apply_left (p : T ⟶ S) [Etale p]
    (X : FiniteEtaleScheme S) (V : T.Etale) (g : p.smallEtaleMap.obj V ⟶ (toEtale S).obj X) :
    (restrictSectionEquiv p X V g).left =
      Limits.pullback.lift g.left V.hom (MorphismProperty.Over.w g) := by
  rfl

/-- Underlying scheme morphism of `(restrictSectionEquiv p X V).symm h`. -/
@[simp]
lemma restrictSectionEquiv_symm_apply_left (p : T ⟶ S) [Etale p]
    (X : FiniteEtaleScheme S) (V : T.Etale) (h : V ⟶ (toEtale T).obj ((pullback p).obj X)) :
    ((restrictSectionEquiv p X V).symm h).left = h.left ≫ Limits.pullback.fst X.obj.hom p := by
  rfl

/-- Restricting the sheaf of sections of a finite étale `S`-scheme along an étale morphism
`p : T ⟶ S` via `p.smallEtaleMap` gives the sheaf of sections of its base change to `T`,
naturally in `X`. -/
noncomputable def toSheafCompSmallEtaleMapPushforwardIso (p : T ⟶ S) [Etale p] :
    toSheaf S ⋙ p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology T) (Scheme.smallEtaleTopology S) ≅
      pullback p ⋙ toSheaf T :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ <| NatIso.ofComponents
      (fun V ↦ (restrictSectionEquiv p X V.unop).toIso)
      (fun {V W} a ↦ by
        rcases V with ⟨V⟩; rcases W with ⟨W⟩
        ext g
        apply MorphismProperty.Over.Hom.ext
        refine Limits.pullback.hom_ext ?_ ?_
        · exact (Limits.pullback.lift_fst _ _ _).trans
            ((Category.assoc _ _ _).trans
              (congrArg (a.unop.left ≫ ·) (Limits.pullback.lift_fst _ _ _))).symm
        · exact (Limits.pullback.lift_snd _ _ _).trans
            ((MorphismProperty.Over.w a.unop).symm.trans
              ((Category.assoc _ _ _).trans
                (congrArg (a.unop.left ≫ ·) (Limits.pullback.lift_snd _ _ _))).symm)))
    (fun {X Y} f ↦ by
      ext ⟨V⟩ g
      apply MorphismProperty.Over.Hom.ext
      refine Limits.pullback.hom_ext ?_ ?_
      · exact (Limits.pullback.lift_fst _ _ _).trans <|
          ((Category.assoc _ _ _).trans <|
            (congrArg ((restrictSectionEquiv p X V g).left ≫ ·)
              (Limits.pullback.lift_fst _ _ _)).trans <|
              ((Category.assoc _ _ _).symm.trans <|
                congrArg (· ≫ f.hom.left) (Limits.pullback.lift_fst _ _ _))).symm
      · exact (Limits.pullback.lift_snd _ _ _).trans <|
          ((Category.assoc _ _ _).trans <|
            (congrArg ((restrictSectionEquiv p X V g).left ≫ ·)
              (Limits.pullback.lift_snd _ _ _)).trans <|
              Limits.pullback.lift_snd _ _ _).symm)

/-- Forward component formula for `toSheafCompSmallEtaleMapPushforwardIso`. -/
@[simp]
lemma toSheafCompSmallEtaleMapPushforwardIso_hom_app_hom_app (p : T ⟶ S) [Etale p]
    (X : FiniteEtaleScheme S) (V : T.Etale) :
    ((toSheafCompSmallEtaleMapPushforwardIso p).hom.app X).hom.app (op V) =
      TypeCat.ofHom (restrictSectionEquiv p X V) := by
  rfl

/-- Inverse component formula for `toSheafCompSmallEtaleMapPushforwardIso`. -/
@[simp]
lemma toSheafCompSmallEtaleMapPushforwardIso_inv_app_hom_app (p : T ⟶ S) [Etale p]
    (X : FiniteEtaleScheme S) (V : T.Etale) :
    ((toSheafCompSmallEtaleMapPushforwardIso p).inv.app X).hom.app (op V) =
      TypeCat.ofHom (restrictSectionEquiv p X V).symm := by
  rfl

/-- Pulling back the sheaf of sections of a finite étale `S`-scheme along an étale morphism
`p : T ⟶ S` gives the sheaf of sections of its base change to `T`, naturally in `X`. -/
noncomputable def toSheafCompSmallEtalePullbackIso (p : T ⟶ S) [Etale p] :
    toSheaf S ⋙ p.smallEtalePullback (Type u) ≅ pullback p ⋙ toSheaf T :=
  Functor.isoWhiskerLeft (toSheaf S) (p.smallEtalePullbackIsoMapPushforward (Type u)) ≪≫
    toSheafCompSmallEtaleMapPushforwardIso p

end RestrictSheaf

end TauCeti.FiniteEtaleScheme
