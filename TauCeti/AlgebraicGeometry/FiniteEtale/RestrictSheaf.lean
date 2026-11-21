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
`TauCeti.FiniteEtaleScheme.toSheafCompSmallEtalePullbackIso`).

## Main definitions

* `TauCeti.FiniteEtaleScheme.trivialCover`: the finite étale cover of `S` given by a finite
  coproduct of copies of `S`.
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
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (toSheaf S)
  ((isTerminalOfHomId S).isTerminalObj (toSheaf S)).uniqueUpToIso
      (Sheaf.isTerminalTerminal (Scheme.smallEtaleTopology S) Types.isTerminalPUnit.{u}) ≪≫
    (asIso ((sheafificationAdjunction (Scheme.smallEtaleTopology S) (Type u)).counit.app
      (Sheaf.terminal (Scheme.smallEtaleTopology S) Types.isTerminalPUnit.{u}))).symm

/-- The sheaf of sections of `trivialCover S M` is the constant étale sheaf with value `M`. -/
noncomputable def toSheafTrivialCoverIso (M : Type u) [Finite M] :
    (toSheaf S).obj (trivialCover S M) ≅
      (constantSheaf (Scheme.smallEtaleTopology S) (Type u)).obj M :=
  haveI : Fintype M := Fintype.ofFinite M
  have := hasColimitsOfShape_of_hasFiniteColimits
    (C := Sheaf (Scheme.smallEtaleTopology S) (Type u)) (Discrete M)
  have := (constantSheafAdj (Scheme.smallEtaleTopology S) (Type u)
      (Scheme.Etale.mkIdTerminal S)).isLeftAdjoint
  PreservesCoproduct.iso (toSheaf S) _ ≪≫
    Sigma.mapIso (fun _ ↦ toSheafOfHomIdIso S) ≪≫
    (PreservesCoproduct.iso (constantSheaf (Scheme.smallEtaleTopology S) (Type u)) _).symm ≪≫
    (constantSheaf (Scheme.smallEtaleTopology S) (Type u)).mapIso
      (Types.coproductIso _ ≪≫ Equiv.toIso (Equiv.sigmaPUnit M))

end TrivialCover

section RestrictSheaf

variable {S T : Scheme.{u}}

/-- Restricting the sheaf of sections of a finite étale `S`-scheme along an étale morphism
`p : T ⟶ S` via `p.smallEtaleMap` gives the sheaf of sections of its base change to `T`,
naturally in `X`. -/
noncomputable def toSheafCompSmallEtaleMapPushforwardIso (p : T ⟶ S) [Etale p] :
    toSheaf S ⋙ p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology T) (Scheme.smallEtaleTopology S) ≅
      pullback p ⋙ toSheaf T :=
  let eBC : toEtale S ⋙ p.smallEtaleBaseChange ≅ pullback p ⋙ toEtale T :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext; rfl)
  ((fullyFaithfulSheafToPresheaf (Scheme.smallEtaleTopology T) (Type u)).whiskeringRight _)
    |>.preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (toSheaf S)
        (p.smallEtaleMap.sheafPushforwardContinuousCompSheafToPresheafIso (Type u)
          (Scheme.smallEtaleTopology T) (Scheme.smallEtaleTopology S)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (toEtale S)
            (Scheme.smallEtaleTopology S).yonedaCompSheafToPresheaf)
        _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (toEtale S) p.smallEtaleMapBaseChangeAdj.compYonedaIso.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eBC yoneda ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (pullback p)
        (Functor.isoWhiskerLeft (toEtale T)
          (Scheme.smallEtaleTopology T).yonedaCompSheafToPresheaf.symm) ≪≫
      (Functor.associator _ _ _).symm)

/-- Pulling back the sheaf of sections of a finite étale `S`-scheme along an étale morphism
`p : T ⟶ S` gives the sheaf of sections of its base change to `T`, naturally in `X`. -/
noncomputable def toSheafCompSmallEtalePullbackIso (p : T ⟶ S) [Etale p] :
    toSheaf S ⋙ p.smallEtalePullback (Type u) ≅ pullback p ⋙ toSheaf T :=
  Functor.isoWhiskerLeft (toSheaf S) (p.smallEtalePullbackIsoMapPushforward (Type u)) ≪≫
    toSheafCompSmallEtaleMapPushforwardIso p

end RestrictSheaf

end TauCeti.FiniteEtaleScheme
