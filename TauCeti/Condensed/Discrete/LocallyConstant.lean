/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Discrete.LocallyConstant
public import Mathlib.Condensed.Functors
public import TauCeti.Topology.Category.Profinite.Basic

/-!
# Finite sets as discrete condensed sets

For a finite set `T`, the condensed set represented by the finite profinite set `T` is the
discrete condensed set on `T` (`TauCeti.toProfiniteCompProfiniteToCondensedIso`, natural in `T`):
on sections over a compact Hausdorff space `X`, a continuous map `X → T` is the same as a locally
constant one, since `T` is discrete.
-/

public section

universe u

open CategoryTheory Functor

noncomputable section

namespace TauCeti

open Condensed

/-- For a finite set `T`, the condensed set represented by the finite profinite set `T` is the
discrete condensed set on `T`: a continuous map from a compact Hausdorff space to the finite
discrete space `T` is the same as a locally constant one. -/
def toProfiniteCompProfiniteToCondensedIso :
    FintypeCat.toProfinite.{u} ⋙ profiniteToCondensed ≅
      FintypeCat.incl ⋙ uliftFunctor.{u + 1} ⋙ CondensedSet.LocallyConstant.functor :=
  NatIso.ofComponents (fun T ↦ ObjectProperty.isoMk _ <| NatIso.ofComponents (fun X ↦ Equiv.toIso
    { toFun (g : ULift.{u + 1} (X.unop ⟶ profiniteToCompHaus.obj (FintypeCat.toProfinite.obj T))) :=
        ⟨ULift.up ∘ g.down.hom.hom,
          ((IsLocallyConstant.iff_continuous _).2 g.down.hom.hom.continuous).comp _⟩
      invFun (f : LocallyConstant X.unop (ULift.{u + 1} T)) :=
        ⟨CompHausLike.ofHom _ ⟨ULift.down ∘ f, (f.isLocallyConstant.comp _).continuous⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }) fun _ ↦ rfl) fun _ ↦ rfl

/-- On sections over `X`, `toProfiniteCompProfiniteToCondensedIso` regards a continuous map
`X → T` as a locally constant one. -/
@[simp]
lemma toProfiniteCompProfiniteToCondensedIso_hom_hom_app_apply (T : FintypeCat.{u})
    (X : CompHaus.{u}ᵒᵖ)
    (g : ULift.{u + 1} (X.unop ⟶ profiniteToCompHaus.obj (FintypeCat.toProfinite.obj T)))
    (x : X.unop) :
    (dsimp% (toProfiniteCompProfiniteToCondensedIso.hom.app T).hom.app X g) x =
      ULift.up (g.down x) :=
  (rfl)

/-- On sections over `X`, the inverse of `toProfiniteCompProfiniteToCondensedIso` regards a
locally constant map `X → T` as a continuous one. -/
@[simp]
lemma toProfiniteCompProfiniteToCondensedIso_inv_hom_app_apply (T : FintypeCat.{u})
    (X : CompHaus.{u}ᵒᵖ) (f : LocallyConstant X.unop (ULift.{u + 1} T)) (x : X.unop) :
    (dsimp% ULift.down (α := X.unop ⟶ profiniteToCompHaus.obj (FintypeCat.toProfinite.obj T))
      ((toProfiniteCompProfiniteToCondensedIso.inv.app T).hom.app X f)) x =
      (f x).down :=
  (rfl)

end TauCeti
