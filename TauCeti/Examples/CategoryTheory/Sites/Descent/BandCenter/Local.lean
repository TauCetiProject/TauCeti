/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Local

/-!
# Checks for the local determination of central sections

* On a gerbe, if one object `x` over `U` has only the identity automorphism, there is only the
  identity central section over `U`: evaluation at `x` is injective.
* On a prestack, evaluations that agree after pullback along the maximal sieve agree.
-/

public section

namespace TauCeti.Examples.BandCenterLocal

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory IntrinsicBandSections

variable {C : Type*} [Category* C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {J : GrothendieckTopology C}
  {U : C}

/-- On a gerbe, an object with trivial automorphism group forces the central sections to be
trivial. -/
example [F.IsGerbe J] (x : F.obj (.mk (op U))) [Subsingleton (Aut x)] :
    Subsingleton (IntrinsicBandSections F U) :=
  ⟨fun _ _ ↦ evaluation_injective (J := J) x (Subsingleton.elim _ _)⟩

/-- On a prestack, evaluations agreeing along the maximal sieve agree. -/
example [F.IsPrestack J] {V : C} (a : V ⟶ U) (x : F.obj (.mk (op V)))
    {s t : IntrinsicBandSections F U}
    (h : ∀ ⦃W : C⦄ (g : W ⟶ V), evaluation (g ≫ a) ((F.map g.op.toLoc).toFunctor.obj x) s =
      evaluation (g ≫ a) ((F.map g.op.toLoc).toFunctor.obj x) t) :
    evaluation a x s = evaluation a x t :=
  evaluation_eq_of_cover a x (J.top_mem V) fun _ g _ ↦ h g

end TauCeti.Examples.BandCenterLocal
