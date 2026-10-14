/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Properties local at the target, for morphisms over a base

Let `P` be a property of morphisms of schemes which is local at the target in the Zariski
topology, and `g : X ⟶ Y` a morphism of schemes over `S`. Mathlib's
`AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover` tests `P g` on the pullbacks of `g`
along an open cover of `Y`. This file tests it instead on the base changes of `g` along an open
cover `𝒰` of `S`, that is on the morphisms `X ×_S Uᵢ ⟶ Y ×_S Uᵢ` given by `Over.pullback`.
This is the form needed to check a property of a morphism over `S`, for instance of a morphism
of descent data relative to `S' ⟶ S`, over the members of an affine open cover of `S`.

## Main statements

* `TauCeti.IsZariskiLocalAtTarget.iff_of_openCover_overPullback`: for `g : X ⟶ Y` over `S` and an
  open cover `𝒰` of `S`, `P g` holds if and only if `P` holds for every base change of `g` along
  a member of `𝒰`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

/-- A property of morphisms which is Zariski-local at the target holds for a morphism `g` over
`S` if and only if it holds for the base change `X ×_S Uᵢ ⟶ Y ×_S Uᵢ` of `g` along every member
`Uᵢ ⟶ S` of an open cover of `S`. -/
theorem IsZariskiLocalAtTarget.iff_of_openCover_overPullback
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P] {S : Scheme.{u}}
    (𝒰 : S.OpenCover) {X Y : Over S} (g : X ⟶ Y) :
    P g.left ↔ ∀ i, P ((Over.pullback (𝒰.f i)).map g).left := by
  -- The base change of `g` along `Uᵢ ⟶ S` is the pullback of `g` along the open immersion
  -- `Y ×_S Uᵢ ⟶ Y`, and these open immersions cover `Y`.
  have hsq (i) : IsPullback ((Over.pullback (𝒰.f i)).map g).left (pullback.fst _ _)
      (pullback.fst _ _) g.left := by
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback Y.hom (𝒰.f i)).flip
    simpa using (IsPullback.of_hasPullback X.hom (𝒰.f i)).flip
  refine ⟨fun h i ↦ IsZariskiLocalAtTarget.of_isPullback (hsq i).flip h, fun h ↦ ?_⟩
  refine IsZariskiLocalAtTarget.of_openCover (𝒰.pullback₁ Y.hom) fun i ↦ ?_
  exact (P.arrow_mk_iso_iff (Arrow.isoMk (hsq i).flip.isoPullback (Iso.refl _)
    (hsq i).flip.isoPullback_hom_snd)).mp (h i)

end TauCeti
