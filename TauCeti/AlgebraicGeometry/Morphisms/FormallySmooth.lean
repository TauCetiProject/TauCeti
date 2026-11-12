/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import TauCeti.AlgebraicGeometry.Morphisms.Thickening

/-!
# Formally smooth morphisms of schemes

A morphism of schemes `f : X ⟶ S` is *formally smooth* if it has the infinitesimal lifting
property: for every first-order thickening `i : T ⟶ T'` with `T'` affine, every morphism `T ⟶ X`
compatible with a morphism `T' ⟶ S` extends along `i` to at least one morphism `T' ⟶ X` over `S`
(Stacks, Definition 37.11.1 (02H0)). The test thickenings are Tau Ceti's
`IsFirstOrderThickening`: closed immersions whose ideal sheaf squares to zero.

## Main definitions

* `TauCeti.AlgebraicGeometry.FormallySmooth f`: lifts exist along affine first-order
  thickenings.

## Main results

* `TauCeti.AlgebraicGeometry.formallySmooth_eq_rlp`: the formally smooth morphisms are those with
  the right lifting property against first-order thickenings with affine target.
* Formally smooth morphisms contain the identities and are stable under composition, base change
  and restriction to open subschemes of the target.

## References

* [Stacks Project, Definition 37.11.1](https://stacks.math.columbia.edu/tag/02H0).
* [Stacks Project, Lemma 37.11.2](https://stacks.math.columbia.edu/tag/02H1), composition.
* [Stacks Project, Lemma 37.11.3](https://stacks.math.columbia.edu/tag/02H2), base change.
* [Stacks Project, Lemma 37.11.5](https://stacks.math.columbia.edu/tag/02H3), restriction to
  open subschemes.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ S` is *formally smooth* if for every first-order thickening
`i : T ⟶ T'` with `T'` affine, every morphism `g : T ⟶ X` with `g ≫ f = i ≫ h` for some
`h : T' ⟶ S` extends along `i` to a morphism `l : T' ⟶ X` over `S`. Stacks, Definition 37.11.1
(02H0). -/
@[stacks 02H0, mk_iff]
class FormallySmooth (f : X ⟶ S) : Prop where
  exists_lift : ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T') [IsFirstOrderThickening i]
    (g : T ⟶ X) (h : T' ⟶ S), g ≫ f = i ≫ h → ∃ l : T' ⟶ X, i ≫ l = g ∧ l ≫ f = h

/-- A formally smooth morphism has the right lifting property against every first-order
thickening with affine target. -/
instance FormallySmooth.hasLiftingProperty {T T' : Scheme.{u}} (i : T ⟶ T') [IsAffine T']
    [IsFirstOrderThickening i] (f : X ⟶ S) [FormallySmooth f] : HasLiftingProperty i f where
  sq_hasLift sq := by
    obtain ⟨l, hl, hl'⟩ := FormallySmooth.exists_lift i _ _ sq.w
    exact .mk' ⟨l, hl, hl'⟩

/-- The formally smooth morphisms are those with the right lifting property against first-order
thickenings with affine target. -/
theorem formallySmooth_eq_rlp :
    @FormallySmooth.{u} =
      rlp (fun _ T' i ↦ IsAffine T' ∧ IsFirstOrderThickening i : MorphismProperty Scheme.{u}) := by
  ext X S f
  refine ⟨fun _ T T' i ⟨_, _⟩ ↦ inferInstance, fun H ↦ ⟨fun i _ g h w ↦ ?_⟩⟩
  have := H i ⟨‹_›, ‹_›⟩
  have sq : CommSq g i f h := ⟨w⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

namespace FormallySmooth

-- The instances for `rlp` are not found by instance search through `formallySmooth_eq_rlp`, so
-- they are named explicitly.
instance isMultiplicative : IsMultiplicative @FormallySmooth.{u} :=
  formallySmooth_eq_rlp ▸ rlp_isMultiplicative _

instance isStableUnderComposition : IsStableUnderComposition @FormallySmooth.{u} :=
  isMultiplicative.toIsStableUnderComposition

instance isStableUnderBaseChange : IsStableUnderBaseChange @FormallySmooth.{u} :=
  formallySmooth_eq_rlp ▸ rlp_isStableUnderBaseChange _

instance respectsIso : RespectsIso @FormallySmooth.{u} :=
  IsStableUnderBaseChange.respectsIso

/-- A composite of formally smooth morphisms is formally smooth. -/
@[stacks 02H1]
instance comp (f : X ⟶ Y) (g : Y ⟶ S) [FormallySmooth f] [FormallySmooth g] :
    FormallySmooth (f ≫ g) :=
  comp_mem _ f g ‹_› ‹_›

/-- Formal smoothness is stable under base change. -/
@[stacks 02H2]
instance pullback_snd (f : X ⟶ S) (g : Y ⟶ S) [FormallySmooth f] :
    FormallySmooth (pullback.snd f g) :=
  of_isPullback (IsPullback.of_hasPullback f g) ‹_›

/-- Formal smoothness is stable under base change, on the other side. -/
instance pullback_fst (f : X ⟶ S) (g : Y ⟶ S) [FormallySmooth g] :
    FormallySmooth (pullback.fst f g) :=
  of_isPullback (IsPullback.of_hasPullback f g).flip ‹_›

/-- The restriction of a formally smooth morphism over an open subscheme of the target is formally
smooth. -/
@[stacks 02H3]
instance restrict (f : X ⟶ S) [FormallySmooth f] (U : S.Opens) : FormallySmooth (f ∣_ U) :=
  of_isPullback (isPullback_morphismRestrict f U).flip ‹_›

end FormallySmooth

end TauCeti.AlgebraicGeometry
