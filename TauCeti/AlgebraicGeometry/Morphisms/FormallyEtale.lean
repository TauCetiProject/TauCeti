/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth

/-!
# Formally étale morphisms of schemes

A morphism of schemes `f : X ⟶ S` is *formally étale* if for every first-order thickening
`i : T ⟶ T'` with `T'` affine, every morphism `T ⟶ X` compatible with a morphism `T' ⟶ S` extends
along `i` to exactly one morphism `T' ⟶ X` over `S` (Stacks, Definition 37.8.1 (02HG)).

Uniqueness of such lifts is Mathlib's `AlgebraicGeometry.FormallyUnramified`
(`formallyUnramified_iff_hom_ext`), so a morphism is formally étale exactly when it is formally
smooth and formally unramified.

## Main definitions

* `TauCeti.AlgebraicGeometry.FormallyEtale f`: lifts exist and are unique along affine
  first-order thickenings.

## Main results

* `TauCeti.AlgebraicGeometry.formallyUnramified_iff_hom_ext`: `f` is formally unramified exactly
  when lifts along affine first-order thickenings are unique.
* `TauCeti.AlgebraicGeometry.FormallyEtale.iff_formallySmooth_and_formallyUnramified`: `f` is
  formally étale exactly when it is formally smooth and formally unramified.
* `TauCeti.AlgebraicGeometry.FormallyEtale.of_isOpenImmersion`: an open immersion is formally
  étale.
* Formally étale morphisms are stable under composition, base change and restriction to open
  subschemes of the target.

## References

* [Stacks Project, Definition 37.8.1](https://stacks.math.columbia.edu/tag/02HG).
* [Stacks Project, Lemma 37.8.3](https://stacks.math.columbia.edu/tag/02HI), composition.
* [Stacks Project, Lemma 37.8.4](https://stacks.math.columbia.edu/tag/02HJ), base change.
* [Stacks Project, Lemma 37.8.5](https://stacks.math.columbia.edu/tag/02HK), restriction to
  open subschemes.
* [Stacks Project, Lemma 37.11.4](https://stacks.math.columbia.edu/tag/02HH), formally étale
  is formally smooth and formally unramified.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ S` is *formally étale* if lifts as in `FormallySmooth` exist
and are unique. Stacks, Definition 37.8.1 (02HG). -/
@[stacks 02HG, mk_iff]
class FormallyEtale (f : X ⟶ S) : Prop where
  existsUnique_lift : ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T')
    [IsFirstOrderThickening i] (g : T ⟶ X) (h : T' ⟶ S), g ≫ f = i ≫ h →
      ∃! l : T' ⟶ X, i ≫ l = g ∧ l ≫ f = h

/-- A morphism is formally unramified exactly when lifts along first-order thickenings with
affine target are unique. -/
theorem formallyUnramified_iff_hom_ext (f : X ⟶ S) :
    FormallyUnramified f ↔
      ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T') [IsFirstOrderThickening i]
        (l₁ l₂ : T' ⟶ X), i ≫ l₁ = i ≫ l₂ → l₁ ≫ f = l₂ ≫ f → l₁ = l₂ := by
  refine ⟨fun _ _ _ _ i _ _ _ h₁ h₂ ↦ FormallyUnramified.hom_ext i
    ⟨2, by rw [pow_two, IsFirstOrderThickening.ker_mul_self]; rfl⟩ f h₁ h₂,
    fun H ↦ FormallyUnramified.of_hom_ext f fun _ _ φ hφ hker _ _ h₁ h₂ ↦ ?_⟩
  have := (IsFirstOrderThickening.SpecMap_iff φ hφ).mpr (by rwa [← pow_two])
  exact H (Spec.map φ) _ _ h₁ h₂

namespace FormallyEtale

/-- A morphism is formally étale exactly when it is formally smooth and formally unramified.
Stacks, Lemma 37.11.4 (02HH). -/
@[stacks 02HH]
theorem iff_formallySmooth_and_formallyUnramified (f : X ⟶ S) :
    FormallyEtale f ↔ FormallySmooth f ∧ FormallyUnramified f := by
  rw [formallyUnramified_iff_hom_ext]
  refine ⟨fun hf ↦ ⟨⟨fun i _ g h w ↦ (hf.existsUnique_lift i g h w).exists⟩,
    fun i _ l₁ l₂ h₁ h₂ ↦ (hf.existsUnique_lift i (i ≫ l₁) (l₁ ≫ f) (Category.assoc _ _ _)).unique
      ⟨rfl, rfl⟩ ⟨h₁.symm, h₂.symm⟩⟩, fun ⟨hs, hu⟩ ↦ ⟨fun i _ g h w ↦ ?_⟩⟩
  obtain ⟨l, hl, hl'⟩ := hs.exists_lift i g h w
  exact ⟨l, ⟨hl, hl'⟩, fun l' ⟨hl₁, hl₂⟩ ↦ hu i l' l (hl₁.trans hl.symm) (hl₂.trans hl'.symm)⟩

/-- A formally étale morphism is formally smooth. -/
instance (priority := 100) formallySmooth (f : X ⟶ S) [FormallyEtale f] : FormallySmooth f :=
  ((iff_formallySmooth_and_formallyUnramified f).mp ‹_›).1

/-- A formally étale morphism is formally unramified. -/
instance (priority := 100) formallyUnramified (f : X ⟶ S) [FormallyEtale f] :
    FormallyUnramified f :=
  ((iff_formallySmooth_and_formallyUnramified f).mp ‹_›).2

/-- An open immersion is formally étale. -/
instance (priority := 900) of_isOpenImmersion (f : X ⟶ S) [IsOpenImmersion f] :
    FormallyEtale f where
  existsUnique_lift i _ g h w := by
    -- A thickening is surjective, so `h` lands in the image of `f`.
    have hrange : Set.range h ⊆ Set.range f := by
      rintro _ ⟨t', rfl⟩
      obtain ⟨t, rfl⟩ := i.surjective t'
      exact ⟨g t, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩
    refine ⟨IsOpenImmersion.lift f h hrange, ⟨?_, IsOpenImmersion.lift_fac _ _ _⟩,
      fun l ⟨_, hl⟩ ↦ IsOpenImmersion.lift_uniq _ _ _ l hl⟩
    rw [← cancel_mono f, Category.assoc, IsOpenImmersion.lift_fac, w]

end FormallyEtale

/-- The formally étale morphisms are those that are formally smooth and formally unramified. -/
theorem formallyEtale_eq :
    @FormallyEtale.{u} = (@FormallySmooth ⊓ @FormallyUnramified : MorphismProperty Scheme.{u}) := by
  ext X S f
  exact FormallyEtale.iff_formallySmooth_and_formallyUnramified f

namespace FormallyEtale

-- The instances for `⊓` are not found by instance search through `formallyEtale_eq`, so they are
-- named explicitly.
instance isMultiplicative : IsMultiplicative @FormallyEtale.{u} :=
  formallyEtale_eq ▸ IsMultiplicative.inf

instance isStableUnderComposition : IsStableUnderComposition @FormallyEtale.{u} :=
  isMultiplicative.toIsStableUnderComposition

instance isStableUnderBaseChange : IsStableUnderBaseChange @FormallyEtale.{u} :=
  formallyEtale_eq ▸ IsStableUnderBaseChange.inf

instance respectsIso : RespectsIso @FormallyEtale.{u} :=
  IsStableUnderBaseChange.respectsIso

/-- A composite of formally étale morphisms is formally étale. -/
@[stacks 02HI]
instance comp (f : X ⟶ Y) (g : Y ⟶ S) [FormallyEtale f] [FormallyEtale g] :
    FormallyEtale (f ≫ g) :=
  comp_mem _ f g ‹_› ‹_›

/-- Formal étaleness is stable under base change. -/
@[stacks 02HJ]
instance pullback_snd (f : X ⟶ S) (g : Y ⟶ S) [FormallyEtale f] :
    FormallyEtale (pullback.snd f g) :=
  of_isPullback (IsPullback.of_hasPullback f g) ‹_›

/-- Formal étaleness is stable under base change, on the other side. -/
instance pullback_fst (f : X ⟶ S) (g : Y ⟶ S) [FormallyEtale g] :
    FormallyEtale (pullback.fst f g) :=
  of_isPullback (IsPullback.of_hasPullback f g).flip ‹_›

/-- The restriction of a formally étale morphism over an open subscheme of the target is formally
étale. -/
@[stacks 02HK]
instance restrict (f : X ⟶ S) [FormallyEtale f] (U : S.Opens) : FormallyEtale (f ∣_ U) :=
  of_isPullback (isPullback_morphismRestrict f U).flip ‹_›

end FormallyEtale

/-- Lifts of a square along a first-order thickening through a formally unramified morphism are
unique. -/
instance (priority := 100) subsingleton_liftStruct_of_formallyUnramified {T T' : Scheme.{u}}
    {i : T ⟶ T'} [IsFirstOrderThickening i] {f : X ⟶ S} [FormallyUnramified f] {g : T ⟶ X}
    {h : T' ⟶ S} (sq : CommSq g i f h) : Subsingleton sq.LiftStruct :=
  ⟨fun l₁ l₂ ↦ CommSq.LiftStruct.ext <| FormallyUnramified.hom_ext i
    ⟨2, by rw [pow_two, IsFirstOrderThickening.ker_mul_self]; rfl⟩ f
    (l₁.fac_left.trans l₂.fac_left.symm) (l₁.fac_right.trans l₂.fac_right.symm)⟩

end TauCeti.AlgebraicGeometry
