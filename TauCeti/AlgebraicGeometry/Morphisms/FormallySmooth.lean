/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Thickening

/-!
# Formally smooth and formally étale morphisms of schemes

A morphism of schemes `f : X ⟶ S` is *formally smooth* if it has the infinitesimal lifting
property: for every first-order thickening `i : T ⟶ T'` with `T'` affine, every morphism `T ⟶ X`
compatible with a morphism `T' ⟶ S` extends along `i` to at least one morphism `T' ⟶ X` over `S`.
It is *formally étale* if such an extension always exists and is unique (Stacks,
Definitions 37.11.1 (02H0) and 37.8.1 (02HG)). The test thickenings are Tau Ceti's
`IsFirstOrderThickening`: closed immersions whose ideal sheaf squares to zero.

## Main definitions

* `TauCeti.AlgebraicGeometry.FormallySmooth f`: lifts exist along affine first-order
  thickenings.
* `TauCeti.AlgebraicGeometry.FormallyEtale f`: lifts exist and are unique along affine
  first-order thickenings.

## Main results

* Isomorphisms are formally smooth and formally étale, and both classes are stable under
  composition and base change.
* `TauCeti.AlgebraicGeometry.FormallyEtale.formallySmooth`: a formally étale morphism is formally
  smooth.
* `TauCeti.AlgebraicGeometry.formallyEtale_iff`: `f` is formally étale exactly when it is formally
  smooth and lifts along affine first-order thickenings are unique.

## References

* [Stacks Project, Definition 37.11.1](https://stacks.math.columbia.edu/tag/02H0).
* [Stacks Project, Definition 37.8.1](https://stacks.math.columbia.edu/tag/02HG).
* [Stacks Project, Lemmas 37.11.4 and 37.11.5](https://stacks.math.columbia.edu/tag/02HH), for
  composition and base change.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ S` is *formally smooth* if for every first-order thickening
`i : T ⟶ T'` with `T'` affine, every morphism `g : T ⟶ X` with `g ≫ f = i ≫ h` for some
`h : T' ⟶ S` extends along `i` to a morphism `l : T' ⟶ X` over `S`. Stacks, Definition 37.11.1
(02H0). -/
@[stacks 02H0]
class FormallySmooth (f : X ⟶ S) : Prop where
  exists_lift : ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T') [IsFirstOrderThickening i]
    (g : T ⟶ X) (h : T' ⟶ S), g ≫ f = i ≫ h → ∃ l : T' ⟶ X, i ≫ l = g ∧ l ≫ f = h

/-- A morphism of schemes `f : X ⟶ S` is *formally étale* if lifts as in `FormallySmooth` exist
and are unique. Stacks, Definition 37.8.1 (02HG). -/
@[stacks 02HG]
class FormallyEtale (f : X ⟶ S) : Prop where
  existsUnique_lift : ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T')
    [IsFirstOrderThickening i] (g : T ⟶ X) (h : T' ⟶ S), g ≫ f = i ≫ h →
      ∃! l : T' ⟶ X, i ≫ l = g ∧ l ≫ f = h

namespace FormallySmooth

/-- An isomorphism is formally smooth: the lift is `h ≫ f⁻¹`. -/
instance (priority := 100) of_isIso (f : X ⟶ S) [IsIso f] : FormallySmooth f where
  exists_lift i _ g h w := ⟨h ≫ inv f, by rw [← Category.assoc, ← w, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id], by simp⟩

/-- A composite of formally smooth morphisms is formally smooth: lift through the second
morphism, then through the first. -/
instance comp (f : X ⟶ Y) (g : Y ⟶ S) [FormallySmooth f] [FormallySmooth g] :
    FormallySmooth (f ≫ g) where
  exists_lift i _ a h w := by
    obtain ⟨l₁, hl₁, hl₁'⟩ := exists_lift (f := g) i (a ≫ f) h (by rw [Category.assoc, w])
    obtain ⟨l₂, hl₂, hl₂'⟩ := exists_lift (f := f) i a l₁ hl₁.symm
    exact ⟨l₂, hl₂, by rw [← Category.assoc, hl₂', hl₁']⟩

/-- Formal smoothness is stable under base change: lift into `X` and pair with the given map to
`Y`. -/
instance pullback_snd (f : X ⟶ S) (g : Y ⟶ S) [FormallySmooth f] :
    FormallySmooth (pullback.snd f g) where
  exists_lift i _ a h w := by
    obtain ⟨l, hl, hl'⟩ := exists_lift (f := f) i (a ≫ pullback.fst f g) (h ≫ g) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, w, Category.assoc])
    refine ⟨pullback.lift l h (by rw [hl']), ?_, by simp⟩
    apply pullback.hom_ext <;> simp [hl, w]

/-- Formal smoothness is stable under base change, on the other side. -/
instance pullback_fst (f : X ⟶ S) (g : Y ⟶ S) [FormallySmooth g] :
    FormallySmooth (pullback.fst f g) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

end FormallySmooth

namespace FormallyEtale

/-- A formally étale morphism is formally smooth. -/
instance (priority := 100) formallySmooth (f : X ⟶ S) [FormallyEtale f] : FormallySmooth f where
  exists_lift i _ g h w := (existsUnique_lift i g h w).exists

/-- Lifts along an affine first-order thickening through a formally étale morphism are unique. -/
theorem lift_unique (f : X ⟶ S) [FormallyEtale f] {T T' : Scheme.{u}} [IsAffine T']
    (i : T ⟶ T') [IsFirstOrderThickening i] {l₁ l₂ : T' ⟶ X} (h₁ : i ≫ l₁ = i ≫ l₂)
    (h₂ : l₁ ≫ f = l₂ ≫ f) : l₁ = l₂ :=
  (existsUnique_lift (f := f) i (i ≫ l₁) (l₁ ≫ f) (Category.assoc _ _ _)).unique
    ⟨rfl, rfl⟩ ⟨h₁.symm, h₂.symm⟩

end FormallyEtale

/-- A morphism is formally étale exactly when it is formally smooth and lifts along affine
first-order thickenings are unique. -/
theorem formallyEtale_iff (f : X ⟶ S) :
    FormallyEtale f ↔ FormallySmooth f ∧
      ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T') [IsFirstOrderThickening i]
        (l₁ l₂ : T' ⟶ X), i ≫ l₁ = i ≫ l₂ → l₁ ≫ f = l₂ ≫ f → l₁ = l₂ := by
  refine ⟨fun _ ↦ ⟨inferInstance, fun i _ _ _ h₁ h₂ ↦ FormallyEtale.lift_unique f i h₁ h₂⟩,
    fun ⟨hs, hu⟩ ↦ ⟨fun i _ g h w ↦ ?_⟩⟩
  obtain ⟨l, hl, hl'⟩ := hs.exists_lift i g h w
  exact ⟨l, ⟨hl, hl'⟩, fun l' ⟨hl₁, hl₂⟩ ↦ hu i l' l (hl₁.trans hl.symm) (hl₂.trans hl'.symm)⟩

namespace FormallyEtale

/-- An isomorphism is formally étale. -/
instance (priority := 100) of_isIso (f : X ⟶ S) [IsIso f] : FormallyEtale f :=
  (formallyEtale_iff f).mpr ⟨inferInstance, fun _ _ _ _ _ h ↦ by simpa using h =≫ inv f⟩

/-- A composite of formally étale morphisms is formally étale. -/
instance comp (f : X ⟶ Y) (g : Y ⟶ S) [FormallyEtale f] [FormallyEtale g] :
    FormallyEtale (f ≫ g) := by
  refine (formallyEtale_iff _).mpr ⟨inferInstance, fun i _ l₁ l₂ h₁ h₂ ↦ ?_⟩
  have h₂' : l₁ ≫ f = l₂ ≫ f := lift_unique g i (by simp [reassoc_of% h₁]) (by simpa using h₂)
  exact lift_unique f i h₁ h₂'

/-- Formal étaleness is stable under base change. -/
instance pullback_snd (f : X ⟶ S) (g : Y ⟶ S) [FormallyEtale f] :
    FormallyEtale (pullback.snd f g) := by
  refine (formallyEtale_iff _).mpr ⟨inferInstance, fun i _ l₁ l₂ h₁ h₂ ↦ ?_⟩
  have h : l₁ ≫ pullback.fst f g = l₂ ≫ pullback.fst f g :=
    lift_unique f i (by simp [reassoc_of% h₁]) (by simp [pullback.condition, reassoc_of% h₂])
  exact pullback.hom_ext h h₂

/-- Formal étaleness is stable under base change, on the other side. -/
instance pullback_fst (f : X ⟶ S) (g : Y ⟶ S) [FormallyEtale g] :
    FormallyEtale (pullback.fst f g) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

end FormallyEtale

end TauCeti.AlgebraicGeometry
