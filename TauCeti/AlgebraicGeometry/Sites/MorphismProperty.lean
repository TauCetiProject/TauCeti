/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.MorphismProperty.Local

/-!
# Locality of morphism properties for general scheme precoverages

Given a morphism property `Q` on `Scheme`, `Scheme.precoverage Q` is the precoverage of jointly
surjective families of `Q`-morphisms. This file records basic covering constructors and locality
consequences that hold for an arbitrary `Scheme.precoverage Q` without needing topology-specific
structure theorems.

## Main results

* `AlgebraicGeometry.Scheme.ofArrows_pair_mem_precoverage` and
  `AlgebraicGeometry.Scheme.ofArrows_id_mem_precoverage`: two `Q`-morphisms jointly covering a
  scheme (and in particular a single `Q`-morphism adjoined with the identity when
  `Q.ContainsIdentities`) form a two-arrow covering presieve in `Scheme.precoverage Q`.
* `CategoryTheory.MorphismProperty.of_isEmpty_of_isLocalAtSource_precoverage`: a property local at
  the source for `Scheme.precoverage Q` holds for every morphism out of an empty scheme.
* `CategoryTheory.MorphismProperty.respectsLeft_of_isLocalAtSource_precoverage` and
  `CategoryTheory.MorphismProperty.isStableUnderBaseChangeAgainst_of_isLocalAtTarget_precoverage`:
  source (resp. target) locality for `Scheme.precoverage Q` implies precomposition (resp. base
  change) stability along `Q` whenever `Q` contains identities.
* `CategoryTheory.MorphismProperty.of_isPullback_pair_of_isLocalAtSource_precoverage`: pulling back
  a two-arrow `Q`-cover along `q : X ⟶ Z` lets a `Scheme.precoverage Q`-source-local property be
  checked on the two pullback legs.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Two `Q`-morphisms `e₁ : U₁ ⟶ U` and `e₂ : U₂ ⟶ U` whose ranges cover `U` form a two-arrow
`Q`-covering presieve of `U`. -/
theorem ofArrows_pair_mem_precoverage {Q : MorphismProperty Scheme.{u}}
    {U₁ U₂ U : Scheme.{u}} (e₁ : U₁ ⟶ U) (e₂ : U₂ ⟶ U) (he₁ : Q e₁) (he₂ : Q e₂)
    (hcov : ∀ x : U, x ∈ Set.range e₁ ∨ x ∈ Set.range e₂) :
    Presieve.ofArrows (fun b : Bool ↦ cond b U₁ U₂)
      (fun b ↦ match b with | true => e₁ | false => e₂) ∈ Scheme.precoverage Q U :=
  (Scheme.ofArrows_mem_precoverage_iff Q).mpr
    ⟨fun x ↦ by
      rcases hcov x with hx | hx
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩,
     by rintro (_ | _); exacts [he₂, he₁]⟩

/-- Adding the identity arrow turns any `Q`-morphism `e : U' ⟶ U` into a two-arrow `Q`-covering
presieve of `U`. -/
theorem ofArrows_id_mem_precoverage {Q : MorphismProperty Scheme.{u}} [Q.ContainsIdentities]
    {U' U : Scheme.{u}} (e : U' ⟶ U) (he : Q e) :
    Presieve.ofArrows (fun b : Bool ↦ cond b U' U)
      (fun b ↦ match b with | true => e | false => 𝟙 U) ∈ Scheme.precoverage Q U :=
  ofArrows_pair_mem_precoverage e (𝟙 U) he (Q.id_mem U) fun x ↦ Or.inr ⟨x, rfl⟩

end AlgebraicGeometry.Scheme

namespace CategoryTheory.MorphismProperty

/-- If `P` is local at the source for `Scheme.precoverage Q`, any morphism out of an empty scheme
satisfies `P`. -/
theorem of_isEmpty_of_isLocalAtSource_precoverage {P : MorphismProperty Scheme.{u}}
    (Q : MorphismProperty Scheme.{u}) [P.IsLocalAtSource (Scheme.precoverage Q)]
    {U V : Scheme.{u}} (f : U ⟶ V) [IsEmpty U] : P f :=
  IsLocalAtSource.of_forall_comp (Scheme.bot_mem_precoverage Q U) fun _ _ hg ↦ False.elim hg

/-- If `P` is local at the source for `Scheme.precoverage Q` and `Q` contains identities, then `P`
respects precomposition with `Q`-morphisms. -/
theorem respectsLeft_of_isLocalAtSource_precoverage (P Q : MorphismProperty Scheme.{u})
    [Q.ContainsIdentities] [P.IsLocalAtSource (Scheme.precoverage Q)] : P.RespectsLeft Q where
  precomp e he _ hf :=
    IsLocalAtSource.comp (Scheme.ofArrows_id_mem_precoverage e he) e (.mk true) hf

/-- If `P` is local at the target for `Scheme.precoverage Q` and `Q` contains identities, then `P`
is stable under base change along `Q`-morphisms. -/
theorem isStableUnderBaseChangeAgainst_of_isLocalAtTarget_precoverage
    (P Q : MorphismProperty Scheme.{u}) [Q.ContainsIdentities]
    [P.IsLocalAtTarget (Scheme.precoverage Q)] : P.IsStableUnderBaseChangeAgainst Q where
  isStableUnderBaseChangeAlong {_ _} e he :=
    ⟨fun sq hf ↦
      have := sq.hasPullback
      (P.cancel_left_of_respectsIso sq.isoPullback.inv _).mp
        (by rw [sq.isoPullback_inv_snd]; exact
          IsLocalAtTarget.pullbackSnd (Scheme.ofArrows_id_mem_precoverage e he) (.mk true) hf)⟩

/-- If two `Q`-morphisms `e₁ : U₁ ⟶ Z` and `e₂ : U₂ ⟶ Z` jointly cover `Z` and
`Scheme.precoverage Q` is stable under base change, then a property `P` local at the source for
`Scheme.precoverage Q` holds for `g : X ⟶ Y` once it holds after precomposing with the pullback
legs `p₁`, `p₂` of `e₁`, `e₂` along any morphism `q : X ⟶ Z`. -/
theorem of_isPullback_pair_of_isLocalAtSource_precoverage {P Q : MorphismProperty Scheme.{u}}
    [P.IsLocalAtSource (Scheme.precoverage Q)] [(Scheme.precoverage Q).IsStableUnderBaseChange]
    {U₁ U₂ W₁ W₂ X Y Z : Scheme.{u}} {q : X ⟶ Z} {g : X ⟶ Y} {e₁ : U₁ ⟶ Z} {e₂ : U₂ ⟶ Z}
    {p₁ : W₁ ⟶ X} {r₁ : W₁ ⟶ U₁} {p₂ : W₂ ⟶ X} {r₂ : W₂ ⟶ U₂}
    (he₁ : Q e₁) (he₂ : Q e₂) (hcov : ∀ z : Z, z ∈ Set.range e₁ ∨ z ∈ Set.range e₂)
    (sq₁ : IsPullback p₁ r₁ q e₁) (sq₂ : IsPullback p₂ r₂ q e₂)
    (h₁ : P (p₁ ≫ g)) (h₂ : P (p₂ ≫ g)) : P g := by
  have hR := Scheme.ofArrows_pair_mem_precoverage e₁ e₂ he₁ he₂ hcov
  have hpb : Presieve.ofArrows (fun b : Bool ↦ cond b W₁ W₂)
      (fun b ↦ match b with | true => p₁ | false => p₂) ∈ Scheme.precoverage Q X :=
    Precoverage.mem_coverings_of_isPullback _ hR q _
      (fun b ↦ match b with | true => r₁ | false => r₂)
      (fun b ↦ match b with | true => sq₁ | false => sq₂)
  refine IsLocalAtSource.of_forall_comp hpb ?_
  rintro _ _ ⟨_ | _⟩
  · exact h₂
  · exact h₁

end CategoryTheory.MorphismProperty
