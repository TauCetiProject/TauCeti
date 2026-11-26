/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
import TauCeti.AlgebraicGeometry.Sites.MorphismProperty

/-!
# Zariski-local morphism properties and open-immersion stability

This file records supplementary API for `AlgebraicGeometry.IsZariskiLocalAtSource` and
postcomposition stability with open immersions
(`MorphismProperty.RespectsRight _ @IsOpenImmersion`), mirroring
`Mathlib.AlgebraicGeometry.Morphisms.Basic`.

## Main results

* `AlgebraicGeometry.IsZariskiLocalAtSource.respectsRight_isOpenImmersion`: any multiplicative
  Zariski-local-at-source property respects postcomposition with open immersions.
* `AlgebraicGeometry.respectsRight_isOpenImmersion_of_respects`: projects two-sided open-immersion
  stability of a raw scheme morphism predicate to `RespectsRight _ @IsOpenImmersion`.
* `AlgebraicGeometry.IsZariskiLocalAtSource.of_isPullback_pair` and
  `AlgebraicGeometry.IsZariskiLocalAtSource.of_pullback_pair`: a Zariski-local-at-source property
  holds for `g : X ⟶ Y` once it holds after pulling back two open immersions covering `Z` along
  any morphism `q : X ⟶ Z`.
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- If `P` is Zariski-local at the source and multiplicative, then `P` respects postcomposition
with open immersions. -/
instance IsZariskiLocalAtSource.respectsRight_isOpenImmersion
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P] [P.IsMultiplicative] :
    P.RespectsRight @IsOpenImmersion where
  postcomp i _ _ hf := P.comp_mem _ i hf (IsZariskiLocalAtSource.of_isOpenImmersion i)

/-- Two-sided open-immersion stability for a raw scheme morphism predicate supplies
`RespectsRight _ @IsOpenImmersion` at `instances` transparency. -/
instance respectsRight_isOpenImmersion_of_respects
    (P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop)
    [MorphismProperty.Respects P @IsOpenImmersion] :
    MorphismProperty.RespectsRight P @IsOpenImmersion :=
  ‹MorphismProperty.Respects P @IsOpenImmersion›.toRespectsRight

/-- If two open immersions `i₁ : U₁ ⟶ Z` and `i₂ : U₂ ⟶ Z` cover `Z`, then a
Zariski-local-at-source property `P` holds for `g : X ⟶ Y` once it holds after precomposing with
the pullback legs `p₁`, `p₂` of `i₁`, `i₂` along any morphism `q : X ⟶ Z`. -/
theorem IsZariskiLocalAtSource.of_isPullback_pair {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] {U₁ U₂ W₁ W₂ X Y Z : Scheme.{u}} {q : X ⟶ Z} {g : X ⟶ Y}
    {i₁ : U₁ ⟶ Z} {i₂ : U₂ ⟶ Z} {p₁ : W₁ ⟶ X} {r₁ : W₁ ⟶ U₁} {p₂ : W₂ ⟶ X} {r₂ : W₂ ⟶ U₂}
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (hcov : ∀ z : Z, z ∈ Set.range i₁ ∨ z ∈ Set.range i₂)
    (sq₁ : IsPullback p₁ r₁ q i₁) (sq₂ : IsPullback p₂ r₂ q i₂)
    (h₁ : P (p₁ ≫ g)) (h₂ : P (p₂ ≫ g)) : P g :=
  MorphismProperty.of_isPullback_pair_of_isLocalAtSource_precoverage
    (P := P) (Q := @IsOpenImmersion) inferInstance inferInstance hcov sq₁ sq₂ h₁ h₂

/-- Canonical pullback form of `IsZariskiLocalAtSource.of_isPullback_pair`: if two open immersions
`i₁ : U₁ ⟶ Z` and `i₂ : U₂ ⟶ Z` cover `Z`, then a Zariski-local-at-source property `P` holds for
`g : X ⟶ Y` once it holds after precomposing with `pullback.fst q i₁` and `pullback.fst q i₂`. -/
theorem IsZariskiLocalAtSource.of_pullback_pair {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] {U₁ U₂ X Y Z : Scheme.{u}} {g : X ⟶ Y} (q : X ⟶ Z)
    (i₁ : U₁ ⟶ Z) (i₂ : U₂ ⟶ Z) [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (hcov : ∀ z : Z, z ∈ Set.range i₁ ∨ z ∈ Set.range i₂)
    (h₁ : P (pullback.fst q i₁ ≫ g)) (h₂ : P (pullback.fst q i₂ ≫ g)) : P g :=
  of_isPullback_pair hcov (.of_hasPullback q i₁) (.of_hasPullback q i₂) h₁ h₂

end AlgebraicGeometry
