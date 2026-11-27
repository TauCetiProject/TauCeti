/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Sums.Basic
public import Mathlib.Data.ZMod.Basic
public import TauCeti.CategoryTheory.Sites.Descent.BandFixtures.Restriction

/-!
# Checks for the central sections of a varying one-object diagram

On the chain site `(Fin 3)ᵒᵖ` with coefficients `C₄ → C₂ → C₂` (reduction mod 2, then the
identity), written additively as `ZMod 4` and `ZMod 2`:

* restriction of compatible central sections sends the generator over the source to the generator
  over the target, along the composite as along the two successive arrows;
* it kills the coefficient `2` of `C₄`, so it is not injective;
* there are four compatible sections over the `C₄` object and two over a `C₂` object;
* the diagram is a gerbe for the bottom topology.

On the site of two disjoint chains, which has no terminal object, the compatible sections at every
object are the coefficients and the diagram is a gerbe for the bottom topology.
-/

public section

namespace TauCeti.Examples.RestrictionBandFixtures

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.RestrictionBandFixtures IntrinsicBandSections

/-- Reduction mod 2 as a homomorphism `C₄ → C₂` of multiplicative groups. -/
abbrev reduction : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)).toAddMonoidHom.toMultiplicative

/-- The coefficient chain `C₄ → C₂ → C₂`. -/
abbrev chainGroups : Fin 3 ⥤ CommGrpCat :=
  ComposableArrows.mk₂ (CommGrpCat.ofHom reduction)
    (𝟙 (CommGrpCat.of (Multiplicative (ZMod 2))))

/-- The chain site `(Fin 3)ᵒᵖ`. -/
abbrev ChainSite := (Fin 3)ᵒᵖ

/-- The chain coefficients as a presheaf on the chain site. -/
abbrev chainPresheaf : ChainSiteᵒᵖ ⥤ CommGrpCat := unopUnop (Fin 3) ⋙ chainGroups

/-- The one-object diagram of the chain coefficients. -/
abbrev chainF := groupDiagram chainPresheaf

/-- The `C₄` object of the chain site. -/
abbrev U₀ : ChainSite := op (0 : Fin 3)

/-- The first `C₂` object of the chain site. -/
abbrev U₁ : ChainSite := op (1 : Fin 3)

/-- The second `C₂` object of the chain site. -/
abbrev U₂ : ChainSite := op (2 : Fin 3)

/-- The arrow `U₁ ⟶ U₀`, along which coefficients are reduced mod 2. -/
abbrev f₀₁ : U₁ ⟶ U₀ := (homOfLE (show (0 : Fin 3) ≤ 1 by decide)).op

/-- The arrow `U₂ ⟶ U₁`, along which coefficients are kept. -/
abbrev f₁₂ : U₂ ⟶ U₁ := (homOfLE (show (1 : Fin 3) ≤ 2 by decide)).op

/-- The coefficient `g` of `C₄`, as an element of the coefficients over `U₀`. -/
abbrev c₄ (g : ZMod 4) : chainPresheaf.obj (op U₀) := Multiplicative.ofAdd g

/-- The coefficient `g` of `C₂`, as an element of the coefficients over `U₁`. -/
abbrev c₂ (g : ZMod 2) : chainPresheaf.obj (op U₁) := Multiplicative.ofAdd g

/-- Restriction along `U₁ ⟶ U₀` reduces coefficients mod 2. -/
theorem chainPresheaf_map_f₀₁ (g : ZMod 4) :
    chainPresheaf.map f₀₁.op (c₄ g) = c₂ (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2) g) :=
  rfl

/-- Restriction sends the section of the generator over `U₀` to the section of the generator over
`U₁`. -/
theorem chain_generator_restrict : restrict f₀₁ (groupSection chainPresheaf U₀ (c₄ 1)) =
    groupSection chainPresheaf U₁ (c₂ 1) := by
  rw [restrict_groupSection, chainPresheaf_map_f₀₁, map_one]

/-- Successive restrictions along `U₂ ⟶ U₁ ⟶ U₀` agree with restriction along the composite. -/
theorem chain_generator_comp :
    restrict f₁₂ (restrict f₀₁ (groupSection chainPresheaf U₀ (c₄ 1))) =
    restrict (f₁₂ ≫ f₀₁) (groupSection chainPresheaf U₀ (c₄ 1)) :=
  restrict_comp _ _ _

/-- Restriction along `U₁ ⟶ U₀` kills the section of the coefficient `2` of `C₄`. -/
theorem chain_two_killed : restrict f₀₁ (groupSection chainPresheaf U₀ (c₄ 2)) = 1 := by
  -- Reduction mod 2 sends `2` to `0`, and `c₂ 0` unfolds (`c₂` is an abbreviation) to
  -- `Multiplicative.ofAdd 0 = 1`.
  have h₂ : ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2) 2 = 0 := by decide
  have h₀ : c₂ 0 = 1 := ofAdd_zero (α := ZMod 2)
  rw [restrict_groupSection, chainPresheaf_map_f₀₁, h₂, h₀, map_one]

/-- The section of the coefficient `2` of `C₄` is not the unit section. -/
theorem groupSection_two_ne_one : groupSection chainPresheaf U₀ (c₄ 2) ≠ 1 := by
  intro h
  have h' : groupSectionsEquiv chainPresheaf U₀ (c₄ 2) = groupSectionsEquiv chainPresheaf U₀ 1 := by
    rw [groupSectionsEquiv_apply, groupSectionsEquiv_apply, map_one]
    exact h
  have := (groupSectionsEquiv chainPresheaf U₀).injective h'
  exact absurd (congrArg Multiplicative.toAdd this : (2 : ZMod 4) = 0) (by decide)

/-- Restriction of compatible central sections along `U₁ ⟶ U₀` is not injective. -/
theorem chain_restrict_not_injective : ¬ Function.Injective (restrict (F := chainF) f₀₁) :=
  fun h ↦ groupSection_two_ne_one (h (chain_two_killed.trans (map_one _).symm))

/-- There are four compatible central sections over the `C₄` object. -/
theorem chain_source_card : Nat.card (IntrinsicBandSections chainF U₀) = 4 := by
  rw [← Nat.card_congr (groupSectionsEquiv chainPresheaf U₀).toEquiv]
  exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 4)

/-- There are two compatible central sections over a `C₂` object. -/
theorem chain_target_card : Nat.card (IntrinsicBandSections chainF U₁) = 2 := by
  rw [← Nat.card_congr (groupSectionsEquiv chainPresheaf U₁).toEquiv]
  exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)

/-- The chain diagram is a stack for the bottom topology. -/
theorem chain_stack : chainF.IsStack ⊥ :=
  inferInstance

/-- The chain diagram is a gerbe for the bottom topology. -/
theorem chain_gerbe : chainF.IsGerbe ⊥ :=
  inferInstance

/-! ### Two disjoint chains -/

/-- The site of two disjoint chains. -/
abbrev TwoChainSite := (Fin 3 ⊕ Fin 3)ᵒᵖ

/-- The chain coefficients on each of the two chains. -/
abbrev twoChainPresheaf : TwoChainSiteᵒᵖ ⥤ CommGrpCat :=
  unopUnop (Fin 3 ⊕ Fin 3) ⋙ chainGroups.sum' chainGroups

/-- The site of two disjoint chains has no terminal object. -/
theorem twoChains_no_terminal (X : TwoChainSite) : IsEmpty (Limits.IsTerminal X) := by
  refine ⟨fun hX ↦ ?_⟩
  obtain ⟨x | x⟩ := X
  · exact (hX.from (op (Sum.inr 0))).unop.elim
  · exact (hX.from (op (Sum.inl 0))).unop.elim

/-- At every object of the two-chain site, the compatible central sections are the coefficients. -/
theorem twoChains_sections_equiv (U : TwoChainSite) :
    Nonempty (twoChainPresheaf.obj (op U) ≃*
      IntrinsicBandSections (groupDiagram twoChainPresheaf) U) :=
  ⟨groupSectionsEquiv twoChainPresheaf U⟩

/-- The two-chain diagram is a stack for the bottom topology. -/
theorem twoChains_stack : (groupDiagram twoChainPresheaf).IsStack ⊥ :=
  inferInstance

/-- The two-chain diagram is a gerbe for the bottom topology, although its site has no terminal
object. -/
theorem twoChains_gerbe : (groupDiagram twoChainPresheaf).IsGerbe ⊥ :=
  inferInstance

end TauCeti.Examples.RestrictionBandFixtures
