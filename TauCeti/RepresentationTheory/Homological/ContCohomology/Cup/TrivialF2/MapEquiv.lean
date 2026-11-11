/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2.MapDegreeOne
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2.MapDegreeTwo
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality

/-!
# Mod-two cup products and transport across universes

For an isomorphism `φ : H ≃ₜ* G` of locally compact groups in independent universes, such as the
absolute Galois groups of a field `K` and of its universe lift `ULift K`, the transports
`TauCeti.trivialF2Map1Equiv φ` and `TauCeti.trivialF2Map2Equiv φ` identify `H¹(G, 𝔽₂)` with
`H¹(H, 𝔽₂)` and `H²(G, 𝔽₂)` with `H²(H, 𝔽₂)`. This file proves that they intertwine the
mod-two cup product `TauCeti.trivialF2TopPairing` in bidegree `(1, 1)`:

```text
trivialF2Map2Equiv φ (x ⌣ y) = trivialF2Map1Equiv φ x ⌣ trivialF2Map1Equiv φ y.
```

In a single universe this is `TauCeti.trivialF2Map_cup` read through
`TauCeti.trivialF2Map1Equiv_apply` and `TauCeti.trivialF2Map2Equiv_apply`; across universes it
is the explicit cup naturality `TauCeti.ContCohomology.explicitMap2_explicitCup11` read through
the explicit description `TauCeti.trivialF2TopPairing_cup_one_one_explicitH1` of the cup product.

## Main results

* `TauCeti.trivialF2Map2Equiv_cup_one_one`: transport of `H²(-, 𝔽₂)` along `φ` sends the cup
  product of two degree-one classes to the cup product of their transports.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.4.2):
  naturality of cup products in compatible coefficient maps.
-/

public section

namespace TauCeti

open CategoryTheory ContCohomology

universe u v

attribute [local instance] TopRep.distribMulAction

/-- The trivial `𝔽₂` coefficients are a discrete module. -/
local instance continuousSMul_trivialF2_cupMapEquiv (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]

/-- **Transport across universes preserves mod-two cup products**: for a topological group
isomorphism `φ : H ≃ₜ* G` with `G` and `H` in independent universes, transport of `H²(-, 𝔽₂)`
along `φ` sends the cup product of `x, y ∈ H¹(G, 𝔽₂)` to the cup product of their transports in
`H¹(H, 𝔽₂)`. -/
@[simp]
theorem trivialF2Map2Equiv_cup_one_one (φ : H ≃ₜ* G)
    (x y : continuousCohomology 1 (trivialF2 G)) :
    trivialF2Map2Equiv φ ((trivialF2TopPairing G).cup 1 1 x y) =
      (trivialF2TopPairing H).cup 1 1 (trivialF2Map1Equiv φ x) (trivialF2Map1Equiv φ y) := by
  -- Write both classes through the explicit model of `H¹(G, 𝔽₂)`.
  let eG := eqToIso (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))
  obtain ⟨x₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso eG.hom).2 x
  obtain ⟨a, rfl⟩ := (explicitH1AddEquivContinuousCohomology G (trivialF2 G).V).surjective x₀
  obtain ⟨y₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso eG.hom).2 y
  obtain ⟨b, rfl⟩ := (explicitH1AddEquivContinuousCohomology G (trivialF2 G).V).surjective y₀
  -- The coefficient identification intertwines multiplication in the two copies of `𝔽₂`.
  have hpair : ∀ m n : (trivialF2 G).V,
      trivialF2CoeffHom (trivialF2Pairing G m n) =
        trivialF2Pairing H (trivialF2CoeffHom m) (trivialF2CoeffHom n) := fun m n ↦ by
    simp only [trivialF2CoeffHom_apply, trivialF2Pairing_apply, AddEquiv.apply_symm_apply]
  -- Normalize both sides to explicit cup products and explicit transports of explicit classes.
  simp only [eG, eqToIso.hom, trivialF2TopPairing_cup_one_one_explicitH1,
    trivialF2Map2Equiv_eqToHom, trivialF2Map1Equiv_eqToHom,
    explicitH2AddEquivContinuousCohomology_continuousCohomologyMap2,
    explicitH1AddEquivContinuousCohomology_continuousCohomologyMap1, ← trivialF2CoeffHom_def]
  -- The comparison is explicit cup naturality for the compatible pair `(φ, trivialF2CoeffHom)`.
  rw [explicitMap2_explicitCup11 G _ _ _ (trivialF2Pairing G) continuous_of_discreteTopology
    (trivialF2Pairing_smul_smul G) H _ _ _ (trivialF2Pairing H) continuous_of_discreteTopology
    (trivialF2Pairing_smul_smul H) φ trivialF2CoeffHom trivialF2CoeffHom trivialF2CoeffHom
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    _ _ _ hpair]

end TauCeti
