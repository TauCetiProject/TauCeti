/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.Action.Invariant
public import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup

/-!
# Ramification quotients for subgroups

Let a group `G` act on a nonarchimedean local field `L`, preserving its integer ring, and let
`H ≤ G`. The ramification filtration for the restricted action is the intersection of `H` with
the filtration for `G`. Consequently, inclusion induces an injective homomorphism

`H_i / H_{i+1} → G_i / G_{i+1}`.

This file constructs that homomorphism and proves that the ramification-quotient embedding
`θ_i : G_i / G_{i+1} → U(L,i) / U(L,i+1)` is natural for it. Thus passing to a subgroup does not
change the uniformizer ratio representing a ramification class. This is the subgroup counterpart
to the quotient behavior used by Herbrand theory.

## Main results

* `TauCeti.IsLocalRing.ramificationGroupGradedSubgroupHom`: the injective map on successive
  ramification quotients induced by subgroup inclusion.
* `TauCeti.ramificationGroupGradedToUnitFiltrationGraded_comp_subgroupHom`: the embeddings
  `θ_i` commute with passage to `H`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField TauCeti.IsLocalRing

namespace TauCeti

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
variable {G : Type*} [Group G] [MulSemiringAction G L] [IsInvariantSubring G 𝒪[L]]
variable {H : Subgroup G}

/-- **Naturality of the ramification-quotient embedding under subgroups.** Including
`H_i/H_{i+1}` into `G_i/G_{i+1}` and then applying `θ_i` gives the same class in
`U(L,i)/U(L,i+1)` as applying the quotient embedding for the restricted `H`-action. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_comp_subgroupHom
    (n : ℕ) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    (ramificationGroupGradedToUnitFiltrationGraded (G := G) n hϖ).comp
        (ramificationGroupGradedSubgroupHom G 𝒪[L] H n) =
      ramificationGroupGradedToUnitFiltrationGraded (G := H) n hϖ := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    rw [MonoidHom.comp_apply, ramificationGroupGradedSubgroupHom_mk,
      ramificationGroupGradedToUnitFiltrationGraded_mk,
      ramificationGroupGradedToUnitFiltrationGraded_mk]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [coe_uniformizerRatio, coe_uniformizerRatio,
      coe_ramificationGroupSubgroupHom]
    rfl

end TauCeti
