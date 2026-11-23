/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.TopBranchedCover.Basic
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.TopBranchedCover.Deck
public import TauCeti.Combinatorics.PermutationTriple.ClassInvariants

/-!
# Invariant comparisons for topological branched covers

Matches `ramificationPartitions`, `natCardDeck`, and `IsRegular` along
`TopBranchedCover.IsoClass.equivConnectedIsoClass`.
-/

public noncomputable section

namespace TauCeti.TopBranchedCover.IsoClass

open ThricePuncturedSphere

variable {n : ℕ} (c : IsoClass.{0} n)

/-- `IsoClass.equivConnectedIsoClass` matches `ramificationPartitions` with `cycleData`. -/
@[simp] theorem cycleData_equivConnectedIsoClass :
    (equivConnectedIsoClass n c).cycleData = c.ramificationPartitions := by
  obtain ⟨X, rfl⟩ := IsoClass.mk_surjective c
  exact (X.nonempty_restrict_preimage_singleton_equiv basePt).elim fun ν ↦ by
    simp [equivConnectedIsoClass_mk X ν, X.ramificationPartitions_eq_cycleData_monodromyTriple ν]

/-- `IsoClass.equivConnectedIsoClass` preserves the order of the deck/automorphism group. -/
@[simp] theorem natCardAutomorphismGroup_equivConnectedIsoClass :
    (equivConnectedIsoClass n c).natCardAutomorphismGroup = c.natCardDeck := by
  obtain ⟨X, rfl⟩ := IsoClass.mk_surjective c
  exact (X.nonempty_restrict_preimage_singleton_equiv basePt).elim fun ν ↦ by
    simpa [equivConnectedIsoClass_mk X ν] using
      (Nat.card_congr (X.deckMulEquivAutomorphismGroup ν).toEquiv).symm

/-- `IsoClass.equivConnectedIsoClass` preserves regularity. -/
@[simp] theorem isRegular_equivConnectedIsoClass :
    (equivConnectedIsoClass n c).IsRegular ↔ c.IsRegular := by
  obtain ⟨X, rfl⟩ := IsoClass.mk_surjective c
  exact (X.nonempty_restrict_preimage_singleton_equiv basePt).elim fun ν ↦ by
    rw [equivConnectedIsoClass_mk X ν]; simp [X.isRegular_iff_monodromyTriple ν]

end TauCeti.TopBranchedCover.IsoClass
