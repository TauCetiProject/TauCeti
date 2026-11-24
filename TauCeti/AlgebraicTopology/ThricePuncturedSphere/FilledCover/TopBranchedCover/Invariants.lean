/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.TopBranchedCover.Classification
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.TopBranchedCover.Deck
public import TauCeti.Combinatorics.PermutationTriple.ClassInvariants

/-!
# Invariant comparisons for topological branched covers

Matches `ramificationPartitions`, `natCardDeck`, and `IsRegular` along `equivConnectedIsoClass`.
-/

public noncomputable section

namespace TauCeti.TopBranchedCover.IsoClass

open ThricePuncturedSphere

variable {n : ℕ} (c : IsoClass.{0} n)

/-- `IsoClass.equivConnectedIsoClass` matches `ramificationPartitions` with `cycleData`. -/
@[simp] theorem cycleData_equivConnectedIsoClass :
    (equivConnectedIsoClass n c).cycleData = c.ramificationPartitions := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  simp [equivConnectedIsoClass_mk X ν, X.ramificationPartitions_eq_cycleData_monodromyTriple ν]

/-- `IsoClass.equivConnectedIsoClass` preserves the order of the deck/automorphism group. -/
@[simp] theorem automorphismOrder_equivConnectedIsoClass :
    (equivConnectedIsoClass n c).automorphismOrder = c.natCardDeck := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  simpa [equivConnectedIsoClass_mk X ν] using
    (Nat.card_congr (X.deckMulEquivAutomorphismGroup ν).toEquiv).symm

/-- `IsoClass.equivConnectedIsoClass` preserves regularity. -/
@[simp] theorem isRegular_equivConnectedIsoClass :
    (equivConnectedIsoClass n c).IsRegular ↔ c.IsRegular := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [equivConnectedIsoClass_mk X ν]; simp [X.isRegular_iff_monodromyTriple ν]

end TauCeti.TopBranchedCover.IsoClass
