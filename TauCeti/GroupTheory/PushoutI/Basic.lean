/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers of the amalgamated subgroup in a pushout of groups

Let `Monoid.PushoutI φ` be the pushout of a family of groups `G i` along homomorphisms
`φ i : C →* G i`. An element of a factor `G i` that centralizes the image of `C` in `G i`
commutes in the pushout with every element of the image `base φ c` of `C`, since that image is
also the image of `φ i c` under the inclusion of `G i`.

## Main results

* `Monoid.PushoutI.commute_of_base_of_mem_centralizer`: an element of a factor centralizing the
  image of `C` commutes with the image of `C` in the pushout.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.1 (amalgams).
-/

public section

namespace Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*} {C : Type*} [∀ i, Group (G i)] [Group C]
  {φ : ∀ i, C →* G i}

/-- An element of a factor centralizing the image of the amalgamating group commutes in the
pushout with every element of the image of the amalgamating group. -/
theorem commute_of_base_of_mem_centralizer {i : ι} {z : G i}
    (hz : z ∈ Subgroup.centralizer (Set.range (φ i))) (c : C) :
    Commute (of (φ := φ) i z) (base φ c) := by
  rw [← of_apply_eq_base φ i]
  exact (Commute.map (Subgroup.mem_centralizer_iff.mp hz (φ i c) ⟨c, rfl⟩) (of i)).symm

end Monoid.PushoutI
