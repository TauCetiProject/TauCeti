/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Amalgamated products along non-injective maps, and centralizers of the amalgamated subgroup

Mathlib's `Monoid.PushoutI φ` is defined for an arbitrary family of homomorphisms
`φ i : H →* G i`, and `Monoid.PushoutI.of_injective` shows that the factors `G i` embed in it when
every `φ i` is injective. This file records the converse obstruction: two elements of `H`
identified by one map `φ j` have the same image in the pushout, so a factor `G i` that embeds
forces `φ i` to identify them as well. In particular, if `φ i` is injective and some `φ j` is
not, then `G i` does not embed in the pushout.

This is the reason the boundary maps of a graph of groups are required to be injective: for the
data of an amalgam `A ∗_C B` with a non-injective map `C →* B` and an injective map `C →* A`, the
vertex group `A` does not embed in the amalgam, and the normal form theorem fails.

For a pushout of groups along `φ i : C →* G i`, an element of a factor `G i` that centralizes the
image of `C` in `G i` commutes in the pushout with every element of the image `base φ c` of `C`,
since that image is also the image of `φ i c` under the inclusion of `G i`.

## Main results

* `Monoid.PushoutI.apply_eq_apply_of_injective_of`: if `G i` embeds in the pushout, then `φ i`
  identifies every pair of elements identified by some `φ j`.
* `Monoid.PushoutI.not_injective_of`: if `φ i` is injective and `φ j` is not, then `G i` does not
  embed in the pushout.
* `Monoid.PushoutI.commute_of_base_of_mem_centralizer`: an element of a factor centralizing the
  image of `C` commutes with the image of `C` in the pushout.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.1.
-/

public section

namespace Monoid.PushoutI

section Monoid

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Monoid (G i)] [Monoid H]
  {φ : ∀ i, H →* G i} {i : ι}

/-- If the factor `G i` embeds in the pushout of the maps `φ k : H →* G k`, then `φ i` identifies
any two elements of `H` that some map `φ j` identifies: both pairs of images are the images of
the same two elements of `H` in the pushout. -/
theorem apply_eq_apply_of_injective_of (hi : Function.Injective (of (φ := φ) i)) {j : ι}
    {x y : H} (hxy : φ j x = φ j y) : φ i x = φ i y :=
  hi <| by rw [of_apply_eq_base, of_apply_eq_base, ← of_apply_eq_base φ j, hxy, of_apply_eq_base]

/-- If `φ i` is injective and some `φ j` is not, then the factor `G i` does not embed in the
pushout of the maps `φ k : H →* G k`. -/
theorem not_injective_of (hi : Function.Injective (φ i)) {j : ι}
    (hj : ¬ Function.Injective (φ j)) : ¬ Function.Injective (of (φ := φ) i) :=
  fun h => hj fun _ _ hxy => hi (apply_eq_apply_of_injective_of h hxy)

end Monoid

section Group

variable {ι : Type*} {G : ι → Type*} {C : Type*} [∀ i, Group (G i)] [Group C]
  {φ : ∀ i, C →* G i}

/-- An element of a factor centralizing the image of the amalgamating group commutes in the
pushout with every element of the image of the amalgamating group. -/
theorem commute_of_base_of_mem_centralizer {i : ι} {z : G i}
    (hz : z ∈ Subgroup.centralizer (Set.range (φ i))) (c : C) :
    Commute (of (φ := φ) i z) (base φ c) := by
  rw [← of_apply_eq_base φ i]
  exact (Commute.map (Subgroup.mem_centralizer_iff.mp hz (φ i c) ⟨c, rfl⟩) (of i)).symm

end Group

end Monoid.PushoutI
