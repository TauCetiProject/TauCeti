/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Separation.Basic
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Cardinality of second-countable spaces

A second-countable `T₀` space has at most continuum many points, since a point is determined by
the basic open sets containing it.

## Main results

* `TauCeti.mk_le_continuum_of_secondCountableTopology`: a second-countable `T₀` space has at most
  `𝔠` points; in particular so does every Polish space.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Corollary 6.3.
-/

public section

open Set Function Cardinal TopologicalSpace

universe u

namespace TauCeti

/-- **A second-countable `T₀` space has at most continuum many points.** A point is determined
by the members of a countable basis containing it. In particular a Polish space has at most `𝔠`
points. -/
theorem mk_le_continuum_of_secondCountableTopology (X : Type u) [TopologicalSpace X]
    [SecondCountableTopology X] [T0Space X] : #X ≤ 𝔠 := by
  obtain ⟨b, hbc, hb⟩ := exists_countable_basis X
  have : Countable b := hbc.to_subtype
  have hinj : Injective fun x : X => {s : b | x ∈ (s : Set X)} := fun x y hxy =>
    hb.2.eq_iff.2 fun s hs => by simpa using congrArg (⟨s, hs⟩ ∈ ·) hxy
  calc #X ≤ #(Set b) := mk_le_of_injective hinj
    _ = 2 ^ #b := mk_set
    _ ≤ 2 ^ ℵ₀ := power_le_power_left two_ne_zero mk_le_aleph0
    _ = 𝔠 := two_power_aleph0

end TauCeti
