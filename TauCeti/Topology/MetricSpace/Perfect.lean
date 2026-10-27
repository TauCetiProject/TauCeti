/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Cardinality of perfect sets

A second-countable `T₀` space has at most continuum many points, since a point is determined by
the basic open sets containing it. A nonempty perfect subset of a completely metrizable space
contains a copy of Cantor space, so it has at least continuum many points. Together these give
the cardinality of a nonempty perfect subset of a Polish space: exactly `𝔠`.

## Main results

* `TauCeti.mk_le_continuum_of_secondCountableTopology`: a second-countable `T₀` space has at most
  `𝔠` points; in particular so does every Polish space.
* `Perfect.continuum_le_mk`: a nonempty perfect subset of a completely metrizable space has at
  least `𝔠` points.
* `Perfect.mk_eq_continuum`: a nonempty perfect subset of a Polish space has exactly `𝔠` points.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 6.2 and Corollary 6.3.
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

variable {X : Type u} [TopologicalSpace X] {C : Set X}

/-- **A nonempty perfect set in a completely metrizable space has at least continuum many
points**: it contains the range of a continuous injection of Cantor space. -/
theorem Perfect.continuum_le_mk [IsCompletelyMetrizableSpace X] (hC : Perfect C)
    (hne : C.Nonempty) : 𝔠 ≤ #C := by
  let := upgradeIsCompletelyMetrizable X
  obtain ⟨f, hfC, -, hf⟩ := hC.exists_nat_bool_injection hne
  have hinj : Injective fun x => (⟨f x, hfC (mem_range_self x)⟩ : C) := fun x y hxy =>
    hf (congrArg Subtype.val hxy)
  simpa using lift_mk_le_lift_mk_of_injective hinj

/-- **A nonempty perfect set in a Polish space has cardinality continuum.** -/
theorem Perfect.mk_eq_continuum [PolishSpace X] (hC : Perfect C) (hne : C.Nonempty) :
    #C = 𝔠 :=
  le_antisymm (TauCeti.mk_le_continuum_of_secondCountableTopology C) (hC.continuum_le_mk hne)
