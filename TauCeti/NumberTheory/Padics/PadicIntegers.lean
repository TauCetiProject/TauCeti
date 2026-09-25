/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Units of the `p`-adic integers

Complements to Mathlib's `PadicInt` API on the units of `ℤ_p`: `1 + x` is a unit whenever
`p ∣ x`, because `ℤ_p` is a local ring whose maximal ideal is `pℤ_p`. This is the criterion
that makes `1 + p^f ℤ_p` a subgroup of `ℤ_pˣ`.

The unit group `ℤ_pˣ` is a profinite group: it is the closed unit sphere of the compact
totally disconnected space `ℤ_p`, and the topology of the units is the subspace topology because
`ℤ_p` is a complete normed ring. The instances `CompactSpace ℤ_[p]ˣ` and
`TotallyDisconnectedSpace ℤ_[p]ˣ` are recorded here.

## Main results

* `PadicInt.isUnit_one_add_of_dvd`: `1 + x` is a unit of `ℤ_[p]` whenever `p ∣ x`.
* `PadicInt.units_neg_one_ne_one`: `-1 ≠ 1` in `ℤ_[p]ˣ`.
* `PadicInt.range_units_val`: the units of `ℤ_[p]` are the elements of norm `1`.
* `PadicInt.compactSpace_units`, `PadicInt.totallyDisconnectedSpace_units`: `ℤ_[p]ˣ` is a
  profinite group.
-/

public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- In `ℤ_p`, `1 + x` is a unit whenever `p ∣ x`. -/
theorem isUnit_one_add_of_dvd {x : ℤ_[p]} (hx : (p : ℤ_[p]) ∣ x) : IsUnit (1 + x) :=
  IsLocalRing.isUnit_of_mem_nonunits_one_sub_self _ <| by
    rw [sub_add_cancel_left, mem_nonunits, norm_neg]
    exact (norm_lt_one_iff_dvd x).mpr hx

/-- `-1 ≠ 1` in `ℤ_pˣ`: the unit group has an element of order two. -/
theorem units_neg_one_ne_one : (-1 : ℤ_[p]ˣ) ≠ 1 := fun h ↦ by
  have := congrArg Units.val h
  rw [Units.val_neg, Units.val_one] at this
  exact (by norm_num : (-1 : ℤ_[p]) ≠ 1) this

/-- The units of `ℤ_p` are the elements of norm `1`. -/
theorem range_units_val : Set.range (Units.val : ℤ_[p]ˣ → ℤ_[p]) = {x | ‖x‖ = 1} :=
  -- `IsUnit x` is by definition `∃ u : ℤ_[p]ˣ, ↑u = x`, that is `x ∈ Set.range Units.val`.
  Set.ext fun _ ↦ isUnit_iff

/-- `ℤ_pˣ` is compact: it is the closed unit sphere of the compact space `ℤ_p`, and the topology
on the units of the complete normed ring `ℤ_p` is the subspace topology. -/
instance compactSpace_units : CompactSpace ℤ_[p]ˣ := by
  have h : IsCompact (Set.range (Units.val : ℤ_[p]ˣ → ℤ_[p])) := by
    rw [range_units_val]
    exact (isClosed_eq continuous_norm continuous_const).isCompact
  rw [← Set.image_univ] at h
  exact isCompact_univ_iff.mp (Units.isOpenEmbedding_val.isInducing.isCompact_iff.mpr h)

/-- `ℤ_pˣ` is totally disconnected, as a subspace of the ultrametric space `ℤ_p`. -/
instance totallyDisconnectedSpace_units : TotallyDisconnectedSpace ℤ_[p]ˣ :=
  ⟨Units.isOpenEmbedding_val.isEmbedding.isTotallyDisconnected
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

end PadicInt
