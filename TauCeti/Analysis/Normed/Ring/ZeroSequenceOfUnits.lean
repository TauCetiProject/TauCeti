/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import TauCeti.Topology.Algebra.ZeroSequenceOfUnits
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Zero sequences of units in seminormed rings and normed fields

In a seminormed ring `R`, the powers of any unit `u : Rˣ` with `‖(u : R)‖ < 1` form a zero
sequence of units, supplying `TauCeti.HasZeroSequenceOfUnits R`. In particular, every
nontrivially normed field (`ℝ`, `ℂ`, `ℚ_[p]`, …) carries a zero sequence of units, without
passing through Huber or Tate ring theory.

This lightweight bridge lets `TauCeti.Topology.Algebra.OpenMapping.BanachSchauder` and
`TauCeti.Topology.Algebra.OpenMapping.Henkel` apply directly to topological vector spaces over
nontrivially normed fields as well as to modules over seminormed rings with a contractive unit.

## Main results

* `TauCeti.HasZeroSequenceOfUnits.tendsto_pow_unit_of_norm_lt_one`: the powers of a unit of norm
  strictly less than `1` in a seminormed ring converge to zero.
* `TauCeti.HasZeroSequenceOfUnits.of_norm_lt_one`: a seminormed ring containing a unit of norm
  strictly less than `1` admits a zero sequence of units.
* `TauCeti.HasZeroSequenceOfUnits.of_nontriviallyNormedField`: every nontrivially normed field
  admits a zero sequence of units.
-/

public section

open Filter Topology

namespace TauCeti.HasZeroSequenceOfUnits

/-- The powers of a unit `u` with `‖(u : R)‖ < 1` in a seminormed ring form a sequence of units
converging to zero. -/
theorem tendsto_pow_unit_of_norm_lt_one {R : Type*} [SeminormedRing R] (u : Rˣ)
    (hu : ‖(u : R)‖ < 1) :
    Tendsto (fun n : ℕ ↦ ((u ^ n : Rˣ) : R)) atTop (𝓝 0) := by
  simpa only [Units.val_pow_eq_pow_val] using tendsto_pow_atTop_nhds_zero_of_norm_lt_one hu

/-- A seminormed ring admitting a unit of norm strictly less than `1` carries a zero sequence of
units. -/
theorem of_norm_lt_one {R : Type*} [SeminormedRing R] (u : Rˣ) (hu : ‖(u : R)‖ < 1) :
    HasZeroSequenceOfUnits R :=
  ⟨fun n ↦ u ^ n, tendsto_pow_unit_of_norm_lt_one u hu⟩

/-- Every nontrivially normed field carries a zero sequence of units, given by the powers of any
nonzero element of norm strictly less than `1`. -/
instance (priority := 100) of_nontriviallyNormedField {𝕜 : Type*} [NontriviallyNormedField 𝕜] :
    HasZeroSequenceOfUnits 𝕜 := by
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one 𝕜
  exact of_norm_lt_one (Units.mk0 c (norm_pos_iff.mp hc0)) hc1

end TauCeti.HasZeroSequenceOfUnits

end
