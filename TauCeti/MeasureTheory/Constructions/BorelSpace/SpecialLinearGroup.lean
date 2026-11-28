/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# The Borel σ-algebra on `SL(n, ℝ)`

The special linear group `SL(n, ℝ)` carries the topology induced from the matrices. This file
equips it with the Borel σ-algebra of that topology, so it is a Borel space by definition. This is
the measurable structure on which Haar measures of `SL(n, ℝ)` live.

## Main definitions

* `Matrix.SpecialLinearGroup.instMeasurableSpace`, `instBorelSpace`: the Borel measurable
  structure of `SL(n, ℝ)`.
-/

public section

namespace Matrix.SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Borel measurable structure of `SL(n, ℝ)`. -/
instance instMeasurableSpace : MeasurableSpace (SpecialLinearGroup n ℝ) := borel _

/-- `SL(n, ℝ)` carries its Borel measurable structure. -/
instance instBorelSpace : BorelSpace (SpecialLinearGroup n ℝ) := ⟨rfl⟩

end Matrix.SpecialLinearGroup
