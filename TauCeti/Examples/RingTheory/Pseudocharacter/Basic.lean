/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Pseudocharacter.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Examples: pseudocharacters

* `id : ℚ → ℚ` is a `1`-dimensional pseudocharacter.
* The trace on `M₂(ℚ)` is not `1`-dimensional: `T(1) = 2 ≠ 1`, and the `S₂` identity
  `T(x)T(y) − T(xy) = 0` fails at `x = y = 1`.
-/

open TauCeti

-- `id : ℚ → ℚ` is a `1`-dimensional pseudocharacter.
example : IsPseudocharacter (LinearMap.id : ℚ →ₗ[ℚ] ℚ) 1 :=
  (isPseudocharacter_one_iff _).mpr ⟨rfl, fun _ _ ↦ rfl⟩

-- The trace on `M₂(ℚ)` is not a `1`-dimensional pseudocharacter: `T(1) = 2 ≠ 1`.
example : ¬ IsPseudocharacter (Matrix.traceLinearMap (Fin 2) ℚ ℚ) 1 := fun h ↦ by
  have := h.map_one
  norm_num [Matrix.trace_one] at this

-- The `S₂` identity `T(x)T(y) − T(xy) = 0` fails for the trace on `M₂(ℚ)` at `x = y = 1`.
example : cycleSum (Matrix.traceLinearMap (Fin 2) ℚ ℚ) ![1, 1] ≠ 0 := by
  rw [cycleSum_fin_two]
  norm_num [Matrix.trace_one]
