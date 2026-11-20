/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FinCases

/-!
# Affine independence of three points

## Main results

* `TauCeti.affineIndependent_iff_linearIndependent_vsub_vsub`: three points of an affine space
  are affinely independent iff the two vectors from the middle point to the outer points are
  linearly independent.
-/

public section

namespace TauCeti

variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- Three points are affinely independent exactly when the two vectors from the middle point to
the outer points are linearly independent. -/
theorem affineIndependent_iff_linearIndependent_vsub_vsub {x y z : P} :
    AffineIndependent k ![x, y, z] ↔ LinearIndependent k ![x -ᵥ y, z -ᵥ y] := by
  rw [affineIndependent_iff_linearIndependent_vsub k _ (1 : Fin 3),
    ← linearIndependent_equiv (finSuccAboveEquiv (1 : Fin 3))]
  convert Iff.rfl using 2
  funext j
  fin_cases j <;> rfl

end TauCeti
