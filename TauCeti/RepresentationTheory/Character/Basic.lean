/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Characters in infinite dimension

The trace character vanishes when the representation space is not finite-dimensional.
-/

public section

namespace Representation

/-- The character vanishes on a representation space that is not finite-dimensional. -/
theorem character_eq_zero_of_not_finite {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ¬ FiniteDimensional k V) :
    ρ.character = 0 := by
  funext g
  simp [character, TauCeti.LinearMap.trace_eq_zero_of_not_finite h]

end Representation
