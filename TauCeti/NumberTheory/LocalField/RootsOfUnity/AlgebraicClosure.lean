/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Roots of unity in the algebraic closure of a local field

The algebraic closure of a nonarchimedean local field has enough roots of unity of every
order prime to the residue characteristic.
-/

public section

namespace TauCeti

open _root_.ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The algebraic closure has enough roots of unity at every order prime to the residue
characteristic. -/
theorem hasEnoughRootsOfUnity_algebraicClosure_of_coprime_ringChar {m : ℕ}
    (hm : m.Coprime (ringChar 𝓀[K])) : HasEnoughRootsOfUnity (AlgebraicClosure K) m := by
  have : NeZero (m : K) := ⟨natCast_ne_zero_of_coprime_ringChar hm⟩
  infer_instance

end TauCeti
