/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Completeness for a terminating adic filtration

If a power of an ideal annihilates a module, its adic filtration terminates and every Cauchy
sequence is eventually constant. In particular, quotients by powers of an ideal are complete
for the image ideal, so Mathlib's completeness criterion makes these pairs henselian.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] {I : Ideal R}
  {M : Type*} [AddCommGroup M] [Module R M]

/-- A module annihilated by a power of `I` is `I`-adically complete. -/
theorem isAdicComplete_of_pow_smul_eq_bot {k : ℕ}
    (hk : I ^ k • (⊤ : Submodule R M) = ⊥) : IsAdicComplete I M where
  haus' x hx := by simpa [hk] using hx k
  prec' f hf := by
    refine ⟨f k, fun n ↦ ?_⟩
    rcases le_total n k with h | h
    · exact hf h
    · have heq : f k = f n := by simpa [hk] using hf h
      rw [heq]

end TauCeti
