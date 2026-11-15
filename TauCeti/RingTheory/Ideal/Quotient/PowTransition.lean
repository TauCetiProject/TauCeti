/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# The decreasing ideal-power filtration of a module

The submodules `I ^ (n + 1) • ⊤` form a decreasing filtration. This monotonicity supplies the
inclusions used to construct the transition maps between successive quotients.
-/

public section

namespace Ideal

variable {A : Type*} [Ring A] (I : Ideal A)
variable (M : Type*) [AddCommGroup M] [Module A M]

/-- The `I`-adic filtration `n ↦ I^{n+1} M` of `M` is decreasing. -/
theorem pow_succ_smul_top_antitone :
    Antitone fun n : ℕ ↦ (I ^ (n + 1) • ⊤ : Submodule A M) :=
  fun _ _ h ↦ Submodule.pow_smul_top_le I M (Nat.add_le_add_right h 1)

end Ideal
