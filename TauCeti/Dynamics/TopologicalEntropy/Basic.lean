/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Topological entropy is infinite or a nonnegative real

The topological entropy `coverEntropy T F` of a map `T` on a nonempty set `F` is either `⊤` or a
nonnegative real number (`TauCeti.coverEntropy_eq_top_or_exists_eq_coe`). This is the case split
that reduces a bound on the topological entropy to a bound by a real number.
-/

public section

open Dynamics Set

namespace TauCeti

variable {X : Type*} [UniformSpace X]

/-- The topological entropy of a map on a nonempty set is `⊤` or a nonnegative real number. -/
theorem coverEntropy_eq_top_or_exists_eq_coe (T : X → X) {F : Set X} (hF : F.Nonempty) :
    coverEntropy T F = ⊤ ∨ ∃ t : ℝ, 0 ≤ t ∧ coverEntropy T F = t := by
  rcases eq_or_ne (coverEntropy T F) ⊤ with htop | htop
  · exact .inl htop
  have h0 := coverEntropy_nonneg T hF
  exact .inr ⟨_, EReal.toReal_nonneg h0,
    (EReal.coe_toReal htop (h0.trans_lt' EReal.bot_lt_zero).ne').symm⟩

end TauCeti
