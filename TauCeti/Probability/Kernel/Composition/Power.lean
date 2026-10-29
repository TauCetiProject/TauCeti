/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Powers of finite and Markov kernels

Iterating a uniformly finite kernel remains uniformly finite. This permits taking finite
transition masses, and thus nonnegative real transition matrices, for every iterate.
Iterating a Markov kernel also preserves the probability normalization of every row.
-/

public section

namespace ProbabilityTheory

/-- Every natural power of a finite kernel is finite. -/
instance IsFiniteKernel.pow {α : Type*} [MeasurableSpace α] (κ : Kernel α α)
    [IsFiniteKernel κ] (n : ℕ) : IsFiniteKernel (κ ^ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsFiniteKernel Kernel.id)
  | succ n ih =>
    -- Multiplication in the kernel monoid is composition.
    exact inferInstanceAs (IsFiniteKernel ((κ ^ n) ∘ₖ κ))

/-- Every natural power of a Markov kernel is a Markov kernel. -/
instance IsMarkovKernel.pow {α : Type*} [MeasurableSpace α] (κ : Kernel α α)
    [IsMarkovKernel κ] (n : ℕ) : IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih =>
    -- Multiplication in the kernel monoid is composition.
    exact inferInstanceAs (IsMarkovKernel ((κ ^ n) ∘ₖ κ))

end ProbabilityTheory
