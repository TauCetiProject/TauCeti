/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis

/-!
# Real powers of diagonal endomorphisms in a basis

Over `ℝ`, composing real-power diagonal endomorphisms `b.diagMap fun i ↦ lam i ^ s` (for
strictly positive eigenvalues `lam i > 0`) adds the exponents (`Module.Basis.diagMap_rpow_comp`).
-/

public section

namespace Module.Basis

/-- Composing two real-power diagonal endomorphisms adds their exponents. -/
theorem diagMap_rpow_comp {ι V : Type*} [AddCommMonoid V] [Module ℝ V]
    (b : Module.Basis ι ℝ V) {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i) (s t : ℝ) :
    (b.diagMap fun i ↦ lam i ^ t).comp (b.diagMap fun i ↦ lam i ^ s) =
      b.diagMap fun i ↦ lam i ^ (s + t) := by
  rw [b.diagMap_comp]; congr 1; ext i; rw [← Real.rpow_add (hlam i), add_comm]

end Module.Basis
