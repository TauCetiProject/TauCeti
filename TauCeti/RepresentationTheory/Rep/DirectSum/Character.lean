/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
import TauCeti.LinearAlgebra.Trace.Pi
import TauCeti.RepresentationTheory.Rep.DirectSum.Basic

/-!
# Characters of finite direct sums

The character of a finite direct sum of finite-dimensional representations is the sum of
its summands' characters. This allows character identities with natural multiplicities to
be interpreted as decompositions into concrete direct sums.

The trace computation uses `LinearMap.trace_piMap` after identifying the finite direct sum
with the corresponding dependent product.
-/

public section

namespace Representation

variable {k G ι : Type*} [Field k] [Monoid G] [Fintype ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, FiniteDimensional k (V i)]

/-- The character of a finite direct sum is the sum of the characters of its summands. -/
@[simp]
theorem char_directSum (ρ : ∀ i, Representation k G (V i)) (g : G) :
    (directSum ρ).character g = ∑ i, (ρ i).character g := by
  classical
  let e := DirectSum.linearEquivFunOnFintype k ι V
  rw [character, ← LinearMap.trace_conj' _ e,
    conj_directSum_linearEquivFunOnFintype, LinearMap.trace_piMap]
  simp only [character]

end Representation
