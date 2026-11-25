/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import TauCeti.Topology.Algebra.Group.Perm

/-!
# The Borel σ-algebra on permutation groups

For every topological space `α`, the permutation type `Equiv.Perm α` carries the Borel σ-algebra
of its pointwise topology `Equiv.Perm.instTopologicalSpace`, so it is a Borel space by definition.
For a countable discrete `α`, in particular for `α = ℕ`, the topology is Polish
(`Equiv.Perm.instPolishSpace`), so Mathlib's `standardBorel_of_polish` makes `Equiv.Perm α` a
standard Borel space. Forward and inverse evaluations are measurable.

This is the σ-algebra of the Borel `S∞`-spaces of descriptive set theory: a standard Borel space
`X` with an action `[MulAction (Equiv.Perm ℕ) X]` that is jointly measurable,
`[MeasurableSMul₂ (Equiv.Perm ℕ) X]`.
-/

public section

namespace Equiv.Perm

variable {α : Type*} [TopologicalSpace α]

/-- The Borel σ-algebra of the pointwise topology on permutations. -/
instance instMeasurableSpace : MeasurableSpace (Equiv.Perm α) :=
  borel (Equiv.Perm α)

/-- Permutations carry the Borel σ-algebra of their topology, by definition. -/
instance instBorelSpace : BorelSpace (Equiv.Perm α) :=
  ⟨rfl⟩

variable [MeasurableSpace α] [BorelSpace α]

/-- Forward evaluation at a fixed point is measurable. -/
@[fun_prop]
theorem measurable_apply (a : α) : Measurable (fun σ : Equiv.Perm α => σ a) :=
  (continuous_apply a).measurable

/-- Inverse evaluation at a fixed point is measurable. -/
@[fun_prop]
theorem measurable_inv_apply (a : α) : Measurable (fun σ : Equiv.Perm α => σ⁻¹ a) :=
  (continuous_inv_apply a).measurable

end Equiv.Perm
