/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.Equivalence
public import TauCeti.CategoryTheory.Preadditive.Opposite

/-!
# Transport of opposite exact structures

`TauCeti.ExactStructure.transport_opOpEquivalence` identifies the double opposite with the
original exact structure along Mathlib's `CategoryTheory.opOpEquivalence`.
`TauCeti.ExactStructure.transport_opOpEquivalence_symm` gives the inverse comparison.
At the level of conflations, these comparisons combine
`TauCeti.ExactStructure.transport_conflation_iff` and `TauCeti.ExactStructure.op_conflation`.
`TauCeti.ExactStructure.transport_symm` relates the two directions.

See Bühler, *Exact categories*, Remarks 2.2–2.8.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.ExactStructure

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

/-- Transport along the canonical equivalence from the double opposite recovers the original
exact structure (Bühler, *Exact categories*, Remarks 2.2–2.8).
Simplify the transport before rewriting the opposite of a split or canonical structure. -/
@[simp↓]
theorem transport_opOpEquivalence (E : ExactStructure C) :
    E.op.op.transport (opOpEquivalence C) = E := by
  apply ExactStructure.ext
  intro S
  rw [transport_conflation_iff, op_conflation, op_conflation]
  -- Double unop reverses the arrows twice and cancels the double op on each map.
  cases S
  rfl

/-- Transport to the double opposite gives the twice-opposite exact structure. -/
@[simp]
theorem transport_opOpEquivalence_symm (E : ExactStructure C) :
    E.transport (opOpEquivalence C).symm = E.op.op := by
  have h := E.op.op.transport_symm (opOpEquivalence C)
  rwa [transport_opOpEquivalence] at h

end TauCeti.ExactStructure
