/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.Equivalence
public import TauCeti.CategoryTheory.Exact.Split
public import TauCeti.CategoryTheory.Preadditive.Opposite

/-!
# Transport of opposite exact structures

`TauCeti.ExactStructure.transport_opOpEquivalence` identifies the double opposite with the
original exact structure along Mathlib's `CategoryTheory.opOpEquivalence`.
`TauCeti.ExactStructure.op_split` and `TauCeti.ExactStructure.op_abelian` identify the opposites
of the split and canonical abelian structures. These comparisons use
`TauCeti.ExactStructure.transport_conflation_iff`, Mathlib's duality for short-complex
splittings, and `TauCeti.ExactStructure.abelian_conflation_unop_iff`.

See Bühler, *Exact categories*, Remarks 2.2–2.8 and Sections 13.1–13.2.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.ExactStructure

variable {C : Type*} [Category* C]

section

variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

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

/-- The opposite of the split exact structure is split (Bühler, *Exact categories*, §13.1). -/
@[simp]
theorem op_split (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] : (split C).op = split Cᵒᵖ := by
  apply ExactStructure.ext
  intro S
  rw [op_conflation, split_conflation, split_conflation]
  exact ⟨fun ⟨s⟩ ↦ ⟨s.op.ofIso S.unopOp⟩, fun ⟨s⟩ ↦ ⟨s.unop⟩⟩

end

/-- The opposite of the canonical exact structure on an abelian category is canonical
(Bühler, *Exact categories*, §13.2). -/
@[simp]
theorem op_abelian (C : Type*) [Category* C] [Abelian C] : (abelian C).op = abelian Cᵒᵖ := by
  apply ExactStructure.ext
  intro S
  rw [op_conflation]
  exact abelian_conflation_unop_iff S

end TauCeti.ExactStructure
