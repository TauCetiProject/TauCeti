/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Radical
public import TauCeti.RingTheory.VonNeumannRegular.Basic
import TauCeti.RingTheory.Idempotents.Ideal
import TauCeti.RingTheory.Idempotents.Jacobson

/-!
# The Jacobson radical of a von Neumann regular ring

A von Neumann regular ring has zero Jacobson radical.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R]

namespace IsVonNeumannRegularSemigroup

/-- A von Neumann regular ring has zero Jacobson radical. -/
@[simp]
theorem jacobson_eq_bot [IsVonNeumannRegularSemigroup R] : Ring.jacobson R = ⊥ := by
  refine eq_bot_iff.mpr fun a ha ↦ ?_
  obtain ⟨e, he, hspan⟩ :=
    (exists_isIdempotentElem_span_singleton_eq_iff a).mpr (exists_mul_mul_eq_self a)
  have hle := (Ideal.span_singleton_le_iff_mem _).mpr ha
  rw [hspan, Ideal.span_singleton_le_iff_mem] at hle
  rw [he.eq_zero_of_mem_jacobson hle, Ideal.span_singleton_zero] at hspan
  exact hspan ▸ Ideal.mem_span_singleton_self a

end IsVonNeumannRegularSemigroup

end TauCeti
