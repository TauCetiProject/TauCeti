/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.Algebra.DirectSum.BaseChange

/-!
# Scalar extension of internal gradings

An internal grading extends along any homomorphism of commutative semirings. Its pieces are
Mathlib's scalar-extended submodules; their internality is `DirectSum.IsInternal.baseChange`.
Thus no flatness hypothesis is needed.
-/

public section

namespace TauCeti.InternalGrading

open scoped TensorProduct

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (G : InternalGrading R M ι) (S : Type*) [CommSemiring S] [Algebra R S]

/-- Extend every homogeneous summand along the coefficient homomorphism. -/
noncomputable def baseChange : InternalGrading S (S ⊗[R] M) ι where
  piece i := (G.piece i).baseChange S
  isInternal := G.isInternal.baseChange

/-- The pieces of the extended grading are the scalar extensions of the original pieces. -/
@[simp]
theorem baseChange_piece (i : ι) : (G.baseChange S).piece i = (G.piece i).baseChange S := (rfl)

end TauCeti.InternalGrading
