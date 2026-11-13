/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraTower

/-!
# Recovering linear independence in a scalar tower

If a family spans the intermediate scalar ring over the smaller ring, linear independence of
its products with a second family implies independence of the second family over the intermediate
ring. Together with its converse `linearIndependent_smul`, this detects independence using a basis
of scalars.
-/

public section

namespace LinearIndependent

variable {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
variable [Module R S] [Module S M] [Module R M] [IsScalarTower R S M]

/-- Independence of all products with a spanning family of scalars implies independence over
the larger scalar ring. This is a converse to `linearIndependent_smul`. -/
theorem of_smul_of_span_eq_top {ι κ : Type*} {b : ι → S} {c : κ → M}
    (h : LinearIndependent R fun p : ι × κ ↦ b p.1 • c p.2)
    (hb : Submodule.span R (Set.range b) = ⊤) : LinearIndependent S c := by
  rw [← linearIndependent_equiv' (.prodComm ..) (g := fun p : κ × ι ↦ b p.2 • c p.1) rfl,
    LinearIndependent, Finsupp.linearCombination_smul] at h
  exact .of_comp_right h <| (Finsupp.mapRange_surjective _ (map_zero _) <|
    (span_range_eq_top_iff_surjective_finsuppLinearCombination R).mp hb).comp
      (Finsupp.curryLinearEquiv R).surjective

end LinearIndependent
