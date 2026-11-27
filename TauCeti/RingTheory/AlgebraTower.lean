/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraTower

/-!
# Recovering linear independence and composite algebras in a scalar tower

If a family spans the intermediate scalar ring over the smaller ring, linear independence of
its products with a second family implies independence of the second family over the intermediate
ring. Together with its converse `linearIndependent_smul`, this detects independence using a basis
of scalars.

For a tower `R → S → A` where `R` and `S` are commutative, `TauCeti.compAlgebra` builds the
composite `R`-algebra structure on `A`, together with its scalar-tower compatibilities
`TauCeti.isScalarTower_compAlgebra_left` (`R → S → A`) and
`TauCeti.isScalarTower_compAlgebra_right` (`R → A → T` when `R → S → T` and `S → A → T`).
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

namespace TauCeti

/-- The composite `R`-algebra structure on `A` induced by a tower `R → S → A`. -/
abbrev compAlgebra (R S A : Type*) [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R S] [Algebra S A] : Algebra R A :=
  ((algebraMap S A).comp (algebraMap R S)).toAlgebra' fun _ a ↦ Algebra.commutes _ a

/-- Through `TauCeti.compAlgebra`, the maps `R → S → A` form a scalar tower. -/
theorem isScalarTower_compAlgebra_left (R S A : Type*) [CommSemiring R] [CommSemiring S]
    [Semiring A] [Algebra R S] [Algebra S A] :
    letI := compAlgebra R S A
    IsScalarTower R S A :=
  letI := compAlgebra R S A
  .of_algebraMap_eq fun _ ↦ rfl

/-- Through `TauCeti.compAlgebra`, if `R → S → T` and `S → A → T` are scalar towers, then
`R → A → T` is also a scalar tower. -/
theorem isScalarTower_compAlgebra_right (R S A T : Type*) [CommSemiring R] [CommSemiring S]
    [CommSemiring A] [Semiring T] [Algebra R S] [Algebra S A] [Algebra R T] [Algebra S T]
    [Algebra A T] [IsScalarTower R S T] [IsScalarTower S A T] :
    letI := compAlgebra R S A
    IsScalarTower R A T :=
  letI := compAlgebra R S A
  .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra', ← IsScalarTower.algebraMap_apply _ _ T]

end TauCeti
