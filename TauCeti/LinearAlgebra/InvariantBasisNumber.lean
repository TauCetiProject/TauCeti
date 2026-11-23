/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import TauCeti.RingTheory.LocalRing.Residue

/-!
# The rank condition along ring homomorphisms and for local rings

A semiring `R` satisfies the rank condition when every surjective linear map `Rⁿ → Rᵐ` has
`m ≤ n`; equivalently, `B * A = 1` for an `n × m` matrix `A` and an `m × n` matrix `B` forces
`m ≤ n` (`rankCondition_iff_matrix`). Applying a ring homomorphism `f : R →+* S` to the entries
preserves such a matrix identity, so the rank condition passes from `S` back to `R`.

A possibly noncommutative local ring maps onto the division ring `R ⧸ Ring.jacobson R`, which
satisfies the rank condition. Hence every local ring satisfies the rank condition, and in
particular has invariant basis number. Mathlib provides these instances for commutative rings and
for division rings; the local case is needed to identify the projective `K₀` of a noncommutative
local ring with `ℤ`.

## Main results

* `RankCondition.of_ringHom`: if `f : R →+* S` and `S` satisfies the rank condition, so does `R`.
* `IsLocalRing.rankCondition`: a possibly noncommutative local ring satisfies the rank condition.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, GTM 189, Springer (1999), Chapter 1,
  §1 (Free modules: invariant basis number and the rank condition).
-/

public section

/-- The rank condition pulls back along ring homomorphisms: a matrix identity `B * A = 1`
over `R` maps to one over `S`. -/
theorem RankCondition.of_ringHom {R S : Type*} [Semiring R] [Semiring S] [RankCondition S]
    (f : R →+* S) : RankCondition R :=
  rankCondition_iff_matrix.mpr fun n m A B h ↦ rankCondition_iff_matrix.mp ‹_› n m (A.map f)
    (B.map f) (by rw [← Matrix.map_mul, h, Matrix.map_one _ f.map_zero f.map_one])

/-- A possibly noncommutative local ring satisfies the rank condition, hence has invariant basis
number: it maps onto the division ring `R ⧸ Ring.jacobson R`. -/
instance (priority := 100) IsLocalRing.rankCondition {R : Type*} [Ring R] [IsLocalRing R] :
    RankCondition R :=
  .of_ringHom (Ideal.Quotient.mk (Ring.jacobson R))
