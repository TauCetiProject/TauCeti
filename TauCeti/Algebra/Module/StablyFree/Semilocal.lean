/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Stably free modules over semilocal rings are free

A module `M` over a commutative ring `R` is stably free (`Module.IsStablyFree`) when `M × N` is
free for some finite free module `N`. Over a semilocal ring, a commutative ring with finitely many
maximal ideals, every finitely generated stably free module is free. Such a module is projective,
hence flat, and its rank at a maximal ideal `P`, the dimension of `(R ⧸ P) ⊗[R] M`, is the
difference of the ranks of the free modules `M × N` and `N`, which does not depend on `P`; a finite
flat module of constant rank over a semilocal ring is free (Mathlib's
`Module.free_of_flat_of_finrank_eq`, Stacks 02M9).

Over a semilocal ring this is the cancellation that turns a unimodular frame of `Rⁿ`, an `n × k`
matrix with a left inverse, into the first `k` columns of an invertible matrix: the kernel of the
left inverse is a complement of the frame, and it is stably free.

## Main results

* `Module.free_of_isStablyFree_of_finite_maximalSpectrum`: over a commutative ring with finitely
  many maximal ideals, a finitely generated stably free module is free.

## References

* [The Stacks Project, Tag 02M9](https://stacks.math.columbia.edu/tag/02M9)
-/

public section

namespace Module

open TensorProduct

/-- Over a commutative semilocal ring, a ring with finitely many maximal ideals, every finitely
generated stably free module is free. -/
theorem free_of_isStablyFree_of_finite_maximalSpectrum (R M : Type*) [CommRing R]
    [Finite (MaximalSpectrum R)] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [IsStablyFree R M] : Free R M := by
  obtain ⟨N, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R M
  refine free_of_flat_of_finrank_eq R M (finrank R (M × N) - finrank R N) fun P ↦ ?_
  let := @Ideal.Quotient.field
  have : Nontrivial R := (Ideal.Quotient.mk P.asIdeal).domain_nontrivial
  have h := (prodRight R (R ⧸ P.asIdeal) (R ⧸ P.asIdeal) M N).finrank_eq
  rw [finrank_prod, finrank_baseChange (M' := M × N), finrank_baseChange (M' := N)] at h
  omega

end Module
