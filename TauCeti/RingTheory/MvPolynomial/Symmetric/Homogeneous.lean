/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# The symmetric homogeneous polynomials of a fixed degree

The symmetric polynomials of `Mathlib.RingTheory.MvPolynomial.Symmetric.Defs` are graded by total
degree, each graded piece being the intersection of `MvPolynomial.symmetricSubalgebra` with the
homogeneous polynomials `MvPolynomial.homogeneousSubmodule` of that degree.  This file names that
intersection, `TauCeti.symmetricHomogeneousSubmodule`, and nothing else; it is the module the
classical families of symmetric polynomials are bases of, one degree at a time: the monomial
symmetric polynomials over any commutative semiring, and the Schur polynomials over a commutative
ring.

## Main definitions

* `TauCeti.symmetricHomogeneousSubmodule σ R n`: the polynomials in `σ` over `R` that are both
  symmetric and homogeneous of degree `n`.

## Main results

* `MvPolynomial.isHomogeneous_esymm`: the elementary symmetric polynomial `eₖ` is homogeneous of
  degree `k`.
-/

public section

namespace TauCeti

open MvPolynomial

variable (σ : Type*) (R : Type*) [CommSemiring R] (n : ℕ)

/-- **The symmetric polynomials of degree `n`**: those polynomials in the alphabet `σ` over `R`
that are both symmetric and homogeneous of degree `n`.  The monomial symmetric polynomials of the
partitions of `n` are a basis of this module over any commutative semiring; the Schur polynomials
of those partitions are a basis of it over a commutative ring. -/
noncomputable def symmetricHomogeneousSubmodule : Submodule R (MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).toSubmodule ⊓ homogeneousSubmodule σ R n

variable {σ R n}

/-- Membership in `TauCeti.symmetricHomogeneousSubmodule` is the conjunction of the two
conditions defining it. -/
@[simp]
theorem mem_symmetricHomogeneousSubmodule {p : MvPolynomial σ R} :
    p ∈ symmetricHomogeneousSubmodule σ R n ↔ p.IsSymmetric ∧ p.IsHomogeneous n :=
  Iff.rfl

end TauCeti

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The elementary symmetric polynomial `eₖ` is homogeneous of degree `k`. -/
theorem isHomogeneous_esymm [Fintype σ] (k : ℕ) : (esymm σ R k).IsHomogeneous k := by
  rw [esymm_eq_sum_subtype]
  refine IsHomogeneous.sum _ _ _ fun t _ => ?_
  have h := IsHomogeneous.prod (t : Finset σ) (fun i => (X i : MvPolynomial σ R)) (fun _ => 1)
    fun i _ => isHomogeneous_X R i
  rwa [Finset.sum_const, smul_eq_mul, mul_one, t.2] at h

end MvPolynomial
