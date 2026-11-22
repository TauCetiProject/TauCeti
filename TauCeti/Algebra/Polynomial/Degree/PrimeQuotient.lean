/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Detecting degree bounds modulo prime ideals

The nilradical of a commutative ring is the intersection of its prime ideals
(`nilpotent_iff_mem_prime`). Hence if a polynomial `p` has degree at most `n` modulo every prime
ideal, then every coefficient of `p` of degree above `n` is nilpotent, and over a reduced ring
`p` itself has degree at most `n`.

## Main results

* `Polynomial.isNilpotent_coeff_of_forall_natDegree_map_mk_le`: a degree bound modulo every prime
  ideal makes the higher coefficients nilpotent.
* `Polynomial.natDegree_le_of_forall_natDegree_map_mk_le`: over a reduced ring, a degree bound
  modulo every prime ideal is a degree bound.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] {p : R[X]} {n : ℕ}

/-- If `p` has degree at most `n` modulo every prime ideal, then every coefficient of `p` of
degree above `n` lies in every prime ideal, hence is nilpotent. -/
theorem isNilpotent_coeff_of_forall_natDegree_map_mk_le
    (hp : ∀ (P : Ideal R) [P.IsPrime], (p.map (Ideal.Quotient.mk P)).natDegree ≤ n)
    {m : ℕ} (hm : n < m) : IsNilpotent (p.coeff m) :=
  nilpotent_iff_mem_prime.2 fun P _ => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map]
    exact coeff_eq_zero_of_natDegree_lt ((hp P).trans_lt hm)

/-- Over a reduced commutative ring, a degree bound can be checked modulo prime ideals: if `p` has
degree at most `n` modulo every prime ideal, then `p.natDegree ≤ n`. -/
theorem natDegree_le_of_forall_natDegree_map_mk_le [IsReduced R]
    (hp : ∀ (P : Ideal R) [P.IsPrime], (p.map (Ideal.Quotient.mk P)).natDegree ≤ n) :
    p.natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.2 fun _ hm =>
    IsReduced.eq_zero _
      (isNilpotent_coeff_of_forall_natDegree_map_mk_le hp (by exact_mod_cast hm))

end Polynomial
