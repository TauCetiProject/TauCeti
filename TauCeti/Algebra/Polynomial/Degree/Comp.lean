/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Compositional inverses over a reduced ring

Over a domain, the degree of a composition is the product of the degrees
(`Polynomial.natDegree_comp`), so two polynomials with `p.comp q = X` both have degree one. Over
a reduced commutative ring the same conclusion holds for the degree bound: modulo every prime
ideal the composition identity persists in a polynomial domain, so every coefficient of degree
at least two of `p` or `q` lies in every prime ideal, hence is nilpotent and thus zero.

Reducedness cannot be dropped: over `ℤ[ε]/(ε²)` the polynomials `X + ε X²` and `X - ε X²` are
inverse to each other under composition.

## Main results

* `Polynomial.natDegree_le_one_of_comp_eq_X_left`: over a reduced ring, `p.comp q = X` forces
  `p.natDegree ≤ 1`.
* `Polynomial.natDegree_le_one_of_comp_eq_X_right`: under the same hypothesis, `q.natDegree ≤ 1`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Modulo a prime ideal, both factors of a compositional identity `p.comp q = X` have degree
one. -/
private theorem natDegree_map_mk_eq_one_of_comp_eq_X {p q : R[X]} (h : p.comp q = X)
    (P : Ideal R) [P.IsPrime] :
    (p.map (Ideal.Quotient.mk P)).natDegree = 1 ∧ (q.map (Ideal.Quotient.mk P)).natDegree = 1 := by
  have hmap : (p.map (Ideal.Quotient.mk P)).comp (q.map (Ideal.Quotient.mk P)) = X := by
    rw [← map_comp, h, map_X]
  have hdeg := congrArg natDegree hmap
  rw [natDegree_comp, natDegree_X] at hdeg
  exact ⟨Nat.eq_one_of_mul_eq_one_right hdeg, Nat.eq_one_of_mul_eq_one_left hdeg⟩

/-- A coefficient that vanishes modulo every prime ideal of a reduced ring is zero. -/
private theorem coeff_eq_zero_of_forall_natDegree_map_le_one [IsReduced R] {p : R[X]}
    (hp : ∀ (P : Ideal R) [P.IsPrime], (p.map (Ideal.Quotient.mk P)).natDegree ≤ 1)
    {n : ℕ} (hn : 1 < n) : p.coeff n = 0 := by
  refine IsReduced.eq_zero _ ((nilpotent_iff_mem_prime).2 fun P hP => ?_)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map]
  exact coeff_eq_zero_of_natDegree_lt ((hp P).trans_lt hn)

/-- Over a reduced commutative ring, a polynomial `p` with a right compositional inverse, that
is `p.comp q = X`, has degree at most one. Without reducedness this fails: over `ℤ[ε]/(ε²)`,
`(X + ε X²).comp (X - ε X²) = X`. -/
theorem natDegree_le_one_of_comp_eq_X_left [IsReduced R] {p q : R[X]} (h : p.comp q = X) :
    p.natDegree ≤ 1 :=
  natDegree_le_iff_coeff_eq_zero.2 fun n hn =>
    coeff_eq_zero_of_forall_natDegree_map_le_one
      (fun P _ => (natDegree_map_mk_eq_one_of_comp_eq_X h P).1.le) (by exact_mod_cast hn)

/-- Over a reduced commutative ring, a polynomial `q` with a left compositional inverse, that is
`p.comp q = X`, has degree at most one. -/
theorem natDegree_le_one_of_comp_eq_X_right [IsReduced R] {p q : R[X]} (h : p.comp q = X) :
    q.natDegree ≤ 1 :=
  natDegree_le_iff_coeff_eq_zero.2 fun n hn =>
    coeff_eq_zero_of_forall_natDegree_map_le_one
      (fun P _ => (natDegree_map_mk_eq_one_of_comp_eq_X h P).2.le) (by exact_mod_cast hn)

end Polynomial
