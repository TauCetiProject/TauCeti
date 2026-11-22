/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Degree.PrimeQuotient

/-!
# Compositional inverses over a reduced ring

Over a domain, the degree of a composition is the product of the degrees
(`Polynomial.natDegree_comp`), so two polynomials with `p.comp q = X` both have degree one. Over
a reduced commutative ring the same conclusion holds for the degree bound: modulo every prime
ideal the composition identity persists in a polynomial domain, so every coefficient of degree
at least two of `p` or `q` lies in every prime ideal, hence is nilpotent
(`Polynomial.isNilpotent_coeff_of_forall_natDegree_map_mk_le`) and thus zero.

Reducedness cannot be dropped: over `ℤ[ε]/(ε²)` the polynomials `X + ε X²` and `X - ε X²` are
inverse to each other under composition.

## Main results

* `Polynomial.natDegree_map_mk_eq_one_of_comp_eq_X`: over any commutative ring, `p.comp q = X`
  forces both `p` and `q` to have degree one modulo every prime ideal.
* `Polynomial.isNilpotent_coeff_of_comp_eq_X`: over any commutative ring, the coefficients of
  degree at least two of `p` and `q` are nilpotent.
* `Polynomial.natDegree_le_one_of_comp_eq_X_left`: over a reduced ring, `p.comp q = X` forces
  `p.natDegree ≤ 1`.
* `Polynomial.natDegree_le_one_of_comp_eq_X_right`: under the same hypothesis, `q.natDegree ≤ 1`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Modulo a prime ideal, both factors of a compositional identity `p.comp q = X` have degree
one. This holds over any commutative ring, reduced or not. -/
theorem natDegree_map_mk_eq_one_of_comp_eq_X {p q : R[X]} (h : p.comp q = X)
    (P : Ideal R) [P.IsPrime] :
    (p.map (Ideal.Quotient.mk P)).natDegree = 1 ∧ (q.map (Ideal.Quotient.mk P)).natDegree = 1 := by
  have hmap : (p.map (Ideal.Quotient.mk P)).comp (q.map (Ideal.Quotient.mk P)) = X := by
    rw [← map_comp, h, map_X]
  have hdeg := congrArg natDegree hmap
  rw [natDegree_comp, natDegree_X] at hdeg
  exact ⟨Nat.eq_one_of_mul_eq_one_right hdeg, Nat.eq_one_of_mul_eq_one_left hdeg⟩

/-- Over any commutative ring, if `p.comp q = X` then the coefficients of degree at least two of
both `p` and `q` are nilpotent. In particular a nonnilpotent coefficient of degree at least two
rules out a compositional inverse on either side. -/
theorem isNilpotent_coeff_of_comp_eq_X {p q : R[X]} (h : p.comp q = X) {n : ℕ} (hn : 1 < n) :
    IsNilpotent (p.coeff n) ∧ IsNilpotent (q.coeff n) :=
  ⟨isNilpotent_coeff_of_forall_natDegree_map_mk_le
      (fun P _ => (natDegree_map_mk_eq_one_of_comp_eq_X h P).1.le) hn,
    isNilpotent_coeff_of_forall_natDegree_map_mk_le
      (fun P _ => (natDegree_map_mk_eq_one_of_comp_eq_X h P).2.le) hn⟩

/-- Over a reduced commutative ring, a polynomial `p` with a right compositional inverse, that
is `p.comp q = X`, has degree at most one. Without reducedness this fails: over `ℤ[ε]/(ε²)`,
`(X + ε X²).comp (X - ε X²) = X`. -/
theorem natDegree_le_one_of_comp_eq_X_left [IsReduced R] {p q : R[X]} (h : p.comp q = X) :
    p.natDegree ≤ 1 :=
  natDegree_le_iff_coeff_eq_zero.2 fun _ hn =>
    IsReduced.eq_zero _ (isNilpotent_coeff_of_comp_eq_X h (by exact_mod_cast hn)).1

/-- Over a reduced commutative ring, a polynomial `q` with a left compositional inverse, that is
`p.comp q = X`, has degree at most one. -/
theorem natDegree_le_one_of_comp_eq_X_right [IsReduced R] {p q : R[X]} (h : p.comp q = X) :
    q.natDegree ≤ 1 :=
  natDegree_le_iff_coeff_eq_zero.2 fun _ hn =>
    IsReduced.eq_zero _ (isNilpotent_coeff_of_comp_eq_X h (by exact_mod_cast hn)).2

end Polynomial
