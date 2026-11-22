/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Polynomial.Content

/-!
# Bivariate specialization and swapped-degree formulas

In the bivariate polynomial ring `R[X][Y]`, a coefficient homomorphism `evalRingHom b : R[X] →+* R`
evaluates the inner variable `X` at `b`, yielding the univariate fiber `P(b, Y)`. Over a
nontrivial commutative ring, this inner-variable specialization of any primitive bivariate
polynomial `F : R[X][Y]` is nonzero for every `b : R`
(`Polynomial.IsPrimitive.map_evalRingHom_ne_zero`).

When a bivariate polynomial factors as `P = C c * s.prod`, its swapped natural degree
`(Bivariate.swap P).natDegree` splits additively as `c.natDegree` plus the sum of
`(Bivariate.swap F).natDegree` over `F ∈ s`
(`Polynomial.natDegree_swap_eq_of_eq_C_mul_multiset_prod`).

## Main results

* `Polynomial.natDegree_swap_eq_of_eq_C_mul_multiset_prod`: swapped (inner-variable) natural
  degree of a bivariate product `C c * s.prod`.
* `Polynomial.IsPrimitive.map_evalRingHom_ne_zero`: over a nontrivial commutative ring,
  specializing the inner variable `X` of a primitive bivariate polynomial `F : R[X][Y]` at any
  `b : R` yields a nonzero polynomial `F(b, Y)`.
-/

public section

open scoped Polynomial.Bivariate

namespace Polynomial

/-- Over a commutative semiring without zero divisors, if a bivariate polynomial factors as
`P = C c * s.prod` with `c ≠ 0` and all factors in `s` nonzero, then `(Bivariate.swap P).natDegree`
is `c.natDegree` plus the sum of `(Bivariate.swap F).natDegree` over `F ∈ s`. -/
theorem natDegree_swap_eq_of_eq_C_mul_multiset_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    {P : R[X][Y]} {c : R[X]} {s : Multiset R[X][Y]} (hPeq : P = C c * s.prod) (hc0 : c ≠ 0)
    (hs0 : ∀ F ∈ s, F ≠ 0) :
    (Bivariate.swap P).natDegree =
      c.natDegree + (s.map fun F ↦ (Bivariate.swap F).natDegree).sum := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact absurd (Subsingleton.elim c 0) hc0
  have hswap_ne : ∀ q ∈ s.map (Bivariate.swap (R := R)), q ≠ 0 := by
    intro q hq
    obtain ⟨F, hF, rfl⟩ := Multiset.mem_map.mp hq
    simpa using hs0 F hF
  have hmap_c : c.map (C : R →+* R[X]) ≠ 0 := by
    simpa using (Polynomial.map_injective (C : R →+* R[X]) C_injective).ne hc0
  have hswap_prod : (s.map (Bivariate.swap (R := R))).prod ≠ 0 :=
    Multiset.prod_ne_zero fun h0 ↦ hswap_ne 0 h0 rfl
  rw [hPeq, map_mul, Bivariate.swap_C, map_multiset_prod,
    natDegree_mul hmap_c hswap_prod,
    natDegree_map_eq_of_injective C_injective,
    natDegree_multiset_prod _ fun h0 ↦ hswap_ne 0 h0 rfl,
    Multiset.map_map, Function.comp_def]

/-- Over a nontrivial commutative ring, specializing the inner variable `X` (i.e. evaluating the
coefficient polynomials in `R[X]`) of a primitive bivariate polynomial `F : R[X][Y]` at any scalar
`b : R` yields a nonzero univariate polynomial `F(b, Y)` (unlike specializing the outer variable
`Y`, which can vanish). -/
theorem IsPrimitive.map_evalRingHom_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    {F : R[X][Y]} (hF : F.IsPrimitive) (b : R) :
    F.map (evalRingHom b) ≠ 0 := by
  intro h0
  have hdvd : C (X - C b) ∣ F := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [dvd_iff_isRoot, IsRoot]
    have hi : (F.map (evalRingHom b)).coeff i = 0 := by rw [h0, coeff_zero]
    simpa [coeff_map] using hi
  exact not_isUnit_X_sub_C b (hF _ hdvd)

end Polynomial
