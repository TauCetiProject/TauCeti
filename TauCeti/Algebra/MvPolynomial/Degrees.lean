/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Degree bounds for multivariate polynomials

A ring homomorphism `f : R →+* S` applied to the coefficients of a multivariate polynomial `P`
can only remove monomials, so it does not raise any partial degree. This is the partial-degree
form of Mathlib's `MvPolynomial.degrees_map_le`.

Every element in the `R`-linear span of a family `x : σ → S` in an `R`-algebra `S` is the value at
`x` of a polynomial over `R` of total degree at most `1`, obtained by replacing each generator `xᵢ`
with `Xᵢ`.

## Main results

* `MvPolynomial.degreeOf_map_le`: `degreeOf i (P.map f) ≤ degreeOf i P`.
* `MvPolynomial.exists_totalDegree_le_one_aeval_eq_of_mem_span`: every
  `t ∈ Submodule.span R (Set.range x)` is `aeval x P` for some `P` with `P.totalDegree ≤ 1`.
-/

public section

namespace MvPolynomial

/-- Mapping the coefficients of `P` does not raise its degree in `Xᵢ`. -/
theorem degreeOf_map_le {σ R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (P : MvPolynomial σ R) (i : σ) : (P.map f).degreeOf i ≤ P.degreeOf i :=
  degreeOf_le_iff.2 fun _ hs ↦ monomial_le_degreeOf i (support_map_subset f P hs)

/-- Every element in the `R`-linear span of a family `x : σ → S` is the value at `x` of a
multivariate polynomial over `R` of total degree at most `1`. -/
theorem exists_totalDegree_le_one_aeval_eq_of_mem_span {σ R S : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] {x : σ → S} {t : S}
    (ht : t ∈ Submodule.span R (Set.range x)) :
    ∃ P : MvPolynomial σ R, P.totalDegree ≤ 1 ∧ aeval x P = t := by
  induction ht using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨i, rfl⟩ := h
    exact ⟨X i,
      by simpa [← X_pow_eq_monomial] using totalDegree_monomial_le (Finsupp.single i 1) (1 : R),
      aeval_X x i⟩
  | zero => exact ⟨0, by simp, map_zero _⟩
  | add _ _ _ _ hp hq =>
    obtain ⟨P, hPd, rfl⟩ := hp
    obtain ⟨Q, hQd, rfl⟩ := hq
    exact ⟨P + Q, (totalDegree_add P Q).trans (max_le hPd hQd), map_add _ P Q⟩
  | smul c _ _ hp =>
    obtain ⟨P, hPd, rfl⟩ := hp
    exact ⟨c • P, (totalDegree_smul_le c P).trans hPd, map_smul _ c P⟩

end MvPolynomial
