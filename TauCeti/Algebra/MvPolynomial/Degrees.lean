/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Degree bounds for multivariate polynomials

A variable `Xᵢ` has total degree at most `1` over every commutative semiring. Mathlib's
`MvPolynomial.totalDegree_X` computes it exactly but needs a nontrivial semiring.

A ring homomorphism `f : R →+* S` applied to the coefficients of a multivariate polynomial `P`
can only remove monomials, so it does not raise any partial degree. This is the partial-degree
form of Mathlib's `MvPolynomial.degrees_map_le`.

Every element in the `R`-linear span of a family `x : σ → S` in an `R`-algebra `S` is the value at
`x` of a polynomial over `R` of total degree at most `1`, obtained by replacing each generator `xᵢ`
with `Xᵢ`.

Substituting polynomials of total degree at most `D` for the variables of a polynomial `p`
multiplies the total degree by at most `D`. This bounds the degrees of polynomial expressions
after a change of generators of a finitely generated algebra.

## Main results

* `MvPolynomial.totalDegree_X_le`: `(X i).totalDegree ≤ 1`, over any commutative semiring.
* `MvPolynomial.degreeOf_map_le`: `degreeOf i (P.map f) ≤ degreeOf i P`.
* `MvPolynomial.exists_totalDegree_le_one_aeval_eq_of_mem_span`: every
  `t ∈ Submodule.span R (Set.range x)` is `aeval x P` for some `P` with `P.totalDegree ≤ 1`.
* `MvPolynomial.totalDegree_aeval_le`: if every `f i` has total degree at most `D`, then
  `aeval f p` has total degree at most `p.totalDegree * D`.
-/

public section

namespace MvPolynomial

/-- A variable has total degree at most `1`. Unlike Mathlib's `MvPolynomial.totalDegree_X`, this
needs no nontriviality assumption on `R`. -/
theorem totalDegree_X_le {σ R : Type*} [CommSemiring R] (i : σ) :
    (X i : MvPolynomial σ R).totalDegree ≤ 1 := by
  rw [X]
  exact (totalDegree_monomial_le _ _).trans_eq (by simp)

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
    exact ⟨X i, totalDegree_X_le i, aeval_X x i⟩
  | zero => exact ⟨0, by simp, map_zero _⟩
  | add _ _ _ _ hp hq =>
    obtain ⟨P, hPd, rfl⟩ := hp
    obtain ⟨Q, hQd, rfl⟩ := hq
    exact ⟨P + Q, (totalDegree_add P Q).trans (max_le hPd hQd), map_add _ P Q⟩
  | smul c _ _ hp =>
    obtain ⟨P, hPd, rfl⟩ := hp
    exact ⟨c • P, (totalDegree_smul_le c P).trans hPd, map_smul _ c P⟩

/-- Substituting polynomials of total degree at most `D` for the variables multiplies the total
degree by at most `D`. -/
theorem totalDegree_aeval_le {σ τ R : Type*} [CommSemiring R] {f : σ → MvPolynomial τ R} {D : ℕ}
    (hf : ∀ i, (f i).totalDegree ≤ D) (p : MvPolynomial σ R) :
    (aeval f p).totalDegree ≤ p.totalDegree * D := by
  rw [aeval_def, eval₂_eq, algebraMap_eq]
  refine totalDegree_finsetSum_le fun s hs ↦ ?_
  rw [← smul_eq_C_mul]
  refine (totalDegree_smul_le _ _).trans <| (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ s.support, (f i ^ s i).totalDegree ≤ ∑ i ∈ s.support, s i * D :=
        Finset.sum_le_sum fun i _ ↦ (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i))
    _ = (s.sum fun _ e ↦ e) * D := (Finsupp.sum_mul D s (f := fun _ e ↦ e)).symm
    _ ≤ p.totalDegree * D := Nat.mul_le_mul_right _ (le_totalDegree hs)

end MvPolynomial
