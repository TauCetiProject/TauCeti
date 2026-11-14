/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Funext
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization

/-!
# Good shear directions over infinite integral domains

For any finite family of polynomials in `n + 1` variables over a nontrivial commutative semiring
without zero divisors, the product of the dehomogenizations of the top homogeneous components of
its nonzero members is a nonzero polynomial `P` in `n` variables whose nonvanishing at
`a : Fin n → R` characterizes simultaneous good shear directions `i.insertNth 1 a`
(`TauCeti.exists_ne_zero_and_eval_ne_zero_iff_forall_eval_insertNth_homogeneousComponent_ne_zero`).

Over an infinite integral domain `R`, combining this characterization with
`MvPolynomial.exists_eval_ne_zero` shows that any finite family of polynomials in `n + 1` variables
admits a simultaneous shear direction `i.insertNth 1 a` on which the top homogeneous component of
each nonzero member is nonzero
(`TauCeti.exists_forall_eval_insertNth_homogeneousComponent_ne_zero`).

Together with `MvPolynomial.coeff_shearToPolynomial_totalDegree` and
`MvPolynomial.leadingCoeff_shearToPolynomial_of_eval_ne_zero`, such a shear turns every nonzero
member of the family into a univariate polynomial in the distinguished coordinate whose leading
coefficient is a nonzero constant in `R`. This is the algebraic generic-direction lemma underlying
linear Noether normalization over infinite fields, without any topological assumptions on `R`
(compare `TauCeti.dense_setOf_forall_eval_insertNth_homogeneousComponent_ne_zero`).

## Main results

* `TauCeti.exists_ne_zero_and_eval_ne_zero_iff_forall_eval_insertNth_homogeneousComponent_ne_zero`:
  simultaneous good shear directions are cut out by the nonvanishing of a single nonzero polynomial.
* `TauCeti.exists_forall_eval_insertNth_homogeneousComponent_ne_zero`: simultaneous good shear
  directions exist for any finite family of polynomials over an infinite domain.
* `TauCeti.exists_eval_insertNth_homogeneousComponent_ne_zero`: specialization to a single nonzero
  polynomial.

## References

* J. S. Milne, *Algebraic Geometry*, Lemma 2.46.
* [Stacks Project, Tag 00OY](https://stacks.math.columbia.edu/tag/00OY)
-/

public section

namespace TauCeti

open MvPolynomial

/-- For any finite family of polynomials in `n + 1` variables over a nontrivial commutative semiring
without zero divisors, there is a nonzero polynomial `P` in `n` variables whose nonvanishing at
`a : Fin n → R` characterizes simultaneous nonvanishing of the top homogeneous components of all
nonzero members at `i.insertNth 1 a`. -/
theorem exists_ne_zero_and_eval_ne_zero_iff_forall_eval_insertNth_homogeneousComponent_ne_zero
    {ι R : Type*} [Finite ι] [CommSemiring R] [Nontrivial R] [NoZeroDivisors R] {n : ℕ}
    (p : ι → MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)) :
    ∃ P : MvPolynomial (Fin n) R, P ≠ 0 ∧ ∀ a : Fin n → R,
      eval a P ≠ 0 ↔ ∀ k, p k ≠ 0 →
        eval (i.insertNth 1 a) (homogeneousComponent (p k).totalDegree (p k)) ≠ 0 := by
  classical
  cases nonempty_fintype ι
  let H (k : ι) : MvPolynomial (Fin n) R :=
    if p k = 0 then 1 else dehomogenize i (homogeneousComponent (p k).totalDegree (p k))
  have hH (k : ι) : H k ≠ 0 := by
    by_cases hk : p k = 0
    · simp [H, hk]
    · simp only [H, hk, ite_false]
      exact dehomogenize_ne_zero_of_isHomogeneous i (homogeneousComponent_isHomogeneous _ _)
        ((p k).homogeneousComponent_totalDegree_ne_zero hk)
  refine ⟨∏ k, H k, Finset.prod_ne_zero_iff.mpr fun k _ ↦ hH k, fun a ↦ ?_⟩
  simp only [map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]
  refine forall_congr' fun k ↦ ?_
  by_cases hk : p k = 0 <;> simp [H, hk]

/-- Over an infinite integral domain, any finite family of polynomials in `n + 1` variables admits
a simultaneous shear parameter `a : Fin n → R` on which the top homogeneous part of every nonzero
member is nonzero at `i.insertNth 1 a`. -/
theorem exists_forall_eval_insertNth_homogeneousComponent_ne_zero
    {ι R : Type*} [Finite ι] [CommRing R] [IsDomain R] [Infinite R] {n : ℕ}
    (p : ι → MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)) :
    ∃ a : Fin n → R, ∀ k, p k ≠ 0 →
      eval (i.insertNth 1 a) (homogeneousComponent (p k).totalDegree (p k)) ≠ 0 := by
  obtain ⟨P, hP, hiff⟩ :=
    exists_ne_zero_and_eval_ne_zero_iff_forall_eval_insertNth_homogeneousComponent_ne_zero p i
  obtain ⟨a, ha⟩ := exists_eval_ne_zero hP
  exact ⟨a, (hiff a).mp ha⟩

/-- Over an infinite integral domain, a nonzero polynomial `p` in `n + 1` variables admits a shear
parameter `a : Fin n → R` at which its top homogeneous component is nonzero at `i.insertNth 1 a`. -/
theorem exists_eval_insertNth_homogeneousComponent_ne_zero
    {R : Type*} [CommRing R] [IsDomain R] [Infinite R] {n : ℕ}
    {p : MvPolynomial (Fin (n + 1)) R} (hp : p ≠ 0) (i : Fin (n + 1)) :
    ∃ a : Fin n → R, eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p) ≠ 0 := by
  obtain ⟨a, ha⟩ :=
    exists_forall_eval_insertNth_homogeneousComponent_ne_zero (fun _ : Unit ↦ p) i
  exact ⟨a, ha () hp⟩

end TauCeti
