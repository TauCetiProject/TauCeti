/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import TauCeti.RingTheory.MvPolynomial.LineRestriction

/-!
# Good shear directions over infinite integral domains

Over an infinite integral domain `R`, every nonzero multivariate polynomial takes a nonzero value
at some assignment of the variables (`MvPolynomial.exists_eval_ne_zero`). Together with the
injectivity of dehomogenization on forms of fixed degree (`TauCeti.dehomogenize_injOn`), any finite
family of polynomials in `n + 1` variables admits a simultaneous shear direction `i.insertNth 1 a`
on which the top homogeneous component of each nonzero member is nonzero
(`TauCeti.exists_forall_eval_insertNth_homogeneousComponent_ne_zero`).

Combined with `MvPolynomial.coeff_shearToPolynomial_totalDegree` and
`MvPolynomial.leadingCoeff_shearToPolynomial_of_eval_ne_zero`, such a shear turns every nonzero
member of the family into a univariate polynomial in the distinguished coordinate whose leading
coefficient is a nonzero constant in `R`. This is the algebraic generic-direction lemma underlying
linear Noether normalization over infinite fields, without any topological assumptions on `R`
(compare `TauCeti.dense_setOf_forall_eval_insertNth_homogeneousComponent_ne_zero`).

## Main results

* `MvPolynomial.exists_eval_ne_zero`: a nonzero polynomial over an infinite domain does not vanish
  everywhere.
* `TauCeti.dehomogenize_ne_zero_of_isHomogeneous`: dehomogenizing a nonzero homogeneous polynomial
  in any standard affine chart yields a nonzero polynomial.
* `TauCeti.exists_forall_eval_insertNth_homogeneousComponent_ne_zero`: simultaneous good shear
  directions exist for any finite family of polynomials over an infinite domain.
* `TauCeti.exists_eval_insertNth_homogeneousComponent_ne_zero`: specialization to a single nonzero
  polynomial, together with the resulting degree and leading-coefficient formulas for
  `MvPolynomial.shearToPolynomial`.

## References

* J. S. Milne, *Algebraic Geometry*, Lemma 2.46.
* [Stacks Project, Tag 00OY](https://stacks.math.columbia.edu/tag/00OY)
-/

public section

namespace MvPolynomial

/-- Over an infinite integral domain, a nonzero multivariate polynomial takes a nonzero value at
some assignment of the variables. -/
theorem exists_eval_ne_zero {σ R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    {p : MvPolynomial σ R} (hp : p ≠ 0) : ∃ x : σ → R, eval x p ≠ 0 := by
  contrapose! hp
  exact funext fun x ↦ by simp [hp x]

end MvPolynomial

namespace TauCeti

open MvPolynomial

/-- Dehomogenizing a nonzero homogeneous polynomial in any standard chart produces a nonzero
polynomial. -/
theorem dehomogenize_ne_zero_of_isHomogeneous {R : Type*} [CommSemiring R] {n d : ℕ}
    (i : Fin (n + 1)) {p : MvPolynomial (Fin (n + 1)) R} (hp : p.IsHomogeneous d) (hne : p ≠ 0) :
    dehomogenize i p ≠ 0 := fun hzero ↦
  hne <| dehomogenize_injOn i d hp (isHomogeneous_zero _ _ _) (by simpa using hzero)

/-- Over an infinite integral domain, any finite family of polynomials in `n + 1` variables admits
a simultaneous shear parameter `a : Fin n → R` on which the top homogeneous part of every nonzero
member is nonzero at `i.insertNth 1 a`. -/
theorem exists_forall_eval_insertNth_homogeneousComponent_ne_zero
    {ι R : Type*} [Finite ι] [CommRing R] [IsDomain R] [Infinite R] {n : ℕ}
    (p : ι → MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)) :
    ∃ a : Fin n → R, ∀ k, p k ≠ 0 →
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
  have hprod : (∏ k, H k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hH k
  obtain ⟨a, ha⟩ := exists_eval_ne_zero hprod
  rw [map_prod, Finset.prod_ne_zero_iff] at ha
  refine ⟨a, fun k hk ↦ ?_⟩
  simpa [H, hk] using ha k (Finset.mem_univ k)

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
