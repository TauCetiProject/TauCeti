/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Wronskian
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Partial-degree bounds for generalized Wronskians

The generalized Wronskian of `m` multivariate polynomials is an `m × m` determinant whose
entries are Hasse derivatives. Since Hasse derivatives do not increase partial degree, its
partial degree in any variable is at most the sum of the corresponding partial-degree bounds
for the columns. In particular, a common bound `N` on the columns gives the bound `m * N`.

This is the degree estimate used for the auxiliary generalized Wronskians in Roth's lemma.

## Main results

* `MvPolynomial.degreeOf_genWronskian_le_sum`: bounds a generalized Wronskian using a separate
  partial-degree bound for every column.
* `MvPolynomial.degreeOf_genWronskian_le`: a common partial-degree bound `N` gives the bound
  `m * N`.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.4.5.
-/

public section

noncomputable section

namespace MvPolynomial

open Matrix Finset

variable {R σ : Type*} [CommRing R] {m : ℕ}

private theorem degreeOf_det_le_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial σ R)) (i : σ) (e : n → ℕ)
    (hA : ∀ k l, (A k l).degreeOf i ≤ e l) :
    A.det.degreeOf i ≤ ∑ l, e l := by
  rw [Matrix.det_apply]
  refine (degreeOf_sum_le i univ _).trans (Finset.sup_le fun p _ ↦ ?_)
  calc
    (Equiv.Perm.sign p • ∏ l, A (p l) l).degreeOf i =
        (∏ l, A (p l) l).degreeOf i := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp
      · rw [hp, one_smul]
      · rw [hp, Units.neg_smul, one_smul, degreeOf_neg]
    _ ≤ ∑ l, (A (p l) l).degreeOf i := degreeOf_prod_le i univ _
    _ ≤ ∑ l, e l := Finset.sum_le_sum fun l _ ↦ hA (p l) l

/-- If the `l`-th polynomial has partial degree at most `e l` in `Xᵢ`, then the partial degree
of any generalized Wronskian of the family in `Xᵢ` is at most `∑ l, e l`.

No admissibility hypothesis on the derivative rows is needed: every Hasse derivative weakly
decreases each partial degree. -/
theorem degreeOf_genWronskian_le_sum (D : Fin m → σ →₀ ℕ) (f : Fin m → MvPolynomial σ R)
    (i : σ) (e : Fin m → ℕ) (hf : ∀ l, (f l).degreeOf i ≤ e l) :
    (genWronskian D f).degreeOf i ≤ ∑ l, e l := by
  rw [genWronskian_def]
  refine degreeOf_det_le_sum _ i e fun k l ↦ ?_
  exact (degreeOf_hasseDeriv_le (D k) (f l) i).trans
    ((Nat.sub_le _ _).trans (hf l))

/-- If every polynomial in a family of size `m` has partial degree at most `N` in `Xᵢ`, then
the partial degree of any generalized Wronskian of the family in `Xᵢ` is at most `m * N`. -/
theorem degreeOf_genWronskian_le (D : Fin m → σ →₀ ℕ) (f : Fin m → MvPolynomial σ R)
    (i : σ) (N : ℕ) (hf : ∀ l, (f l).degreeOf i ≤ N) :
    (genWronskian D f).degreeOf i ≤ m * N := by
  simpa using degreeOf_genWronskian_le_sum D f i (fun _ ↦ N) hf

end MvPolynomial
