/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Wronskian
import TauCeti.LinearAlgebra.Matrix.MvPolynomial

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
* `MvPolynomial.notMem_vars_genWronskian`, `MvPolynomial.eq_zero_of_genWronskian_ne_zero`: a
  variable that no column involves does not occur in a generalized Wronskian, and a nonzero one
  has no row differentiating in it.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.4.5.
-/

public section

noncomputable section

namespace MvPolynomial

open Matrix Finset

variable {R σ : Type*} [CommRing R] {m : ℕ}

/-- If the `l`-th polynomial has partial degree at most `e l` in `Xᵢ`, then the partial degree
of any generalized Wronskian of the family in `Xᵢ` is at most `∑ l, e l`.

No admissibility hypothesis on the derivative rows is needed: every Hasse derivative weakly
decreases each partial degree. -/
theorem degreeOf_genWronskian_le_sum (D : Fin m → σ →₀ ℕ) (f : Fin m → MvPolynomial σ R)
    (i : σ) (e : Fin m → ℕ) (hf : ∀ l, (f l).degreeOf i ≤ e l) :
    (genWronskian D f).degreeOf i ≤ ∑ l, e l := by
  rw [genWronskian_def]
  refine Matrix.degreeOf_det_le_sum _ i e fun k l ↦ ?_
  exact (degreeOf_hasseDeriv_le (D k) (f l) i).trans
    ((Nat.sub_le _ _).trans (hf l))

/-- If every polynomial in a family of size `m` has partial degree at most `N` in `Xᵢ`, then
the partial degree of any generalized Wronskian of the family in `Xᵢ` is at most `m * N`. -/
theorem degreeOf_genWronskian_le (D : Fin m → σ →₀ ℕ) (f : Fin m → MvPolynomial σ R)
    (i : σ) (N : ℕ) (hf : ∀ l, (f l).degreeOf i ≤ N) :
    (genWronskian D f).degreeOf i ≤ m * N := by
  simpa using degreeOf_genWronskian_le_sum D f i (fun _ ↦ N) hf

/-- A generalized Wronskian of polynomials that do not involve `Xᵢ` does not involve `Xᵢ`. -/
theorem notMem_vars_genWronskian {i : σ} {f : Fin m → MvPolynomial σ R}
    (hf : ∀ l, i ∉ (f l).vars) (D : Fin m → σ →₀ ℕ) : i ∉ (genWronskian D f).vars := by
  rw [mem_vars_iff_degreeOf_ne_zero, not_not]
  simpa using degreeOf_genWronskian_le D f i 0 fun l ↦
    (not_not.1 (mt mem_vars_iff_degreeOf_ne_zero.2 (hf l))).le

/-- If no polynomial of the family involves `Xᵢ` and the generalized Wronskian is nonzero, then
no row differentiates in `Xᵢ`: each Hasse derivative in a row differentiating in `Xᵢ` vanishes. -/
theorem eq_zero_of_genWronskian_ne_zero {i : σ} {D : Fin m → σ →₀ ℕ} {f : Fin m → MvPolynomial σ R}
    (hf : ∀ l, i ∉ (f l).vars) (hW : genWronskian D f ≠ 0) (k : Fin m) : D k i = 0 := by
  by_contra hk
  refine hW ?_
  rw [genWronskian_def]
  exact Matrix.det_eq_zero_of_row_eq_zero k fun l ↦ by
    rw [Matrix.of_apply]
    exact hasseDeriv_eq_zero_of_degreeOf_lt (by
      rw [not_not.1 (mt mem_vars_iff_degreeOf_ne_zero.2 (hf l))]; omega)

end MvPolynomial
