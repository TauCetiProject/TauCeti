/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic

/-!
# Polynomials of bounded partial degrees and the vanishing conditions of the index

The auxiliary polynomial of Roth's method is bounded one variable at a time,
`degreeOf j P ≤ d j`, rather than in total degree. Its coefficients therefore sit on the box
`∏ j, {0, …, d j}` of exponents, and this file is the dictionary between coefficient vectors on
that box and polynomials. The box is named by the `Pi` type `∀ j, Fin (d j + 1)`, so that its
cardinality is `∏ j, (d j + 1)` by `Fintype.card_pi`, and a vector indexed by it is a function of
one index per variable.

Through this dictionary, the vanishing of a Hasse derivative `∂^μ P` at a point `α` becomes a
linear condition on the coefficient vector of `P`: its row has the entry
`∏ j, (I j choose μ j) α j ^ (I j - μ j)` at the exponent `I`. A polynomial of prescribed index at
several points is then a nonzero vector in the kernel of finitely many such rows, which is what
Siegel's lemma produces. The rows are products over the variables of rows in one variable, and
that is what makes their heights computable (`MvPolynomial.mulHeight_hasseDerivRow_le` in
`TauCeti/NumberTheory/Height/MvPolynomial.lean`).

## Main definitions

* `MvPolynomial.boxMonomial d I`: the exponent named by a point `I` of the box.
* `MvPolynomial.ofBox d`: the linear map sending a coefficient vector on the box to its
  polynomial.
* `MvPolynomial.hasseDerivRow d α μ`: the row of the condition "`∂^μ P` vanishes at `α`".

## Main results

* `MvPolynomial.coeff_ofBox`, `MvPolynomial.coeff_ofBox_of_not_le`,
  `MvPolynomial.degreeOf_ofBox_le`, `MvPolynomial.ofBox_coeff`, `MvPolynomial.ofBox_injective`
  and `MvPolynomial.range_ofBox`: `ofBox d` is injective with image the polynomials whose
  partial degrees are bounded by `d`, that is `restrictSupport R {ν | ∀ j, ν j ≤ d j}`.
* `MvPolynomial.aeval_hasseDeriv_ofBox` and `MvPolynomial.aeval_hasseDeriv_eq_sum`: the value at
  `α` of a Hasse derivative of a polynomial of the box is the row `hasseDerivRow d α μ` applied to
  its coefficient vector. The point may lie in any algebra over the coefficients, which is how a
  polynomial over a number field `K` is tested at points of an extension of `K`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), Lemma 6.3.4.
* The statements follow `DiophantineApproximation/BoxMonomial.lean` and
  `DiophantineApproximation/IndexConditions.lean` of Ralf Stephan's `rwst/Subspace-Theorems`,
  commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

open Finset

namespace MvPolynomial

/-! ### The exponents of the box -/

section Monomials

variable {σ : Type*} [Finite σ] {d : σ → ℕ}

/-- The exponent named by a point `I` of the box `∀ j, Fin (d j + 1)`: the exponent of `X j` is
`I j`. -/
noncomputable def boxMonomial (d : σ → ℕ) (I : ∀ j, Fin (d j + 1)) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j ↦ (I j : ℕ)

@[simp]
theorem boxMonomial_apply (d : σ → ℕ) (I : ∀ j, Fin (d j + 1)) (j : σ) :
    boxMonomial d I j = I j := by
  simp [boxMonomial]

/-- Every exponent named by the box lies in the box. -/
theorem boxMonomial_le (d : σ → ℕ) (I : ∀ j, Fin (d j + 1)) (j : σ) :
    boxMonomial d I j ≤ d j := by
  simpa using Nat.lt_succ_iff.mp (I j).isLt

/-- Distinct points of the box name distinct exponents. -/
theorem boxMonomial_injective : Function.Injective (boxMonomial d) := fun I J h ↦
  funext fun j ↦ Fin.ext (by simpa using DFunLike.congr_fun h j)

/-- The exponents named by the box are exactly the exponents bounded by `d`. -/
theorem range_boxMonomial : Set.range (boxMonomial d) = {ν | ∀ j, ν j ≤ d j} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun I ↦ boxMonomial_le d I) fun ν hν ↦ ?_
  exact ⟨fun j ↦ ⟨ν j, Nat.lt_succ_of_le (hν j)⟩, Finsupp.ext fun j ↦ by simp⟩

/-- Every exponent bounded by `d` is named by the box. -/
theorem exists_boxMonomial_eq {ν : σ →₀ ℕ} (h : ∀ j, ν j ≤ d j) :
    ∃ I, boxMonomial d I = ν :=
  (range_boxMonomial (d := d)).ge h

/-- The exponents of a polynomial whose partial degrees are bounded by `d` are named by the box. -/
theorem exists_boxMonomial_eq_of_mem_support {R : Type*} [CommSemiring R]
    {P : MvPolynomial σ R} (hP : ∀ j, P.degreeOf j ≤ d j) {ν : σ →₀ ℕ} (hν : ν ∈ P.support) :
    ∃ I, boxMonomial d I = ν :=
  exists_boxMonomial_eq fun j ↦ (monomial_le_degreeOf j hν).trans (hP j)

end Monomials

/-! ### Coefficient vectors on the box -/

section OfBox

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R] {d : σ → ℕ}

/-- The polynomial `∑ I, x I • X ^ (boxMonomial d I)` with coefficient vector `x` on the box
`∀ j, Fin (d j + 1)`. -/
noncomputable def ofBox (d : σ → ℕ) : ((∀ j, Fin (d j + 1)) → R) →ₗ[R] MvPolynomial σ R :=
  ∑ I, (monomial (boxMonomial d I)).comp (LinearMap.proj I)

theorem ofBox_apply (x : (∀ j, Fin (d j + 1)) → R) :
    ofBox d x = ∑ I, monomial (boxMonomial d I) (x I) := by
  simp [ofBox, LinearMap.sum_apply]

@[simp]
theorem coeff_ofBox (x : (∀ j, Fin (d j + 1)) → R) (I : ∀ j, Fin (d j + 1)) :
    (ofBox d x).coeff (boxMonomial d I) = x I := by
  rw [ofBox_apply, coeff_sum, sum_eq_single I (fun J _ hJ ↦ ?_) (by simp)]
  · simp
  · simp [coeff_monomial, boxMonomial_injective.ne hJ]

/-- Outside the box, the polynomial with a given coefficient vector has no coefficients. -/
theorem coeff_ofBox_of_not_le (x : (∀ j, Fin (d j + 1)) → R) {ν : σ →₀ ℕ}
    (hν : ¬ ∀ j, ν j ≤ d j) : (ofBox d x).coeff ν = 0 := by
  rw [ofBox_apply, coeff_sum]
  refine sum_eq_zero fun I _ ↦ ?_
  have hI : boxMonomial d I ≠ ν := fun h ↦ hν (h ▸ boxMonomial_le d I)
  simp [coeff_monomial, hI]

/-- The polynomial with a coefficient vector on the box has its support in the box. -/
theorem ofBox_mem_restrictSupport (x : (∀ j, Fin (d j + 1)) → R) :
    ofBox d x ∈ restrictSupport R {ν | ∀ j, ν j ≤ d j} := by
  rw [mem_restrictSupport_iff R]
  intro ν hν
  by_contra h
  exact (mem_support_iff.mp hν) (coeff_ofBox_of_not_le x h)

/-- The polynomial with a coefficient vector on the box has partial degrees bounded by `d`. -/
theorem degreeOf_ofBox_le (x : (∀ j, Fin (d j + 1)) → R) (j : σ) :
    (ofBox d x).degreeOf j ≤ d j :=
  degreeOf_le_iff.2 fun _ hν ↦ (mem_restrictSupport_iff R).1 (ofBox_mem_restrictSupport x) hν j

/-- A polynomial whose partial degrees are bounded by `d` is the polynomial of its own
coefficient vector on the box. -/
theorem ofBox_coeff {P : MvPolynomial σ R} (hP : ∀ j, P.degreeOf j ≤ d j) :
    ofBox d (fun I ↦ P.coeff (boxMonomial d I)) = P := by
  ext ν
  by_cases hν : ∀ j, ν j ≤ d j
  · obtain ⟨I, rfl⟩ := exists_boxMonomial_eq hν
    exact coeff_ofBox _ I
  · rw [coeff_ofBox_of_not_le _ hν, eq_comm, ← notMem_support_iff]
    exact fun h ↦ hν fun j ↦ (monomial_le_degreeOf j h).trans (hP j)

theorem ofBox_injective : Function.Injective (ofBox (R := R) d) := fun x y h ↦
  funext fun I ↦ by rw [← coeff_ofBox x I, h, coeff_ofBox]

/-- The polynomials with a coefficient vector on the box are exactly the polynomials supported
in the box. -/
theorem range_ofBox :
    LinearMap.range (ofBox (R := R) d) = restrictSupport R {ν | ∀ j, ν j ≤ d j} := by
  refine le_antisymm (LinearMap.range_le_iff_comap.2 (eq_top_iff.2 fun x _ ↦
    ofBox_mem_restrictSupport x)) fun P hP ↦ ⟨_, ofBox_coeff fun j ↦ degreeOf_le_iff.2 fun ν hν ↦
      (mem_restrictSupport_iff R).1 hP hν j⟩

end OfBox

/-! ### The vanishing conditions as linear forms -/

section Row

variable {σ S : Type*} [Fintype σ] [CommSemiring S]

/-- The row of the linear condition "`∂^μ P` vanishes at `α`" on the coefficient vector of a
polynomial `P` of the box: its entry at the exponent `I` is
`∏ j, (I j choose μ j) α j ^ (I j - μ j)`. -/
def hasseDerivRow (d : σ → ℕ) (α : σ → S) (μ : σ →₀ ℕ) (I : ∀ j, Fin (d j + 1)) : S :=
  ∏ j, ((I j : ℕ).choose (μ j) : S) * α j ^ ((I j : ℕ) - μ j)

theorem hasseDerivRow_def (d : σ → ℕ) (α : σ → S) (μ : σ →₀ ℕ) (I : ∀ j, Fin (d j + 1)) :
    hasseDerivRow d α μ I = ∏ j, ((I j : ℕ).choose (μ j) : S) * α j ^ ((I j : ℕ) - μ j) :=
  (rfl)

/-- The row of order `0` is the tuple of the monomials of the box at `α`: the condition of order
`0` is the vanishing of `P` at `α`. -/
@[simp]
theorem hasseDerivRow_zero (d : σ → ℕ) (α : σ → S) (I : ∀ j, Fin (d j + 1)) :
    hasseDerivRow d α 0 I = ∏ j, α j ^ (I j : ℕ) := by
  simp [hasseDerivRow]

/-- An order that leaves the box in some variable has the zero row. -/
theorem hasseDerivRow_eq_zero {d : σ → ℕ} (α : σ → S) {μ : σ →₀ ℕ} {j : σ} (hj : d j < μ j) :
    hasseDerivRow d α μ = 0 := by
  funext I
  refine prod_eq_zero (mem_univ j) ?_
  rw [Nat.choose_eq_zero_of_lt ((Nat.lt_succ_iff.mp (I j).isLt).trans_lt hj), Nat.cast_zero,
    zero_mul]

variable [DecidableEq σ] {R : Type*} [CommSemiring R] [Algebra R S] {d : σ → ℕ}

/-- The value at `α` of a Hasse derivative of the polynomial with coefficient vector `x` on the
box is the row `hasseDerivRow d α μ` applied to `x`. -/
theorem aeval_hasseDeriv_ofBox (x : (∀ j, Fin (d j + 1)) → R) (α : σ → S) (μ : σ →₀ ℕ) :
    aeval α (hasseDeriv μ (ofBox d x)) = ∑ I, hasseDerivRow d α μ I * algebraMap R S (x I) := by
  simp only [ofBox_apply, map_sum, hasseDeriv_monomial, aeval_monomial, hasseDerivRow, map_mul,
    map_prod, map_natCast, Finsupp.prod_fintype _ _ (fun j ↦ Nat.choose_zero_right _),
    Finsupp.prod_fintype _ _ (fun j ↦ pow_zero (α j)), Finsupp.tsub_apply, boxMonomial_apply,
    Nat.cast_prod, prod_mul_distrib]
  exact sum_congr rfl fun I _ ↦ by ring

/-- The value at `α` of a Hasse derivative of a polynomial whose partial degrees are bounded
by `d` is the row `hasseDerivRow d α μ` applied to its coefficient vector on the box. -/
theorem aeval_hasseDeriv_eq_sum {P : MvPolynomial σ R} (hP : ∀ j, P.degreeOf j ≤ d j)
    (α : σ → S) (μ : σ →₀ ℕ) :
    aeval α (hasseDeriv μ P) =
      ∑ I, hasseDerivRow d α μ I * algebraMap R S (P.coeff (boxMonomial d I)) := by
  conv_lhs => rw [← ofBox_coeff hP]
  exact aeval_hasseDeriv_ofBox _ α μ

end Row

/-! ### Examples -/

/-- The box has `∏ j, (d j + 1)` points: the number of coefficients of a polynomial with partial
degrees bounded by `d`. -/
example {σ : Type*} [Fintype σ] [DecidableEq σ] (d : σ → ℕ) :
    Fintype.card (∀ j, Fin (d j + 1)) = ∏ j, (d j + 1) := by
  simp

/-- At order `0` the condition is evaluation at `α`. -/
example {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R] {d : σ → ℕ}
    {P : MvPolynomial σ R} (hP : ∀ j, P.degreeOf j ≤ d j) (α : σ → R) :
    eval α P = ∑ I : ∀ j, Fin (d j + 1), (∏ j, α j ^ (I j : ℕ)) * P.coeff (boxMonomial d I) := by
  simpa using aeval_hasseDeriv_eq_sum hP α 0

end MvPolynomial
