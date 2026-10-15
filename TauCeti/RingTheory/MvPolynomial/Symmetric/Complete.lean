/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finset.Sym
import TauCeti.Data.Sym.Basic

/-!
# Evaluating the complete homogeneous symmetric polynomial

The complete homogeneous symmetric polynomial `h_d` in variables indexed by a finite type `σ` is
the sum of all monomials of degree `d`, one for each unordered `d`-tuple of indices.  Evaluating it
at a family `f : σ → R` therefore sums, over those unordered tuples, the product of the values `f`
takes on the tuple: `TauCeti.eval_hsymm`.

In two variables the unordered `d`-tuples are the `d + 1` splittings counted by
`TauCeti.symFinTwoEquiv`, and the evaluation reads `h_d(x, y) = ∑_{i ≤ d} xⁱ y^{d-i}`:
`TauCeti.eval_hsymm_fin_two`.

Reading the unordered tuples as their multiplicity functions instead writes `h_d` as the sum of the
monomials of degree `d`, indexed by `Finset.piAntidiag`: `TauCeti.hsymm_eq_sum_piAntidiag`.  Summed
over all degrees, this is the generating function `∑ₙ hₙ tⁿ = ∏ᵢ ∑ₙ xᵢⁿ tⁿ`, the product over the
variables of the geometric series `(1 - xᵢ t)⁻¹`: `TauCeti.mk_hsymm_eq_prod_mk_pow`.

Determinantal formulas such as Jacobi--Trudi index `h` by integers, `h_m` being `0` for `m < 0`;
reading a negative index as `0` through a truncated subtraction of natural numbers would silently
give the wrong formula.  `TauCeti.hsymmInt` is this integer-indexed complete homogeneous symmetric
polynomial.

## Main results

* `TauCeti.eval_hsymm` evaluates the complete homogeneous symmetric polynomial as a sum over the
  unordered `d`-tuples of indices.
* `TauCeti.eval_hsymm_fin_two` reads that off in two variables: `h_d(x, y) = ∑_{i ≤ d} xⁱ y^{d-i}`.
* `TauCeti.hsymm_eq_sum_piAntidiag` writes `h_d` as the sum of the monomials of degree `d`.
* `TauCeti.mk_hsymm_eq_prod_mk_pow`: the generating function of the `h_d`.
* `TauCeti.hsymmInt`: the complete homogeneous symmetric polynomial `h_m` of an integer degree `m`,
  which is `0` for `m < 0`.
-/

public section

namespace TauCeti

/-- **The complete homogeneous symmetric polynomial evaluated**: `h_d(f)` is the sum, over the
unordered `d`-tuples of indices, of the product of the values `f` takes on the tuple. -/
theorem eval_hsymm {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R] (f : σ → R)
    (d : ℕ) : MvPolynomial.eval f (MvPolynomial.hsymm σ R d)
      = ∑ s : Sym σ d, ((s : Multiset σ).map f).prod := by
  rw [MvPolynomial.hsymm, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_multiset_prod, Multiset.map_map]
  simp [Function.comp_def]

/-- **The complete homogeneous symmetric polynomial in two variables**: `h_d(x, y)` is the sum of
all `d + 1` monomials `xⁱ y^{d-i}` of degree `d`. -/
theorem eval_hsymm_fin_two {R : Type*} [CommSemiring R] (f : Fin 2 → R) (d : ℕ) :
    MvPolynomial.eval f (MvPolynomial.hsymm (Fin 2) R d)
      = ∑ i ∈ Finset.range (d + 1), f 0 ^ i * f 1 ^ (d - i) := by
  rw [eval_hsymm, ← Fin.sum_univ_eq_sum_range _ (d + 1),
    ← Equiv.sum_comp (symFinTwoEquiv d).symm]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [coe_symFinTwoEquiv_symm_apply]
  simp

/-- **The monomial expansion of the complete homogeneous symmetric polynomial**: `h_d` is the sum of
the monomials `∏ᵢ X_i ^ γ_i` over the exponent vectors `γ` of total degree `d`.  This is the
multiplicity-function form of `MvPolynomial.hsymm`, whose summands are indexed by the unordered
`d`-tuples of variables. -/
theorem hsymm_eq_sum_piAntidiag {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*)
    [CommSemiring R] (d : ℕ) :
    MvPolynomial.hsymm σ R d =
      ∑ γ ∈ Finset.piAntidiag (Finset.univ : Finset σ) d,
        ∏ i, (MvPolynomial.X i : MvPolynomial σ R) ^ γ i := by
  rw [← Finset.map_sym_eq_piAntidiag, Finset.sum_map, Finset.sym_univ, MvPolynomial.hsymm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hi), pow_zero]

/-- **The generating function of the complete homogeneous symmetric polynomials**:
`∑ₙ hₙ tⁿ = ∏ᵢ ∑ₙ xᵢⁿ tⁿ`, as power series over `MvPolynomial σ R`.  Each factor is the geometric
series `(1 - xᵢ t)⁻¹`, so the coefficient of `tⁿ` collects one monomial of degree `n` for every
exponent vector. -/
theorem mk_hsymm_eq_prod_mk_pow {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*)
    [CommSemiring R] :
    PowerSeries.mk (fun n => MvPolynomial.hsymm σ R n) =
      ∏ i, PowerSeries.mk fun n => (MvPolynomial.X i : MvPolynomial σ R) ^ n := by
  ext d
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_prod, hsymm_eq_sum_piAntidiag, Finset.finsuppAntidiag,
    Finset.sum_map, ← Finset.sum_attach (Finset.piAntidiag Finset.univ d)]
  simp

section hsymmInt

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommSemiring R]

/-- The **complete homogeneous symmetric polynomial of integer degree** `m`: `h_m` for `m ≥ 0`
and `0` for `m < 0`.  This is the indexing determinantal formulas such as Jacobi--Trudi use. -/
noncomputable def hsymmInt (m : ℤ) : MvPolynomial σ R :=
  if 0 ≤ m then MvPolynomial.hsymm σ R m.toNat else 0

variable {σ R}

/-- In a nonnegative degree, `TauCeti.hsymmInt` is `MvPolynomial.hsymm`. -/
@[simp]
theorem hsymmInt_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    hsymmInt σ R m = MvPolynomial.hsymm σ R m.toNat := by
  simp [hsymmInt, hm]

/-- In a negative degree, `TauCeti.hsymmInt` vanishes. -/
@[simp]
theorem hsymmInt_of_neg {m : ℤ} (hm : m < 0) : hsymmInt σ R m = 0 := by
  simp [hsymmInt, not_le.mpr hm]

/-- In a natural-number degree, `TauCeti.hsymmInt` is `MvPolynomial.hsymm`. -/
theorem hsymmInt_natCast (n : ℕ) : hsymmInt σ R n = MvPolynomial.hsymm σ R n := by
  simp [hsymmInt]

/-- `h_0 = 1`. -/
theorem hsymmInt_zero : hsymmInt σ R 0 = 1 := by
  simp

/-- Changing the coefficients along a ring homomorphism preserves `TauCeti.hsymmInt`. -/
@[simp]
theorem map_hsymmInt {S : Type*} [CommSemiring S] (m : ℤ) (f : R →+* S) :
    MvPolynomial.map f (hsymmInt σ R m) = hsymmInt σ S m := by
  unfold hsymmInt
  split_ifs <;> simp [MvPolynomial.map_hsymm]

/-- Renaming the variables along a bijection preserves `TauCeti.hsymmInt`. -/
@[simp]
theorem rename_hsymmInt {τ : Type*} [Fintype τ] [DecidableEq τ] (m : ℤ) (e : σ ≃ τ) :
    MvPolynomial.rename e (hsymmInt σ R m) = hsymmInt τ R m := by
  unfold hsymmInt
  split_ifs <;> simp [MvPolynomial.rename_hsymm]

end hsymmInt

end TauCeti
