/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree

/-!
# Boxes of integer polynomial systems with bounded degree and coefficients

For a finite index type `ι`, a finite type of variables `σ` and natural numbers `d` and `C`, the
*coefficient box* `TauCeti.MvPolynomial.coefficientBox ι σ d C` is the set of `ι`-indexed tuples
`E` of integer polynomials in the variables `σ` with total degree at most `d` and every coefficient
of absolute value at most `C`. Only degree and coefficient bounds enter; the polynomials need not
be nonzero, and no condition on their common zeros is imposed.

A polynomial of total degree at most `d` is determined by its coefficients at the
`M = (d + card σ choose card σ)` exponents of degree at most `d`, and every choice of these
coefficients occurs. So the monomial coefficients identify the box with `card ι * M` independent
copies of the integer interval `[-C, C]` (`coefficientBoxEquiv`), and the box has exactly
`(2 * C + 1) ^ (card ι * M)` elements (`ncard_coefficientBox`). For a real coefficient bound
`B ≥ 0` the box of natural bound `⌊B⌋₊` is the same set of tuples, since an integer has absolute
value at most `B` exactly when it has absolute value at most `⌊B⌋₊`.

This is the counting input of Couveignes's bound on the number of number fields of bounded
discriminant: every number field of degree `n` is a factor of an algebra cut out by `r` integer
equations in `r` variables of total degree at most `d` with coefficients bounded in terms of the
discriminant, and the systems of a box are counted here. The analogous count of single
polynomials in one variable is `TauCeti.Polynomial.ncard_natDegree_le_abs_intCoeff_le`.

## Main definitions

* `TauCeti.MvPolynomial.coefficientBox ι σ d C`: the tuples of integer polynomials of total
  degree at most `d` with coefficients bounded by `C` in absolute value.
* `TauCeti.MvPolynomial.coefficientBoxEquiv ι σ d C`: monomial coefficients identify the box with
  the functions from pairs of an index and an exponent of degree at most `d` to `[-C, C]`.

## Main results

* `TauCeti.MvPolynomial.mem_coefficientBox`: membership is the conjunction of the degree and
  coefficient bounds.
* `TauCeti.MvPolynomial.coefficientBox_mono`: the box grows with `d` and `C`.
* `TauCeti.MvPolynomial.finite_coefficientBox`: the box is finite.
* `TauCeti.MvPolynomial.ncard_coefficientBox`: the box has `(2 * C + 1) ^ (card ι * M)` elements,
  with `M = (d + card σ choose card σ)`.
* `TauCeti.MvPolynomial.setOf_abs_coeff_le_eq_coefficientBox_floor`: bounding the coefficients by
  a real number `B ≥ 0` gives the box of bound `⌊B⌋₊`.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), 487–497, §4.
-/

public section

open MvPolynomial

namespace TauCeti.MvPolynomial

variable (ι σ : Type*)

/-- The coefficient box: the `ι`-indexed tuples of integer polynomials in the variables `σ` all
of whose entries have total degree at most `d` and all coefficients of absolute value at most
`C`. -/
def coefficientBox (d C : ℕ) : Set (ι → MvPolynomial σ ℤ) :=
  {E | ∀ i, (E i).totalDegree ≤ d ∧ ∀ s, |(E i).coeff s| ≤ C}

variable {ι σ}

@[simp]
theorem mem_coefficientBox {d C : ℕ} {E : ι → MvPolynomial σ ℤ} :
    E ∈ coefficientBox ι σ d C ↔ ∀ i, (E i).totalDegree ≤ d ∧ ∀ s, |(E i).coeff s| ≤ C :=
  Iff.rfl

/-- Every entry of a tuple in the coefficient box of degree `d` has total degree at most `d`. -/
theorem mem_restrictTotalDegree_of_mem_coefficientBox {d C : ℕ} {E : ι → MvPolynomial σ ℤ}
    (hE : E ∈ coefficientBox ι σ d C) (i : ι) : E i ∈ restrictTotalDegree σ ℤ d :=
  (mem_restrictTotalDegree σ d (E i)).2 (hE i).1

/-- The coefficient box grows with the degree bound and the coefficient bound. -/
theorem coefficientBox_mono {d d' C C' : ℕ} (hd : d ≤ d') (hC : C ≤ C') :
    coefficientBox ι σ d C ⊆ coefficientBox ι σ d' C' := fun _ hE i ↦
  ⟨(hE i).1.trans hd, fun s ↦ ((hE i).2 s).trans (by exact_mod_cast hC)⟩

/-- Bounding the coefficients by a real number `B ≥ 0` defines the coefficient box of the natural
bound `⌊B⌋₊`: integer coefficients cannot tell `B` from its floor. -/
theorem setOf_abs_coeff_le_eq_coefficientBox_floor (d : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    {E : ι → MvPolynomial σ ℤ | ∀ i, (E i).totalDegree ≤ d ∧ ∀ s, |((E i).coeff s : ℝ)| ≤ B} =
      coefficientBox ι σ d ⌊B⌋₊ := by
  have key (a : ℤ) : |(a : ℝ)| ≤ B ↔ |a| ≤ (⌊B⌋₊ : ℤ) := by
    rw [Int.abs_eq_natAbs, Nat.cast_le, Nat.le_floor_iff hB, Nat.cast_natAbs, Int.cast_abs]
  ext E
  simp [key]

variable (ι σ) in
/-- Monomial coefficients identify the coefficient box with the functions from pairs of an index
and an exponent of degree at most `d` to the integer interval `[-C, C]`. A tuple in the box is
sent to the coefficients of its entries at these exponents; the coefficients at exponents of
larger degree vanish. -/
noncomputable def coefficientBoxEquiv [Finite σ] (d C : ℕ) :
    coefficientBox ι σ d C ≃ (ι × {s : σ →₀ ℕ // s.degree ≤ d} → Set.Icc (-(C : ℤ)) C) where
  toFun E p := ⟨(E.val p.1).coeff p.2, abs_le.1 ((E.property p.1).2 p.2)⟩
  invFun a := ⟨fun i ↦ ((boundedCoefficientEquiv σ ℤ ι d).symm (fun p ↦ (a p : ℤ)) i : _),
    fun i ↦ by
      refine ⟨(mem_restrictTotalDegree σ d _).1 (Subtype.prop _), fun s ↦ ?_⟩
      by_cases hs : s.degree ≤ d
      · rw [show s = ((⟨s, hs⟩ : {s : σ →₀ ℕ // s.degree ≤ d}) : σ →₀ ℕ) from rfl,
          coeff_boundedCoefficientEquiv_symm_apply]
        exact abs_le.2 (a (i, ⟨s, hs⟩)).property
      · rw [coeff_eq_zero_of_mem_restrictTotalDegree (Subtype.prop _) (not_le.1 hs), abs_zero]
        exact C.cast_nonneg⟩
  left_inv E := by
    refine Subtype.ext (funext fun i ↦ MvPolynomial.ext _ _ fun s ↦ ?_)
    by_cases hs : s.degree ≤ d
    · rw [show s = ((⟨s, hs⟩ : {s : σ →₀ ℕ // s.degree ≤ d}) : σ →₀ ℕ) from rfl,
        coeff_boundedCoefficientEquiv_symm_apply]
    · rw [coeff_eq_zero_of_mem_restrictTotalDegree (Subtype.prop _) (not_le.1 hs),
        coeff_eq_zero_of_mem_restrictTotalDegree
          (mem_restrictTotalDegree_of_mem_coefficientBox E.property i) (not_le.1 hs)]
  right_inv a := by
    ext p
    exact coeff_boundedCoefficientEquiv_symm_apply _ p.1 p.2

/-- A coordinate of a tuple in the coefficient box is the corresponding coefficient of an
entry. -/
@[simp]
theorem coe_coefficientBoxEquiv_apply [Finite σ] {d C : ℕ} (E : coefficientBox ι σ d C)
    (p : ι × {s : σ →₀ ℕ // s.degree ≤ d}) :
    (coefficientBoxEquiv ι σ d C E p : ℤ) = (E.val p.1).coeff p.2 :=
  (rfl)

/-- The tuple with prescribed coordinates has those coefficients. -/
@[simp]
theorem coeff_coefficientBoxEquiv_symm_apply [Finite σ] {d C : ℕ}
    (a : ι × {s : σ →₀ ℕ // s.degree ≤ d} → Set.Icc (-(C : ℤ)) C) (i : ι)
    (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
    (((coefficientBoxEquiv ι σ d C).symm a).val i).coeff s = a (i, s) :=
  coeff_boundedCoefficientEquiv_symm_apply _ i s

variable (ι σ) in
/-- The coefficient box is finite. -/
theorem finite_coefficientBox [Finite ι] [Finite σ] (d C : ℕ) :
    (coefficientBox ι σ d C).Finite :=
  Set.finite_coe_iff.1 (Finite.of_equiv _ (coefficientBoxEquiv ι σ d C).symm)

variable (ι σ) in
/-- The coefficient box has exactly `(2 * C + 1) ^ (card ι * M)` elements, where
`M = (d + card σ choose card σ)` is the number of monomials of total degree at most `d`: each of
the `card ι * M` coefficients ranges independently over the `2 * C + 1` integers in `[-C, C]`. -/
theorem ncard_coefficientBox [Fintype ι] [Fintype σ] (d C : ℕ) :
    (coefficientBox ι σ d C).ncard =
      (2 * C + 1) ^ (Fintype.card ι * (d + Fintype.card σ).choose (Fintype.card σ)) := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr (coefficientBoxEquiv ι σ d C), Nat.card_fun,
    Nat.card_prod, card_degree_le_eq_choose, Nat.card_eq_fintype_card (α := ι),
    Nat.card_eq_fintype_card (α := Set.Icc _ _)]
  congr 1
  simp only [Fintype.card_ofFinset, Int.card_Icc]
  omega

end TauCeti.MvPolynomial
