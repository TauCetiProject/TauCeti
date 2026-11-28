/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Non-divisor monomial ideals and colon extraction for square-free products

Over a commutative ring `O` and a finite index type `J`, let `nonDivisorIdeal O J` be the ideal
of `MvPolynomial J O` consisting of polynomials supported on monomials that do not divide the
square-free product `∏ j : J, X j`. For a monotone partition `ty : J →o Fin t`, any variable
`X i` with `ty i < e` lies in the colon ideal `(nonDivisorIdeal O J).colon {∏_{ty j < e} X j}`,
and a product `F * ∏ e, d e` of factors congruent to `Γ e * ∏_{ty j = e} X j` modulo these colon
ideals vanishes on all proper divisors of `∏ j, X j` and has top coefficient
`constantCoeff (F * ∏ e, Γ e)`.

## Main definitions and results

* `TauCeti.nonDivisorIdeal`: the ideal of `MvPolynomial J O` of polynomials supported off the
  divisors of `∏ j : J, X j`.
* `TauCeti.mem_nonDivisorIdeal`: membership characterization in terms of `MvPolynomial.support`.
* `TauCeti.X_mem_colon_nonDivisorIdeal`: `X i` lies in the colon ideal of `∏_{ty j < e} X j`
  whenever `ty i < e`.
* `TauCeti.prod_add_ordered`: ordered telescoping expansion of `∏ e ∈ s, (a e + b e)`.
* `TauCeti.coeff_mul_prod_of_mem_colon`: extracts the coefficients at all divisors of
  `∏ j : J, X j` of `F * ∏ e, d e`.

## Provenance

Adapted from `src/New/Congruences/FirstOrder/FittingBlock.lean`
(`New.Selmer.nonDivisorIdeal`, `New.Selmer.mem_nonDivisorIdeal`,
`New.Selmer.X_mem_colon_nonDivisorIdeal`, `New.Selmer.coeff_mul_prod_of_mem_colon`) in
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Finset MvPolynomial

/-- The ideal of `MvPolynomial J O` consisting of polynomials none of whose monomials divide
`∏ j : J, X j`. -/
def nonDivisorIdeal (O J : Type*) [CommSemiring O] [Fintype J] : Ideal (MvPolynomial J O) where
  carrier := {f | ∀ d ∈ f.support, ¬ d ≤ ∑ j : J, Finsupp.single j 1}
  zero_mem' d hd := by simp at hd
  add_mem' hf hg d hd := by
    classical
    rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
    · exact hf d h
    · exact hg d h
  smul_mem' c f hf d hd hle := by
    classical
    rw [smul_eq_mul] at hd
    rcases Finset.mem_add.mp (MvPolynomial.support_mul c f hd) with ⟨d₁, _, d₂, hd₂, rfl⟩
    exact hf d₂ hd₂ ((le_add_of_nonneg_left zero_le).trans hle)

/-- A polynomial lies in `nonDivisorIdeal O J` iff none of its monomials divide `∏ j, X j`. -/
theorem mem_nonDivisorIdeal {O J : Type*} [CommSemiring O] [Fintype J] {f : MvPolynomial J O} :
    f ∈ nonDivisorIdeal O J ↔ ∀ d ∈ f.support, ¬ d ≤ ∑ j : J, Finsupp.single j 1 :=
  Iff.rfl

/-- If `ty i < e`, then `X i` multiplies `∏ j with ty j < e, X j` into `nonDivisorIdeal O J`. -/
theorem X_mem_colon_nonDivisorIdeal {O J : Type*} [CommSemiring O] [Fintype J] {t : ℕ}
    {ty : J → Fin t} {i : J} {e : Fin t} (h_lt : ty i < e) :
    MvPolynomial.X i ∈
      (nonDivisorIdeal O J).colon {∏ j : J with ty j < e, MvPolynomial.X j} := by
  classical
  let d : J →₀ ℕ := Finsupp.single i 1 + ∑ j : J with ty j < e, Finsupp.single j 1
  have h_mon : MvPolynomial.X i * ∏ j : J with ty j < e, MvPolynomial.X j =
      monomial d (1 : O) := by
    simp [d, MvPolynomial.X, ← monomial_sum_one]
  have h_not_le : ¬ d ≤ ∑ j : J, Finsupp.single j 1 := fun h_le ↦ by
    have hi := h_le i
    simp [d, h_lt, Finsupp.single_apply] at hi
  rw [Submodule.mem_colon_singleton, smul_eq_mul, h_mon, mem_nonDivisorIdeal]
  intro d' hd'
  rwa [Finset.mem_singleton.mp (support_monomial_subset hd')]

/-- Ordered telescoping expansion of `∏ e ∈ s, (a e + b e)` over a linearly ordered finite set. -/
theorem prod_add_ordered {ι R : Type*} [LinearOrder ι] [CommSemiring R] (s : Finset ι)
    (a b : ι → R) :
    ∏ e ∈ s, (a e + b e) = ∏ e ∈ s, a e +
      ∑ e ∈ s, b e * (∏ k ∈ s with k < e, (a k + b k)) * ∏ k ∈ s with e < k, a k := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert m s hm ih =>
    have h_notMem : m ∉ s := fun h ↦ lt_irrefl m (hm m h)
    have h_lt (e : ι) (he : e ∈ s) : (insert m s).filter (· < e) = s.filter (· < e) := by
      simp [Finset.filter_insert, not_lt_of_gt (hm e he)]
    have h_gt (e : ι) (he : e ∈ s) :
        (insert m s).filter (e < ·) = insert m (s.filter (e < ·)) := by
      simp [Finset.filter_insert, hm e he]
    have h_mlt : (insert m s).filter (· < m) = s := by
      simp [Finset.filter_insert, Finset.filter_eq_self.mpr fun x hx ↦ hm x hx]
    have h_mgt : (insert m s).filter (m < ·) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun x hx ↦ by
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact lt_irrefl x
        · exact not_lt_of_gt (hm x hx')
    rw [Finset.prod_insert h_notMem, Finset.prod_insert h_notMem, Finset.sum_insert h_notMem,
      h_mlt, h_mgt, Finset.prod_empty, mul_one,
      Finset.sum_congr rfl fun e he ↦ by
        rw [h_lt e he, h_gt e he, Finset.prod_insert (by simp [h_notMem]), ← mul_assoc,
          mul_comm _ (a m), mul_assoc],
      ← Finset.mul_sum, ih]
    ring

/-- If `d e + ζ e = Γ e * ∏_{ty j = e} X j` with `ζ e` in the colon ideal of `∏_{ty j < e} X j`
relative to `nonDivisorIdeal O J`, then `F * ∏ e, d e` vanishes at every proper divisor of
`∏ j, X j` and has coefficient `constantCoeff (F * ∏ e, Γ e)` at `∏ j, X j`. -/
theorem coeff_mul_prod_of_mem_colon {O J : Type*} [CommRing O] [Fintype J] [LinearOrder J]
    {t : ℕ} (ty : J →o Fin t) {d ζ Γ : Fin t → MvPolynomial J O}
    (hζ : ∀ e : Fin t,
      ζ e ∈ (nonDivisorIdeal O J).colon {∏ j : J with ty j < e, MvPolynomial.X j})
    (hdζ : ∀ e : Fin t, d e + ζ e = Γ e * ∏ j : J with ty j = e, MvPolynomial.X j)
    (F : MvPolynomial J O) {i : J →₀ ℕ} (hi : i ≤ ∑ j : J, Finsupp.single j 1) :
    (F * ∏ e : Fin t, d e).coeff i =
      if ∑ j : J, Finsupp.single j 1 = i then constantCoeff (F * ∏ e : Fin t, Γ e) else 0 := by
  set 𝔫 : Ideal (MvPolynomial J O) := nonDivisorIdeal O J
  let err : MvPolynomial J O :=
    ∑ e : Fin t, ζ e * (∏ k : Fin t with k < e, (d k + ζ k)) * ∏ k : Fin t with e < k, d k
  have h_dvd (e : Fin t) :
      ∏ j : J with ty j < e, MvPolynomial.X j ∣ ∏ k : Fin t with k < e, (d k + ζ k) := by
    simp [hdζ, Finset.prod_fiberwise_eq_prod_filter, Finset.prod_mul_distrib]
  have h_err : err ∈ 𝔫 := sum_mem fun e _ ↦
    𝔫.mem_of_dvd ((mul_dvd_mul_left (ζ e) (h_dvd e)).mul_right _)
      (Submodule.mem_colon_singleton.mp (hζ e))
  have h_prod : ∏ e : Fin t, d e = ∏ e : Fin t, (d e + ζ e) - err :=
    eq_sub_of_add_eq (prod_add_ordered univ d ζ).symm
  have h_zero : (F * err).coeff i = 0 :=
    notMem_support_iff.mp fun h ↦ mem_nonDivisorIdeal.mp (𝔫.mul_mem_left F h_err) i h hi
  have h_main : F * ∏ e : Fin t, (d e + ζ e) =
      (F * ∏ e : Fin t, Γ e) * monomial (∑ j : J, Finsupp.single j 1) 1 := by
    simp [hdζ, Finset.sum_fiberwise, MvPolynomial.X, ← mul_assoc, ← monomial_sum_one,
      Finset.prod_mul_distrib]
  rw [h_prod, mul_sub, AddMonoidAlgebra.coeff_sub_apply, h_zero, sub_zero, h_main,
    coeff_mul_monomial']
  simp +contextual [hi.ge_iff_eq', ← constantCoeff_eq]

end TauCeti
