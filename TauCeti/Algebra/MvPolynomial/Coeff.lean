/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.Regular.Basic

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Coefficients of multivariate polynomials

The coefficients of a power sum `∑ g ∈ s, (∑ i, a g i • X i) ^ n` of linear forms are multinomial
multiples of the power sums `∑ g ∈ s, ∏ i, a g i ^ e i`.

If some combination `∑ i ∈ s, p.coeff (m i) * c i` of coefficients of a multivariate polynomial
`p` equals `1`, then scalar multiplication on `p` is faithful: `r ↦ r • p` is injective, since
taking the same combination of the coefficients of `r • p` recovers `r`. In particular
`r • p = 0` if and only if `r = 0`. This holds in every commutative semiring, including rings with
torsion, where `p` having a nonzero coefficient would not be enough.

A multivariate polynomial over any commutative semiring having a nonzerodivisor coefficient is
itself a nonzerodivisor (`MvPolynomial.mem_nonZeroDivisors_of_coeff_mem`), the multivariate
counterpart of `Polynomial.mem_nonZeroDivisors_of_coeff_mem`; over a commutative ring, having a
regular coefficient implies regularity (`MvPolynomial.isRegular_of_isRegular_coeff`).

The coefficient of a single variable `Xᵢ` in a product obeys the Leibniz rule at `0`, as for the
linear coefficient of a univariate power series (`PowerSeries.coeff_one_mul`).

A linear operator that acts diagonally on the monomials, `X ^ m ↦ w m • X ^ m`, acts on the
coefficients by the same scalars.

## Main results

* `MvPolynomial.coeff_sum_linearCombination_X_pow_of_fintype`: the coefficients of a power sum of
  linear forms.
* `MvPolynomial.smul_left_injective_of_sum_coeff_mul_eq_one`: if a combination of the
  coefficients of `p` is `1`, then `r ↦ r • p` is injective.
* `MvPolynomial.smul_eq_zero_iff_left_of_sum_coeff_mul_eq_one`: under the same hypothesis,
  `r • p = 0 ↔ r = 0`.
* `MvPolynomial.mem_nonZeroDivisors_of_coeff_mem`, `MvPolynomial.isRegular_of_isRegular_coeff`:
  a multivariate polynomial with a nonzerodivisor (or regular) coefficient is a nonzerodivisor
  (or regular).
* `MvPolynomial.coeff_single_one_mul`: the coefficient of `Xᵢ` in `p * q` is
  `pᵢ q(0) + p(0) qᵢ`.
* `MvPolynomial.coeff_apply_eq_mul_of_apply_monomial`: an operator multiplying each monomial
  `X ^ m` by `w m` multiplies the coefficient of `X ^ m` by `w m`.
-/

public section

namespace MvPolynomial

open scoped nonZeroDivisors Polynomial

variable {R σ ι : Type*} [CommSemiring R] {p : MvPolynomial σ R}

/-- If some combination `∑ i ∈ s, p.coeff (m i) * c i` of coefficients of `p` is `1`, then
`r ↦ r • p` is injective: the same combination of the coefficients of `r • p` is `r`. -/
theorem smul_left_injective_of_sum_coeff_mul_eq_one (s : Finset ι) (m : ι → σ →₀ ℕ) (c : ι → R)
    (hc : ∑ i ∈ s, p.coeff (m i) * c i = 1) : Function.Injective fun r : R => r • p :=
  Function.LeftInverse.injective (g := fun q => ∑ i ∈ s, q.coeff (m i) * c i) fun r => by
    simp only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hc,
      mul_one]

/-- If some combination `∑ i ∈ s, p.coeff (m i) * c i` of coefficients of `p` is `1`, then
`r • p = 0` if and only if `r = 0`. -/
theorem smul_eq_zero_iff_left_of_sum_coeff_mul_eq_one (s : Finset ι) (m : ι → σ →₀ ℕ)
    (c : ι → R) (hc : ∑ i ∈ s, p.coeff (m i) * c i = 1) {r : R} : r • p = 0 ↔ r = 0 :=
  (smul_left_injective_of_sum_coeff_mul_eq_one s m c hc).eq_iff' (zero_smul R p)

/-- **Coefficients of power sums of linear forms.** The coefficient of `X ^ e` in
`∑ g ∈ s, (∑ i, a g i • X i) ^ n` is `multinomial e * ∑ g ∈ s, ∏ i, a g i ^ e i` if `e` has total
degree `n`, and zero otherwise. -/
theorem coeff_sum_linearCombination_X_pow_of_fintype [Fintype σ] (s : Finset ι) (a : ι → σ → R)
    (e : σ →₀ ℕ) (n : ℕ) :
    (∑ g ∈ s, (∑ i, a g i • X i : MvPolynomial σ R) ^ n).coeff e =
      if e.sum (fun _ m ↦ m) = n then e.multinomial * ∑ g ∈ s, e.prod (fun i m ↦ a g i ^ m)
      else 0 := by
  simp only [coeff_sum, coeff_linearCombination_X_pow_of_fintype]
  split_ifs <;> simp [Finset.mul_sum]

private theorem mem_nonZeroDivisors_fin_of_coeff_mem :
    ∀ {n : ℕ} {q : MvPolynomial (Fin n) R} (d : Fin n →₀ ℕ),
      q.coeff d ∈ R⁰ → q ∈ (MvPolynomial (Fin n) R)⁰
  | 0, q, d, hd => by
    let e := isEmptyAlgEquiv R (Fin 0)
    have hcoeff : e q = q.coeff d := by
      conv_lhs => rw [q.eq_C_of_isEmpty, ← algebraMap_eq, AlgEquiv.commutes]
      simp [Subsingleton.elim d 0]
    exact mem_nonZeroDivisors_of_injective e.injective (hcoeff ▸ hd)
  | n + 1, q, d, hd => by
    let e := finSuccEquiv R n
    let d' : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j ↦ d j.succ
    have hcons : d'.cons (d 0) = d := by
      ext k
      refine Fin.cases rfl (fun j ↦ ?_) k
      simp [d', Finsupp.cons_succ]
    have hcoeff : ((e q).coeff (d 0)).coeff d' = q.coeff d := by
      rw [finSuccEquiv_coeff_coeff, hcons]
    have hq' : (e q).coeff (d 0) ∈ (MvPolynomial (Fin n) R)⁰ :=
      mem_nonZeroDivisors_fin_of_coeff_mem d' (hcoeff ▸ hd)
    have heq : e q ∈ (MvPolynomial (Fin n) R)[X]⁰ :=
      Polynomial.mem_nonZeroDivisors_of_coeff_mem (d 0) hq'
    exact mem_nonZeroDivisors_of_injective e.injective heq

/-- A multivariate polynomial over a commutative semiring having a nonzerodivisor coefficient is
itself a nonzerodivisor (the multivariate counterpart of
`Polynomial.mem_nonZeroDivisors_of_coeff_mem`). -/
theorem mem_nonZeroDivisors_of_coeff_mem (d : σ →₀ ℕ) (hp : p.coeff d ∈ R⁰) :
    p ∈ (MvPolynomial σ R)⁰ := by
  classical
  refine mem_nonZeroDivisors_iff_right.mpr fun q hq ↦ ?_
  let s : Finset σ := p.vars ∪ q.vars ∪ d.support
  obtain ⟨n, f, hf, hrange⟩ :
      ∃ (n : ℕ) (f : Fin n → σ), Function.Injective f ∧ (s : Set σ) ⊆ Set.range f := by
    refine ⟨s.card, Subtype.val ∘ s.equivFin.symm,
      Subtype.val_injective.comp s.equivFin.symm.injective, fun x hx ↦ ?_⟩
    exact ⟨s.equivFin ⟨x, hx⟩, by simp⟩
  have hp_vars : (p.vars : Set σ) ⊆ Set.range f :=
    (Finset.coe_subset.mpr (Finset.subset_union_left.trans Finset.subset_union_left)).trans hrange
  have hq_vars : (q.vars : Set σ) ⊆ Set.range f :=
    (Finset.coe_subset.mpr (Finset.subset_union_right.trans Finset.subset_union_left)).trans hrange
  have hd_supp : (d.support : Set σ) ⊆ Set.range f :=
    (Finset.coe_subset.mpr Finset.subset_union_right).trans hrange
  obtain ⟨p', hp'⟩ := exists_rename_eq_of_vars_subset_range p f hf hp_vars
  obtain ⟨q', hq'⟩ := exists_rename_eq_of_vars_subset_range q f hf hq_vars
  obtain ⟨d', hd'⟩ : ∃ d' : Fin n →₀ ℕ, d'.mapDomain f = d :=
    ⟨d.comapDomain f hf.injOn, Finsupp.mapDomain_comapDomain f hf d hd_supp⟩
  have hcoeff : p'.coeff d' = p.coeff d := by
    rw [← hp', ← hd', coeff_rename_mapDomain f hf]
  have hp'mem : p' ∈ (MvPolynomial (Fin n) R)⁰ :=
    mem_nonZeroDivisors_fin_of_coeff_mem d' (hcoeff ▸ hp)
  have hmul : rename f (q' * p') = rename f 0 := by
    rw [map_mul, hq', hp', hq, map_zero]
  have hq'0 : q' = 0 :=
    mem_nonZeroDivisors_iff_right.mp hp'mem q' (rename_injective f hf hmul)
  rw [← hq', hq'0, map_zero]

/-- A multivariate polynomial over a commutative ring with a regular coefficient is regular. -/
theorem isRegular_of_isRegular_coeff {R : Type*} [CommRing R] {p : MvPolynomial σ R}
    (d : σ →₀ ℕ) (hp : IsRegular (p.coeff d)) : IsRegular p :=
  isRegular_iff_mem_nonZeroDivisors.mpr
    (mem_nonZeroDivisors_of_coeff_mem d (isRegular_iff_mem_nonZeroDivisors.mp hp))

/-- **The linear coefficients of a product**: the coefficient of the variable `Xᵢ` in `p * q` is
`pᵢ q(0) + p(0) qᵢ`, so taking it is a derivation at `0`. -/
theorem coeff_single_one_mul (i : σ) (p q : MvPolynomial σ R) :
    (p * q).coeff (Finsupp.single i 1) =
      p.coeff (Finsupp.single i 1) * constantCoeff q +
        constantCoeff p * q.coeff (Finsupp.single i 1) := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, constantCoeff_eq, add_comm]

/-- **Coefficients under an operator diagonal on monomials.** If a linear operator `f` multiplies
each monomial `X ^ m` by a scalar `w m`, then it multiplies the coefficient of `X ^ m` of every
polynomial by `w m`. -/
theorem coeff_apply_eq_mul_of_apply_monomial {f : Module.End R (MvPolynomial σ R)}
    {w : (σ →₀ ℕ) → R} (hf : ∀ m r, f (monomial m r) = w m • monomial m r)
    (p : MvPolynomial σ R) (m : σ →₀ ℕ) : (f p).coeff m = w m * p.coeff m := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  simp only [hf, coeff_sum, smul_monomial, coeff_monomial, smul_eq_mul]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.1 hm, mul_zero]

end MvPolynomial
