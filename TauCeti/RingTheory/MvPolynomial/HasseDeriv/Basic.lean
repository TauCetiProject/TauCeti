/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import TauCeti.Algebra.MvPolynomial.Equiv
public import TauCeti.Data.Finsupp.Choose

/-!
# Hasse derivatives of multivariate polynomials

For a multi-index `d : σ →₀ ℕ`, the `d`-th Hasse (divided) partial derivative `∂^d` of a
multivariate polynomial sends the monomial `X^m` to `(∏ⱼ (mⱼ choose dⱼ)) X^(m - d)`, which is
zero unless `d ≤ m`. It is defined over any commutative semiring, so it preserves integrality of
coefficients, and in a single variable `k! • ∂^(k eᵢ)` is the `k`-th partial derivative in `Xᵢ`
(`MvPolynomial.factorial_smul_hasseDeriv_single`).

Hasse derivatives are the Taylor coefficients of a polynomial: `P(X + Y) = ∑_d (∂^d P)(X) Y^d`
(see `TauCeti.RingTheory.MvPolynomial.HasseDeriv.Taylor`). They are the jets used to measure the
vanishing of auxiliary polynomials at a point, as in the index of a polynomial in the proof of
Roth's theorem.

## Main definitions

* `MvPolynomial.hasseDeriv d`: the `d`-th Hasse derivative, as an `R`-linear endomorphism of
  `MvPolynomial σ R`.

## Main results

* `MvPolynomial.hasseDeriv_monomial`, `MvPolynomial.hasseDeriv_coeff`: the values on monomials
  and the coefficients `[X^m] ∂^d P = (∏ⱼ (mⱼ + dⱼ choose dⱼ)) [X^(m + d)] P`.
* `MvPolynomial.hasseDeriv_zero`, `MvPolynomial.hasseDeriv_C`: `∂^0` is the identity and every
  other Hasse derivative kills constants.
* `MvPolynomial.hasseDeriv_map`: Hasse derivatives commute with coefficient ring maps.
* `MvPolynomial.hasseDeriv_eq_zero_of_degreeOf_lt`, `MvPolynomial.degreeOf_hasseDeriv_le`: the
  derivative lowers the degree in `Xᵢ` by `dᵢ`.
* `MvPolynomial.factorial_smul_hasseDeriv_single`: `k! • ∂^(k eᵢ) P = (∂/∂Xᵢ)^k P`.
* `MvPolynomial.hasseDeriv_single_toMvPolynomial`,
  `MvPolynomial.hasseDeriv_toMvPolynomial_eq_zero`: on a polynomial in the single variable `Xᵢ`,
  `∂^(k eᵢ)` is the univariate `k`-th Hasse derivative, and `∂^d` vanishes whenever `d`
  differentiates in another variable `Xⱼ`.
* `MvPolynomial.hasseDeriv_comp`: `∂^a ∘ ∂^b = (∏ⱼ (aⱼ + bⱼ choose aⱼ)) • ∂^(a + b)`.
* `MvPolynomial.hasseDeriv_mul_X`: the Leibniz rule for multiplication by a variable,
  `∂^d (P Xᵢ) = ∂^(d - eᵢ) P + (∂^d P) Xᵢ` (the first term only when `dᵢ ≠ 0`).

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (2022), §2.6, Lemma 2.6.1 and
  §3.5.3.
* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, p. 117.
* Mathlib's univariate Hasse derivative `Polynomial.hasseDeriv`
  (`Mathlib/Algebra/Polynomial/HasseDeriv.lean`, Johan Commelin), whose definition by `lsum` over
  monomials and whose statements of `hasseDeriv_map` and `hasseDeriv_comp` this file follows.
-/

public section

namespace MvPolynomial

open Finsupp

variable {R σ : Type*} [CommSemiring R]

/-- The `d`-th Hasse derivative `∂^d` of a multivariate polynomial, the linear map sending the
monomial `a X^m` to `(∏ⱼ (mⱼ choose dⱼ)) a X^(m - d)`. The coefficient vanishes unless `d ≤ m`. -/
noncomputable def hasseDeriv (d : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  Finsupp.lsum ℕ (fun m ↦ monomial (m - d) ∘ₗ
      DistribSMul.toLinearMap R R ((d.prod fun j k ↦ (m j).choose k : ℕ) : R)) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- The Hasse derivative of a monomial: `∂^d (a X^m) = (∏ⱼ (mⱼ choose dⱼ)) a X^(m - d)`. -/
@[simp]
theorem hasseDeriv_monomial (d m : σ →₀ ℕ) (a : R) :
    hasseDeriv d (monomial m a) =
      monomial (m - d) (((d.prod fun j k ↦ (m j).choose k : ℕ) : R) * a) := by
  simp [hasseDeriv]

/-- The coefficients of a Hasse derivative:
`[X^m] ∂^d P = (∏ⱼ (mⱼ + dⱼ choose dⱼ)) [X^(m + d)] P`. -/
@[simp]
theorem hasseDeriv_coeff (d m : σ →₀ ℕ) (P : MvPolynomial σ R) :
    (hasseDeriv d P).coeff m =
      ((d.prod fun j k ↦ (m j + k).choose k : ℕ) : R) * P.coeff (m + d) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial n a =>
    rw [hasseDeriv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : n = m + d
    · subst h
      simp only [add_tsub_cancel_right, ↓reduceIte]
      exact congrArg (fun c : ℕ ↦ (c : R) * a)
        (Finsupp.prod_congr fun j _ ↦ by rw [Finsupp.add_apply])
    · rw [ite_eq_right h, mul_zero, ite_eq_right_iff]
      intro h'
      by_cases hdn : d ≤ n
      · exact absurd ((tsub_eq_iff_eq_add_of_le hdn).1 h') h
      · simp [prod_choose_eq_zero hdn]
  | add p q hp hq => simp [hp, hq, mul_add]

/-- The `0`-th Hasse derivative is the identity. -/
@[simp]
theorem hasseDeriv_zero :
    hasseDeriv (0 : σ →₀ ℕ) = (LinearMap.id : MvPolynomial σ R →ₗ[R] _) := by
  refine LinearMap.ext fun P ↦ ?_
  ext m
  simp [hasseDeriv_coeff]

/-- Every Hasse derivative of positive order kills constants. -/
@[simp]
theorem hasseDeriv_C {d : σ →₀ ℕ} (hd : d ≠ 0) (a : R) : hasseDeriv d (C a) = 0 := by
  rw [← monomial_zero', hasseDeriv_monomial,
    prod_choose_eq_zero (by simpa [nonpos_iff_eq_zero] using hd)]
  simp

/-- Hasse derivatives commute with coefficient ring maps. -/
@[simp]
theorem hasseDeriv_map {S : Type*} [CommSemiring S] (f : R →+* S) (d : σ →₀ ℕ)
    (P : MvPolynomial σ R) : hasseDeriv d (map f P) = map f (hasseDeriv d P) := by
  ext m
  simp [hasseDeriv_coeff, coeff_map, map_finsuppProd]

/-- If the degree of `P` in `Xᵢ` is less than `dᵢ`, then `∂^d P = 0`. -/
theorem hasseDeriv_eq_zero_of_degreeOf_lt {d : σ →₀ ℕ} {P : MvPolynomial σ R} {i : σ}
    (h : P.degreeOf i < d i) : hasseDeriv d P = 0 := by
  refine MvPolynomial.ext _ _ fun m ↦ ?_
  have : P.coeff (m + d) = 0 := notMem_support_iff.1 fun hm ↦ by
    have := monomial_le_degreeOf i hm
    simp only [Finsupp.add_apply] at this
    omega
  simp [hasseDeriv_coeff, this]

/-- The Hasse derivative `∂^d` lowers the degree in `Xᵢ` by at least `dᵢ`. -/
theorem degreeOf_hasseDeriv_le (d : σ →₀ ℕ) (P : MvPolynomial σ R) (i : σ) :
    (hasseDeriv d P).degreeOf i ≤ P.degreeOf i - d i := by
  refine degreeOf_le_iff.2 fun m hm ↦ ?_
  rw [mem_support_iff, hasseDeriv_coeff] at hm
  have := monomial_le_degreeOf i (mem_support_iff.2 (right_ne_zero_of_mul hm))
  simp only [Finsupp.add_apply] at this
  omega

/-- Differentiating `∂^(k eᵢ)` with respect to `Xᵢ` gives `(k + 1) ∂^((k + 1) eᵢ)`. -/
private theorem pderiv_hasseDeriv_single (i : σ) (k : ℕ) (P : MvPolynomial σ R) :
    pderiv i (hasseDeriv (single i k) P) = (k + 1) • hasseDeriv (single i (k + 1)) P := by
  induction P using MvPolynomial.induction_on' with
  | monomial n a =>
    simp only [hasseDeriv_monomial, pderiv_monomial, prod_single_index, Nat.choose_zero_right,
      tsub_tsub, ← single_add, smul_monomial, tsub_apply, single_eq_same]
    congr 1
    rw [nsmul_eq_mul, mul_right_comm, ← Nat.cast_mul, ← Nat.choose_succ_right_eq]
    push_cast
    ring
  | add p q hp hq => simp [hp, hq]

/-- The Hasse derivative `∂^(k eᵢ)` is the `k`-th partial derivative in `Xᵢ` divided by `k!`:
`k! • ∂^(k eᵢ) P = (∂/∂Xᵢ)^k P`. -/
theorem factorial_smul_hasseDeriv_single (i : σ) (k : ℕ) (P : MvPolynomial σ R) :
    k.factorial • hasseDeriv (single i k) P = (pderiv i)^[k] P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, map_nsmul, pderiv_hasseDeriv_single, smul_smul,
      Nat.factorial_succ, mul_comm]

/-- On a polynomial in the single variable `Xᵢ`, the Hasse derivative `∂^(k eᵢ)` is the
univariate `k`-th Hasse derivative. -/
theorem hasseDeriv_single_toMvPolynomial (i : σ) (k : ℕ) (p : Polynomial R) :
    hasseDeriv (single i k) (p.toMvPolynomial i) =
      (Polynomial.hasseDeriv k p).toMvPolynomial i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [single_tsub]

/-- On a polynomial in the single variable `Xᵢ`, every Hasse derivative `∂^d` that differentiates
in another variable `Xⱼ` (that is, `dⱼ ≠ 0` for some `j ≠ i`) vanishes. -/
theorem hasseDeriv_toMvPolynomial_eq_zero {d : σ →₀ ℕ} {i j : σ} (hij : i ≠ j) (hd : d j ≠ 0)
    (p : Polynomial R) : hasseDeriv d (p.toMvPolynomial i) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    rw [Polynomial.toMvPolynomial_monomial, hasseDeriv_monomial, prod_choose_eq_zero fun h ↦ hd ?_]
    · simp
    · simpa [hij, hij.symm] using Finsupp.le_def.1 h j

/-- The composition rule `∂^a ∘ ∂^b = (∏ⱼ (aⱼ + bⱼ choose aⱼ)) • ∂^(a + b)`. -/
theorem hasseDeriv_comp (a b : σ →₀ ℕ) :
    (hasseDeriv a).comp (hasseDeriv b) =
      (a.prod fun j k ↦ (k + b j).choose k) •
        (hasseDeriv (a + b) : MvPolynomial σ R →ₗ[R] _) := by
  classical
  refine linearMap_ext fun m ↦ LinearMap.ext_ring ?_
  have ha : a.support ⊆ a.support ∪ b.support := Finset.subset_union_left
  have hb : b.support ⊆ a.support ∪ b.support := Finset.subset_union_right
  have hab : (a + b).support ⊆ a.support ∪ b.support := Finsupp.support_add
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, hasseDeriv_monomial, smul_monomial,
    tsub_tsub, add_comm b a, prod_choose_eq_prod _ ha, prod_choose_eq_prod _ hb,
    prod_choose_eq_prod _ hab,
    Finsupp.prod_of_support_subset _ ha (fun j k ↦ (k + b j).choose k) fun _ _ ↦
      Nat.choose_zero_right _]
  congr 1
  rw [nsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 2
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  -- In each coordinate:
  -- `(m - b).choose a * m.choose b = (a + b).choose a * m.choose (a + b)`.
  have h := Nat.choose_mul (n := m j) (Nat.le_add_left (b j) (a j))
  rw [Nat.add_sub_cancel] at h
  rw [tsub_apply, Finsupp.add_apply, Nat.choose_symm_add]
  linarith

/-- The Leibniz rule for multiplication by a variable:
`∂^d (P Xᵢ) = ∂^(d - eᵢ) P + (∂^d P) Xᵢ`, where the first term is present only when `dᵢ ≠ 0`. -/
theorem hasseDeriv_mul_X (d : σ →₀ ℕ) (P : MvPolynomial σ R) (i : σ) :
    hasseDeriv d (P * X i) =
      (if d i = 0 then 0 else hasseDeriv (d - single i 1) P) + hasseDeriv d P * X i := by
  classical
  -- Restate the condition `dᵢ ≠ 0` as `i ∈ d.support`, the form in which Pascal's rule
  -- `prod_choose_add_single` splits off the extra term.
  have hcond : (if d i = 0 then 0 else hasseDeriv (d - single i 1) P) =
      if i ∈ d.support then hasseDeriv (d - single i 1) P else 0 := by
    simp [Finsupp.mem_support_iff]
  rw [hcond]
  clear hcond
  induction P using MvPolynomial.induction_on' with
  | monomial n a =>
    -- A monomial whose coefficient carries the binomial factor of `d'` only depends on its
    -- exponent when `d' ≤ n`.
    have key {e e' d' : σ →₀ ℕ} (h : d' ≤ n → e = e') :
        monomial e (((d'.prod fun j k ↦ (n j).choose k : ℕ) : R) * a) =
          monomial e' (((d'.prod fun j k ↦ (n j).choose k : ℕ) : R) * a) := by
      by_cases hd : d' ≤ n
      · rw [h hd]
      · rw [prod_choose_eq_zero hd, Nat.cast_zero, zero_mul, monomial_zero, monomial_zero]
    rw [← pow_one (X i), ← monomial_add_single, hasseDeriv_monomial, hasseDeriv_monomial,
      hasseDeriv_monomial, ← monomial_add_single, prod_choose_add_single]
    split_ifs with hi
    · rw [Nat.cast_add, add_mul, map_add, add_comm]
      congr 1
      · refine key fun h ↦ ?_
        ext j
        have hj := Finsupp.le_def.1 h j
        rcases eq_or_ne i j with rfl | hij
        · have hi' := Finsupp.mem_support_iff.1 hi
          simp only [tsub_apply, Finsupp.add_apply, single_eq_same] at hj ⊢
          omega
        · simp [hij] at hj ⊢
      · exact key fun h ↦ (tsub_add_eq_add_tsub h).symm
    · rw [add_zero, zero_add]
      exact key fun h ↦ (tsub_add_eq_add_tsub h).symm
  | add p q hp hq =>
    simp only [add_mul, map_add, hp, hq]
    split_ifs <;> abel

/-- `∂^(2, 0) (X₀³ X₁) = 3 X₀ X₁` over `ℤ`. -/
example : hasseDeriv (single 0 2) (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) ℤ) = 3 * (X 0 * X 1) := by
  have h1 : (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) ℤ) = monomial (single 0 3 + single 1 1) 1 := by
    rw [X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
  have h2 : (3 * (X 0 * X 1) : MvPolynomial (Fin 2) ℤ) = monomial (single 0 1 + single 1 1) 3 := by
    rw [X, X, monomial_mul_monomial, one_mul, ← map_ofNat C 3, C_mul_monomial, mul_one]
  have h3 : (single 0 3 + single 1 1 - single 0 2 : Fin 2 →₀ ℕ) = single 0 1 + single 1 1 := by
    ext j
    fin_cases j <;> simp
  rw [h1, h2, hasseDeriv_monomial, prod_single_index (by simp), h3]
  simp

/-- The divided derivative is not the ordinary one: `∂^(2) X₀² = 1`, while differentiating
`X₀²` twice gives `2`. -/
example : hasseDeriv (single 0 2) (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ) = 1 ∧
    (pderiv 0)^[2] (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ) = 2 := by
  refine ⟨by simp [X_pow_eq_monomial], ?_⟩
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, X_pow_eq_monomial,
    pderiv_monomial, ← single_tsub]
  norm_num [monomial_zero', map_ofNat]

end MvPolynomial
