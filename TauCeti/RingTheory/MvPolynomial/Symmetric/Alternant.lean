/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.LinearAlgebra.Determinant

/-!
# Alternants

For a finite alphabet `σ` and an exponent vector `α : σ → ℕ`, the **alternant**

`a_α = det (X_i ^ α_j)_{i, j ∈ σ}`

is the determinant of the matrix whose row `i` records the powers of the variable `X_i` and whose
column `j` records a single exponent `α_j`.  It is the antisymmetric counterpart of a monomial
symmetric polynomial: expanding the determinant, `a_α` is the signed sum of the monomials
`∏ᵢ X_{τ i} ^ α_i` over the permutations `τ` of `σ`.

Alternants are the numerators of Jacobi's bialternant formula `s_λ = a_{λ+δ} / a_δ` for the Schur
polynomials, and the carriers of Frobenius's formula for the characters of the symmetric group,
`p_ν · a_δ = ∑_λ χ^λ(ν) · a_{λ+δ}`.  The identity that makes the latter compute is the
multiplication rule for power sums proved here,

`p_r · a_α = ∑_j a_{α + r e_j}`,

`TauCeti.psum_mul_alternant`: multiplying by a power sum raises one exponent at a time.  Rewriting
each `a_{α + r e_j}` in terms of a strictly decreasing exponent vector — it vanishes when an
exponent repeats (`TauCeti.alternant_eq_zero_of_not_injective`) and otherwise changes by the sign
of the sorting permutation (`TauCeti.alternant_comp_perm`) — is the move of one bead on the abacus
of beta-numbers, which is how the Murnaghan-Nakayama rule arises from it.

## Main definitions

* `TauCeti.alternant σ R α`: the alternant `det (X_i ^ α_j)` in `MvPolynomial σ R`.

## Main statements

* `TauCeti.alternant_eq_sum`: the Leibniz expansion of the alternant as a signed sum of monomials,
  and `TauCeti.coeff_alternant` with `TauCeti.coeff_alternant_of_injective` its coefficients.
* `TauCeti.alternant_ne_zero_of_injective`: an alternant of pairwise distinct exponents is
  nonzero.
* `TauCeti.isHomogeneous_alternant`: `a_α` is homogeneous of degree `∑ i, α i`.
* `TauCeti.rename_alternant`: `a_α` is antisymmetric, permuting the variables by `e` multiplying
  it by `sign e`.
* `TauCeti.alternant_comp_perm` and `TauCeti.alternant_eq_zero_of_not_injective`: permuting the
  exponents multiplies `a_α` by the sign, and a repeated exponent kills it.
* `TauCeti.alternant_add_const`: shifting every exponent by `c` multiplies `a_α` by
  `(∏ i, X i) ^ c`.
* `TauCeti.alternant_fin_val_eq_vandermonde`: for the exponents `0, 1, …, n - 1` the alternant
  is the Vandermonde product `∏_{i < j} (X_j - X_i)`.
* `TauCeti.psum_mul_alternant`: the power-sum multiplication rule `p_r · a_α = ∑_j a_{α + r e_j}`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3 (alternants and the bialternant formula) and Section 7 (the characters of the
  symmetric groups).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Sections 7.15 (the classical definition of
  Schur functions) and 7.17 (the Murnaghan-Nakayama rule).
-/

public section

namespace TauCeti

open MvPolynomial Equiv Finset

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R]

/-- The **alternant** `a_α = det (X_i ^ α_j)` of an exponent vector `α : σ → ℕ`: the determinant of
the matrix whose entry in row `i` and column `j` is the variable `X_i` raised to the exponent
`α_j`. -/
noncomputable def alternant (α : σ → ℕ) : MvPolynomial σ R :=
  (Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j).det

variable {σ R}

/-- The alternant `a_α` is the determinant of the matrix whose `(i, j)` entry is `X i ^ α j`. -/
theorem alternant_def (α : σ → ℕ) :
    alternant σ R α = (Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j).det :=
  (rfl)

/-- **The Leibniz expansion of an alternant**: `a_α` is the signed sum, over the permutations `τ`
of the alphabet, of the monomials `∏ᵢ X_{τ i} ^ α_i`. -/
theorem alternant_eq_sum (α : σ → ℕ) :
    alternant σ R α = ∑ τ : Perm σ, Perm.sign τ • ∏ i, (X (τ i) : MvPolynomial σ R) ^ α i := by
  simp only [alternant_def, Matrix.det_apply, Matrix.of_apply]

/-- The coefficient of the monomial `x^d` in the alternant `a_α` is the signed count of the
permutations `τ` that carry `d` to `α`, in the sense that `d (τ i) = α i` for every `i`. -/
theorem coeff_alternant (α : σ → ℕ) (d : σ →₀ ℕ) :
    (alternant σ R α).coeff d =
      ∑ τ ∈ univ.filter (fun τ : Perm σ => ⇑d ∘ ⇑τ = α), ((Perm.sign τ : ℤ) : R) := by
  rw [alternant_eq_sum, coeff_sum, sum_filter]
  refine sum_congr rfl fun τ _ => ?_
  have hprod : ∏ i, (X (τ i) : MvPolynomial σ R) ^ α i = ∏ k, (X k) ^ α (τ.symm k) := by
    rw [← Equiv.prod_comp τ fun k => (X k : MvPolynomial σ R) ^ α (τ.symm k)]
    simp
  have hiff : d = Finsupp.indicator (univ : Finset σ) (fun k _ => α (τ.symm k)) ↔
      ⇑d ∘ ⇑τ = α := by
    constructor
    · rintro rfl
      funext i
      simp
    · intro h
      ext k
      simp [← h]
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R), coeff_C_mul,
    hprod, coeff_prod_X_pow]
  by_cases h : ⇑d ∘ ⇑τ = α <;> simp [hiff, h]

/-- For an alternant of pairwise distinct exponents, the coefficient of the monomial
`∏ᵢ X_i ^ α (τ i)` is the sign of `τ`. -/
theorem coeff_alternant_of_injective {α : σ → ℕ} (hα : Function.Injective α) (τ : Perm σ) :
    (alternant σ R α).coeff (Finsupp.equivFunOnFinite.symm (α ∘ τ)) =
      ((Perm.sign τ : ℤ) : R) := by
  rw [coeff_alternant, sum_eq_single τ⁻¹]
  · simp
  · intro ρ hρ hne
    have hρ' : (α ∘ τ) ∘ ρ = α := by simpa using (mem_filter.1 hρ).2
    refine absurd ?_ hne
    ext i
    have hi : τ (ρ i) = i := hα (congrFun hρ' i)
    exact Perm.eq_inv_iff_eq.2 hi
  · intro h
    refine absurd (mem_filter.2 ⟨mem_univ _, ?_⟩) h
    funext i
    simp

/-- **An alternant of pairwise distinct exponents is nonzero**: the monomial `∏ᵢ X_i ^ α i`
occurs in it with coefficient `1`. -/
theorem alternant_ne_zero_of_injective [Nontrivial R] {α : σ → ℕ} (hα : Function.Injective α) :
    alternant σ R α ≠ 0 := by
  intro h
  have := coeff_alternant_of_injective (R := R) hα 1
  simp [h] at this

/-- An alternant is homogeneous of degree the total of its exponents. -/
theorem isHomogeneous_alternant (α : σ → ℕ) :
    (alternant σ R α).IsHomogeneous (∑ i, α i) := by
  rw [alternant_eq_sum]
  refine IsHomogeneous.sum _ _ _ fun τ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R)]
  exact (IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X_pow (τ i) (α i)).C_mul _

/-- **Alternants are antisymmetric**: renaming the variables along a permutation `e` multiplies
an alternant by the sign of `e`. -/
@[simp]
theorem rename_alternant (e : Perm σ) (α : σ → ℕ) :
    rename e (alternant σ R α) = Perm.sign e • alternant σ R α := by
  rw [alternant_def, AlgHom.map_det, Units.smul_def, zsmul_eq_mul,
    ← Matrix.det_permute]
  congr 1
  ext i j
  simp

/-- Permuting the exponents of an alternant multiplies it by the sign of the permutation. -/
@[simp]
theorem alternant_comp_perm (e : Perm σ) (α : σ → ℕ) :
    alternant σ R (α ∘ e) = Perm.sign e • alternant σ R α := by
  rw [alternant_def, alternant_def, Units.smul_def, zsmul_eq_mul, ← Matrix.det_permute']
  congr 1

/-- An alternant with a repeated exponent vanishes. -/
theorem alternant_eq_zero_of_not_injective {α : σ → ℕ} (hα : ¬ Function.Injective α) :
    alternant σ R α = 0 := by
  simp only [Function.Injective, not_forall] at hα
  obtain ⟨i, j, hij, hne⟩ := hα
  exact Matrix.det_zero_of_column_eq hne fun k => by simp [hij]

/-- Raising every exponent of an alternant by `c` multiplies it by `(∏ i, X i) ^ c`. -/
theorem alternant_add_const (α : σ → ℕ) (c : ℕ) :
    alternant σ R (fun j => α j + c) = (∏ i, (X i : MvPolynomial σ R)) ^ c * alternant σ R α := by
  have hmat : (Matrix.of fun i j => (X i : MvPolynomial σ R) ^ (α j + c)) =
      Matrix.diagonal (fun i => (X i : MvPolynomial σ R) ^ c) *
        Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j := by
    ext i j
    simp [Matrix.diagonal_mul, pow_add, mul_comm]
  rw [alternant_def, alternant_def, hmat, Matrix.det_mul, Matrix.det_diagonal, prod_pow]

/-- **The Vandermonde alternant**: for the exponents `0, 1, …, n - 1` the alternant is the
Vandermonde product `∏_{i < j} (X_j - X_i)`. -/
theorem alternant_fin_val_eq_vandermonde (n : ℕ) :
    alternant (Fin n) R (fun j => (j : ℕ)) = ∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i) :=
  Matrix.det_vandermonde (X : Fin n → MvPolynomial (Fin n) R)

/-- **The power-sum multiplication rule for alternants**: multiplying `a_α` by the power sum
`p_r = ∑ᵢ X_i ^ r` gives the sum of the alternants obtained from `α` by raising a single exponent
by `r`, `p_r · a_α = ∑_j a_{α + r e_j}`. -/
theorem psum_mul_alternant (r : ℕ) (α : σ → ℕ) :
    psum σ R r * alternant σ R α =
      ∑ j, alternant σ R (Function.update α j (α j + r)) := by
  set A := Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j with hA
  have hcol : ∀ j, alternant σ R (Function.update α j (α j + r)) =
      (A.transpose.updateRow j fun i => (X i : MvPolynomial σ R) ^ r * A.transpose j i).det := by
    intro j
    rw [alternant_def, ← Matrix.det_transpose]
    congr 1
    ext k i
    rcases eq_or_ne k j with rfl | hk
    · simp [hA, pow_add, mul_comm]
    · simp [hA, Matrix.updateRow_ne hk, Function.update_of_ne hk]
  rw [sum_congr rfl fun j _ => hcol j, Matrix.sum_det_updateRow_mul_row, Matrix.det_transpose,
    psum, alternant_def]

end TauCeti
