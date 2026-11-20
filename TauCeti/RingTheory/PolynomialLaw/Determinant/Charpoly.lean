/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Coeff
public import TauCeti.RingTheory.PolynomialLaw.Determinant.Basic
public import Mathlib.Algebra.Polynomial.Monic

/-!
# The characteristic polynomial and the trace of a determinant

For a `d`-dimensional determinant `D` on an `A`-algebra `R` and `x ∈ R`, the characteristic
polynomial of `x` is `χ(x, X) = D_{A[X]}(X − x)`, the value of the law `D` after scalar extension
to the polynomial ring `A[X]`. Writing

`χ(x, X) = ∑ᵢ (−1)ⁱ Λᵢ(x) Xᵈ⁻ⁱ`,

the coefficient `Λ₀` is `1`, so `χ(x, X)` is monic of degree `d`, the constant coefficient `Λ_d`
is the ground value `D x`, and `Λ₁` is the trace `Tr x`, which is `A`-linear in `x` with
`Tr 1 = d`. The model case is `D = det ∘ ρ` for a representation `ρ : R →ₐ[A] Mₙ(A)`, where
`χ(x, X)` is the characteristic polynomial of the matrix `ρ x` and `Tr x` is its trace.

The trace is defined directly as a coefficient of the polynomial law `D`, the coefficient of
`D (s • 1 + t • x)` with exponent `d − 1` on `s` and exponent `1` on `t`; this makes sense over a
commutative semiring, it is `0` in dimension `0`, and its linearity follows from the coefficient
calculus of polynomial laws. The comparison `Tr x = −(coefficient of Xᵈ⁻¹ in χ(x, X))` holds in
every positive dimension.

## Main declarations

* `TauCeti.Determinant.charpoly`: the characteristic polynomial `χ(x, X) = D_{A[X]}(X − x)`.
* `TauCeti.Determinant.charpoly_monic`, `TauCeti.Determinant.charpoly_natDegree_eq_dim`: it is
  monic of degree `d`.
* `TauCeti.Determinant.charpoly_eval_zero`, `TauCeti.Determinant.charpoly_coeff_zero`:
  `χ(x, 0) = (−1)ᵈ D x`.
* `TauCeti.Determinant.charpoly_one`: `χ(1, X) = (X − 1)ᵈ`.
* `TauCeti.Determinant.trace`: the trace `Λ₁`, as an `A`-linear map `R →ₗ[A] A`.
* `TauCeti.Determinant.trace_one`: `Tr 1 = d`; `TauCeti.Determinant.trace_eq_zero`: the trace
  vanishes in dimension `0`.
* `TauCeti.Determinant.trace_eq_neg_charpoly_coeff`: for `d ≠ 0`, the trace is minus the
  coefficient of `Xᵈ⁻¹` in the characteristic polynomial.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.10](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u

open TensorProduct Polynomial

namespace TauCeti

namespace Determinant

section CommSemiring

variable {A : Type u} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R] {d : ℕ}

/-- The coefficient of `D (s • 1 + t • x)` with exponent `j` on `s` and `d - j` on `t`; up to
sign, it is the characteristic coefficient `Λ_{d - j}(x)`. -/
private def binCoeff (D : Determinant A R d) (x : R) (j : ℕ) : A :=
  PolynomialLaw.coeff A A (Option.elim' x fun _ : Unit ↦ (1 : R)) D.toLaw
    ((Finsupp.single () j).optionElim (d - j))

/-- The value of a determinant at `s • 1 + t • x` is the binary form `∑ⱼ binCoeff j · sʲ tᵈ⁻ʲ`. -/
private theorem rid_toFun_tmul_one_add_tmul (D : Determinant A R d) (x : R) {S : Type*}
    [CommSemiring S] [Algebra A S] (s t : S) :
    Algebra.TensorProduct.rid A A S (D.toLaw.toFun S (s ⊗ₜ[A] 1 + t ⊗ₜ[A] x)) =
      ∑ j ∈ Finset.range (d + 1), D.binCoeff x j • (s ^ j * t ^ (d - j)) := by
  rw [D.isHomogeneousOfDegree.toFun_tmul_add_tmul, map_sum]
  simp [binCoeff]

/-- The ground value of `D` at `s • 1 + t • x`, for scalars `s t : A`. -/
private theorem apply_smul_one_add_smul (D : Determinant A R d) (x : R) (s t : A) :
    D (s • 1 + t • x) = ∑ j ∈ Finset.range (d + 1), D.binCoeff x j * (s ^ j * t ^ (d - j)) := by
  have hlr (y : A ⊗[A] A) : TensorProduct.lid A A y = Algebra.TensorProduct.rid A A A y := by
    induction y using TensorProduct.inductionOn with
    | tmul a b => simp [mul_comm]
    | add y z hy hz => simp [hy, hz]
  have hx : (1 : A) ⊗ₜ[A] (s • (1 : R) + t • x) = s ⊗ₜ[A] 1 + t ⊗ₜ[A] x := by
    simp [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [PolynomialLaw.ground_apply, hlr, hx, PolynomialLaw.toFun'_eq_toFun,
    rid_toFun_tmul_one_add_tmul]
  simp only [smul_eq_mul]

private theorem binCoeff_self (D : Determinant A R d) (x : R) : D.binCoeff x d = 1 := by
  have h := D.apply_smul_one_add_smul x 1 0
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun j hj ↦ by
    rw [zero_pow (by have := Finset.mem_range.mp hj; omega), mul_zero, mul_zero]] at h
  simpa using h.symm

private theorem binCoeff_zero (D : Determinant A R d) (x : R) : D.binCoeff x 0 = D x := by
  have h := D.apply_smul_one_add_smul x 0 1
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun j _ ↦ by
    rw [zero_pow (Nat.succ_ne_zero j), zero_mul, mul_zero]] at h
  simpa using h.symm

/-- The trace `Λ₁` of a determinant `D` of dimension `d`: the coefficient of `D (s • 1 + t • x)`
with exponent `d - 1` on `s` and exponent `1` on `t`. It is `0` in dimension `0`, and in positive
dimension it is minus the coefficient of `Xᵈ⁻¹` in the characteristic polynomial
(`Determinant.trace_eq_neg_charpoly_coeff`). -/
def trace (D : Determinant A R d) : R →ₗ[A] A where
  toFun x := PolynomialLaw.coeff A A (Option.elim' x fun _ : Unit ↦ (1 : R)) D.toLaw
    ((Finsupp.single () (d - 1)).optionElim 1)
  map_add' x y := by
    classical
    set k : Unit →₀ ℕ := Finsupp.single () (d - 1)
    -- the coefficients with exponent `1` on `x + y` split into those with exponent `1` on `x`
    -- and on `y`; the one with exponent `1` on `x` is computed after exchanging `x` and `y`
    let e : Option (Option Unit) ≃ Option (Option Unit) := Equiv.swap none (some none)
    have hswap := PolynomialLaw.coeff_comp_equiv e
      (Option.elim' y (Option.elim' x fun _ : Unit ↦ (1 : R))) D.toLaw
      ((k.optionElim 1).optionElim 0)
    have hm : Option.elim' y (Option.elim' x fun _ : Unit ↦ (1 : R)) ∘ e =
        Option.elim' x (Option.elim' y fun _ : Unit ↦ (1 : R)) := by
      ext o
      rcases o with _ | _ | ⟨⟨⟩⟩ <;> simp [e, Equiv.swap_apply_of_ne_of_ne]
    have hk : ((k.optionElim 1).optionElim 0).equivMapDomain e.symm =
        (k.optionElim 0).optionElim 1 := by
      ext o
      rcases o with _ | _ | ⟨⟨⟩⟩ <;>
        simp [e, Finsupp.optionElim_apply_eq_elim, Equiv.swap_apply_of_ne_of_ne]
    rw [PolynomialLaw.coeff_optionElim_add, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton, zero_add,
      PolynomialLaw.coeff_optionElim_zero, ← hk, ← hm, hswap,
      PolynomialLaw.coeff_optionElim_zero, add_comm]
  map_smul' a x := by
    rw [PolynomialLaw.coeff_optionElim_smul, pow_one, RingHom.id_apply]

theorem trace_apply (D : Determinant A R d) (x : R) :
    D.trace x = PolynomialLaw.coeff A A (Option.elim' x fun _ : Unit ↦ (1 : R)) D.toLaw
      ((Finsupp.single () (d - 1)).optionElim 1) :=
  (rfl)

private theorem trace_eq_binCoeff (D : Determinant A R d) (hd : d ≠ 0) (x : R) :
    D.trace x = D.binCoeff x (d - 1) := by
  rw [trace_apply, binCoeff, Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr hd)]

/-- The trace of a determinant of dimension `0` vanishes. -/
@[simp]
theorem trace_eq_zero (D : Determinant A R 0) : D.trace = 0 := by
  ext x
  exact D.isHomogeneousOfDegree.coeff_eq_zero _ (by simp)

/-- The trace of `1` is the dimension: `Tr 1 = d`. -/
@[simp]
theorem trace_one (D : Determinant A R d) : D.trace 1 = d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  -- compare the coefficients of `Xᵈ⁻¹` in `D (X • 1 + 1 • 1) = (X + 1)ᵈ`
  have h := D.rid_toFun_tmul_one_add_tmul 1 (X : A[X]) 1
  rw [← add_tmul, ← mul_one (X + 1 : A[X]), ← smul_eq_mul, ← smul_tmul',
    D.isHomogeneousOfDegree.toFun_smul, ← Algebra.TensorProduct.one_def,
    D.isMultiplicative.toFun_one] at h
  simp only [Algebra.TensorProduct.one_def, smul_tmul', Algebra.TensorProduct.rid_tmul,
    one_smul, smul_eq_mul, mul_one, one_pow, smul_eq_C_mul] at h
  have hc := congrArg (fun p : A[X] ↦ p.coeff (d - 1)) h
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range,
    coeff_X_add_one_pow] at hc
  rw [ite_eq_left (by omega), Nat.choose_symm (by omega), Nat.choose_one_right] at hc
  rw [D.trace_eq_binCoeff hd.ne', hc]

end CommSemiring

section CommRing

variable {A : Type u} [CommRing A] {R : Type*} [Ring R] [Algebra A R] {d : ℕ}

/-- The characteristic polynomial `χ(x, X) = D_{A[X]}(X − x)` of an element `x` for a determinant
`D`: the value of the law `D` at `X ⊗ 1 − 1 ⊗ x ∈ A[X] ⊗[A] R`. -/
def charpoly (D : Determinant A R d) (x : R) : A[X] :=
  Algebra.TensorProduct.rid A A A[X] (D.toLaw.toFun' A[X] (X ⊗ₜ[A] 1 - 1 ⊗ₜ[A] x))

theorem charpoly_def (D : Determinant A R d) (x : R) :
    D.charpoly x =
      Algebra.TensorProduct.rid A A A[X] (D.toLaw.toFun' A[X] (X ⊗ₜ[A] 1 - 1 ⊗ₜ[A] x)) :=
  (rfl)

/-- The characteristic polynomial as a binary form evaluated at `(X, −1)`. -/
private theorem charpoly_eq_sum (D : Determinant A R d) (x : R) :
    D.charpoly x = ∑ j ∈ Finset.range (d + 1), C ((-1) ^ (d - j) * D.binCoeff x j) * X ^ j := by
  rw [charpoly, sub_eq_add_neg, ← neg_tmul, PolynomialLaw.toFun'_eq_toFun,
    rid_toFun_tmul_one_add_tmul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_eq_C_mul, C_mul, C_pow, C_neg, C_1]
  ring

private theorem coeff_charpoly (D : Determinant A R d) (x : R) (k : ℕ) :
    (D.charpoly x).coeff k = if k ≤ d then (-1) ^ (d - k) * D.binCoeff x k else 0 := by
  simp only [charpoly_eq_sum, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq,
    Finset.mem_range, Nat.lt_succ_iff]

theorem charpoly_natDegree_le (D : Determinant A R d) (x : R) : (D.charpoly x).natDegree ≤ d :=
  natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ by
    rw [coeff_charpoly, ite_eq_right (by exact_mod_cast hk.not_ge)]

private theorem charpoly_coeff_dim (D : Determinant A R d) (x : R) :
    (D.charpoly x).coeff d = 1 := by
  rw [coeff_charpoly, ite_eq_left le_rfl, Nat.sub_self, pow_zero, one_mul, binCoeff_self]

/-- The characteristic polynomial of a determinant is monic. -/
theorem charpoly_monic (D : Determinant A R d) (x : R) : (D.charpoly x).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one d (D.charpoly_natDegree_le x) (D.charpoly_coeff_dim x)

/-- The characteristic polynomial of a determinant of dimension `d` has degree `d`. -/
@[simp]
theorem charpoly_natDegree_eq_dim [Nontrivial A] (D : Determinant A R d) (x : R) :
    (D.charpoly x).natDegree = d :=
  natDegree_eq_of_le_of_coeff_ne_zero (D.charpoly_natDegree_le x)
    (by rw [charpoly_coeff_dim]; exact one_ne_zero)

/-- The constant coefficient of the characteristic polynomial is `(−1)ᵈ D x`. -/
theorem charpoly_coeff_zero (D : Determinant A R d) (x : R) :
    (D.charpoly x).coeff 0 = (-1) ^ d * D x := by
  rw [coeff_charpoly, ite_eq_left (Nat.zero_le d), Nat.sub_zero, binCoeff_zero]

/-- The characteristic polynomial at `0` is `(−1)ᵈ D x`. -/
@[simp]
theorem charpoly_eval_zero (D : Determinant A R d) (x : R) :
    (D.charpoly x).eval 0 = (-1) ^ d * D x := by
  rw [← coeff_zero_eq_eval_zero, charpoly_coeff_zero]

/-- The characteristic polynomial of `1` is `(X − 1)ᵈ`. -/
@[simp]
theorem charpoly_one (D : Determinant A R d) : D.charpoly 1 = (X - 1) ^ d := by
  rw [charpoly, ← sub_tmul, ← mul_one (X - 1 : A[X]), ← smul_eq_mul, ← smul_tmul',
    D.isHomogeneousOfDegree.toFun'_smul, ← Algebra.TensorProduct.one_def,
    D.isMultiplicative.toFun'_one]
  simp only [Algebra.TensorProduct.one_def, smul_tmul', Algebra.TensorProduct.rid_tmul,
    one_smul, smul_eq_mul, mul_one]

/-- In positive dimension, the trace is minus the coefficient of `Xᵈ⁻¹` in the characteristic
polynomial. -/
theorem trace_eq_neg_charpoly_coeff (D : Determinant A R d) (hd : d ≠ 0) (x : R) :
    D.trace x = -(D.charpoly x).coeff (d - 1) := by
  rw [coeff_charpoly, ite_eq_left (Nat.sub_le d 1),
    Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr hd), pow_one, neg_one_mul, neg_neg,
    trace_eq_binCoeff D hd]

end CommRing

end Determinant

end TauCeti
