/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Kronecker
public import TauCeti.RingTheory.MvPolynomial.RestrictSupport
import TauCeti.Data.Finsupp.Weight

/-!
# The power substitution `F ↦ F(X, X ^ B)`

For `B : ℕ`, the *power substitution* `MvPolynomial.powerSubstitution B` sends a bivariate
polynomial `F(Z, W)` (variable `0` is `Z`, variable `1` is `W`) to the univariate polynomial
`F(X, X ^ B)`. It is the Kronecker substitution of `TauCeti.RingTheory.MvPolynomial.Kronecker`
for the weight `![1, B]`, which sends the exponent `μ` to `μ 0 + B * μ 1`. On exponents with
`μ 0 < B` this map is injective (uniqueness of quotient and remainder on division by `B`), so the
substitution is injective on polynomials of `Z`-degree below `B`.

## Main results

* `MvPolynomial.coeff_powerSubstitution`: for `F` of `Z`-degree below `B` and `μ 0 < B`, the
  coefficient of `X ^ (μ 0 + B * μ 1)` in `F(X, X ^ B)` is the coefficient of `Z ^ μ 0 W ^ μ 1`.
* `MvPolynomial.powerSubstitution_injOn`: the substitution is injective on polynomials of
  `Z`-degree below `B`, for every `B` (at `B = 0` this set is empty).
* `MvPolynomial.support_powerSubstitution_subset`,
  `MvPolynomial.natDegree_powerSubstitution_le`: the exponents of `F(X, X ^ B)` are among the
  weights `μ 0 + B * μ 1` of the exponents of `F`, so its degree is at most
  `degreeOf 0 F + B * degreeOf 1 F`.
* `MvPolynomial.powerSubstitution_map`: naturality under a ring map of the coefficients.
* `MvPolynomial.eval_powerSubstitution`: `F(X, X ^ B)` evaluated at `a` is `F(a, a ^ B)`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  Lemma 11.17, which uses the substitution `h(X, X ^ q)`.
* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  proof of Theorem 3.3.7 and Exercise 3.5(a), the Kronecker substitution `xᵢ ↦ t ^ (d ^ (i - 1))`,
  injective on monomials of partial degrees below `d`.
-/

public section

noncomputable section

namespace MvPolynomial

open Finsupp

variable {R S : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring S]

/-- The power substitution `Z ↦ X`, `W ↦ X ^ B` on bivariate polynomials, with variable `0 = Z`
and variable `1 = W`: the evaluation homomorphism `F ↦ F(X, X ^ B)`. -/
def powerSubstitution (B : ℕ) : MvPolynomial (Fin 2) R →ₐ[R] Polynomial R :=
  aeval ![Polynomial.X, Polynomial.X ^ B]

@[simp]
theorem powerSubstitution_X_zero (B : ℕ) :
    powerSubstitution (R := R) B (X 0) = Polynomial.X := by
  simp [powerSubstitution]

@[simp]
theorem powerSubstitution_X_one (B : ℕ) :
    powerSubstitution (R := R) B (X 1) = Polynomial.X ^ B := by
  simp [powerSubstitution]

/-- The power substitution is the Kronecker substitution `Xₛ ↦ X ^ eₛ` for the weight
`e = ![1, B]`. -/
theorem powerSubstitution_eq_aeval_X_pow (B : ℕ) :
    powerSubstitution (R := R) B = aeval fun s ↦ (Polynomial.X : Polynomial R) ^ ![1, B] s := by
  refine algHom_ext fun s ↦ ?_
  fin_cases s <;> simp [powerSubstitution]

/-- The power substitution sends the monomial `c Z ^ μ 0 W ^ μ 1` to `c X ^ (μ 0 + B * μ 1)`. -/
@[simp]
theorem powerSubstitution_monomial (B : ℕ) (μ : Fin 2 →₀ ℕ) (c : R) :
    powerSubstitution B (monomial μ c) = Polynomial.monomial (μ 0 + B * μ 1) c := by
  rw [powerSubstitution_eq_aeval_X_pow, aeval_X_pow_left_monomial, weight_vecCons_one]

/-- For `F` of `Z`-degree below `B` and an exponent `μ` with `μ 0 < B`, the coefficient of
`X ^ (μ 0 + B * μ 1)` in `F(X, X ^ B)` is the coefficient of `Z ^ μ 0 W ^ μ 1` in `F`. -/
theorem coeff_powerSubstitution {B : ℕ} {F : MvPolynomial (Fin 2) R} (hF : F.degreeOf 0 < B)
    {μ : Fin 2 →₀ ℕ} (hμ : μ 0 < B) :
    (powerSubstitution B F).coeff (μ 0 + B * μ 1) = F.coeff μ := by
  rw [powerSubstitution_eq_aeval_X_pow, ← weight_vecCons_one]
  exact coeff_aeval_X_pow_weight (injOn_weight_vecCons_one B)
    ((mem_restrictSupport_iff (R := R)).mp (mem_restrictSupport_of_degreeOf_lt hF)) hμ

/-- **The power substitution is injective below the `Z`-degree `B`.** Two bivariate polynomials
of `Z`-degree below `B` with the same image `F(X, X ^ B)` are equal. No positivity of `B` is
needed: for `B = 0` the set is empty. -/
theorem powerSubstitution_injOn (B : ℕ) :
    Set.InjOn (powerSubstitution (R := R) B) {F : MvPolynomial (Fin 2) R | F.degreeOf 0 < B} := by
  rw [powerSubstitution_eq_aeval_X_pow]
  exact (injOn_aeval_X_pow (injOn_weight_vecCons_one B)).mono fun _ ↦
    mem_restrictSupport_of_degreeOf_lt

/-- The power substitution preserves linear independence of a family of polynomials of
`Z`-degree below `B`. -/
theorem linearIndependent_powerSubstitution {ι : Type*} {B : ℕ} {φ : ι → MvPolynomial (Fin 2) R}
    (hφB : ∀ i, (φ i).degreeOf 0 < B) (hφ : LinearIndependent R φ) :
    LinearIndependent R fun i ↦ powerSubstitution B (φ i) := by
  rw [powerSubstitution_eq_aeval_X_pow]
  exact linearIndependent_aeval_X_pow (injOn_weight_vecCons_one B)
    (fun i ↦ (mem_restrictSupport_iff (R := R)).mp (mem_restrictSupport_of_degreeOf_lt (hφB i))) hφ

/-- The exponents of `F(X, X ^ B)` are among the weights `μ 0 + B * μ 1` of the exponents `μ`
of `F`. -/
theorem support_powerSubstitution_subset (B : ℕ) (F : MvPolynomial (Fin 2) R) :
    (powerSubstitution B F).support ⊆ F.support.image fun μ ↦ μ 0 + B * μ 1 := by
  classical
  intro N hN
  by_contra hNim
  apply Polynomial.mem_support_iff.mp hN
  conv_lhs => rw [F.as_sum]
  simp only [map_sum, powerSubstitution_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial_apply]
  exact Finset.sum_eq_zero fun μ hμ ↦ ite_eq_right fun h ↦ hNim (Finset.mem_image.mpr ⟨μ, hμ, h⟩)

/-- The degree of `F(X, X ^ B)` is at most `degreeOf 0 F + B * degreeOf 1 F`. -/
theorem natDegree_powerSubstitution_le (B : ℕ) (F : MvPolynomial (Fin 2) R) :
    (powerSubstitution B F).natDegree ≤ F.degreeOf 0 + B * F.degreeOf 1 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
  refine Polynomial.notMem_support_iff.mp fun hmem ↦ ?_
  obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp (support_powerSubstitution_subset B F hmem)
  exact hN.not_ge (Nat.add_le_add (monomial_le_degreeOf 0 hμ)
    (Nat.mul_le_mul_left B (monomial_le_degreeOf 1 hμ)))

/-- The power substitution commutes with a ring map `f : R →+* S` applied to the coefficients. -/
@[simp]
theorem powerSubstitution_map (f : R →+* S) (B : ℕ) (F : MvPolynomial (Fin 2) R) :
    powerSubstitution B (map f F) = Polynomial.map f (powerSubstitution B F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial μ c => simp
  | add F G hF hG => simp [hF, hG, Polynomial.map_add]

/-- **Evaluation formula.** `F(X, X ^ B)` evaluated at `a` is `F(a, a ^ B)`. -/
@[simp]
theorem eval_powerSubstitution (B : ℕ) (a : R) (F : MvPolynomial (Fin 2) R) :
    (powerSubstitution B F).eval a = eval ![a, a ^ B] F := by
  induction F using MvPolynomial.induction_on' with
  | monomial μ c => simp [eval_monomial, Finsupp.prod_fintype, pow_add, pow_mul]
  | add F G hF hG => simp [hF, hG]

end CommSemiring

/-! The bound `B` on the `Z`-degree cannot be dropped: `Z ^ 2` and `W` both map to `X ^ 2`. -/

example : powerSubstitution (R := ℤ) 2 (X 0 ^ 2) = powerSubstitution 2 (X 1) := by
  simp

example : (X 0 ^ 2 : MvPolynomial (Fin 2) ℤ) ≠ X 1 := by
  intro h
  simpa [degreeOf_X] using congrArg (degreeOf 0) h

end MvPolynomial
