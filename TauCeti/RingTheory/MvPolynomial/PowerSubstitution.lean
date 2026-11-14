/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic
public import TauCeti.Algebra.Polynomial.Expand
public import TauCeti.RingTheory.MvPolynomial.Kronecker
public import TauCeti.RingTheory.MvPolynomial.RestrictSupport

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.Data.Finsupp.Weight

/-!
# The power substitution `F ↦ F(X, X ^ B)` and its derivatives

For `B : ℕ`, the *power substitution* `MvPolynomial.powerSubstitution B` sends a bivariate
polynomial `F(Z, W)` (variable `0` is `Z`, variable `1` is `W`) to the univariate polynomial
`F(X, X ^ B)`. It is the Kronecker substitution of `TauCeti.RingTheory.MvPolynomial.Kronecker`
for the weight `![1, B]`, which sends the exponent `μ` to `μ 0 + B * μ 1`. On exponents with
`μ 0 < B` this map is injective (uniqueness of quotient and remainder on division by `B`), so the
substitution is injective on polynomials of `Z`-degree below `B`.

Over a commutative semiring `R` of characteristic `p` and for a prime power `q = p ^ e`:
* When `0 < e`, `(q : R) = 0`, so `D(X ^ q) = 0` and ordinary derivatives of *every* order commute
  with `powerSubstitution q`: `D ^ k (F(X, X ^ q)) = (∂_Z ^ k F)(X, X ^ q)`
  (`MvPolynomial.iterate_derivative_powerSubstitution`). At `e = 0` (`q = 1`) this fails on
  `F = W`.
* For every `e ≥ 0` and every order `k < q`, Hasse derivatives commute with `powerSubstitution q`:
  `D^[k] (F(X, X ^ q)) = (∂_Z^[k] F)(X, X ^ q)` (`MvPolynomial.hasseDeriv_powerSubstitution`),
  proved coefficientwise from `Polynomial.hasseDeriv_expand_mul`. At `k = q` this fails on `F = W`,
  since `D^[q] (X ^ q) = 1` whereas `∂_Z^[q] W = 0`
  (`MvPolynomial.hasseDeriv_powerSubstitution_X_one_self`).

## Main results

* `MvPolynomial.coeff_powerSubstitution`: for `F` of `Z`-degree below `B` and `μ 0 < B`, the
  coefficient of `X ^ (μ 0 + B * μ 1)` in `F(X, X ^ B)` is the coefficient of `Z ^ μ 0 W ^ μ 1`.
* `MvPolynomial.powerSubstitution_injOn`, `MvPolynomial.powerSubstitution_eq_zero_iff`,
  `MvPolynomial.powerSubstitution_ne_zero`: the substitution is injective (and reflects zero) on
  polynomials of `Z`-degree below `B`, for every `B` (at `B = 0` this set is empty).
* `MvPolynomial.support_powerSubstitution_subset`,
  `MvPolynomial.natDegree_powerSubstitution_le`,
  `MvPolynomial.natDegree_powerSubstitution_lt_of_mem_restrictSupport`: the exponents of
  `F(X, X ^ B)` are among the weights `μ 0 + B * μ 1` of the exponents of `F`, bounding its degree
  from partial degrees or from a weighted support condition.
* `MvPolynomial.powerSubstitution_map`, `MvPolynomial.eval_powerSubstitution`,
  `MvPolynomial.aeval_powerSubstitution`: naturality under coefficient ring maps and evaluation in
  `R` or any `R`-algebra.
* `MvPolynomial.derivative_powerSubstitution`, `MvPolynomial.iterate_derivative_powerSubstitution`,
  `MvPolynomial.eval_iterate_derivative_powerSubstitution`,
  `MvPolynomial.aeval_iterate_derivative_powerSubstitution`: the chain rule for
  `powerSubstitution B` and commutation of iterated ordinary derivatives with
  `powerSubstitution (p ^ e)` when `0 < e`.
* `MvPolynomial.hasseDeriv_powerSubstitution`, `MvPolynomial.eval_hasseDeriv_powerSubstitution`,
  `MvPolynomial.aeval_hasseDeriv_powerSubstitution`: commutation of Hasse derivatives of order
  `k < p ^ e` with `powerSubstitution (p ^ e)` in exponential characteristic `p`, including orders
  `p ≤ k < p ^ e`.
* `MvPolynomial.hasseDeriv_powerSubstitution_X_one_self`: sharpness witness `F = W` at order
  `k = B`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6, pp. 283–284, Lemma 11.17, which uses the substitution `h(X, X ^ q)` and Hasse derivatives
  of order `k < q`.
* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  proof of Theorem 3.3.7 and Exercise 3.5(a), the Kronecker substitution `xᵢ ↦ t ^ (d ^ (i - 1))`,
  injective on monomials of partial degrees below `d`.
-/

public section

noncomputable section

namespace MvPolynomial

open Finsupp

section CommSemiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

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

/-- On polynomials of `Z`-degree below `B`, `F(X, X ^ B)` vanishes if and only if `F = 0`. -/
theorem powerSubstitution_eq_zero_iff {B : ℕ} {F : MvPolynomial (Fin 2) R}
    (hZ : F.degreeOf 0 < B) :
    powerSubstitution B F = 0 ↔ F = 0 := by
  have hB : 0 < B := (Nat.zero_le _).trans_lt hZ
  have h0 : (0 : MvPolynomial (Fin 2) R).degreeOf 0 < B := by simp [hB]
  exact ⟨fun h ↦ powerSubstitution_injOn B hZ h0 (by simpa using h), fun h ↦ by simp [h]⟩

/-- A nonzero bivariate polynomial of `Z`-degree below `B` has nonzero image `F(X, X ^ B)`. -/
theorem powerSubstitution_ne_zero {B : ℕ} {F : MvPolynomial (Fin 2) R} (hF : F ≠ 0)
    (hZ : F.degreeOf 0 < B) :
    powerSubstitution B F ≠ 0 :=
  (powerSubstitution_eq_zero_iff hZ).not.mpr hF

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

/-- If `0 < D` and every exponent `μ ∈ s` has weight `μ 0 + B * μ 1 < D`, then every polynomial
`F ∈ restrictSupport R s` satisfies `(powerSubstitution B F).natDegree < D`. -/
theorem natDegree_powerSubstitution_lt_of_mem_restrictSupport {B D : ℕ} {s : Set (Fin 2 →₀ ℕ)}
    {F : MvPolynomial (Fin 2) R} (hD : 0 < D) (hF : F ∈ restrictSupport R s)
    (hs : ∀ μ ∈ s, μ 0 + B * μ 1 < D) :
    (powerSubstitution B F).natDegree < D := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hD.ne'
  refine Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_)
  refine Polynomial.notMem_support_iff.mp fun hmem ↦ ?_
  obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp (support_powerSubstitution_subset B F hmem)
  have := hs μ (hF hμ)
  omega

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

/-- **Algebra evaluation formula.** Evaluating `F(X, X ^ B)` at `a : A` in any `R`-algebra `A`
gives `F(a, a ^ B)`. -/
@[simp]
theorem aeval_powerSubstitution {A : Type*} [CommSemiring A] [Algebra R A] (B : ℕ) (a : A)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (powerSubstitution B F) = aeval ![a, a ^ B] F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [powerSubstitution]
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    fin_cases i <;> simp [hF]

/-- **Chain rule for the power substitution.** For any `B : ℕ`,
`D(F(X, X ^ B)) = (∂_Z F)(X, X ^ B) + (∂_W F)(X, X ^ B) · B X ^ (B - 1)`. -/
theorem derivative_powerSubstitution (B : ℕ) (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative (powerSubstitution B F) =
      powerSubstitution B (pderiv 0 F) +
        powerSubstitution B (pderiv 1 F) * (Polynomial.C (B : R) * Polynomial.X ^ (B - 1)) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [powerSubstitution]
  | add F G hF hG =>
    simp only [map_add, hF, hG, add_mul]
    abel
  | mul_X F i hF =>
    fin_cases i
    · rw [Fin.zero_eta]
      simp only [Derivation.leibniz, pderiv_X_self, pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1),
        smul_eq_mul, map_add, map_mul, mul_zero, mul_one, zero_add,
        powerSubstitution_X_zero, Polynomial.derivative_mul, hF, Polynomial.derivative_X]
      ring
    · rw [Fin.mk_one]
      simp only [Derivation.leibniz, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), pderiv_X_self,
        smul_eq_mul, map_add, map_mul, mul_zero, mul_one, zero_add,
        powerSubstitution_X_one, Polynomial.derivative_mul, hF, Polynomial.derivative_X_pow]
      ring

/-- Whenever `(B : R) = 0`, ordinary differentiation commutes with `powerSubstitution B`:
`D(F(X, X ^ B)) = (∂_Z F)(X, X ^ B)`. -/
theorem derivative_powerSubstitution_of_natCast_eq_zero {B : ℕ} (hB : (B : R) = 0)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative (powerSubstitution B F) = powerSubstitution B (pderiv 0 F) := by
  simp [derivative_powerSubstitution, hB]

/-- Whenever `(B : R) = 0`, iterated ordinary derivatives of every order commute with
`powerSubstitution B`: `D ^ k (F(X, X ^ B)) = (∂_Z ^ k F)(X, X ^ B)`. -/
theorem iterate_derivative_powerSubstitution_of_natCast_eq_zero {B : ℕ} (hB : (B : R) = 0)
    (k : ℕ) (F : MvPolynomial (Fin 2) R) :
    (Polynomial.derivative^[k]) (powerSubstitution B F) =
      powerSubstitution B ((pderiv (0 : Fin 2))^[k] F) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      derivative_powerSubstitution_of_natCast_eq_zero hB, ih]

/-- **Sharpness witness at order `B`.** The `B`-th univariate Hasse derivative of
`powerSubstitution B W = X ^ B` is `1`, whereas for `0 < B` the `Z`-Hasse derivative `∂_Z^[B] W`
is `0` (`MvPolynomial.hasseDeriv_single_zero_X_one`). -/
theorem hasseDeriv_powerSubstitution_X_one_self (B : ℕ) :
    Polynomial.hasseDeriv B (powerSubstitution (R := R) B (X 1)) = 1 := by
  simp [powerSubstitution_X_one, ← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow]

/-- Every positive-order `Z`-Hasse derivative of `W = X 1` vanishes. -/
theorem hasseDeriv_single_zero_X_one {k : ℕ} (hk : 0 < k) :
    hasseDeriv (single (0 : Fin 2) k) (X 1 : MvPolynomial (Fin 2) R) = 0 := by
  simp [hasseDeriv_X, single_eq_single_iff, hk.ne']

end CommSemiring

section CharP

variable {R : Type*} [CommSemiring R] {p : ℕ} [CharP R p]

/-- In characteristic `p` and for `q = p ^ e` with `0 < e`, the first ordinary derivative commutes
with the Frobenius substitution `F ↦ F(X, X ^ q)`. -/
theorem derivative_powerSubstitution_charP {e : ℕ} (he : 0 < e) (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) (pderiv 0 F) :=
  derivative_powerSubstitution_of_natCast_eq_zero
    (by rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne']) F

/-- **Ordinary derivatives through the Frobenius substitution.** In characteristic `p` and for
`q = p ^ e` with `0 < e`, ordinary derivatives of every order commute with `F ↦ F(X, X ^ q)`:
`D ^ k (F(X, X ^ q)) = (∂_Z ^ k F)(X, X ^ q)`. -/
theorem iterate_derivative_powerSubstitution {e : ℕ} (he : 0 < e) (k : ℕ)
    (F : MvPolynomial (Fin 2) R) :
    (Polynomial.derivative^[k]) (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) ((pderiv (0 : Fin 2))^[k] F) :=
  iterate_derivative_powerSubstitution_of_natCast_eq_zero
    (by rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne']) k F

/-- **Evaluated ordinary derivatives through the Frobenius substitution.** For `0 < e` and every
order `k`, evaluating `D ^ k (F(X, X ^ (p ^ e)))` at `a : R` gives `(∂_Z ^ k F)(a, a ^ (p ^ e))`.
-/
theorem eval_iterate_derivative_powerSubstitution {e : ℕ} (he : 0 < e) (k : ℕ) (a : R)
    (F : MvPolynomial (Fin 2) R) :
    ((Polynomial.derivative^[k]) (powerSubstitution (p ^ e) F)).eval a =
      eval ![a, a ^ p ^ e] ((pderiv (0 : Fin 2))^[k] F) := by
  rw [iterate_derivative_powerSubstitution he, eval_powerSubstitution]

/-- **Algebra-evaluated ordinary derivatives through the Frobenius substitution.** For `0 < e` and
every order `k`, evaluating `D ^ k (F(X, X ^ (p ^ e)))` at `a : A` in any `R`-algebra `A` gives
`(∂_Z ^ k F)(a, a ^ (p ^ e))`. -/
theorem aeval_iterate_derivative_powerSubstitution {A : Type*} [CommSemiring A] [Algebra R A]
    {e : ℕ} (he : 0 < e) (k : ℕ) (a : A) (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a ((Polynomial.derivative^[k]) (powerSubstitution (p ^ e) F)) =
      aeval ![a, a ^ p ^ e] ((pderiv (0 : Fin 2))^[k] F) := by
  rw [iterate_derivative_powerSubstitution he, aeval_powerSubstitution]

end CharP

section ExpChar

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p]

/-- **Hasse derivatives through the Frobenius substitution** (Iwaniec–Kowalski, Lemma 11.17).
In exponential characteristic `p` and for `q = p ^ e`, Hasse derivatives of order `k < q` commute
with `F ↦ F(X, X ^ q)`: `D^[k] (F(X, X ^ q)) = (∂_Z^[k] F)(X, X ^ q)`. -/
theorem hasseDeriv_powerSubstitution {e : ℕ} (k : ℕ) (hk : k < p ^ e)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) (hasseDeriv (single 0 k) F) := by
  induction F using MvPolynomial.induction_on' with
  | add F G hF hG => simp [hF, hG]
  | monomial μ c =>
    have hsplit : Polynomial.monomial (μ 0 + p ^ e * μ 1) c =
        Polynomial.expand R (p ^ e) (Polynomial.monomial (μ 1) 1) *
          Polynomial.monomial (μ 0) c := by
      rw [Polynomial.expand_monomial, Polynomial.monomial_mul_monomial, one_mul,
        Nat.mul_comm (μ 1), Nat.add_comm]
    rw [powerSubstitution_monomial, hsplit, Polynomial.hasseDeriv_expand_mul hk,
      Polynomial.expand_monomial, Polynomial.hasseDeriv_monomial, Polynomial.monomial_mul_monomial,
      one_mul, hasseDeriv_monomial, prod_single_index (by simp), powerSubstitution_monomial]
    simp [Nat.mul_comm (μ 1), Nat.add_comm]

/-- **Evaluated Hasse derivatives through the Frobenius substitution.** For `k < p ^ e`,
evaluating `D^[k] (F(X, X ^ (p ^ e)))` at `a : R` gives `(∂_Z^[k] F)(a, a ^ (p ^ e))`. -/
theorem eval_hasseDeriv_powerSubstitution {e : ℕ} (k : ℕ) (hk : k < p ^ e) (a : R)
    (F : MvPolynomial (Fin 2) R) :
    (Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F)).eval a =
      eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) := by
  rw [hasseDeriv_powerSubstitution k hk, eval_powerSubstitution]

/-- **Algebra-evaluated Hasse derivatives through the Frobenius substitution.** For `k < p ^ e`,
evaluating `D^[k] (F(X, X ^ (p ^ e)))` at `a : A` in any `R`-algebra `A` gives
`(∂_Z^[k] F)(a, a ^ (p ^ e))`. -/
theorem aeval_hasseDeriv_powerSubstitution {A : Type*} [CommSemiring A] [Algebra R A] {e : ℕ}
    (k : ℕ) (hk : k < p ^ e) (a : A) (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F)) =
      aeval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) := by
  rw [hasseDeriv_powerSubstitution k hk, aeval_powerSubstitution]

end ExpChar

/-! ### Examples -/

/-! The bound `B` on the `Z`-degree cannot be dropped: `Z ^ 2` and `W` both map to `X ^ 2`. -/

example : powerSubstitution (R := ℤ) 2 (X 0 ^ 2) = powerSubstitution 2 (X 1) := by
  simp

example : (X 0 ^ 2 : MvPolynomial (Fin 2) ℤ) ≠ X 1 := by
  intro h
  simpa [degreeOf_X] using congrArg (degreeOf 0) h

/-- Over `ZMod 2` (`p = 2`, `e = 1`), `D(powerSubstitution 2 (Z W)) = X ^ 2 =
powerSubstitution 2 (∂_Z (Z W))`. -/
example :
    Polynomial.derivative (powerSubstitution (2 ^ 1) (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
      Polynomial.X ^ 2 ∧
    powerSubstitution (2 ^ 1) (pderiv 0 (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
      Polynomial.X ^ 2 := by
  refine ⟨?_, ?_⟩
  · rw [derivative_powerSubstitution_charP (p := 2) (e := 1) (by decide)]
    simp [Derivation.leibniz]
  · simp [Derivation.leibniz]

/-- Over `ZMod 2` (`p = 2`, `e = 1`), ordinary derivatives of `F = W` commute with
`powerSubstitution 2` at every order `k`. -/
example (k : ℕ) (hk : 0 < k) :
    (Polynomial.derivative^[k])
        (powerSubstitution (2 ^ 1) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 ∧
      powerSubstitution (2 ^ 1) ((pderiv (0 : Fin 2))^[k]
        (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [iterate_derivative_powerSubstitution (p := 2) (e := 1) (by decide) (m + 1)]
  have h0 : ((pderiv (0 : Fin 2))^[m + 1] (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
    rw [Function.iterate_succ_apply, pderiv_X_of_ne (by decide)]
    exact Function.iterate_fixed (map_zero _) m
  simp [h0]

/-- Over `ZMod 3` (`p = 3`, `e = 1`, `k = 2`), `D^[2] (powerSubstitution 3 (Z ^ 2 W)) = X ^ 3`. -/
example :
    Polynomial.hasseDeriv 2
        (powerSubstitution (3 ^ 1) (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) =
      Polynomial.X ^ 3 := by
  rw [hasseDeriv_powerSubstitution (p := 3) (e := 1) 2 (by decide)]
  have hmon : (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) =
      monomial (single 0 2 + single 1 1) 1 := by
    rw [X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
  have hsub : (single 0 2 + single 1 1 - single 0 2 : Fin 2 →₀ ℕ) = single 1 1 := by
    ext j; fin_cases j <;> simp
  rw [hmon, hasseDeriv_monomial, prod_single_index (by simp), hsub]
  simp [← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow]

/-- Sharpness of `k < p ^ e` in `hasseDeriv_powerSubstitution`: for `p = 2`, `e = 1`, `k = 2`,
`F = W`, `D^[2] (X ^ 2) = 1` whereas `∂_Z^[2] W = 0`. -/
example :
    Polynomial.hasseDeriv 2
        (powerSubstitution (2 ^ 1) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 1 ∧
      powerSubstitution (2 ^ 1)
        (hasseDeriv (single 0 2) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  refine ⟨hasseDeriv_powerSubstitution_X_one_self 2, ?_⟩
  rw [hasseDeriv_single_zero_X_one (by decide), map_zero]

/-- Orders `p ≤ k < p ^ e` are covered by `hasseDeriv_powerSubstitution`: for `p = 2`, `e = 2`,
`q = 4` over `ZMod 2`, `D^[3] (powerSubstitution 4 (Z ^ 3 W)) = X ^ 4`, `D^[2] (X ^ 4) = 0`, and
at `k = q = 4`, `D^[4] (X ^ 4) = 1 ≠ 0 = powerSubstitution 4 (∂_Z^[4] W)`. -/
example :
    Polynomial.hasseDeriv 3
        (powerSubstitution (2 ^ 2) (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
      Polynomial.X ^ 4 ∧
    Polynomial.hasseDeriv 2
        (powerSubstitution (2 ^ 2) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 ∧
    Polynomial.hasseDeriv 4
        (powerSubstitution (2 ^ 2) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 1 ∧
    powerSubstitution (2 ^ 2)
        (hasseDeriv (single 0 4) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  refine ⟨?_, ?_, hasseDeriv_powerSubstitution_X_one_self 4, ?_⟩
  · rw [hasseDeriv_powerSubstitution (p := 2) (e := 2) 3 (by decide)]
    have hmon : (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2)) =
        monomial (single 0 3 + single 1 1) 1 := by
      rw [X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
    have hsub : (single 0 3 + single 1 1 - single 0 3 : Fin 2 →₀ ℕ) = single 1 1 := by
      ext j; fin_cases j <;> simp
    rw [hmon, hasseDeriv_monomial, prod_single_index (by simp), hsub]
    simp [← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow]
  · rw [hasseDeriv_powerSubstitution (p := 2) (e := 2) 2 (by decide),
      hasseDeriv_single_zero_X_one (by decide), map_zero]
  · rw [hasseDeriv_single_zero_X_one (by decide), map_zero]

/-- Sharpness of `0 < e` in `iterate_derivative_powerSubstitution`: at `e = 0` (`q = 1`), `F = W`
maps to `X`, so `D (powerSubstitution 1 W) = 1`, whereas `∂_Z W = 0`. -/
example :
    Polynomial.derivative (powerSubstitution (2 ^ 0) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 1 ∧
      powerSubstitution (2 ^ 0) (pderiv 0 (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  simp

/-- Over `GaloisField 2 2` (four elements, characteristic `2`), `hasseDeriv_powerSubstitution`
holds with `q = 2` (`e = 1`) for `c · Z W`, giving `c X ^ 2` on both sides without any hypothesis
relating `q` to the size of the coefficient field. -/
example (c : GaloisField 2 2) :
    Polynomial.hasseDeriv 1
        (powerSubstitution (2 ^ 1) (C c * X 0 * X 1 : MvPolynomial (Fin 2) (GaloisField 2 2))) =
      Polynomial.C c * Polynomial.X ^ 2 ∧
    powerSubstitution (2 ^ 1)
        (hasseDeriv (single 0 1) (C c * X 0 * X 1 : MvPolynomial (Fin 2) (GaloisField 2 2))) =
      Polynomial.C c * Polynomial.X ^ 2 := by
  have h1 : hasseDeriv (single 0 1) (C c * X 0 * X 1 : MvPolynomial (Fin 2) (GaloisField 2 2)) =
      pderiv 0 (C c * X 0 * X 1) := by
    simpa only [Nat.factorial_one, one_smul, Function.iterate_one] using
      factorial_smul_hasseDeriv_single (0 : Fin 2) 1
        (C c * X 0 * X 1 : MvPolynomial (Fin 2) (GaloisField 2 2))
  have hrhs : powerSubstitution (2 ^ 1)
      (hasseDeriv (single 0 1) (C c * X 0 * X 1 : MvPolynomial (Fin 2) (GaloisField 2 2))) =
      Polynomial.C c * Polynomial.X ^ 2 := by
    rw [h1]
    simp [Derivation.leibniz]
  refine ⟨?_, hrhs⟩
  rw [hasseDeriv_powerSubstitution (p := 2) (e := 1) 1 (by decide), hrhs]

/-- Evaluated form at `p = 3`, `e = 1`, `F = Z ^ 2`, `k = 1`, `a = 2`: both sides equal `1` in
`ZMod 3`. -/
example :
    (Polynomial.hasseDeriv 1
        (powerSubstitution (3 ^ 1) (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3)))).eval 2 = 1 ∧
      eval ![2, (2 : ZMod 3) ^ 3 ^ 1]
        (hasseDeriv (single 0 1) (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3))) = 1 := by
  have h1 : hasseDeriv (single 0 1) (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3)) =
      pderiv 0 (X 0 ^ 2) := by
    simpa only [Nat.factorial_one, one_smul, Function.iterate_one] using
      factorial_smul_hasseDeriv_single (0 : Fin 2) 1
        (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3))
  have hrhs : eval ![2, (2 : ZMod 3) ^ 3 ^ 1]
      (hasseDeriv (single 0 1) (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3))) = 1 := by
    rw [h1]
    simp only [pderiv_pow, Nat.add_one_sub_one, pow_one, pderiv_X_self, map_mul, map_natCast,
      map_one, eval_X, Matrix.cons_val_zero]
    decide
  exact ⟨(eval_hasseDeriv_powerSubstitution (p := 3) (e := 1) 1 (by decide) 2 _).trans hrhs, hrhs⟩

/-- Over `ZMod 3` at `e = 1` (`q = 3`), `F = Z W + Z` maps to `X ^ 4 + X`, whose first and second
Hasse derivatives are `X ^ 3 + 1` and `0`, matching `∂_Z^[1] F = W + 1` and `∂_Z^[2] F = 0`. -/
example :
    let F : MvPolynomial (Fin 2) (ZMod 3) := X 0 * X 1 + X 0
    powerSubstitution (3 ^ 1) F = Polynomial.X ^ 4 + Polynomial.X ∧
      Polynomial.hasseDeriv 1 (powerSubstitution (3 ^ 1) F) = Polynomial.X ^ 3 + 1 ∧
      Polynomial.hasseDeriv 2 (powerSubstitution (3 ^ 1) F) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_add, map_mul, powerSubstitution_X_zero, powerSubstitution_X_one]
    ring
  · rw [hasseDeriv_powerSubstitution (p := 3) (e := 1) 1 (by decide)]
    have h1 : hasseDeriv (single 0 1)
        (X 0 * X 1 + X 0 : MvPolynomial (Fin 2) (ZMod 3)) =
        pderiv 0 (X 0 * X 1 + X 0) := by
      simpa only [Nat.factorial_one, one_smul, Function.iterate_one] using
        factorial_smul_hasseDeriv_single (0 : Fin 2) 1
          (X 0 * X 1 + X 0 : MvPolynomial (Fin 2) (ZMod 3))
    rw [h1]
    simp [Derivation.leibniz]
  · rw [hasseDeriv_powerSubstitution (p := 3) (e := 1) 2 (by decide)]
    simp [hasseDeriv_mul_X, single_eq_single_iff]

end MvPolynomial
