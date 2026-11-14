/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Kronecker
public import TauCeti.RingTheory.MvPolynomial.RestrictSupport

import Mathlib.Data.ZMod.Basic
import TauCeti.Algebra.Polynomial.Expand
import TauCeti.Algebra.Polynomial.HasseDeriv
import TauCeti.Data.Finsupp.Weight

/-!
# The power substitution `F ↦ F(X, X ^ B)` and Frobenius-graph jets

For `B : ℕ`, the *power substitution* `MvPolynomial.powerSubstitution B` sends a bivariate
polynomial `F(Z, W)` (variable `0` is `Z`, variable `1` is `W`) to the univariate polynomial
`F(X, X ^ B)`. It is the Kronecker substitution of `TauCeti.RingTheory.MvPolynomial.Kronecker`
for the weight `![1, B]`, which sends the exponent `μ` to `μ 0 + B * μ 1`. On exponents with
`μ 0 < B` this map is injective (uniqueness of quotient and remainder on division by `B`), so the
substitution is injective on polynomials of `Z`-degree below `B`.

Differentiating `F(X, X ^ B)` gives the chain rule
`D(F(X, X ^ B)) = (∂_Z F)(X, X ^ B) + B • X ^ (B - 1) * (∂_W F)(X, X ^ B)`. When `(B : R) = 0`—in
particular for `B = p ^ e` with `0 < e` in characteristic `p`—the `W`-term vanishes and ordinary
differentiation of every order commutes with the substitution. In exponential characteristic `p`,
Hasse differentiation of every order `k < p ^ e` also commutes with `powerSubstitution (p ^ e)`,
including orders `p ≤ k < p ^ e` when `e ≥ 2` where ordinary derivatives vanish identically.

Combining injectivity below `Z`-degree `p ^ e`, the Hasse Frobenius-substitution identity, and the
univariate root-multiplicity bound yields the Frobenius-graph jet nonvanishing test: over an
integral domain of exponential characteristic `p`, any nonzero `F` with `F.degreeOf 0 < p ^ e` and
`(powerSubstitution (p ^ e) F).natDegree < #S * (m + 1)` for `m < p ^ e` has a nonvanishing Hasse
`Z`-jet of order `k ≤ m` at some Frobenius-graph point `(a, a ^ (p ^ e))` with `a ∈ S`; when
`0 < e` and `m < p` in prime characteristic `p`, the same holds for ordinary `Z`-jets.

## Main results

* `MvPolynomial.coeff_powerSubstitution`: for `F` of `Z`-degree below `B` and `μ 0 < B`, the
  coefficient of `X ^ (μ 0 + B * μ 1)` in `F(X, X ^ B)` is the coefficient of `Z ^ μ 0 W ^ μ 1`.
* `MvPolynomial.powerSubstitution_injOn`, `MvPolynomial.powerSubstitution_eq_zero_iff`: the
  substitution is injective (and detects nonvanishing) on polynomials of `Z`-degree below `B`.
* `MvPolynomial.support_powerSubstitution_subset`,
  `MvPolynomial.natDegree_powerSubstitution_le`: the exponents of `F(X, X ^ B)` are among the
  weights `μ 0 + B * μ 1` of the exponents of `F`, so its degree is at most
  `degreeOf 0 F + B * degreeOf 1 F`.
* `MvPolynomial.powerSubstitution_map`, `MvPolynomial.aeval_powerSubstitution`,
  `MvPolynomial.eval_powerSubstitution`: naturality under coefficient maps and evaluation at
  `(a, a ^ B)`.
* `MvPolynomial.derivative_powerSubstitution`,
  `MvPolynomial.iterate_derivative_powerSubstitution_of_natCast_eq_zero`,
  `MvPolynomial.iterate_derivative_powerSubstitution`: the chain rule for `F(X, X ^ B)` and
  commutation of ordinary derivatives of every order when `(B : R) = 0` (in particular `B = p ^ e`
  with `0 < e` in characteristic `p`).
* `MvPolynomial.hasseDeriv_powerSubstitution`, `MvPolynomial.eval_hasseDeriv_powerSubstitution`:
  in exponential characteristic `p`, Hasse derivatives of order `k < p ^ e` commute with
  `powerSubstitution (p ^ e)`; `MvPolynomial.hasseDeriv_powerSubstitution_X_one_ne` records the
  failure at `k = p ^ e` on `F = X 1`.
* `MvPolynomial.exists_nonzero_hasse_jet_on_frobenius_graph`,
  `MvPolynomial.exists_nonzero_ordinary_jet_on_frobenius_graph`: nonvanishing of Hasse (for
  `m < p ^ e`) and ordinary (for `0 < e`, `m < p`) `Z`-jets on the Frobenius graph over `S`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6, Lemmas 11.16 and 11.17, pp. 282–284, for the multiplicity criterion through Hasse
  derivatives and the substitution `h(X, X ^ q)` at orders `k < q`.
* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  proof of Theorem 3.3.7 and Exercise 3.5(a), the Kronecker substitution `xᵢ ↦ t ^ (d ^ (i - 1))`,
  injective on monomials of partial degrees below `d`.
-/

public section

noncomputable section

namespace MvPolynomial

open Finset Finsupp

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

/-- For `F` of `Z`-degree below `B`, `F(X, X ^ B) = 0` if and only if `F = 0`. Note that
`F.degreeOf 0 < B` forces `0 < B`, so `0` also has `Z`-degree below `B`. -/
theorem powerSubstitution_eq_zero_iff {B : ℕ} {F : MvPolynomial (Fin 2) R}
    (hF : F.degreeOf 0 < B) :
    powerSubstitution B F = 0 ↔ F = 0 := by
  refine ⟨fun h ↦ powerSubstitution_injOn B hF ?_ (h.trans (map_zero _).symm), fun h ↦ by simp [h]⟩
  simpa only [Set.mem_ofPred_eq, degreeOf_zero] using (Nat.zero_le _).trans_lt hF

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

/-- **Scalar-extension evaluation formula.** In any `R`-algebra `A`, evaluating `F(X, X ^ B)` at
`a : A` gives `aeval ![a, a ^ B] F`. -/
@[simp]
theorem aeval_powerSubstitution {A : Type*} [CommSemiring A] [Algebra R A] (B : ℕ) (a : A)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (powerSubstitution B F) = aeval ![a, a ^ B] F := by
  have h : (Polynomial.aeval a).comp (powerSubstitution (R := R) B) =
      aeval (![a, a ^ B] : Fin 2 → A) := by
    refine algHom_ext fun s ↦ ?_
    fin_cases s <;> simp
  exact DFunLike.congr_fun h F

/-- **Evaluation formula.** `F(X, X ^ B)` evaluated at `a` is `F(a, a ^ B)`. -/
@[simp]
theorem eval_powerSubstitution (B : ℕ) (a : R) (F : MvPolynomial (Fin 2) R) :
    (powerSubstitution B F).eval a = eval ![a, a ^ B] F :=
  aeval_powerSubstitution B a F

/-- **Chain rule for the power substitution.** Over any commutative semiring and for every `B : ℕ`
(including `B = 0`), `D(F(X, X ^ B)) = (∂_Z F)(X, X ^ B) + B • X ^ (B - 1) * (∂_W F)(X, X ^ B)`. -/
theorem derivative_powerSubstitution (B : ℕ) (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative (powerSubstitution B F) =
      powerSubstitution B (pderiv 0 F) +
        B • Polynomial.X ^ (B - 1) * powerSubstitution B (pderiv 1 F) := by
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add]
    abel
  | mul_X p s hp =>
    fin_cases s
    · simp only [Fin.zero_eta, map_mul, map_add, powerSubstitution_X_zero,
        Polynomial.derivative_mul, Polynomial.derivative_X, mul_one, pderiv_mul, pderiv_X_self,
        pderiv_X_of_ne zero_ne_one, mul_zero, add_zero, hp]
      ring
    · simp only [Fin.mk_one, map_mul, map_add, map_one, powerSubstitution_X_one,
        Polynomial.derivative_mul, Polynomial.derivative_X_pow, Polynomial.C_eq_natCast, pderiv_mul,
        pderiv_X_self, pderiv_X_of_ne one_ne_zero, mul_zero, add_zero, hp, nsmul_eq_mul]
      ring

/-- When `(B : R) = 0`, differentiating `F(X, X ^ B)` drops the `W`-term since
`D(X ^ B) = B X ^ (B - 1) = 0`, giving `D(F(X, X ^ B)) = (∂_Z F)(X, X ^ B)`. -/
theorem derivative_powerSubstitution_of_natCast_eq_zero {B : ℕ} (hB : (B : R) = 0)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative (powerSubstitution B F) = powerSubstitution B (pderiv 0 F) := by
  rw [derivative_powerSubstitution, ← Nat.cast_smul_eq_nsmul R B, hB, zero_smul, zero_mul,
    add_zero]

/-- When `(B : R) = 0`, iterated ordinary derivatives of every order commute with
`powerSubstitution B`: `D ^ k (F(X, X ^ B)) = (∂_Z ^ k F)(X, X ^ B)`. -/
theorem iterate_derivative_powerSubstitution_of_natCast_eq_zero {B : ℕ} (hB : (B : R) = 0)
    (k : ℕ) (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative^[k] (powerSubstitution B F) =
      powerSubstitution B ((pderiv 0)^[k] F) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      derivative_powerSubstitution_of_natCast_eq_zero hB, ih]

/-- Scalar-extension evaluation of iterated ordinary derivatives when `(B : R) = 0`. -/
theorem aeval_iterate_derivative_powerSubstitution_of_natCast_eq_zero {A : Type*}
    [CommSemiring A] [Algebra R A] {B : ℕ} (hB : (B : R) = 0) (k : ℕ) (a : A)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (Polynomial.derivative^[k] (powerSubstitution B F)) =
      aeval ![a, a ^ B] ((pderiv 0)^[k] F) := by
  rw [iterate_derivative_powerSubstitution_of_natCast_eq_zero hB, aeval_powerSubstitution]

/-- Evaluation of iterated ordinary derivatives when `(B : R) = 0`. -/
theorem eval_iterate_derivative_powerSubstitution_of_natCast_eq_zero {B : ℕ} (hB : (B : R) = 0)
    (k : ℕ) (a : R) (F : MvPolynomial (Fin 2) R) :
    (Polynomial.derivative^[k] (powerSubstitution B F)).eval a =
      eval ![a, a ^ B] ((pderiv 0)^[k] F) := by
  rw [iterate_derivative_powerSubstitution_of_natCast_eq_zero hB, eval_powerSubstitution]

/-- For every `B : ℕ`, the `B`-th Hasse derivative of `powerSubstitution B (X 1) = X ^ B` is `1`. -/
theorem hasseDeriv_self_powerSubstitution_X_one (B : ℕ) :
    Polynomial.hasseDeriv B (powerSubstitution (R := R) B (X 1)) = 1 := by
  rw [powerSubstitution_X_one, ← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow,
    one_mul, one_pow, Polynomial.hasseDeriv_monomial, tsub_self, Nat.choose_self, Nat.cast_one,
    one_mul, Polynomial.monomial_zero_left, map_one]

/-- Over a nontrivial commutative semiring and for `B ≠ 0`, Hasse differentiation of order `B`
does not commute with `powerSubstitution B` on `X 1`: the left side is `1` while
`∂_Z^[B] (X 1) = 0`. -/
theorem hasseDeriv_powerSubstitution_X_one_ne [Nontrivial R] {B : ℕ} (hB : B ≠ 0) :
    Polynomial.hasseDeriv B (powerSubstitution (R := R) B (X 1)) ≠
      powerSubstitution B (hasseDeriv (single 0 B) (X 1)) := by
  have h0 : single (0 : Fin 2) B ≠ 0 := Finsupp.single_ne_zero.2 hB
  have h1 : single (0 : Fin 2) B ≠ single 1 1 := fun h ↦
    hB (by simpa using congrArg (fun f : Fin 2 →₀ ℕ ↦ f 0) h)
  rw [hasseDeriv_self_powerSubstitution_X_one, hasseDeriv_X, ite_eq_right h0, ite_eq_right h1,
    map_zero]
  exact one_ne_zero

end CommSemiring

section Frobenius

section Ordinary

variable [CommSemiring R] {p : ℕ} [CharP R p]

/-- In characteristic `p` and for `q = p ^ e` with `0 < e`, the first ordinary derivative commutes
with the Frobenius substitution: `D(F(X, X ^ q)) = (∂_Z F)(X, X ^ q)`. -/
theorem derivative_powerSubstitution_pow_char {e : ℕ} (he : 0 < e)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) (pderiv 0 F) :=
  derivative_powerSubstitution_of_natCast_eq_zero
    (by rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne']) F

/-- In characteristic `p` and for `q = p ^ e` with `0 < e`, ordinary derivatives of every order
commute with the Frobenius substitution: `D ^ k (F(X, X ^ q)) = (∂_Z ^ k F)(X, X ^ q)`. At `e = 0`
(`q = 1`) this fails for `F = X 1`, since `D X = 1` while `∂_Z (X 1) = 0`. -/
theorem iterate_derivative_powerSubstitution {e : ℕ} (he : 0 < e) (k : ℕ)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative^[k] (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) ((pderiv 0)^[k] F) :=
  iterate_derivative_powerSubstitution_of_natCast_eq_zero
    (by rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne']) k F

/-- Scalar-extension evaluation of the ordinary Frobenius-substitution identity (`0 < e`). -/
theorem aeval_iterate_derivative_powerSubstitution {A : Type*} [CommSemiring A] [Algebra R A]
    {e : ℕ} (he : 0 < e) (k : ℕ) (a : A) (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (Polynomial.derivative^[k] (powerSubstitution (p ^ e) F)) =
      aeval ![a, a ^ p ^ e] ((pderiv 0)^[k] F) := by
  rw [iterate_derivative_powerSubstitution he, aeval_powerSubstitution]

/-- Evaluated ordinary Frobenius-substitution identity: for `q = p ^ e` with `0 < e` and every `k`,
`(D ^ k (F(X, X ^ q)))(a) = (∂_Z ^ k F)(a, a ^ q)`. -/
theorem eval_iterate_derivative_powerSubstitution {e : ℕ} (he : 0 < e) (k : ℕ) (a : R)
    (F : MvPolynomial (Fin 2) R) :
    (Polynomial.derivative^[k] (powerSubstitution (p ^ e) F)).eval a =
      eval ![a, a ^ p ^ e] ((pderiv 0)^[k] F) := by
  rw [iterate_derivative_powerSubstitution he, eval_powerSubstitution]

end Ordinary

section Hasse

variable [CommSemiring R] {p : ℕ} [ExpChar R p]

/-- **Hasse derivatives through the Frobenius substitution** (Iwaniec–Kowalski, Lemma 11.17).
Over a commutative semiring of exponential characteristic `p`, for every `e : ℕ` and every
`k < p ^ e`, `D^[k] (F(X, X ^ (p ^ e))) = (∂_Z^[k] F)(X, X ^ (p ^ e))`.
At `e = 0` only `k = 0` is permitted and the identity is trivial; for `e ≥ 2` it also covers
orders `p ≤ k < p ^ e`, where ordinary derivatives vanish identically. At `k = p ^ e` it fails for
`F = X 1` (`hasseDeriv_powerSubstitution_X_one_ne`). -/
theorem hasseDeriv_powerSubstitution {e k : ℕ} (hk : k < p ^ e) (F : MvPolynomial (Fin 2) R) :
    Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) (hasseDeriv (single 0 k) F) := by
  induction F using MvPolynomial.induction_on' with
  | add F G hF hG => simp only [map_add, hF, hG]
  | monomial μ c =>
    have hsplit : Polynomial.monomial (μ 0 + p ^ e * μ 1) c =
        Polynomial.expand R (p ^ e) (Polynomial.X ^ μ 1) * Polynomial.monomial (μ 0) c := by
      rw [← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow, one_mul, one_pow,
        Polynomial.expand_monomial, Polynomial.monomial_mul_monomial, one_mul,
        Nat.mul_comm (μ 1), Nat.add_comm]
    rw [powerSubstitution_monomial, hsplit, Polynomial.hasseDeriv_expand_mul hk,
      Polynomial.hasseDeriv_monomial, ← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow,
      one_mul, one_pow, Polynomial.expand_monomial, Polynomial.monomial_mul_monomial, one_mul,
      hasseDeriv_monomial, powerSubstitution_monomial, prod_single_index (by simp)]
    have h0 : (μ - single (0 : Fin 2) k) 0 = μ 0 - k := by simp
    have h1 : (μ - single (0 : Fin 2) k) 1 = μ 1 := by simp
    congr 2
    rw [h0, h1, Nat.mul_comm (μ 1), Nat.add_comm]

/-- Scalar-extension evaluation of the Hasse Frobenius-substitution identity (`k < p ^ e`). -/
theorem aeval_hasseDeriv_powerSubstitution {A : Type*} [CommSemiring A] [Algebra R A] {e k : ℕ}
    (hk : k < p ^ e) (a : A) (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F)) =
      aeval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) := by
  rw [hasseDeriv_powerSubstitution hk, aeval_powerSubstitution]

/-- Evaluated Hasse Frobenius-substitution identity: in exponential characteristic `p`, for
`k < p ^ e`, `(D^[k] (F(X, X ^ (p ^ e))))(a) = (∂_Z^[k] F)(a, a ^ (p ^ e))`. -/
theorem eval_hasseDeriv_powerSubstitution {e k : ℕ} (hk : k < p ^ e) (a : R)
    (F : MvPolynomial (Fin 2) R) :
    (Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F)).eval a =
      eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) := by
  rw [hasseDeriv_powerSubstitution hk, eval_powerSubstitution]

end Hasse

end Frobenius

section FrobeniusGraphTest

/-- **The Frobenius-graph nonvanishing test, Hasse form** (Iwaniec–Kowalski, Lemmas 11.16–11.17).
Over an integral domain `R` of exponential characteristic `p`, for `q = p ^ e` with any `e ≥ 0`,
if `F ≠ 0` has `Z`-degree below `q`, `m < q`, and `(powerSubstitution q F).natDegree < #S * (m + 1)`
for a finite set `S ⊆ R`, then some Hasse `Z`-jet `∂_Z^[k] F` with `k ≤ m` is nonzero at
`(a, a ^ q)` for some `a ∈ S`. At `e = 0` (`q = 1`), `m = 0` and this reduces to nonvanishing of a
univariate polynomial in `W` of degree below `#S` on `S`. -/
theorem exists_nonzero_hasse_jet_on_frobenius_graph {R : Type*} [CommRing R] [IsDomain R] {p : ℕ}
    [ExpChar R p] {e : ℕ} {F : MvPolynomial (Fin 2) R} (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e)
    {S : Finset R} {m : ℕ} (hm : m < p ^ e)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < #S * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m, eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) ≠ 0 := by
  have hf : powerSubstitution (p ^ e) F ≠ 0 := mt (powerSubstitution_eq_zero_iff hZ).1 hF
  obtain ⟨a, ha, k, hk, hne⟩ :=
    Polynomial.exists_eval_hasseDeriv_ne_zero_of_natDegree_lt hf hdeg
  refine ⟨a, ha, k, hk, ?_⟩
  rwa [← eval_hasseDeriv_powerSubstitution (hk.trans_lt hm)]

/-- **The Frobenius-graph nonvanishing test, ordinary form.** Over an integral domain `R` of prime
characteristic `p`, for `q = p ^ e` with `0 < e` and an order bound `m < p`, if `F ≠ 0` has
`Z`-degree below `q` and `(powerSubstitution q F).natDegree < #S * (m + 1)`, then some ordinary
`Z`-jet `∂_Z^k F` with `k ≤ m` is nonzero at `(a, a ^ q)` for some `a ∈ S`. Both `0 < e` and
`m < p` are sharp. -/
theorem exists_nonzero_ordinary_jet_on_frobenius_graph {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} [Fact p.Prime] [CharP R p] {e : ℕ} (he : 0 < e) {F : MvPolynomial (Fin 2) R}
    (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e) {S : Finset R} {m : ℕ} (hm : m < p)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < #S * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m, eval ![a, a ^ p ^ e] ((pderiv 0)^[k] F) ≠ 0 := by
  have hpe : p ≤ p ^ e := Nat.le_self_pow he.ne' p
  obtain ⟨a, ha, k, hk, hne⟩ :=
    exists_nonzero_hasse_jet_on_frobenius_graph hF hZ (hm.trans_le hpe) hdeg
  exact ⟨a, ha, k, hk,
    mt (eval_iterate_pderiv_eq_zero_iff_of_lt_char 0 (hk.trans_lt hm) _ F).1 hne⟩

end FrobeniusGraphTest

/-! ### Examples and sharpness checks -/

/-- The bound `B` on the `Z`-degree cannot be dropped in `powerSubstitution_injOn`: `Z ^ 2` and `W`
both map to `X ^ 2` under `powerSubstitution 2`. -/
example : powerSubstitution (R := ℤ) 2 (X 0 ^ 2) = powerSubstitution 2 (X 1) := by
  simp

example : (X 0 ^ 2 : MvPolynomial (Fin 2) ℤ) ≠ X 1 := by
  intro h
  simpa [degreeOf_X] using congrArg (degreeOf 0) h

/-- At `e = 0` (`q = 1`), `iterate_derivative_powerSubstitution` fails on `F = X 1`:
`D(powerSubstitution 1 (X 1)) = D X = 1` whereas `∂_Z (X 1) = 0`. -/
example : Polynomial.derivative (powerSubstitution (R := ZMod 2) (2 ^ 0) (X 1)) = 1 ∧
    powerSubstitution (R := ZMod 2) (2 ^ 0) (pderiv 0 (X 1)) = 0 := by
  simp

/-- For `p = 2`, `e = 2` (`q = 4`) over `ZMod 2`, `hasseDeriv_powerSubstitution` covers the order
`k = 3` (`p ≤ k < q`), giving `D^[3](X 0 ^ 3 * X 1 ↦ X ^ 7) = X ^ 4`, whereas `(pderiv 0)^[3]`
vanishes identically in characteristic `2`. -/
example :
    Polynomial.hasseDeriv 3
      (powerSubstitution (2 ^ 2) (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
      Polynomial.X ^ 4 ∧
    (pderiv 0)^[3] (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2)) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  refine ⟨?_, iterate_pderiv_eq_zero_of_char_le (p := 2) (by decide) 0 (by decide) _⟩
  rw [hasseDeriv_powerSubstitution (p := 2) (e := 2) (by decide)]
  have hmon : (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2)) =
      monomial (single 0 3 + single 1 1) 1 := by
    rw [X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
  have hsub : (single 0 3 + single 1 1 - single 0 3 : Fin 2 →₀ ℕ) = single 1 1 := by
    ext i
    fin_cases i <;> simp
  rw [hmon, hasseDeriv_monomial, prod_single_index (by simp), hsub]
  simp [← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow]

/-- Composite characteristic breaks `hasseDeriv_powerSubstitution` even though ordinary derivatives
still commute: over `ZMod 4` with `B = 4` and `F = X 1`, `D(X ^ 4) = 0 = ∂_Z (X 1)` while
`D^[2](X ^ 4) = 2 * X ^ 2 ≠ 0`. -/
example :
    Polynomial.derivative (powerSubstitution (R := ZMod 4) 4 (X 1)) =
      powerSubstitution (R := ZMod 4) 4 (pderiv 0 (X 1)) ∧
    Polynomial.hasseDeriv 2 (powerSubstitution (R := ZMod 4) 4 (X 1)) ≠
      powerSubstitution (R := ZMod 4) 4 (hasseDeriv (single 0 2) (X 1)) := by
  refine ⟨derivative_powerSubstitution_of_natCast_eq_zero (by decide) _, ?_⟩
  have h0 : single (0 : Fin 2) 2 ≠ 0 := Finsupp.single_ne_zero.2 (by decide)
  have h1 : single (0 : Fin 2) 2 ≠ single 1 1 := fun h ↦ by
    simpa using congrArg (fun f : Fin 2 →₀ ℕ ↦ f 0) h
  rw [powerSubstitution_X_one, ← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow,
    one_mul, one_pow, Polynomial.hasseDeriv_monomial, hasseDeriv_X, ite_eq_right h0,
    ite_eq_right h1, map_zero]
  intro h
  have hc := congrArg (fun f : Polynomial (ZMod 4) ↦ f.coeff 2) h
  simp only [Polynomial.coeff_monomial_same, mul_one, Polynomial.coeff_zero] at hc
  exact absurd hc (by decide)

/-- Over `ZMod 2` with `q = 2` and `S = {0, 1}`, `F = X 0 + X 1` vanishes at every Frobenius-graph
point `(a, a ^ 2)` (at `m = 0` the bound `natDegree (X + X ^ 2) = 2 < 2 * 1` fails), while at
`m = 1` the bound `2 < 2 * 2` holds and the first `Z`-jet is `1`. -/
example :
    (∀ a : ZMod 2, eval ![a, a ^ 2] (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod 2)) = 0) ∧
    ∀ a : ZMod 2, eval ![a, a ^ 2] (pderiv 0 (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 1 := by
  refine ⟨fun a ↦ ?_, fun a ↦ by simp⟩
  simp only [map_add, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  fin_cases a <;> decide

/-- Sharpness of `F.degreeOf 0 < p ^ e` in `exists_nonzero_hasse_jet_on_frobenius_graph`: over
`ZMod 2` with `p = 2`, `e = 1`, `S = {0, 1}`, and `m = 1 < 2`, `F = X 0 ^ 2 + X 1` is nonzero and
`powerSubstitution 2 F = 0` has `natDegree = 0 < #S * (m + 1)`, yet every Hasse `Z`-jet of order
`k ≤ 1` vanishes at `(a, a ^ 2)` for all `a : ZMod 2`. -/
example :
    (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) (ZMod 2)) ≠ 0 ∧
    (powerSubstitution 2 (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) (ZMod 2))).natDegree = 0 ∧
    ∀ (a : ZMod 2) (k : ℕ), k ≤ 1 →
      eval ![a, a ^ 2]
        (hasseDeriv (single 0 k) (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  have hps : powerSubstitution 2 (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) (ZMod 2)) = 0 := by
    simp [CharTwo.add_self_eq_zero]
  refine ⟨?_, by simp [hps], fun a k hk ↦ ?_⟩
  · intro h
    have hc := congrArg (eval ![0, 1]) h
    simp at hc
  · interval_cases k
    · simp only [single_zero, hasseDeriv_zero, LinearMap.id_apply, map_add, map_pow, eval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      fin_cases a <;> decide
    · have h2 : (2 : ZMod 2) = 0 := rfl
      exact (eval_iterate_pderiv_eq_zero_iff 0 (k := 1) (by simp) _ _).1 (by simp [h2])

/-- Sharpness of `0 < e` (and of `m < p ^ e` in the Hasse form): at `p = 2`, `e = 0` (`q = 1`),
`F = X 1` over `ZMod 2`, `S = {0}`, and `m = 1 < p`, `F` is nonzero of `Z`-degree `0 < 1` and
`natDegree X = 1 < #S * (m + 1)`, yet both `F` and `∂_Z F` vanish at `(0, 0)`. -/
example :
    (X 1 : MvPolynomial (Fin 2) (ZMod 2)) ≠ 0 ∧
    (X 1 : MvPolynomial (Fin 2) (ZMod 2)).degreeOf 0 < 2 ^ 0 ∧
    (powerSubstitution (2 ^ 0) (X 1 : MvPolynomial (Fin 2) (ZMod 2))).natDegree <
      #({0} : Finset (ZMod 2)) * (1 + 1) ∧
    ∀ k ≤ 1,
      eval ![0, (0 : ZMod 2) ^ (2 ^ 0)]
        ((pderiv 0)^[k] (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  refine ⟨X_ne_zero 1, by simp [degreeOf_X], by simp, fun k hk ↦ ?_⟩
  interval_cases k <;> simp

/-- Sharpness of `m < p` in `exists_nonzero_ordinary_jet_on_frobenius_graph`: at `p = 2`, `e = 2`
(`q = 4`), `F = X 0 ^ 2` over `ZMod 2`, `S = {0}`, and `m = 2 < q`, the Hasse jet of order `2` at
`(0, 0)` is `1` while every ordinary `Z`-jet of order `k ≤ 2` vanishes at `(0, 0)`. -/
example :
    eval ![0, (0 : ZMod 2) ^ (2 ^ 2)]
      (hasseDeriv (single 0 2) (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 2))) = 1 ∧
    ∀ k ≤ 2,
      eval ![0, (0 : ZMod 2) ^ (2 ^ 2)]
        ((pderiv 0)^[k] (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  refine ⟨by simp [X_pow_eq_monomial], fun k hk ↦ ?_⟩
  interval_cases k
  · simp
  · simp
  · rw [iterate_pderiv_eq_zero_of_char_le (p := 2) (by decide) 0 le_rfl, map_zero]

end MvPolynomial
