/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic
public import TauCeti.RingTheory.MvPolynomial.Kronecker
public import TauCeti.RingTheory.MvPolynomial.RestrictSupport

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.Data.ZMod.Basic
import TauCeti.Algebra.Polynomial.Expand
import TauCeti.Algebra.Polynomial.HasseDeriv
import TauCeti.Data.Finsupp.Weight

/-!
# The power substitution `F ↦ F(X, X ^ B)` and jets on the Frobenius graph

For `B : ℕ`, the *power substitution* `MvPolynomial.powerSubstitution B` sends a bivariate
polynomial `F(Z, W)` (variable `0` is `Z`, variable `1` is `W`) to the univariate polynomial
`F(X, X ^ B)`. It is the Kronecker substitution of `TauCeti.RingTheory.MvPolynomial.Kronecker`
for the weight `![1, B]`, which sends the exponent `μ` to `μ 0 + B * μ 1`. On exponents with
`μ 0 < B` this map is injective (uniqueness of quotient and remainder on division by `B`), so the
substitution is injective on polynomials of `Z`-degree below `B`.

When `B = p ^ e` is a power of the characteristic `p`, differentiating `F(X, X ^ (p ^ e))`
suppresses variation in `W`:
* For `0 < e`, `(p ^ e : R) = 0` annihilates `D(X ^ (p ^ e))`, so ordinary differentiation commutes
  with `powerSubstitution (p ^ e)` at *every* order `k`
  (`MvPolynomial.iterate_derivative_powerSubstitution`). At `e = 0` (`p ^ 0 = 1`) the substitution
  is `W ↦ X` and this fails.
* In exponential characteristic `p`, for *every* `e : ℕ` and every order `k < p ^ e`, Hasse
  differentiation commutes with `powerSubstitution (p ^ e)`:
  `D^[k] (F(X, X ^ (p ^ e))) = (∂_Z^[k] F)(X, X ^ (p ^ e))`
  (`MvPolynomial.hasseDeriv_powerSubstitution`), proved monomial-by-monomial from
  `Polynomial.hasseDeriv_expand_mul`. Unlike the ordinary derivative, this controls orders in the
  range `p ≤ k < p ^ e` where `k !` vanishes in `R`; at `k = p ^ e` it fails on `F = W`.

Combining injectivity below `Z`-degree `p ^ e`, the Hasse derivative identity for `k ≤ m < p ^ e`,
and the univariate root-multiplicity bound
`Polynomial.exists_eval_hasseDeriv_ne_zero_of_natDegree_lt` yields the Frobenius-graph nonvanishing
test (`MvPolynomial.exists_nonzero_hasse_jet_on_frobenius_graph`) and, when `0 < e` and `m < p` so
that `k !` is a unit, its ordinary-derivative counterpart
(`MvPolynomial.exists_nonzero_ordinary_jet_on_frobenius_graph`).

## Main results

* `MvPolynomial.coeff_powerSubstitution`: for `F` of `Z`-degree below `B` and `μ 0 < B`, the
  coefficient of `X ^ (μ 0 + B * μ 1)` in `F(X, X ^ B)` is the coefficient of `Z ^ μ 0 W ^ μ 1`.
* `MvPolynomial.powerSubstitution_injOn`, `MvPolynomial.powerSubstitution_eq_zero_iff`: the
  substitution is injective (hence has trivial kernel) on polynomials of `Z`-degree below `B`, for
  every `B` (at `B = 0` this set is empty).
* `MvPolynomial.support_powerSubstitution_subset`,
  `MvPolynomial.natDegree_powerSubstitution_le`: the exponents of `F(X, X ^ B)` are among the
  weights `μ 0 + B * μ 1` of the exponents of `F`, so its degree is at most
  `degreeOf 0 F + B * degreeOf 1 F`.
* `MvPolynomial.powerSubstitution_map`: naturality under a ring map of the coefficients.
* `MvPolynomial.aeval_powerSubstitution`, `MvPolynomial.eval_powerSubstitution`: `F(X, X ^ B)`
  evaluated at `a` is `F(a, a ^ B)`.
* `MvPolynomial.derivative_powerSubstitution`, `MvPolynomial.iterate_derivative_powerSubstitution`:
  in characteristic `p` with `0 < e`, `D^k (F(X, X ^ (p ^ e))) = (∂_Z^k F)(X, X ^ (p ^ e))` for
  every `k`.
* `MvPolynomial.hasseDeriv_powerSubstitution`, `MvPolynomial.eval_hasseDeriv_powerSubstitution`:
  in exponential characteristic `p`, for every `e : ℕ` and `k < p ^ e`,
  `D^[k] (F(X, X ^ (p ^ e))) = (∂_Z^[k] F)(X, X ^ (p ^ e))`.
* `MvPolynomial.exists_nonzero_hasse_jet_on_frobenius_graph`,
  `MvPolynomial.exists_nonzero_ordinary_jet_on_frobenius_graph`: over an integral domain of
  exponential characteristic `p`, a nonzero bivariate polynomial `F` with `degreeOf 0 F < p ^ e`
  and `(powerSubstitution (p ^ e) F).natDegree < S.card * (m + 1)` has a nonzero `Z`-jet of order
  `≤ m` on the Frobenius graph `{(a, a ^ (p ^ e)) | a ∈ S}` (for `m < p ^ e` in Hasse form, and for
  `0 < e` and `m < p` in ordinary form).

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6, Lemmas 11.16–11.17, pp. 283–284, for the multiplicity bound and Hasse derivatives of
  `h(X, X ^ q)` for `k < q`.
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

/-- For `F` of `Z`-degree below `B`, `F(X, X ^ B) = 0` if and only if `F = 0`. -/
theorem powerSubstitution_eq_zero_iff {B : ℕ} {F : MvPolynomial (Fin 2) R}
    (hF : F.degreeOf 0 < B) : powerSubstitution B F = 0 ↔ F = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rcases B.eq_zero_or_pos with rfl | hB
  · exact (Nat.not_lt_zero _ hF).elim
  · exact powerSubstitution_injOn B hF (by simpa using hB) (by simpa using h)

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

/-- Evaluating `F(X, X ^ B)` at `a` in an `R`-algebra `S` gives `F(a, a ^ B)`. -/
@[simp]
theorem aeval_powerSubstitution [Algebra R S] (B : ℕ) (a : S) (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (powerSubstitution B F) = aeval ![a, a ^ B] F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [powerSubstitution]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp => fin_cases s <;> simp [hp]

/-- **Evaluation formula.** `F(X, X ^ B)` evaluated at `a` is `F(a, a ^ B)`. -/
@[simp]
theorem eval_powerSubstitution (B : ℕ) (a : R) (F : MvPolynomial (Fin 2) R) :
    (powerSubstitution B F).eval a = eval ![a, a ^ B] F := by
  induction F using MvPolynomial.induction_on' with
  | monomial μ c => simp [eval_monomial, Finsupp.prod_fintype, pow_add, pow_mul]
  | add F G hF hG => simp [hF, hG]

/-- When `(B : R) = 0`, differentiating `F(X, X ^ B)` in `X` suppresses the `W`-term
`B · X ^ (B - 1) = 0` and computes `(∂_Z F)(X, X ^ B)`. -/
theorem derivative_powerSubstitution_of_natCast_eq_zero {B : ℕ} (hB : (B : R) = 0)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative (powerSubstitution B F) = powerSubstitution B (pderiv 0 F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [powerSubstitution]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp => fin_cases s <;> simp [hp, Polynomial.derivative_X_pow, hB] <;> ring

/-- When `(B : R) = 0`, iterated ordinary differentiation in `X` commutes with
`powerSubstitution B` at every order `k`. -/
theorem iterate_derivative_powerSubstitution_of_natCast_eq_zero {B : ℕ} (hB : (B : R) = 0)
    (k : ℕ) (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative^[k] (powerSubstitution B F) =
      powerSubstitution B ((pderiv 0)^[k] F) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, derivative_powerSubstitution_of_natCast_eq_zero hB, ih,
      ← Function.iterate_succ_apply]

section CharP

variable {p : ℕ} [CharP R p]

/-- In characteristic `p` and for `0 < e`, differentiating `F(X, X ^ (p ^ e))` in `X` computes
`(∂_Z F)(X, X ^ (p ^ e))`. -/
theorem derivative_powerSubstitution {e : ℕ} (he : 0 < e) (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) (pderiv 0 F) :=
  derivative_powerSubstitution_of_natCast_eq_zero
    (by rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne']) F

/-- In characteristic `p` and for `0 < e`, iterated ordinary differentiation commutes with the
Frobenius substitution `powerSubstitution (p ^ e)` at every order `k`. -/
theorem iterate_derivative_powerSubstitution {e : ℕ} (he : 0 < e) (k : ℕ)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative^[k] (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) ((pderiv 0)^[k] F) :=
  iterate_derivative_powerSubstitution_of_natCast_eq_zero
    (by rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne']) k F

/-- Evaluating `D^k (F(X, X ^ (p ^ e)))` at `a` in an `R`-algebra `S` (for `0 < e` in
characteristic `p`) gives `(∂_Z^k F)(a, a ^ (p ^ e))`. -/
theorem aeval_iterate_derivative_powerSubstitution [Algebra R S] {e : ℕ} (he : 0 < e) (k : ℕ)
    (a : S) (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (Polynomial.derivative^[k] (powerSubstitution (p ^ e) F)) =
      aeval ![a, a ^ p ^ e] ((pderiv 0)^[k] F) := by
  rw [iterate_derivative_powerSubstitution he, aeval_powerSubstitution]

/-- Evaluating `D^k (F(X, X ^ (p ^ e)))` at `a` (for `0 < e` in characteristic `p`) gives
`(∂_Z^k F)(a, a ^ (p ^ e))`. -/
theorem eval_iterate_derivative_powerSubstitution {e : ℕ} (he : 0 < e) (k : ℕ) (a : R)
    (F : MvPolynomial (Fin 2) R) :
    (Polynomial.derivative^[k] (powerSubstitution (p ^ e) F)).eval a =
      eval ![a, a ^ p ^ e] ((pderiv 0)^[k] F) := by
  rw [iterate_derivative_powerSubstitution he, eval_powerSubstitution]

end CharP

section ExpChar

variable {p : ℕ} [ExpChar R p]

/-- **Hasse derivatives commute with the Frobenius substitution below `p ^ e`**
(Iwaniec–Kowalski, Lemma 11.17). Over any commutative semiring of exponential characteristic `p`,
for every `e : ℕ` and every `k < p ^ e`,
`D^[k] (F(X, X ^ (p ^ e))) = (∂_Z^[k] F)(X, X ^ (p ^ e))`. At `e = 0` only `k = 0` is admitted and
the identity is trivial; at `k = p ^ e` it fails on `F = W`. -/
theorem hasseDeriv_powerSubstitution {e k : ℕ} (hk : k < p ^ e) (F : MvPolynomial (Fin 2) R) :
    Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) (hasseDeriv (single 0 k) F) := by
  induction F using MvPolynomial.induction_on' with
  | add F G hF hG => simp [hF, hG]
  | monomial μ c =>
    have hmon : powerSubstitution (p ^ e) (monomial μ c) =
        Polynomial.expand R (p ^ e) (Polynomial.monomial (μ 1) 1) *
          Polynomial.monomial (μ 0) c := by
      rw [powerSubstitution_monomial, Polynomial.expand_monomial,
        Polynomial.monomial_mul_monomial, one_mul, mul_comm, add_comm]
    rw [hmon, Polynomial.hasseDeriv_expand_mul hk, Polynomial.expand_monomial,
      Polynomial.hasseDeriv_monomial, Polynomial.monomial_mul_monomial, one_mul,
      hasseDeriv_monomial, prod_single_index (by simp), powerSubstitution_monomial]
    simp [add_comm, mul_comm]

/-- Evaluating `D^[k] (F(X, X ^ (p ^ e)))` at `a` in an `R`-algebra `S` (for `k < p ^ e` in
exponential characteristic `p`) gives `(∂_Z^[k] F)(a, a ^ (p ^ e))`. -/
theorem aeval_hasseDeriv_powerSubstitution [Algebra R S] {e k : ℕ} (hk : k < p ^ e) (a : S)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F)) =
      aeval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) := by
  rw [hasseDeriv_powerSubstitution hk, aeval_powerSubstitution]

/-- Evaluating `D^[k] (F(X, X ^ (p ^ e)))` at `a` (for `k < p ^ e` in exponential characteristic
`p`) gives `(∂_Z^[k] F)(a, a ^ (p ^ e))`. -/
theorem eval_hasseDeriv_powerSubstitution {e k : ℕ} (hk : k < p ^ e) (a : R)
    (F : MvPolynomial (Fin 2) R) :
    (Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F)).eval a =
      eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) := by
  rw [hasseDeriv_powerSubstitution hk, eval_powerSubstitution]

end ExpChar

end CommSemiring

section FrobeniusTest

variable {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [ExpChar R p]

/-- **The Frobenius-graph nonvanishing test, Hasse form** (Iwaniec–Kowalski, Lemmas 11.16–11.17).
Over an integral domain `R` of exponential characteristic `p`, for every `e : ℕ`, if a nonzero
bivariate polynomial `F` has `Z`-degree below `p ^ e` and its Frobenius substitution
`F(X, X ^ (p ^ e))` has degree strictly below `S.card * (m + 1)` with `m < p ^ e`, then `F` has a
nonzero Hasse `Z`-jet of order at most `m` at some Frobenius-graph point `(a, a ^ (p ^ e))` with
`a ∈ S`. -/
theorem exists_nonzero_hasse_jet_on_frobenius_graph {e : ℕ} {F : MvPolynomial (Fin 2) R}
    (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e) {S : Finset R} {m : ℕ} (hm : m < p ^ e)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < S.card * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m, eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) ≠ 0 := by
  have hf : powerSubstitution (p ^ e) F ≠ 0 := (powerSubstitution_eq_zero_iff hZ).not.mpr hF
  obtain ⟨a, ha, k, hk, hne⟩ :=
    Polynomial.exists_eval_hasseDeriv_ne_zero_of_natDegree_lt hf hdeg
  rw [eval_hasseDeriv_powerSubstitution (hk.trans_lt hm)] at hne
  exact ⟨a, ha, k, hk, hne⟩

/-- **The Frobenius-graph nonvanishing test, ordinary form.** Over an integral domain `R` of
exponential characteristic `p`, for `0 < e` and `m < p`, if a nonzero bivariate polynomial `F` has
`Z`-degree below `p ^ e` and `(powerSubstitution (p ^ e) F).natDegree < S.card * (m + 1)`, then `F`
has a nonzero ordinary `Z`-jet `(∂_Z^k F)(a, a ^ (p ^ e))` of order `k ≤ m` at some `a ∈ S`. -/
theorem exists_nonzero_ordinary_jet_on_frobenius_graph {e : ℕ} (he : 0 < e)
    {F : MvPolynomial (Fin 2) R} (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e)
    {S : Finset R} {m : ℕ} (hm : m < p)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < S.card * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m, eval ![a, a ^ p ^ e] ((pderiv (0 : Fin 2))^[k] F) ≠ 0 := by
  have hm' : m < p ^ e := hm.trans_le (Nat.le_self_pow he.ne' p)
  obtain ⟨a, ha, k, hk, hne⟩ := exists_nonzero_hasse_jet_on_frobenius_graph hF hZ hm' hdeg
  have hunit : IsUnit (k.factorial : R) := by
    rcases ‹ExpChar R p› with _ | ⟨hp⟩
    · obtain rfl : k = 0 := by omega
      simp
    · have : Fact p.Prime := ⟨hp⟩
      exact (IsUnit.natCast_factorial_iff_of_charP p).mpr (hk.trans_lt hm)
  exact ⟨a, ha, k, hk,
    (eval_iterate_pderiv_eq_zero_iff_eval_hasseDeriv_eq_zero hunit 0 _ F).not.mpr hne⟩

end FrobeniusTest

/-! ### Examples and sharpness -/

/-- The bound `B` on the `Z`-degree cannot be dropped: `Z ^ 2` and `W` both map to `X ^ 2` (and over
`ZMod 2`, `Z ^ 2 + W` is nonzero yet maps to `0` under `powerSubstitution 2`). -/
example : powerSubstitution (R := ℤ) 2 (X 0 ^ 2) = powerSubstitution 2 (X 1) := by
  simp

example : (X 0 ^ 2 : MvPolynomial (Fin 2) ℤ) ≠ X 1 := by
  intro h
  simpa [degreeOf_X] using congrArg (degreeOf 0) h

example : (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) (ZMod 2)) ≠ 0 ∧
    powerSubstitution 2 (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) (ZMod 2)) = 0 := by
  refine ⟨fun h ↦ ?_, by simp [CharTwo.add_self_eq_zero]⟩
  simpa using congrArg (eval ![(0 : ZMod 2), 1]) h

/-- Over `ZMod 2` with `q = 2 ^ 2 = 4`, `hasseDeriv_powerSubstitution` holds at order `3`
(`p ≤ 3 < q`), sending `Z ^ 3 * W` to `X ^ 4` on both sides. -/
example :
    Polynomial.hasseDeriv 3
      (powerSubstitution (2 ^ 2) (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
      powerSubstitution (2 ^ 2) (hasseDeriv (single 0 3) (X 0 ^ 3 * X 1)) ∧
    powerSubstitution (2 ^ 2)
      (hasseDeriv (single 0 3) (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
      Polynomial.X ^ 4 := by
  refine ⟨hasseDeriv_powerSubstitution (p := 2) (e := 2) (by decide) _, ?_⟩
  have hmon : (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2)) =
      monomial (single 0 3 + single 1 1) 1 := by
    rw [X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
  have hsub : (single 0 3 + single 1 1 - single 0 3 : Fin 2 →₀ ℕ) = single 1 1 := by
    ext j
    fin_cases j <;> simp
  rw [hmon, hasseDeriv_monomial, prod_single_index (by simp), hsub]
  simp [Polynomial.monomial_one_right_eq_X_pow]

/-- The bound `k < p ^ e` in `hasseDeriv_powerSubstitution` is sharp: at `k = p ^ e = 2` over
`ZMod 2` with `F = W`, `D^[2] (X ^ 2) = 1` whereas `∂_Z^[2] W = 0`. -/
example :
    Polynomial.hasseDeriv 2 (powerSubstitution (2 ^ 1) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 1 ∧
    powerSubstitution (2 ^ 1) (hasseDeriv (single 0 2) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
      0 := by
  have hne : (single 0 2 : Fin 2 →₀ ℕ) ≠ single 1 1 := fun h ↦ by simpa using congrArg (· 0) h
  simp [← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow, hne]

/-- The hypothesis `0 < e` in `derivative_powerSubstitution` and
`exists_nonzero_ordinary_jet_on_frobenius_graph` cannot be dropped: at `e = 0` (`p ^ 0 = 1`) over
`ZMod 2` with `F = W`, `D (powerSubstitution 1 W) = 1` whereas both `W` and `∂_Z W = 0` vanish at
`(0, 0)`. By contrast, `exists_nonzero_hasse_jet_on_frobenius_graph` holds at `e = 0` (`m = 0`) on
`S = {0, 1}`. -/
example :
    Polynomial.derivative (powerSubstitution (2 ^ 0) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 1 ∧
    (∀ k ≤ 1, eval ![0, (0 : ZMod 2) ^ 2 ^ 0]
      ((pderiv (0 : Fin 2))^[k] (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0) ∧
    (∃ a ∈ ({0, 1} : Finset (ZMod 2)), ∃ k ≤ 0,
      eval ![a, a ^ 2 ^ 0]
        (hasseDeriv (single 0 k) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) ≠ 0) := by
  refine ⟨by simp, fun k hk ↦ ?_, ⟨1, by simp, 0, le_rfl, by simp⟩⟩
  interval_cases k <;> simp

/-- For `p ≤ m < p ^ e` (`p = 2, e = 2, q = 4, m = 2`) on `F = Z ^ 2` and `S = {0}` over `ZMod 2`,
the Hasse nonvanishing test applies (`∂_Z^[2] (Z ^ 2)(0, 0) = 1 ≠ 0`), while every ordinary `Z`-jet
of order `k ≤ 2` vanishes at `(0, 0)`. -/
example :
    (∃ a ∈ ({0} : Finset (ZMod 2)), ∃ k ≤ 2,
      eval ![a, a ^ 2 ^ 2]
        (hasseDeriv (single 0 k) (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 2))) ≠ 0) ∧
    (∀ k ≤ 2, eval ![(0 : ZMod 2), (0 : ZMod 2) ^ 2 ^ 2]
      ((pderiv (0 : Fin 2))^[k] (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 2))) = 0) := by
  have hF : (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 2)) ≠ 0 := fun h ↦ by
    simpa using congrArg (eval ![(1 : ZMod 2), 0]) h
  have hZ : (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 2)).degreeOf 0 < 2 ^ 2 := by
    rw [degreeOf_lt_iff (by decide)]
    intro μ hμ
    rw [X_pow_eq_monomial, support_monomial] at hμ
    split_ifs at hμ with h0 <;> simp_all
  have hdeg : (powerSubstitution (2 ^ 2)
      (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 2))).natDegree <
      ({0} : Finset (ZMod 2)).card * (2 + 1) := by
    simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨exists_nonzero_hasse_jet_on_frobenius_graph (p := 2) (e := 2) hF hZ (by decide) hdeg,
    fun k hk ↦ ?_⟩
  rw [eval_iterate_pderiv_eq_factorial_mul]
  interval_cases k
  · simp
  · simp [X_pow_eq_monomial, eval_monomial]
  · simp [Nat.factorial, CharTwo.two_eq_zero]

/-- Both Frobenius-graph nonvanishing tests instantiate directly over any field `K` of prime
characteristic `p` without manual `ExpChar` conversion. -/
example {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] {e : ℕ} (he : 0 < e)
    {F : MvPolynomial (Fin 2) K} (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e)
    {S : Finset K} {m : ℕ} (hm : m < p)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < S.card * (m + 1)) :
    (∃ a ∈ S, ∃ k ≤ m, eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) ≠ 0) ∧
    (∃ a ∈ S, ∃ k ≤ m, eval ![a, a ^ p ^ e] ((pderiv (0 : Fin 2))^[k] F) ≠ 0) :=
  ⟨exists_nonzero_hasse_jet_on_frobenius_graph hF hZ (hm.trans_le (Nat.le_self_pow he.ne' p)) hdeg,
    exists_nonzero_ordinary_jet_on_frobenius_graph he hF hZ hm hdeg⟩

end MvPolynomial
