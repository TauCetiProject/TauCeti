/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic
public import TauCeti.RingTheory.MvPolynomial.PowerSubstitution

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Polynomial.Expand
import TauCeti.Algebra.Polynomial.HasseDeriv
import TauCeti.FieldTheory.Finite.Four

/-!
# Derivatives of the Frobenius power substitution and the Frobenius-graph nonvanishing test

For a bivariate polynomial `F(Z, W)` (`0 = Z`, `1 = W`), the power substitution
`MvPolynomial.powerSubstitution B` sends `F` to the univariate polynomial `F(X, X ^ B)`. When `B`
vanishes in the coefficient ring — in particular for every positive power `q = p ^ e` (`0 < e`) in
characteristic `p` — `X ^ B` has zero ordinary derivative, so `X ^ B` behaves as a constant under
`Polynomial.derivative` and ordinary derivatives of every order commute with `powerSubstitution B`:
`derivative^[k] (F(X, X ^ q)) = (∂_Z^k F)(X, X ^ q)`.

For Hasse derivatives in exponential characteristic `p` and for every `q = p ^ e` (`e ≥ 0`), Hasse
derivatives of order `k < q` are linear over polynomials in `X ^ q`
(`Polynomial.hasseDeriv_expand_mul`), so Hasse derivatives of order `k < q` also commute with
`powerSubstitution q`: `hasseDeriv k (F(X, X ^ q)) = (∂_Z^[k] F)(X, X ^ q)`. Unlike the ordinary
identity, this holds at `e = 0` (where only `k = 0` satisfies `k < 1`) and controls orders
`p ≤ k < q` where iterated ordinary derivatives collapse; at `k = q` it fails
(`hasseDeriv q (X ^ q) = 1` whereas `∂_Z^[q] W = 0`).

Combining injectivity of `powerSubstitution q` below `Z`-degree `q`
(`MvPolynomial.powerSubstitution_ne_zero`), the univariate Hasse-jet nonvanishing bound
(`Polynomial.exists_eval_hasseDeriv_ne_zero_of_natDegree_lt`), and the Hasse commutation identity
yields the **Frobenius-graph nonvanishing test** in Hasse form: over an integral domain `R` of
exponential characteristic `p`, if `F ≠ 0` has `Z`-degree `< q`, `m < q`, and
`(F(X, X ^ q)).natDegree < #S * (m + 1)` for a finite set `S ⊆ R`, then some Hasse `Z`-jet
`∂_Z^[k] F` of order `k ≤ m` is nonzero at `(a, a ^ q)` for some `a ∈ S`. When `R` has prime
characteristic `p`, `0 < e`, and `m < p`, every factorial `k!` for `k ≤ m` is a unit in `R`, giving
the ordinary-derivative form for `(∂_Z)^[k] F`.

## Main results

* `MvPolynomial.derivative_powerSubstitution_of_natCast_eq_zero`,
  `MvPolynomial.iterate_derivative_powerSubstitution_of_natCast_eq_zero`: when `(B : R) = 0`,
  ordinary univariate derivatives of `powerSubstitution B F` match `powerSubstitution B` applied to
  partial `Z`-derivatives `(pderiv 0)^[k] F`.
* `MvPolynomial.derivative_powerSubstitution`,
  `MvPolynomial.iterate_derivative_powerSubstitution`,
  `MvPolynomial.eval_iterate_derivative_powerSubstitution`,
  `MvPolynomial.aeval_iterate_derivative_powerSubstitution`: specialization to `B = p ^ e` with
  `0 < e` in characteristic `p`, together with evaluated forms in `R` and in any `R`-algebra.
* `MvPolynomial.hasseDeriv_powerSubstitution`,
  `MvPolynomial.eval_hasseDeriv_powerSubstitution`,
  `MvPolynomial.aeval_hasseDeriv_powerSubstitution`: in exponential characteristic `p`, Hasse
  derivatives of order `k < p ^ e` commute with `powerSubstitution (p ^ e)`, for all `e ≥ 0`.
* `MvPolynomial.exists_eval_hasseDeriv_single_ne_zero_of_natDegree_powerSubstitution_lt`: the
  Frobenius-graph nonvanishing test in Hasse form, valid for every `e ≥ 0` and `m < p ^ e` over any
  integral domain of exponential characteristic `p`.
* `MvPolynomial.exists_eval_iterate_pderiv_ne_zero_of_natDegree_powerSubstitution_lt`: the
  Frobenius-graph nonvanishing test in ordinary-derivative form, valid for `0 < e` and `m < p` over
  any integral domain of prime characteristic `p`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6, Lemmas 11.16 and 11.17, pp. 283–284.
-/

public section

namespace MvPolynomial

open Finset Finsupp

section Ordinary

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- When `(B : R) = 0`, differentiating `F(X, X ^ B)` with respect to `X` gives `(∂_Z F)(X, X ^ B)`,
since `X ^ B` has zero derivative. -/
theorem derivative_powerSubstitution_of_natCast_eq_zero {B : ℕ} (hB : (B : R) = 0)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative (powerSubstitution B F) = powerSubstitution B (pderiv 0 F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add G H hG hH => simp [hG, hH]
  | mul_X G s hG =>
    fin_cases s
    · simp only [Fin.zero_eta, map_mul, powerSubstitution_X_zero, Polynomial.derivative_mul,
        Polynomial.derivative_X, mul_one, Derivation.leibniz, pderiv_X_self, smul_eq_mul, map_add,
        hG]
      ring
    · have hXB : Polynomial.derivative (Polynomial.X ^ B : Polynomial R) = 0 := by
        rw [Polynomial.derivative_X_pow, hB, map_zero, zero_mul]
      have hpX : pderiv (0 : Fin 2) (X 1 : MvPolynomial (Fin 2) R) = 0 :=
        pderiv_X_of_ne (by decide)
      simp only [Fin.mk_one, map_mul, powerSubstitution_X_one, Polynomial.derivative_mul, hXB,
        mul_zero, zero_add, Derivation.leibniz, hpX, smul_eq_mul, hG]
      ring

/-- When `(B : R) = 0`, iterated ordinary derivatives of every order commute with
`powerSubstitution B`: `D^k (F(X, X ^ B)) = (∂_Z^k F)(X, X ^ B)`. -/
theorem iterate_derivative_powerSubstitution_of_natCast_eq_zero {B : ℕ} (hB : (B : R) = 0)
    (k : ℕ) (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative^[k] (powerSubstitution B F) =
      powerSubstitution B ((pderiv (0 : Fin 2))^[k] F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      derivative_powerSubstitution_of_natCast_eq_zero hB]

/-- In characteristic `p` and for `q = p ^ e` with `0 < e`, differentiating `F(X, X ^ q)` gives
`(∂_Z F)(X, X ^ q)`. -/
theorem derivative_powerSubstitution {p : ℕ} [CharP R p] {e : ℕ} (he : 0 < e)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) (pderiv 0 F) :=
  derivative_powerSubstitution_of_natCast_eq_zero
    (by rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne']) F

/-- In characteristic `p` and for `q = p ^ e` with `0 < e`, ordinary derivatives of every order
commute with the Frobenius power substitution: `D^k (F(X, X ^ q)) = (∂_Z^k F)(X, X ^ q)`. -/
theorem iterate_derivative_powerSubstitution {p : ℕ} [CharP R p] {e : ℕ} (he : 0 < e)
    (k : ℕ) (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative^[k] (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) ((pderiv (0 : Fin 2))^[k] F) :=
  iterate_derivative_powerSubstitution_of_natCast_eq_zero
    (by rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne']) k F

/-- Evaluating the `k`-th ordinary derivative of `F(X, X ^ (p ^ e))` (`0 < e`) at `a : R` gives the
`k`-th partial `Z`-derivative of `F` at the Frobenius-graph point `(a, a ^ (p ^ e))`. -/
theorem eval_iterate_derivative_powerSubstitution {p : ℕ} [CharP R p] {e : ℕ} (he : 0 < e)
    (k : ℕ) (a : R) (F : MvPolynomial (Fin 2) R) :
    (Polynomial.derivative^[k] (powerSubstitution (p ^ e) F)).eval a =
      eval ![a, a ^ p ^ e] ((pderiv (0 : Fin 2))^[k] F) := by
  rw [iterate_derivative_powerSubstitution he, eval_powerSubstitution]

/-- Evaluating the `k`-th ordinary derivative of `F(X, X ^ (p ^ e))` (`0 < e`) at `a : S` in any
`R`-algebra `S` gives the `k`-th partial `Z`-derivative of `F` at `(a, a ^ (p ^ e))`. -/
theorem aeval_iterate_derivative_powerSubstitution {p : ℕ} [CharP R p] {e : ℕ} (he : 0 < e)
    (k : ℕ) (a : S) (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (Polynomial.derivative^[k] (powerSubstitution (p ^ e) F)) =
      aeval ![a, a ^ p ^ e] ((pderiv (0 : Fin 2))^[k] F) := by
  rw [iterate_derivative_powerSubstitution he, aeval_powerSubstitution]

end Ordinary

section Hasse

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] {p : ℕ} [ExpChar R p]

/-- In exponential characteristic `p` and for every `q = p ^ e` (`e ≥ 0`), Hasse derivatives of
order `k < q` commute with the Frobenius power substitution:
`D^[k] (F(X, X ^ q)) = (∂_Z^[k] F)(X, X ^ q)`. -/
theorem hasseDeriv_powerSubstitution {e k : ℕ} (hk : k < p ^ e) (F : MvPolynomial (Fin 2) R) :
    Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) (hasseDeriv (single 0 k) F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial μ c =>
    have hexp : Polynomial.expand R (p ^ e) (Polynomial.X ^ μ 1) =
        (Polynomial.X : Polynomial R) ^ (p ^ e * μ 1) := by
      rw [map_pow, Polynomial.expand_X, pow_mul]
    rw [powerSubstitution_monomial, ← Polynomial.X_pow_mul_monomial, ← hexp,
      Polynomial.hasseDeriv_expand_mul hk, hexp, Polynomial.hasseDeriv_monomial,
      Polynomial.X_pow_mul_monomial, hasseDeriv_monomial, powerSubstitution_monomial]
    simp [prod_single_index]
  | add G H hG hH => simp [hG, hH]

/-- Evaluating the `k`-th Hasse derivative (`k < p ^ e`) of `F(X, X ^ (p ^ e))` at `a : R` gives
the `k`-th Hasse `Z`-jet of `F` at the Frobenius-graph point `(a, a ^ (p ^ e))`. -/
theorem eval_hasseDeriv_powerSubstitution {e k : ℕ} (hk : k < p ^ e) (a : R)
    (F : MvPolynomial (Fin 2) R) :
    (Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F)).eval a =
      eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) := by
  rw [hasseDeriv_powerSubstitution hk, eval_powerSubstitution]

/-- Evaluating the `k`-th Hasse derivative (`k < p ^ e`) of `F(X, X ^ (p ^ e))` at `a : S` in any
`R`-algebra `S` gives the `k`-th Hasse `Z`-jet of `F` at `(a, a ^ (p ^ e))`. -/
theorem aeval_hasseDeriv_powerSubstitution {e k : ℕ} (hk : k < p ^ e) (a : S)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F)) =
      aeval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) := by
  rw [hasseDeriv_powerSubstitution hk, aeval_powerSubstitution]

end Hasse

section Nonvanishing

/-- **The Frobenius-graph nonvanishing test, Hasse form** (Iwaniec–Kowalski, Lemmas 11.16–11.17).
Over an integral domain `R` of exponential characteristic `p`, for any `q = p ^ e` (`e ≥ 0`), any
nonzero bivariate polynomial `F` of `Z`-degree strictly less than `q`, any finite set `S ⊆ R`, and
any order bound `m < q` with `(powerSubstitution q F).natDegree < #S * (m + 1)`, there exist
`a ∈ S` and `k ≤ m` such that the Hasse `Z`-jet `∂_Z^[k] F` does not vanish at `(a, a ^ q)`. -/
theorem exists_eval_hasseDeriv_single_ne_zero_of_natDegree_powerSubstitution_lt
    {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [ExpChar R p] {e : ℕ}
    {F : MvPolynomial (Fin 2) R} (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e)
    {S : Finset R} {m : ℕ} (hm : m < p ^ e)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < #S * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m, eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) ≠ 0 := by
  obtain ⟨a, ha, k, hkm, hne⟩ :=
    Polynomial.exists_eval_hasseDeriv_ne_zero_of_natDegree_lt
      (powerSubstitution_ne_zero hF hZ) hdeg
  refine ⟨a, ha, k, hkm, ?_⟩
  rwa [← eval_hasseDeriv_powerSubstitution (hkm.trans_lt hm)]

/-- **The Frobenius-graph nonvanishing test, ordinary form.** Over an integral domain `R` of prime
characteristic `p`, for `q = p ^ e` with `0 < e`, any nonzero bivariate polynomial `F` of
`Z`-degree strictly less than `q`, any finite set `S ⊆ R`, and any order bound `m < p` with
`(powerSubstitution q F).natDegree < #S * (m + 1)`, there exist `a ∈ S` and `k ≤ m` such that the
iterated partial `Z`-derivative `(∂_Z)^[k] F` does not vanish at `(a, a ^ q)`. -/
theorem exists_eval_iterate_pderiv_ne_zero_of_natDegree_powerSubstitution_lt
    {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [Fact p.Prime] [CharP R p] {e : ℕ} (he : 0 < e)
    {F : MvPolynomial (Fin 2) R} (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e)
    {S : Finset R} {m : ℕ} (hm : m < p)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < #S * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m, eval ![a, a ^ p ^ e] ((pderiv (0 : Fin 2))^[k] F) ≠ 0 := by
  have hm_pow : m < p ^ e := hm.trans_le (Nat.le_self_pow he.ne' p)
  obtain ⟨a, ha, k, hkm, hne⟩ :=
    exists_eval_hasseDeriv_single_ne_zero_of_natDegree_powerSubstitution_lt hF hZ hm_pow hdeg
  exact ⟨a, ha, k, hkm,
    (eval_iterate_pderiv_eq_zero_iff_eval_hasseDeriv_eq_zero_of_lt p
      (hkm.trans_lt hm) 0 F ![a, a ^ p ^ e]).not.2 hne⟩

end Nonvanishing

/-! ### Examples -/

section Examples

/-- Over `ZMod 2` (`p = 2, e = 1`), both sides of `derivative_powerSubstitution` send `Z * W` to
`X ^ 2`. -/
example : Polynomial.derivative
      (powerSubstitution (2 ^ 1) (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
    (Polynomial.X ^ 2 : Polynomial (ZMod 2)) ∧
    powerSubstitution (2 ^ 1) (pderiv 0 (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
    Polynomial.X ^ 2 := by
  refine ⟨?_, ?_⟩
  · rw [derivative_powerSubstitution (p := 2) Nat.one_pos]
    simp [Derivation.leibniz, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  · simp [Derivation.leibniz, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]

/-- Over `ZMod 3` (`p = 3, e = 1, k = 2 < 3`), `hasseDeriv 2` of `(Z ^ 2 * W)(X, X ^ 3) = X ^ 5`
is `X ^ 3`, matching `(∂_Z^[2] (Z ^ 2 * W))(X, X ^ 3) = W(X, X ^ 3) = X ^ 3`. -/
example : Polynomial.hasseDeriv 2
      (powerSubstitution (3 ^ 1) (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) =
    (Polynomial.X ^ 3 : Polynomial (ZMod 3)) := by
  rw [hasseDeriv_powerSubstitution (p := 3) (e := 1) (by decide)]
  have hmon : (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) =
      monomial (single 0 2 + single 1 1) 1 := by
    rw [X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
  have hsub : (single 0 2 + single 1 1 - single 0 2 : Fin 2 →₀ ℕ) = single 1 1 := by
    ext s; fin_cases s <;> simp
  rw [hmon, hasseDeriv_monomial, hsub]
  simp [prod_single_index, ← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow]

/-- The Hasse commutation bound `k < p ^ e` is sharp: at `k = q = 2 ^ 1` over `ZMod 2` for `F = W`,
`hasseDeriv 2 (W(X, X ^ 2)) = hasseDeriv 2 (X ^ 2) = 1`, whereas `∂_Z^[2] W = 0`. -/
example : Polynomial.hasseDeriv 2
      (powerSubstitution (2 ^ 1) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 1 ∧
    powerSubstitution (2 ^ 1)
      (hasseDeriv (single 0 2) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  refine ⟨?_, ?_⟩
  · simp [← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow]
  · rw [hasseDeriv_eq_zero_of_degreeOf_lt (i := 0) (by simp [degreeOf_X]), map_zero]

/-- For `p = 2, e = 2, q = 4` over `ZMod 2`, `hasseDeriv_powerSubstitution` holds at orders
`p ≤ k < q` (`k = 2` on `W` and `k = 3` on `Z ^ 3 * W`) and fails at `k = q = 4` on `W`. -/
example : Polynomial.hasseDeriv 2
      (powerSubstitution (2 ^ 2) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 ∧
    Polynomial.hasseDeriv 3
      (powerSubstitution (2 ^ 2) (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
      Polynomial.X ^ 4 ∧
    Polynomial.hasseDeriv 4
      (powerSubstitution (2 ^ 2) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hasseDeriv_powerSubstitution (p := 2) (e := 2) (by decide),
      hasseDeriv_eq_zero_of_degreeOf_lt (i := 0) (by simp [degreeOf_X]), map_zero]
  · rw [hasseDeriv_powerSubstitution (p := 2) (e := 2) (by decide)]
    have hmon : (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2)) =
        monomial (single 0 3 + single 1 1) 1 := by
      rw [X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
    have hsub : (single 0 3 + single 1 1 - single 0 3 : Fin 2 →₀ ℕ) = single 1 1 := by
      ext s; fin_cases s <;> simp
    rw [hmon, hasseDeriv_monomial, hsub]
    simp [prod_single_index, ← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow]
  · simp [← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow]

/-- The positivity hypothesis `0 < e` in `derivative_powerSubstitution` cannot be dropped: at
`e = 0` (`q = 1`), `derivative (powerSubstitution 1 W) = derivative X = 1` whereas `pderiv 0 W = 0`.
-/
example : Polynomial.derivative
      (powerSubstitution (2 ^ 0) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 1 ∧
    powerSubstitution (2 ^ 0) (pderiv 0 (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  simp [pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]

/-- No restriction on the size of the coefficient ring enters: over `GaloisField 2 2` with `q = 2`
(`e = 1`) and `c ^ 2 + c + 1 = 0`, `derivative_powerSubstitution` sends `c * Z * W` to `c * X ^ 2`.
-/
example : ∃ c : GaloisField 2 2, c ^ 2 + c + 1 = 0 ∧
    Polynomial.derivative
      (powerSubstitution (2 ^ 1) (C c * X 0 * X 1 : MvPolynomial (Fin 2) (GaloisField 2 2))) =
      Polynomial.C c * Polynomial.X ^ 2 := by
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    simpa using GaloisField.card 2 (n := 2) (by decide)
  obtain ⟨c, hc⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_natCard_eq_four hcard
  refine ⟨c, hc, ?_⟩
  rw [derivative_powerSubstitution (p := 2) Nat.one_pos]
  simp [Derivation.leibniz, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]

/-- Evaluated Hasse identity over `ZMod 3` (`p = 3, e = 1, F = Z ^ 2, k = 1, a = 2`): both sides
evaluate to `1`. -/
example : (Polynomial.hasseDeriv 1
      (powerSubstitution (3 ^ 1) (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3)))).eval 2 = 1 ∧
    eval ![2, 2 ^ 3 ^ 1]
      (hasseDeriv (single 0 1) (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3))) = 1 := by
  have h := eval_hasseDeriv_powerSubstitution (R := ZMod 3) (p := 3) (e := 1) (k := 1)
    (by decide) 2 (X 0 ^ 2)
  have hrhs : eval ![(2 : ZMod 3), 2 ^ 3 ^ 1]
      (hasseDeriv (single 0 1) (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3))) = 1 := by
    rw [X_pow_eq_monomial, hasseDeriv_monomial, eval_monomial, ← single_tsub]
    simp only [prod_single_index, Nat.choose_zero_right, Nat.choose_one_right, single_eq_same,
      Fin.isValue, pow_zero, Matrix.cons_val_zero]
    decide
  exact ⟨h.trans hrhs, hrhs⟩

/-- Over `GaloisField 2 2` (`p = 2, e = 1, q = 2`) with `F = Z + W`, `m = 0`, and `S = {0, 1, c}`
(`c ^ 2 + c + 1 = 0`), `(F(X, X ^ 2)).natDegree = 2 < 3 * 1`: `F` vanishes at `(0, 0)` and `(1, 1)`
and takes the nonzero value `1` at `(c, c ^ 2)`. On the two-point subset `{0, 1}`, the degree bound
`2 < 2 * 1` fails and `F` vanishes at both Frobenius-graph points. -/
example [DecidableEq (GaloisField 2 2)] : ∃ c : GaloisField 2 2, c ^ 2 + c + 1 = 0 ∧
    (∀ a ∈ ({0, 1} : Finset (GaloisField 2 2)),
      eval ![a, a ^ 2] (X 0 + X 1 : MvPolynomial (Fin 2) (GaloisField 2 2)) = 0) ∧
    eval ![c, c ^ 2] (X 0 + X 1 : MvPolynomial (Fin 2) (GaloisField 2 2)) = 1 := by
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    simpa using GaloisField.card 2 (n := 2) (by decide)
  obtain ⟨c, hc⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_natCard_eq_four hcard
  have hchar := TauCeti.two_eq_zero_of_natCard_eq_four hcard
  refine ⟨c, hc, fun a ha ↦ ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simp
    · simp only [one_pow, map_add, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination hchar
  · simp only [map_add, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hc - hchar

/-- The `Z`-degree hypothesis `F.degreeOf 0 < p ^ e` cannot be dropped: over `ZMod 2` (`q = 2`),
`F = Z ^ 2 + W` is nonzero of `Z`-degree `2`, yet `powerSubstitution 2 F = 0` so all jets vanish on
the Frobenius graph. -/
example : (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) (ZMod 2)) ≠ 0 ∧
    powerSubstitution 2 (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) (ZMod 2)) = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simpa using congrArg (eval ![0, 1]) h
  · ext n
    simp only [map_add, map_pow, powerSubstitution_X_zero, powerSubstitution_X_one,
      Polynomial.coeff_add, Polynomial.coeff_zero]
    rcases eq_or_ne n 2 with rfl | hn
    · simp only [Polynomial.coeff_X_pow, ↓reduceIte]
      decide
    · simp [Polynomial.coeff_X_pow, hn]

/-- Over `GaloisField 2 2` with `q = 2 ^ 2 = 4`, `F = Z + W`, and `S = Finset.univ` (`#S = 4`),
every element satisfies `a ^ 4 = a` so `F(a, a ^ 4) = 0` on all of `S` (the `m = 0` degree bound
`4 < 4 * 1` fails), while at `m = 1 < 2` (`4 < 4 * 2`) the first `Z`-jet `∂_Z F = 1` is nonzero at
every point. -/
example [Fintype (GaloisField 2 2)] :
    (∀ a : GaloisField 2 2,
      eval ![a, a ^ 4] (X 0 + X 1 : MvPolynomial (Fin 2) (GaloisField 2 2)) = 0) ∧
    (∀ a : GaloisField 2 2,
      eval ![a, a ^ 4] (pderiv 0 (X 0 + X 1 : MvPolynomial (Fin 2) (GaloisField 2 2))) = 1) := by
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    simpa using GaloisField.card 2 (n := 2) (by decide)
  have hchar := TauCeti.two_eq_zero_of_natCard_eq_four hcard
  have hfcard : Fintype.card (GaloisField 2 2) = 4 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  refine ⟨fun a ↦ ?_, fun a ↦ ?_⟩
  · have ha4 : a ^ 4 = a := by simpa [hfcard] using FiniteField.pow_card a
    simp only [map_add, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, ha4]
    linear_combination a * hchar
  · simp [pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]

/-- At `e = 0` (`q = 1`) over `ZMod 2`: the ordinary nonvanishing test fails without `0 < e`
(`F = W`, `S = {0}`, `m = 1` satisfies every other hypothesis, yet `(pderiv 0)^[0] W` and
`(pderiv 0)^[1] W` both vanish at `(0, 0)`), whereas the Hasse nonvanishing test applies at `e = 0`
to `F = W`, `S = {0, 1}`, `m = 0` with witness `a = 1, k = 0`. -/
example : (∀ k ≤ 1,
      eval ![(0 : ZMod 2), 0 ^ 2 ^ 0]
        ((pderiv (0 : Fin 2))^[k] (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0) ∧
    (∃ a ∈ ({0, 1} : Finset (ZMod 2)), ∃ k ≤ 0,
      eval ![a, a ^ 2 ^ 0]
        (hasseDeriv (single 0 k) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) ≠ 0) := by
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · interval_cases k
    · simp
    · simp [pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  · refine exists_eval_hasseDeriv_single_ne_zero_of_natDegree_powerSubstitution_lt
      (p := 2) (e := 0) ?_ (by simp [degreeOf_X]) (by decide) ?_
    · intro h
      simpa using congrArg (eval ![0, 1]) h
    · simp

/-- For `p = 2, e = 2, q = 4` over `ZMod 2`, `F = Z ^ 2`, `S = {0}`, and `m = 2`: the Hasse
nonvanishing test applies (`m = 2 < 4`, `natDegree (X ^ 2) = 2 < 1 * 3`) with witness `k = 2` at
`(0, 0)`, whereas all ordinary `Z`-jets of orders `k ≤ 2` vanish at `(0, 0)` (`m < p` fails). -/
example : (∃ a ∈ ({0} : Finset (ZMod 2)), ∃ k ≤ 2,
      eval ![a, a ^ 2 ^ 2]
        (hasseDeriv (single 0 k) (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 2))) ≠ 0) ∧
    (∀ k ≤ 2,
      eval ![(0 : ZMod 2), 0 ^ 2 ^ 2]
        ((pderiv (0 : Fin 2))^[k] (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 2))) = 0) := by
  refine ⟨?_, fun k hk ↦ ?_⟩
  · refine exists_eval_hasseDeriv_single_ne_zero_of_natDegree_powerSubstitution_lt
      (p := 2) (e := 2) ?_ ?_ (by decide) ?_
    · intro h
      simpa using congrArg (eval ![1, 0]) h
    · refine (degreeOf_le_iff.2 fun μ hμ ↦ ?_).trans_lt (by decide : 2 < 2 ^ 2)
      rw [X_pow_eq_monomial, mem_support_iff, coeff_monomial] at hμ
      split_ifs at hμ with h
      · subst h; simp
      · exact absurd rfl hμ
    · simp
  · interval_cases k
    · simp
    · simp
    · rw [← factorial_smul_hasseDeriv_single, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2)]
      have h2 : ((Nat.factorial 2 : ℕ) : ZMod 2) = 0 := by decide
      rw [h2, zero_smul]

end Examples

end MvPolynomial
