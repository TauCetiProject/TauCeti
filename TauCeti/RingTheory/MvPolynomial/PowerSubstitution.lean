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

import Mathlib.Algebra.Field.ZMod
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

When `B = q = p ^ e` in characteristic `p`, `F ↦ F(X, X ^ q)` restricts `F` to the Frobenius graph
`W = Z ^ q`:
* For `0 < e`, `D(X ^ q) = 0`, so iterated ordinary derivatives of every order commute with
  `powerSubstitution q` (`MvPolynomial.iterate_derivative_powerSubstitution`).
* In exponential characteristic `p`, Hasse differentiation of order `k < q` is linear over
  polynomials in `X ^ q` (`Polynomial.hasseDeriv_expand_mul`), so Hasse derivatives of order
  `k < q` commute with `powerSubstitution q` (`MvPolynomial.hasseDeriv_powerSubstitution`),
  including orders `p ≤ k < q` where ordinary derivatives vanish identically.

Combining injectivity below `Z`-degree `q`, the Hasse substitution identity, and the root-count
bound for univariate Hasse jets yields the *Frobenius-graph nonvanishing test* in both its Hasse
form (`MvPolynomial.exists_nonzero_hasse_jet_on_frobenius_graph`, valid for all `e ≥ 0` and
`m < q`) and its ordinary form (`MvPolynomial.exists_nonzero_ordinary_jet_on_frobenius_graph`, for
`0 < e` and `m < p`).

## Main results

* `MvPolynomial.coeff_powerSubstitution`: for `F` of `Z`-degree below `B` and `μ 0 < B`, the
  coefficient of `X ^ (μ 0 + B * μ 1)` in `F(X, X ^ B)` is the coefficient of `Z ^ μ 0 W ^ μ 1`.
* `MvPolynomial.powerSubstitution_injOn`, `MvPolynomial.powerSubstitution_eq_zero_iff`: the
  substitution is injective on polynomials of `Z`-degree below `B`, so for `degreeOf 0 F < B` we
  have `F(X, X ^ B) = 0 ↔ F = 0`.
* `MvPolynomial.support_powerSubstitution_subset`,
  `MvPolynomial.natDegree_powerSubstitution_le`: the exponents of `F(X, X ^ B)` are among the
  weights `μ 0 + B * μ 1` of the exponents of `F`, so its degree is at most
  `degreeOf 0 F + B * degreeOf 1 F`.
* `MvPolynomial.powerSubstitution_map`, `MvPolynomial.eval_powerSubstitution`,
  `MvPolynomial.aeval_powerSubstitution`: naturality under a ring map of the coefficients, and
  evaluation `(F(X, X ^ B)).eval a = F(a, a ^ B)` (and in an `R`-algebra).
* `MvPolynomial.derivative_powerSubstitution`,
  `MvPolynomial.iterate_derivative_powerSubstitution`,
  `MvPolynomial.eval_iterate_derivative_powerSubstitution`,
  `MvPolynomial.aeval_iterate_derivative_powerSubstitution`: the chain rule for `F(X, X ^ B)` and
  commutation of ordinary derivatives of every order with `powerSubstitution (p ^ e)` when `0 < e`.
* `MvPolynomial.hasseDeriv_powerSubstitution`,
  `MvPolynomial.eval_hasseDeriv_powerSubstitution`,
  `MvPolynomial.aeval_hasseDeriv_powerSubstitution`: commutation of Hasse derivatives of order
  `k < p ^ e` with `powerSubstitution (p ^ e)` in exponential characteristic `p`.
* `MvPolynomial.exists_nonzero_hasse_jet_on_frobenius_graph`,
  `MvPolynomial.exists_nonzero_ordinary_jet_on_frobenius_graph`: nonvanishing of some Hasse (for
  `m < p ^ e`) or ordinary (for `0 < e` and `m < p`) `Z`-jet of order `≤ m` on the Frobenius graph
  over a finite set `S` when `F ≠ 0`, `degreeOf 0 F < p ^ e`, and
  `(F(X, X ^ (p ^ e))).natDegree < #S * (m + 1)`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6, Lemmas 11.16–11.17, pp. 282–284.
* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  proof of Theorem 3.3.7 and Exercise 3.5(a), the Kronecker substitution `xᵢ ↦ t ^ (d ^ (i - 1))`,
  injective on monomials of partial degrees below `d`.
-/

public section

noncomputable section

namespace MvPolynomial

open Finset Finsupp

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
    (hZ : F.degreeOf 0 < B) : powerSubstitution B F = 0 ↔ F = 0 := by
  have h0 : (0 : MvPolynomial (Fin 2) R).degreeOf 0 < B := by
    simpa using (Nat.zero_le _).trans_lt hZ
  exact ⟨fun h ↦ powerSubstitution_injOn B hZ h0 (h.trans (map_zero _).symm), fun h ↦ by simp [h]⟩

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

/-- **Algebra evaluation formula.** Evaluating `F(X, X ^ B)` at `a : S` in an `R`-algebra `S` gives
`F(a, a ^ B)`. -/
@[simp]
theorem aeval_powerSubstitution [Algebra R S] (B : ℕ) (a : S) (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (powerSubstitution B F) = aeval ![a, a ^ B] F := by
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← powerSubstitution_map, eval_powerSubstitution,
    aeval_def, eval_map]

/-- **Chain rule for the power substitution.** The derivative of `F(X, X ^ B)` is
`(∂_Z F)(X, X ^ B) + (∂_W F)(X, X ^ B) * D(X ^ B)`. -/
theorem derivative_powerSubstitution (B : ℕ) (F : MvPolynomial (Fin 2) R) :
    (powerSubstitution B F).derivative =
      powerSubstitution B (pderiv 0 F) +
        powerSubstitution B (pderiv 1 F) * (Polynomial.X ^ B).derivative := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG =>
    simp only [map_add, hF, hG]
    ring
  | mul_X F i hF =>
    fin_cases i <;>
      simp [Derivation.leibniz, Polynomial.derivative_mul, hF] <;>
      ring

/-- When `(B : R) = 0`, differentiating `F(X, X ^ B)` differentiates only in `Z`. -/
theorem derivative_powerSubstitution_of_natCast_eq_zero {B : ℕ} (hB : (B : R) = 0)
    (F : MvPolynomial (Fin 2) R) :
    (powerSubstitution B F).derivative = powerSubstitution B (pderiv 0 F) := by
  rw [derivative_powerSubstitution, Polynomial.derivative_X_pow, hB]
  simp

/-- When `(B : R) = 0`, iterated ordinary derivatives of every order commute with
`powerSubstitution B`. -/
theorem iterate_derivative_powerSubstitution_of_natCast_eq_zero {B : ℕ} (hB : (B : R) = 0)
    (k : ℕ) (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative^[k] (powerSubstitution B F) =
      powerSubstitution B ((pderiv 0)^[k] F) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      derivative_powerSubstitution_of_natCast_eq_zero hB, ih]

/-- In characteristic `p` and for `q = p ^ e` with `0 < e`, iterated ordinary derivatives of every
order commute with the Frobenius substitution `F ↦ F(X, X ^ q)`. -/
theorem iterate_derivative_powerSubstitution {p : ℕ} [CharP R p] {e : ℕ} (he : 0 < e) (k : ℕ)
    (F : MvPolynomial (Fin 2) R) :
    Polynomial.derivative^[k] (powerSubstitution (p ^ e) F) =
      powerSubstitution (p ^ e) ((pderiv 0)^[k] F) :=
  iterate_derivative_powerSubstitution_of_natCast_eq_zero
    (by rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne']) k F

/-- Evaluated form of `iterate_derivative_powerSubstitution`: in characteristic `p` and for
`q = p ^ e` with `0 < e`, the `k`-th ordinary derivative of `F(X, X ^ q)` at `a` is
`(∂_Z^k F)(a, a ^ q)`. -/
theorem eval_iterate_derivative_powerSubstitution {p : ℕ} [CharP R p] {e : ℕ} (he : 0 < e) (k : ℕ)
    (a : R) (F : MvPolynomial (Fin 2) R) :
    (Polynomial.derivative^[k] (powerSubstitution (p ^ e) F)).eval a =
      eval ![a, a ^ p ^ e] ((pderiv 0)^[k] F) := by
  rw [iterate_derivative_powerSubstitution he, eval_powerSubstitution]

/-- Algebra-evaluated form of `iterate_derivative_powerSubstitution`: in characteristic `p` and for
`q = p ^ e` with `0 < e`, evaluating `D^k (F(X, X ^ q))` at `a : S` in an `R`-algebra `S` gives
`(∂_Z^k F)(a, a ^ q)`. -/
theorem aeval_iterate_derivative_powerSubstitution [Algebra R S] {p : ℕ} [CharP R p] {e : ℕ}
    (he : 0 < e) (k : ℕ) (a : S) (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (Polynomial.derivative^[k] (powerSubstitution (p ^ e) F)) =
      aeval ![a, a ^ p ^ e] ((pderiv 0)^[k] F) := by
  rw [iterate_derivative_powerSubstitution he, aeval_powerSubstitution]

/-- **Hasse derivatives commute with the Frobenius substitution below `p ^ e`**
(Iwaniec–Kowalski, Lemma 11.17). Over any commutative semiring of exponential characteristic `p`,
for `q = p ^ e` (`e ≥ 0`) and `k < q`, `D^[k](F(X, X ^ q)) = (∂_Z^[k] F)(X, X ^ q)`. -/
theorem hasseDeriv_powerSubstitution {p : ℕ} [ExpChar R p] {e k : ℕ} (hk : k < p ^ e)
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
        mul_comm (μ 1) (p ^ e), add_comm]
    rw [powerSubstitution_monomial, hsplit, Polynomial.hasseDeriv_expand_mul hk,
      Polynomial.expand_monomial, Polynomial.hasseDeriv_monomial, Polynomial.monomial_mul_monomial,
      one_mul, hasseDeriv_monomial, powerSubstitution_monomial,
      Finsupp.prod_single_index (by simp)]
    simp [mul_comm (μ 1) (p ^ e), add_comm]

/-- Evaluated form of `hasseDeriv_powerSubstitution`: in exponential characteristic `p`, for
`q = p ^ e` (`e ≥ 0`) and `k < q`, the `k`-th Hasse jet of `F(X, X ^ q)` at `a` is
`(∂_Z^[k] F)(a, a ^ q)`. -/
theorem eval_hasseDeriv_powerSubstitution {p : ℕ} [ExpChar R p] {e k : ℕ} (hk : k < p ^ e) (a : R)
    (F : MvPolynomial (Fin 2) R) :
    (Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F)).eval a =
      eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) := by
  rw [hasseDeriv_powerSubstitution hk, eval_powerSubstitution]

/-- Algebra-evaluated form of `hasseDeriv_powerSubstitution`: in exponential characteristic `p`,
for `q = p ^ e` (`e ≥ 0`) and `k < q`, evaluating `D^[k](F(X, X ^ q))` at `a : S` in an
`R`-algebra `S` gives `(∂_Z^[k] F)(a, a ^ q)`. -/
theorem aeval_hasseDeriv_powerSubstitution [Algebra R S] {p : ℕ} [ExpChar R p] {e k : ℕ}
    (hk : k < p ^ e) (a : S) (F : MvPolynomial (Fin 2) R) :
    Polynomial.aeval a (Polynomial.hasseDeriv k (powerSubstitution (p ^ e) F)) =
      aeval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) := by
  rw [hasseDeriv_powerSubstitution hk, aeval_powerSubstitution]

end CommSemiring

section FrobeniusGraph

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {p : ℕ} [ExpChar R p]

/-- **The Frobenius-graph nonvanishing test, Hasse form** (Iwaniec–Kowalski, Lemmas 11.16–11.17).
Over a commutative ring `R` without zero divisors of exponential characteristic `p`, for
`q = p ^ e` (`e ≥ 0`), any nonzero bivariate polynomial `F` of `Z`-degree below `q` whose Frobenius
substitution `F(X, X ^ q)` has degree strictly less than `#S * (m + 1)` with `m < q` has a nonzero
Hasse `Z`-jet of order at most `m` at some Frobenius-graph point `(a, a ^ q)` with `a ∈ S`. -/
theorem exists_nonzero_hasse_jet_on_frobenius_graph {e : ℕ} {F : MvPolynomial (Fin 2) R}
    (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e) {S : Finset R} {m : ℕ} (hm : m < p ^ e)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < #S * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m, eval ![a, a ^ p ^ e] (hasseDeriv (single 0 k) F) ≠ 0 := by
  have : Nontrivial R := ⟨⟨0, 1, fun h ↦ hF <| by
    have := subsingleton_of_zero_eq_one h
    exact Subsingleton.elim _ _⟩⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  obtain ⟨a, ha, k, hk, hne⟩ :=
    Polynomial.exists_eval_hasseDeriv_ne_zero_of_natDegree_lt
      (mt (powerSubstitution_eq_zero_iff hZ).1 hF) hdeg
  refine ⟨a, ha, k, hk, ?_⟩
  rwa [eval_hasseDeriv_powerSubstitution (hk.trans_lt hm)] at hne

/-- **The Frobenius-graph nonvanishing test, ordinary form.** Over a commutative ring `R` without
zero divisors of exponential characteristic `p`, for `q = p ^ e` with `0 < e` and `m < p`, any
nonzero bivariate polynomial `F` of `Z`-degree below `q` with
`(F(X, X ^ q)).natDegree < #S * (m + 1)` has a nonzero ordinary `Z`-jet of order at most `m` at some
Frobenius-graph point `(a, a ^ q)` with `a ∈ S`. -/
theorem exists_nonzero_ordinary_jet_on_frobenius_graph {e : ℕ} (he : 0 < e)
    {F : MvPolynomial (Fin 2) R} (hF : F ≠ 0) (hZ : F.degreeOf 0 < p ^ e) {S : Finset R}
    {m : ℕ} (hm : m < p)
    (hdeg : (powerSubstitution (p ^ e) F).natDegree < #S * (m + 1)) :
    ∃ a ∈ S, ∃ k ≤ m, eval ![a, a ^ p ^ e] ((pderiv 0)^[k] F) ≠ 0 := by
  have hmp : m < p ^ e := hm.trans_le (Nat.le_self_pow he.ne' p)
  obtain ⟨a, ha, k, hk, hne⟩ :=
    exists_nonzero_hasse_jet_on_frobenius_graph hF hZ hmp hdeg
  exact ⟨a, ha, k, hk,
    mt (eval_iterate_pderiv_eq_zero_iff_of_lt_expChar (hk.trans_lt hm) _ _).1 hne⟩

end FrobeniusGraph

/-! ### Examples and sharpness -/

/-- The bound `B` on the `Z`-degree cannot be dropped: `Z ^ 2` and `W` both map to `X ^ 2`. -/
example : powerSubstitution (R := ℤ) 2 (X 0 ^ 2) = powerSubstitution 2 (X 1) := by
  simp

example : (X 0 ^ 2 : MvPolynomial (Fin 2) ℤ) ≠ X 1 := by
  intro h
  simpa [degreeOf_X] using congrArg (degreeOf 0) h

/-- Over `ZMod 2` with `q = 4`, Hasse derivatives commute with `powerSubstitution 4` at order
`3` (`p ≤ 3 < 4`): `D^[3] ((Z ^ 3 W)(X, X ^ 4)) = X ^ 4 = (∂_Z^[3] (Z ^ 3 W))(X, X ^ 4)`. -/
example :
    Polynomial.hasseDeriv 3 (powerSubstitution (2 ^ 2) (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2)
      (ZMod 2))) = Polynomial.X ^ 4 ∧
    powerSubstitution (2 ^ 2) (hasseDeriv (single 0 3) (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2)
      (ZMod 2))) = Polynomial.X ^ 4 := by
  have h : powerSubstitution (2 ^ 2) (hasseDeriv (single 0 3)
      (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) = Polynomial.X ^ 4 := by
    have hm : (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) (ZMod 2)) =
        monomial (single 0 3 + single 1 1) 1 := by
      rw [X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
    have hsub : (single 0 3 + single 1 1 - single 0 3 : Fin 2 →₀ ℕ) = single 1 1 := by
      ext j
      fin_cases j <;> simp
    rw [hm, hasseDeriv_monomial, prod_single_index (by simp), hsub, powerSubstitution_monomial]
    simp [Polynomial.monomial_one_right_eq_X_pow]
  exact ⟨(hasseDeriv_powerSubstitution (p := 2) (e := 2) (by decide) _).trans h, h⟩

/-- The bound `k < p ^ e` in `hasseDeriv_powerSubstitution` is sharp: at `k = p ^ e = 2` over
`ZMod 2` with `F = W`, `D^[2] (X ^ 2) = 1` whereas `∂_Z^[2] W = 0`. -/
example :
    Polynomial.hasseDeriv 2 (powerSubstitution (2 ^ 1) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
      1 ∧
    powerSubstitution (2 ^ 1) (hasseDeriv (single 0 2) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
      0 := by
  refine ⟨by simp [← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow], ?_⟩
  rw [hasseDeriv_eq_zero_of_degreeOf_lt (i := 0) (by simp [degreeOf_X]), map_zero]

/-- The hypothesis `0 < e` in `iterate_derivative_powerSubstitution` and
`exists_nonzero_ordinary_jet_on_frobenius_graph` is necessary: at `e = 0` over `ZMod 2`, `F = W`
has `Z`-degree `0 < 1` and `(W(X, X ^ 1)).natDegree = 1 < #{0} * (1 + 1)`, yet `D(W(X, X ^ 1)) = 1`
while `∂_Z^k W` vanishes at `(0, 0)` for every `k ≤ 1`. -/
example :
    (powerSubstitution (2 ^ 0) (X 1 : MvPolynomial (Fin 2) (ZMod 2))).derivative = 1 ∧
    ∀ k ≤ 1, eval ![0, 0 ^ 2 ^ 0] ((pderiv 0)^[k] (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  refine ⟨by simp, fun k hk ↦ ?_⟩
  interval_cases k <;> simp

/-- At `e = 0`, `exists_nonzero_hasse_jet_on_frobenius_graph` still applies: for `F = W`,
`S = {0, 1}` over `ZMod 2`, and `m = 0`, some Hasse jet of order `0` is nonzero on `S`. -/
example : ∃ a ∈ ({0, 1} : Finset (ZMod 2)), ∃ k ≤ 0,
    eval ![a, a ^ 2 ^ 0] (hasseDeriv (single 0 k) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exists_nonzero_hasse_jet_on_frobenius_graph (p := 2) (e := 0) ?_ ?_ (by decide) ?_
  · intro h
    simpa using congrArg (eval ![0, (1 : ZMod 2)]) h
  · simp [degreeOf_X]
  · simp

/-- The bound `m < p` in `exists_nonzero_ordinary_jet_on_frobenius_graph` cannot be relaxed to
`m < p ^ e`: for `p = 2`, `e = 2`, `F = Z ^ 2`, `S = {0}`, and `m = 2` over `ZMod 2`, the Hasse
jet `∂_Z^[2] (Z ^ 2)` at `(0, 0)` is `1`, while all ordinary jets of orders `k ≤ 2` vanish at
`(0, 0)`. -/
example :
    eval ![(0 : ZMod 2), 0 ^ 2 ^ 2]
      (hasseDeriv (single 0 2) (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 2))) = 1 ∧
    ∀ k ≤ 2, eval ![(0 : ZMod 2), 0 ^ 2 ^ 2]
      ((pderiv 0)^[k] (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  refine ⟨by simp [X_pow_eq_monomial], fun k hk ↦ ?_⟩
  interval_cases k
  · simp
  · simp
  · rw [iterate_pderiv_eq_zero_of_char_le (p := 2) 0 le_rfl]
    simp

end MvPolynomial
