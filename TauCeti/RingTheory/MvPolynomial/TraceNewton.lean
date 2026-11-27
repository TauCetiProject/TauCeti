/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Ring

/-!
# Integral Newton polynomials for traces

`traceNewtonPolynomial j m` is the integral recurrence
`P₀,ₘ = 1`, `Pⱼ₊₁,ₘ = Xₘ Pⱼ,₁ - j Pⱼ,ₘ₊₁`.
At power sums, `Pⱼ,₁` evaluates to `j!` times the elementary symmetric function.
Unlike `esymmPsumPoly`, this family uses no division and is defined over every commutative ring;
the extra index also evaluates geometric power sequences as falling products. This lets trace
identities constrain the values of linear forms on idempotents and square-zero elements.

## Provenance

`TauCeti.traceNewtonPolynomial` and its evaluation lemmas adapt `New.newtonPoly`,
`New.eval_newtonPoly` and the geometric-power calculation in
`src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The commutative-ring generality is new here.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed. (1995), Chapter I, §2.
-/

public section

open MvPolynomial Finset

namespace TauCeti

variable {k : Type*} [CommRing k]

/-- The integral Newton recurrence `P₀,ₘ = 1`, `Pⱼ₊₁,ₘ = Xₘ Pⱼ,₁ - j Pⱼ,ₘ₊₁`.
Evaluating `Pⱼ,₁` at power sums gives `j!` times the `j`-th elementary symmetric function. -/
noncomputable def traceNewtonPolynomial : ℕ → ℕ → MvPolynomial ℕ k :=
  Nat.rec 1 fun j b m ↦ X m * b 1 - j • b (m + 1)

/-- The initial Newton polynomial is one. -/
@[simp]
lemma traceNewtonPolynomial_zero (m : ℕ) : traceNewtonPolynomial 0 m = (1 : MvPolynomial ℕ k) :=
  (rfl)

/-- The recursion that defines `traceNewtonPolynomial`. -/
lemma traceNewtonPolynomial_succ (j m : ℕ) :
    traceNewtonPolynomial (j + 1) m =
      (X m * traceNewtonPolynomial j 1 - j • traceNewtonPolynomial j (m + 1) : MvPolynomial ℕ k) :=
  (rfl)

/-- Newton's identities without denominators: evaluating at the power sums of a multiset
returns the elementary symmetric function multiplied by the factorial of its degree. -/
lemma _root_.Multiset.eval_traceNewtonPolynomial (s : Multiset k) :
    ∀ j : ℕ, eval (fun m : ℕ ↦ (s.map fun a : k ↦ a ^ m).sum) (traceNewtonPolynomial j 1) =
      j.factorial * s.esymm j := by
  -- Adding a root `a` adds `a ^ m` to each power sum `p m`.
  have add_pow_eval (a : k) (p : ℕ → k) (j m : ℕ) :
      eval (fun m ↦ a ^ m + p m) (traceNewtonPolynomial (j + 1) m) =
        eval p (traceNewtonPolynomial (j + 1) m) + j * a * eval p (traceNewtonPolynomial j m) +
          a ^ m * eval p (traceNewtonPolynomial j 1) := by
    induction j generalizing m with
    | zero => simp [traceNewtonPolynomial_succ, traceNewtonPolynomial_zero, add_comm]
    | succ j ih =>
      -- unfold `traceNewtonPolynomial (j + 2) m` and apply `ih` at `1` and at `m + 1`
      simp only [traceNewtonPolynomial_succ (j + 1), map_sub, map_mul, map_nsmul, eval_X, ih]
      -- unfold `traceNewtonPolynomial (j + 1) m` from the right-hand side
      simp only [traceNewtonPolynomial_succ j, map_sub, map_mul, eval_X, nsmul_eq_mul, map_natCast]
      push_cast
      ring
  have const_coeff (j m : ℕ) : (traceNewtonPolynomial (j + 1) m).constantCoeff = (0 : k) := by
    induction j generalizing m <;> simp_all [traceNewtonPolynomial_succ]
  intro j
  induction s using Multiset.induction generalizing j with
  | empty =>
    -- all power sums are zero, so only the constant coefficient is left
    cases j <;>
      simp [traceNewtonPolynomial_zero, const_coeff, Multiset.powersetCard_zero_right,
        Multiset.esymm]
  | cons a s ih =>
    rcases j with _ | j
    · simp [traceNewtonPolynomial_zero, Multiset.esymm]
    -- The power sums of `a ::ₘ s` are `a ^ m` plus those of `s`; `add_pow_eval` and `ih` expand
    -- the left side, and `esymm (j + 1)` of `a ::ₘ s` is `esymm (j + 1) + a * esymm j` of `s`.
    simp only [Multiset.map_cons, Multiset.sum_cons, add_pow_eval, ih]
    simp [Nat.factorial_succ, Multiset.sum_map_mul_left, Multiset.esymm, mul_assoc]
    ring

/-- Let `τ` be a linear form on a `k`-algebra `A` and `y : A` with `y ^ (m + 1) = l ^ m • y` for all
`m`. At the values `τ (y ^ i)`, the Newton polynomial `traceNewtonPolynomial (j + 1) (m + 1)`
takes the value `l ^ m` times the product of `τ y - i * l` over `i ≤ j`. -/
lemma _root_.LinearMap.eval_traceNewtonPolynomial_of_geometric
    {A : Type*} [Semiring A] [Algebra k A]
    (τ : A →ₗ[k] k) {l : k} {y : A} (hy : ∀ m : ℕ, y ^ (m + 1) = l ^ m • y) (j : ℕ) :
    ∀ m : ℕ, eval (fun i : ℕ ↦ τ (y ^ i)) (traceNewtonPolynomial (j + 1) (m + 1)) =
      l ^ m * ∏ i ∈ range (j + 1), (τ y - i * l) := by
  induction j with
  | zero => simp [traceNewtonPolynomial_succ, traceNewtonPolynomial_zero, hy]
  | succ j ih =>
    intro m
    -- unfold one step: `X (m + 1) * traceNewtonPolynomial (j + 1) 1 - (j + 1) •
    -- traceNewtonPolynomial (j + 1) (m + 2)`;
    -- `ih` at `0` and at `m + 1` turns both into products
    rw [traceNewtonPolynomial_succ (j + 1), map_sub, map_mul, map_nsmul, eval_X, ih 0, ih (m + 1),
      hy, map_smul, prod_range_succ _ (j + 1), smul_eq_mul, nsmul_eq_mul]
    ring

/-- Let `τ` be a linear form on a `k`-algebra `A` and `y : A` with `y ^ (m + 1) = l ^ m • y` for all
`m`. If `traceNewtonPolynomial (d + 1) 1` vanishes at `i ↦ τ (y ^ i)`, then
`τ y = j * l` for some natural number `j`. -/
lemma _root_.LinearMap.exists_nat_mul_of_traceNewtonPolynomial_eq_zero
    [NoZeroDivisors k] {A : Type*} [Semiring A] [Algebra k A]
    (τ : A →ₗ[k] k) {l : k} {y : A} (hy : ∀ m : ℕ, y ^ (m + 1) = l ^ m • y) {d : ℕ}
    (h_zero : eval (fun i : ℕ ↦ τ (y ^ i)) (traceNewtonPolynomial (d + 1) 1) = 0) :
    ∃ j : ℕ, τ y = j * l := by
  nontriviality k
  -- at `m = 0` the Newton polynomial is the product of the `τ y - i * l`, `i ≤ d`, so one vanishes
  have h_prod : ∏ i ∈ range (d + 1), (τ y - i * l) = 0 := by
    simpa using (τ.eval_traceNewtonPolynomial_of_geometric hy d 0).symm.trans h_zero
  obtain ⟨i, -, hi⟩ := prod_eq_zero_iff.mp h_prod
  exact ⟨i, sub_eq_zero.mp hi⟩

end TauCeti
