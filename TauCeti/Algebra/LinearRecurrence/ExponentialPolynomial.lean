/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Uniqueness of exponential polynomial sequences

Over a characteristic-zero domain, the sequences `n ↦ p.eval n * θ ^ n`, with distinct
nonzero bases `θ`, admit no nontrivial finite relation. Consequently a sequence has at most
one expression as a sum of polynomial multiples of powers of a fixed finite set of nonzero
bases. No degree bound on the coefficient polynomials is needed for uniqueness.

The connection with linear recurrences is the shift operator: the summand with base `θ`
belongs to its maximal generalized eigenspace for `θ`. Translation of a polynomial preserves
its leading coefficient, so taking a difference lowers its degree. Mathlib's
`Module.End.independent_maxGenEigenspace` then separates the summands; the finite-sum
criterion used here is `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`.

See R. P. Stanley, *Enumerative Combinatorics*, vol. 1, second edition, Theorem 4.1.1
and its proof, pp. 535–536, for the closed-form interpretation and uniqueness.
-/

public section

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- A polynomial multiple of `θ ^ n` lies in the maximal generalized eigenspace of the
forward shift for `θ`. This holds in arbitrary characteristic, and even when `θ = 0`. -/
theorem eval_mul_pow_mem_maxGenEigenspace (p : R[X]) (θ : R) :
    (fun n : ℕ ↦ p.eval (n : R) * θ ^ n) ∈
      Module.End.maxGenEigenspace (LinearMap.funLeft R R Nat.succ) θ := by
  induction p using Polynomial.degree_lt_wf.induction with
  | h p ih =>
    by_cases hp : p = 0
    · simpa only [hp, eval_zero, zero_mul, Pi.zero_def] using
        (Module.End.maxGenEigenspace (LinearMap.funLeft R R Nat.succ) θ).zero_mem
    let q := θ • (taylor 1 p - p)
    have hq : q.degree < p.degree := by
      exact (degree_smul_le _ _).trans_lt <|
        degree_sub_lt_right (degree_taylor p 1) hp (leadingCoeff_taylor 1 p)
    have hdiff :
        (LinearMap.funLeft R R Nat.succ - θ • 1)
            (fun n : ℕ ↦ p.eval (n : R) * θ ^ n) =
          (fun n : ℕ ↦ q.eval (n : R) * θ ^ n) := by
      ext n
      simp only [LinearMap.sub_apply, LinearMap.funLeft_apply, LinearMap.smul_apply,
        Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_succ,
        q, smul_eq_C_mul, eval_mul, eval_sub, taylor_apply, eval_comp, eval_add, eval_X,
        eval_C, pow_succ]
      ring
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (ih q hq)
    apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
    refine ⟨k + 1, ?_⟩
    rw [pow_succ, Module.End.mul_apply, hdiff, hk]

end Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- Distinct nonzero exponential bases are independent even with polynomial coefficients.
In particular, a vanishing exponential polynomial has every coefficient polynomial zero. -/
theorem eq_zero_of_sum_eval_mul_pow_eq_zero {s : Finset R} {p : R → R[X]}
    (hs : ∀ θ ∈ s, θ ≠ 0)
    (h : ∀ n : ℕ, ∑ θ ∈ s, (p θ).eval (n : R) * θ ^ n = 0) :
    ∀ θ ∈ s, p θ = 0 := by
  classical
  have hz : ∀ θ ∈ s, (fun n : ℕ ↦ (p θ).eval (n : R) * θ ^ n) = 0 := by
    apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
      (Module.End.independent_maxGenEigenspace (LinearMap.funLeft R R Nat.succ)) s
    · exact fun θ _ ↦ (p θ).eval_mul_pow_mem_maxGenEigenspace θ
    · ext n
      simpa using h n
  intro θ hθ
  apply (p θ).eq_zero_of_infinite_isRoot
  refine (Set.infinite_range_of_injective (Nat.cast_injective (R := R))).mono ?_
  rintro x ⟨n, rfl⟩
  have hn := congrFun (hz θ hθ) n
  exact (mul_eq_zero.mp hn).resolve_right (pow_ne_zero n (hs θ hθ))

/-- A finite exponential polynomial over nonzero bases vanishes exactly when all of its
coefficient polynomials vanish. The empty sum is included. -/
theorem sum_eval_mul_pow_eq_zero_iff {s : Finset R} {p : R → R[X]}
    (hs : ∀ θ ∈ s, θ ≠ 0) :
    (∀ n : ℕ, ∑ θ ∈ s, (p θ).eval (n : R) * θ ^ n = 0) ↔
      ∀ θ ∈ s, p θ = 0 := by
  refine ⟨eq_zero_of_sum_eval_mul_pow_eq_zero hs, ?_⟩
  intro hp n
  exact Finset.sum_eq_zero fun θ hθ ↦ by simp [hp θ hθ]

/-- Uniqueness of polynomial coefficients in an exponential polynomial expansion, without
any bound on their degrees. This applies in particular to repeated-root recurrence formulas. -/
theorem sum_eval_mul_pow_eq_iff {s : Finset R} {p q : R → R[X]}
    (hs : ∀ θ ∈ s, θ ≠ 0) :
    (∀ n : ℕ, ∑ θ ∈ s, (p θ).eval (n : R) * θ ^ n =
      ∑ θ ∈ s, (q θ).eval (n : R) * θ ^ n) ↔ ∀ θ ∈ s, p θ = q θ := by
  constructor
  · intro h
    have hz : ∀ n : ℕ, ∑ θ ∈ s, (p θ - q θ).eval (n : R) * θ ^ n = 0 := by
      intro n
      simp only [eval_sub, sub_mul, Finset.sum_sub_distrib, h n, sub_self]
    exact fun θ hθ ↦ sub_eq_zero.mp (eq_zero_of_sum_eval_mul_pow_eq_zero hs hz θ hθ)
  · intro h n
    exact Finset.sum_congr rfl fun θ hθ ↦ by rw [h θ hθ]

-- The bases in a repeated-root formula may coincide only after their polynomial coefficients
-- have been combined: with the singleton base `1`, the coefficients are still unique.
example (p q : ℚ[X]) (h : ∀ n : ℕ, p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  have heq := (sum_eval_mul_pow_eq_iff (s := {1}) (p := fun _ ↦ p) (q := fun _ ↦ q)
    (by simp)).mp (by simpa using h)
  exact heq 1 (by simp)

-- The nonzero-base hypothesis cannot be dropped.
example : (fun n : ℕ ↦ (X : ℚ[X]).eval (n : ℚ) * (0 : ℚ) ^ n) = 0 := by
  ext n
  cases n <;> simp

-- Characteristic zero cannot be dropped: `X² - X` vanishes on every natural input in F₂.
example : ∀ n : ℕ, (X ^ 2 - X : (ZMod 2)[X]).eval (n : ZMod 2) = 0 := by
  intro n
  simp only [eval_sub, eval_pow, eval_X]
  generalize (n : ZMod 2) = x
  fin_cases x <;> decide

end TauCeti
