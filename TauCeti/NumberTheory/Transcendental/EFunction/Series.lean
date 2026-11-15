/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.RingTheory.PowerSeries.Derivative
public import TauCeti.RingTheory.PowerSeries.Entire.Taylor
public import TauCeti.RingTheory.PowerSeries.Radius

import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Factorial-divided power series, Hurwitz convolution, and analytic sums

Siegel's E-functions are presented through their exponential Taylor coefficients: a sequence
`a : ℕ → K` represents the formal series

  `ePowerSeries a = ∑ₙ (aₙ / n!) Xⁿ`

and, over a topological division ring, the analytic sum

  `eFun a z = ∑' n, aₙ * zⁿ / n!`.

This file develops the algebraic and analytic calculus of this normalization without imposing
arithmetic hypotheses on `a`:

* **Hurwitz (binomial) multiplication** `hurwitzMul a b n = ∑ₖ ≤ ₙ n.choose k * aₖ * bₙ₋ₖ` is the
  coefficient operation corresponding to Cauchy multiplication of factorial-divided series:
  `ePowerSeries (hurwitzMul a b) = ePowerSeries a * ePowerSeries b`. It forms a commutative
  associative operation with identity `Pi.single 0 1` and satisfies the shift Leibniz rule
  `hurwitzMul a b (n + 1) =
    hurwitzMul (fun k ↦ a (k + 1)) b n + hurwitzMul a (fun k ↦ b (k + 1)) n`.
* **Formal differentiation** shifts the sequence without extra factors:
  `d⁄dX (ePowerSeries a) = ePowerSeries (fun n ↦ a (n + 1))`.
* **Entireness and termwise calculus**: whenever `ePowerSeries a` is an entire formal power series
  (`PowerSeries.IsEntire`), `eFun a` agrees with `PowerSeries.evalAt (ePowerSeries a)`, converges
  at every point, turns Hurwitz convolution into pointwise multiplication, admits a formal power
  series of infinite radius at every center, and satisfies
  `deriv (eFun a) = eFun (fun n ↦ a (n + 1))` and `iteratedDeriv k (eFun a) 0 = a k`. Over `ℝ` or
  `ℂ` (`RCLike`), any geometric bound `‖aₙ‖ ≤ C ^ (n + 1)` ensures that `ePowerSeries a` is entire.

## Main definitions

* `TauCeti.hurwitzMul`: binomial (Hurwitz) convolution of sequences `ℕ → R`.
* `TauCeti.ePowerSeries`: the factorial-divided formal power series `∑ₙ (aₙ / n!) Xⁿ`.
* `TauCeti.eFun`: the analytic sum `z ↦ ∑' n, aₙ * zⁿ / n!`.

## Main results

* `TauCeti.hurwitzMul_comm`, `TauCeti.hurwitzMul_assoc`, `TauCeti.hurwitzMul_succ`: commutativity,
  associativity, and the shift Leibniz rule for Hurwitz convolution.
* `TauCeti.ePowerSeries_hurwitzMul`, `TauCeti.derivative_ePowerSeries`: compatibility of
  `ePowerSeries` with Hurwitz multiplication and formal differentiation.
* `TauCeti.hasFPowerSeriesOnBall_eFun`, `TauCeti.deriv_eFun`, `TauCeti.iteratedDeriv_eFun_zero`,
  `TauCeti.eFun_hurwitzMul`: analyticity, differentiation, Taylor coefficients, and multiplication
  of `eFun` when `ePowerSeries a` is entire.
* `TauCeti.isEntire_ePowerSeries_of_norm_le`: over an `RCLike` field, geometric growth of `‖aₙ‖`
  makes `ePowerSeries a` entire.

## References

* F. Beukers, *E-functions and G-functions*, lecture notes, Arizona Winter School, 2008, §3.1–3.2.
* A. B. Shidlovskii, *Transcendental Numbers*, de Gruyter Studies in Mathematics **12**, 1989,
  Chapter 3, §1.
-/

public section

open Finset PowerSeries
open scoped ENNReal

namespace TauCeti

/-! ### Hurwitz (binomial) convolution -/

section HurwitzMul

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The *Hurwitz* (or *binomial*) product of two sequences `a, b : ℕ → R`, defined by
`(hurwitzMul a b) n = ∑ k ∈ range (n + 1), n.choose k * a k * b (n - k)`. When `R` is a field of
characteristic zero, this is the sequence of exponential coefficients of the product of
`ePowerSeries a` and `ePowerSeries b` (`TauCeti.ePowerSeries_hurwitzMul`). -/
def hurwitzMul (a b : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ range (n + 1), (n.choose k : R) * a k * b (n - k)

/-- Unfolding `hurwitzMul` at index `n`. -/
theorem hurwitzMul_apply (a b : ℕ → R) (n : ℕ) :
    hurwitzMul a b n = ∑ k ∈ range (n + 1), (n.choose k : R) * a k * b (n - k) :=
  (rfl)

/-- Antidiagonal presentation of `hurwitzMul`. -/
theorem hurwitzMul_eq_sum_antidiagonal (a b : ℕ → R) (n : ℕ) :
    hurwitzMul a b n =
      ∑ ij ∈ antidiagonal n, ((ij.1 + ij.2).choose ij.1 : R) * a ij.1 * b ij.2 := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ ((i + j).choose i : R) * a i * b j) n, hurwitzMul_apply]
  refine sum_congr rfl fun k hk ↦ ?_
  have hle : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [Nat.add_sub_of_le hle]

/-- Left multiplication by the zero sequence gives zero. -/
@[simp]
theorem zero_hurwitzMul (b : ℕ → R) : hurwitzMul 0 b = 0 := by
  ext n
  simp [hurwitzMul_apply]

/-- Right multiplication by the zero sequence gives zero. -/
@[simp]
theorem hurwitzMul_zero (a : ℕ → R) : hurwitzMul a 0 = 0 := by
  ext n
  simp [hurwitzMul_apply]

/-- At `n = 0`, the Hurwitz product is `a 0 * b 0`. -/
@[simp]
theorem hurwitzMul_apply_zero (a b : ℕ → R) : hurwitzMul a b 0 = a 0 * b 0 := by
  simp [hurwitzMul_apply]

/-- Left distributivity of `hurwitzMul` over addition. -/
theorem add_hurwitzMul (a₁ a₂ b : ℕ → R) :
    hurwitzMul (a₁ + a₂) b = hurwitzMul a₁ b + hurwitzMul a₂ b := by
  ext n
  simp only [Pi.add_apply, hurwitzMul_apply, ← sum_add_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [mul_add, add_mul]

/-- Right distributivity of `hurwitzMul` over addition. -/
theorem hurwitzMul_add (a b₁ b₂ : ℕ → R) :
    hurwitzMul a (b₁ + b₂) = hurwitzMul a b₁ + hurwitzMul a b₂ := by
  ext n
  simp only [Pi.add_apply, hurwitzMul_apply, ← sum_add_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [mul_add]

/-- A sequence supported at `0` acts on the left by scalar multiplication. -/
@[simp]
theorem single_zero_hurwitzMul (c : R) (b : ℕ → R) (n : ℕ) :
    hurwitzMul (Pi.single 0 c) b n = c * b n := by
  rw [hurwitzMul_apply, sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

/-- A sequence supported at `0` acts on the right by scalar multiplication. -/
@[simp]
theorem hurwitzMul_single_zero (a : ℕ → R) (c : R) (n : ℕ) :
    hurwitzMul a (Pi.single 0 c) n = a n * c := by
  rw [hurwitzMul_apply, sum_eq_single n]
  · simp
  · intro k hk hkn
    have hlt : k < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hk)) hkn
    simp [Pi.single_eq_of_ne (Nat.sub_ne_zero_of_lt hlt)]
  · simp

/-- `Pi.single 0 1` is the left identity for `hurwitzMul`. -/
@[simp]
theorem single_zero_one_hurwitzMul (b : ℕ → R) : hurwitzMul (Pi.single 0 1) b = b := by
  ext n
  simp

/-- `Pi.single 0 1` is the right identity for `hurwitzMul`. -/
@[simp]
theorem hurwitzMul_single_zero_one (a : ℕ → R) : hurwitzMul a (Pi.single 0 1) = a := by
  ext n
  simp

/-- Ring homomorphisms commute with `hurwitzMul`. -/
theorem map_hurwitzMul (f : R →+* S) (a b : ℕ → R) (n : ℕ) :
    f (hurwitzMul a b n) = hurwitzMul (f ∘ a) (f ∘ b) n := by
  simp [hurwitzMul_apply]

/-- **Associativity of Hurwitz multiplication**, proved from the trinomial identity
`n.choose m * m.choose k = n.choose k * (n - k).choose (m - k)`. -/
theorem hurwitzMul_assoc (a b c : ℕ → R) :
    hurwitzMul (hurwitzMul a b) c = hurwitzMul a (hurwitzMul b c) := by
  ext n
  simp only [hurwitzMul_apply]
  calc ∑ m ∈ range (n + 1), (n.choose m : R) *
          (∑ k ∈ range (m + 1), (m.choose k : R) * a k * b (m - k)) * c (n - m)
      = ∑ m ∈ range (n + 1), ∑ k ∈ range (m + 1),
          ((n.choose m * m.choose k : ℕ) : R) * a k * b (m - k) * c (n - m) := by
        refine sum_congr rfl fun m _ ↦ ?_
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun k _ ↦ ?_
        push_cast
        simp only [mul_assoc]
    _ = ∑ k ∈ range (n + 1), ∑ j ∈ range (n - k + 1),
          ((n.choose k * (n - k).choose j : ℕ) : R) * a k * b j * c (n - k - j) := by
        -- Reindex `(m, k)` with `k ≤ m ≤ n` to `(k, j)` with `m = k + j` and `j ≤ n - k`.
        rw [sum_sigma', sum_sigma']
        refine sum_bij (fun p _ ↦ ⟨p.2, p.1 - p.2⟩) ?_ ?_ ?_ ?_
        · rintro ⟨m, k⟩ hp
          simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at hp ⊢
          omega
        · rintro ⟨m₁, k₁⟩ hp₁ ⟨m₂, k₂⟩ hp₂ heq
          simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at hp₁ hp₂
          simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
          obtain ⟨rfl, hsub⟩ := heq
          congr
          omega
        · rintro ⟨k, j⟩ hp
          simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at hp
          refine ⟨⟨k + j, k⟩, ?_, ?_⟩
          · simp only [mem_sigma, mem_range, Nat.lt_succ_iff]
            omega
          · simp
        · rintro ⟨m, k⟩ hp
          simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at hp
          rw [Nat.choose_mul hp.2, show n - m = n - k - (m - k) by omega]
    _ = ∑ k ∈ range (n + 1), (n.choose k : R) * a k *
          ∑ j ∈ range (n - k + 1), ((n - k).choose j : R) * b j * c (n - k - j) := by
        refine sum_congr rfl fun k _ ↦ ?_
        rw [mul_sum]
        refine sum_congr rfl fun j _ ↦ ?_
        push_cast
        simp only [mul_assoc]
        rw [(Nat.cast_commute ((n - k).choose j) (a k)).left_comm]

/-- **Leibniz shift rule for Hurwitz multiplication**: shifting the index by `1` acts as a
derivation on `hurwitzMul`. -/
theorem hurwitzMul_succ (a b : ℕ → R) (n : ℕ) :
    hurwitzMul a b (n + 1) =
      hurwitzMul (fun k ↦ a (k + 1)) b n + hurwitzMul a (fun k ↦ b (k + 1)) n := by
  rw [hurwitzMul_apply, sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.succ_sub_succ_eq_sub,
    Nat.choose_succ_succ, Nat.cast_add, add_mul, sum_add_distrib]
  rw [hurwitzMul_apply, add_assoc]
  congr 1
  rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul, add_zero,
    hurwitzMul_apply, sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  congr 1
  refine sum_congr rfl fun k hk ↦ ?_
  have hlt : k < n := mem_range.mp hk
  rw [show n - (k + 1) + 1 = n - k by omega]

/-- Hurwitz product of two constant-one sequences: `(hurwitzMul 1 1) n = 2 ^ n`. -/
@[simp]
theorem hurwitzMul_const_one (n : ℕ) : hurwitzMul (fun _ ↦ (1 : R)) (fun _ ↦ 1) n = 2 ^ n := by
  simp only [hurwitzMul_apply, mul_one, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow,
    Nat.cast_ofNat]

/-- Hurwitz multiplication is commutative over a commutative semiring. -/
theorem hurwitzMul_comm {R : Type*} [CommSemiring R] (a b : ℕ → R) :
    hurwitzMul a b = hurwitzMul b a := by
  ext n
  rw [hurwitzMul_apply, ← sum_range_reflect]
  refine sum_congr rfl fun k hk ↦ ?_
  have hle : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
  rw [Nat.sub_sub_self hle, Nat.choose_symm hle]
  ring

/-- Geometric scaling distributes across `hurwitzMul`: multiplying both inputs by `c ^ n` scales
the `n`-th Hurwitz coefficient by `c ^ n`. -/
theorem hurwitzMul_mul_pow {R : Type*} [CommSemiring R] (c : R) (a b : ℕ → R) (n : ℕ) :
    hurwitzMul (fun k ↦ c ^ k * a k) (fun k ↦ c ^ k * b k) n = c ^ n * hurwitzMul a b n := by
  rw [hurwitzMul_apply, hurwitzMul_apply, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  have hle : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  calc (n.choose k : R) * (c ^ k * a k) * (c ^ (n - k) * b (n - k))
      = c ^ (k + (n - k)) * ((n.choose k : R) * a k * b (n - k)) := by ring
    _ = c ^ n * ((n.choose k : R) * a k * b (n - k)) := by rw [Nat.add_sub_of_le hle]

end HurwitzMul

/-! ### Factorial-divided formal power series -/

section EPowerSeries

variable {K : Type*} [Field K]

/-- The formal power series `∑ₙ (aₙ / n!) Xⁿ` attached to a coefficient sequence `a : ℕ → K`. -/
noncomputable def ePowerSeries (a : ℕ → K) : K⟦X⟧ :=
  PowerSeries.mk fun n ↦ a n / n.factorial

/-- Unfolding `ePowerSeries`. -/
theorem ePowerSeries_def (a : ℕ → K) :
    ePowerSeries a = PowerSeries.mk fun n ↦ a n / n.factorial :=
  (rfl)

/-- The `n`-th coefficient of `ePowerSeries a` is `a n / n!`. -/
@[simp]
theorem coeff_ePowerSeries (a : ℕ → K) (n : ℕ) :
    coeff n (ePowerSeries a) = a n / n.factorial :=
  coeff_mk n _

/-- The constant coefficient of `ePowerSeries a` is `a 0`. -/
@[simp]
theorem constantCoeff_ePowerSeries (a : ℕ → K) :
    constantCoeff (ePowerSeries a) = a 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_ePowerSeries]
  simp

/-- Zero sequence gives the zero power series. -/
@[simp]
theorem ePowerSeries_zero : ePowerSeries (0 : ℕ → K) = 0 := by
  ext n
  simp

/-- `ePowerSeries` preserves addition. -/
theorem ePowerSeries_add (a b : ℕ → K) :
    ePowerSeries (a + b) = ePowerSeries a + ePowerSeries b := by
  ext n
  simp [add_div]

/-- `ePowerSeries` preserves negation. -/
theorem ePowerSeries_neg (a : ℕ → K) : ePowerSeries (-a) = -ePowerSeries a := by
  ext n
  simp [neg_div]

/-- `ePowerSeries` preserves subtraction. -/
theorem ePowerSeries_sub (a b : ℕ → K) :
    ePowerSeries (a - b) = ePowerSeries a - ePowerSeries b := by
  ext n
  simp [sub_div]

/-- `ePowerSeries` commutes with scalar multiplication. -/
theorem ePowerSeries_smul (c : K) (a : ℕ → K) :
    ePowerSeries (c • a) = c • ePowerSeries a := by
  ext n
  simp [mul_div_assoc]

/-- A sequence supported at a single index `k` gives the monomial `(c / k!) Xᵏ`. -/
theorem ePowerSeries_single (k : ℕ) (c : K) :
    ePowerSeries (Pi.single k c) = monomial k (c / k.factorial) := by
  ext n
  rw [coeff_ePowerSeries, coeff_monomial]
  split_ifs with h
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- Field homomorphisms act coefficientwise on `ePowerSeries`. -/
theorem map_ePowerSeries {L : Type*} [Field L] (f : K →+* L) (a : ℕ → K) :
    PowerSeries.map f (ePowerSeries a) = ePowerSeries (f ∘ a) := by
  ext n
  simp

/-- Rescaling the variable of `ePowerSeries a` by `c` multiplies `a n` by `c ^ n`. -/
theorem rescale_ePowerSeries (c : K) (a : ℕ → K) :
    rescale c (ePowerSeries a) = ePowerSeries fun n ↦ c ^ n * a n := by
  ext n
  simp [coeff_rescale, mul_div_assoc]

section CharZero

variable [CharZero K]

/-- Over a field of characteristic zero, `ePowerSeries` is injective. -/
@[simp]
theorem ePowerSeries_eq_iff {a b : ℕ → K} : ePowerSeries a = ePowerSeries b ↔ a = b := by
  refine ⟨fun h ↦ funext fun n ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hn : a n / n.factorial = b n / n.factorial := by
    simpa only [coeff_ePowerSeries] using congrArg (coeff n) h
  have hfact : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact (div_left_inj₀ hfact).mp hn

/-- Constant-one data give the formal exponential series `PowerSeries.exp K`. -/
@[simp]
theorem ePowerSeries_one : ePowerSeries (fun _ ↦ (1 : K)) = PowerSeries.exp K := by
  ext n
  simp

/-- Constant data `c` give `C c * exp K`. -/
theorem ePowerSeries_const (c : K) : ePowerSeries (fun _ ↦ c) = C c * PowerSeries.exp K := by
  ext n
  simp [coeff_C_mul, div_eq_mul_inv]

/-- Formal differentiation of `ePowerSeries a` shifts the sequence by one step:
`d⁄dX (ePowerSeries a) = ePowerSeries (fun n ↦ a (n + 1))`. -/
@[simp]
theorem derivative_ePowerSeries (a : ℕ → K) :
    d⁄dX (ePowerSeries a) = ePowerSeries fun n ↦ a (n + 1) := by
  ext n
  rw [coeff_derivative, coeff_ePowerSeries, coeff_ePowerSeries, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hne : (n : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hfact : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

/-- The `k`-th formal derivative of `ePowerSeries a` shifts the sequence by `k`. -/
@[simp]
theorem iterate_derivative_ePowerSeries (a : ℕ → K) (k : ℕ) :
    (d⁄dX)^[k] (ePowerSeries a) = ePowerSeries fun n ↦ a (n + k) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, derivative_ePowerSeries, ih]
    simp only [add_assoc]

/-- The `k`-th Hasse derivative of `ePowerSeries a` is `(k!)⁻¹` times the `k`-shifted series. -/
theorem hasseDeriv_ePowerSeries (a : ℕ → K) (k : ℕ) :
    PowerSeries.hasseDeriv k (ePowerSeries a) =
      (k.factorial : K)⁻¹ • ePowerSeries fun n ↦ a (n + k) := by
  ext n
  rw [coeff_hasseDeriv, coeff_ePowerSeries, coeff_smul, coeff_ePowerSeries, smul_eq_mul]
  have hchoose : ((n + k).factorial : K) =
      ((n + k).choose k : K) * (n.factorial : K) * (k.factorial : K) := by
    exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial n k).symm
  have hc : ((n + k).choose k : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_left k n)).ne'
  have hk : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [hchoose]
  field_simp

/-- **Cauchy product of factorial-divided series.** Hurwitz multiplication of coefficient sequences
corresponds to multiplication of `ePowerSeries`. -/
@[simp]
theorem ePowerSeries_hurwitzMul (a b : ℕ → K) :
    ePowerSeries (hurwitzMul a b) = ePowerSeries a * ePowerSeries b := by
  ext n
  rw [coeff_ePowerSeries, coeff_mul, hurwitzMul_eq_sum_antidiagonal, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun ij hij ↦ ?_
  have hsum : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
  have hchoose : (n.factorial : K) =
      ((ij.1 + ij.2).choose ij.1 : K) * (ij.1.factorial : K) * (ij.2.factorial : K) := by
    rw [← hsum]
    have hnat := (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right ij.1 ij.2)).symm
    rw [Nat.add_sub_cancel_left] at hnat
    exact_mod_cast hnat
  have hc : ((ij.1 + ij.2).choose ij.1 : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right ij.1 ij.2)).ne'
  have h1 : (ij.1.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (ij.2.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [coeff_ePowerSeries, coeff_ePowerSeries, hchoose]
  field_simp

end CharZero

end EPowerSeries

/-! ### Analytic evaluation `eFun` and entireness -/

section EFun

/-- The analytic sum `eFun a z = ∑' n, a n * z ^ n / n!` attached to a sequence `a : ℕ → K`.
Outside the domain of convergence it takes the junk value of `tsum`. -/
noncomputable def eFun {K : Type*} [DivisionRing K] [TopologicalSpace K] (a : ℕ → K) (z : K) : K :=
  ∑' n, a n * z ^ n / n.factorial

section Field

variable {K : Type*} [Field K] [TopologicalSpace K]

/-- Unfolding `eFun`. -/
theorem eFun_def (a : ℕ → K) (z : K) : eFun a z = ∑' n, a n * z ^ n / n.factorial :=
  (rfl)

/-- `eFun a z` is `PowerSeries.evalAt (ePowerSeries a) z`. -/
theorem evalAt_ePowerSeries (a : ℕ → K) (z : K) : (ePowerSeries a).evalAt z = eFun a z := by
  rw [evalAt_def, eFun_def]
  refine tsum_congr fun n ↦ ?_
  rw [coeff_ePowerSeries, smul_eq_mul, div_mul_eq_mul_div]

/-- The zero sequence evaluates to `0` at every point. -/
@[simp]
theorem eFun_zero (z : K) : eFun (0 : ℕ → K) z = 0 := by
  simp [eFun_def]

/-- At `z = 0`, `eFun a 0 = a 0` unconditionally, since all higher terms vanish identically. -/
@[simp]
theorem eFun_apply_zero (a : ℕ → K) : eFun a 0 = a 0 := by
  rw [eFun_def, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- A sequence supported at index `k` sums to the single term `c * z ^ k / k!`. -/
@[simp]
theorem eFun_single (k : ℕ) (c z : K) :
    eFun (Pi.single k c) z = c * z ^ k / k.factorial := by
  rw [eFun_def, tsum_eq_single k]
  · simp
  · intro n hn
    simp [Pi.single_eq_of_ne hn]

end Field

/-- Over `ℂ`, constant-one data sum to `Complex.exp`. -/
@[simp]
theorem eFun_one_complex (z : ℂ) : eFun (fun _ ↦ (1 : ℂ)) z = Complex.exp z := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div, eFun_def]
  simp

section Entire

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] {a b : ℕ → K}

/-- When `ePowerSeries a` is entire, the defining series of `eFun a z` converges to `eFun a z` at
every point `z`. -/
theorem hasSum_eFun (ha : (ePowerSeries a).IsEntire) (z : K) :
    HasSum (fun n ↦ a n * z ^ n / n.factorial) (eFun a z) := by
  rw [← evalAt_ePowerSeries]
  simpa only [coeff_ePowerSeries, smul_eq_mul, div_mul_eq_mul_div] using ha.hasSum_evalAt z

/-- When `ePowerSeries a` is entire, its terms at `z` are summable. -/
theorem summable_eFun (ha : (ePowerSeries a).IsEntire) (z : K) :
    Summable fun n ↦ a n * z ^ n / n.factorial :=
  (hasSum_eFun ha z).summable

/-- Pointwise addition of `eFun` for entire factorial-divided series. -/
theorem eFun_add (ha : (ePowerSeries a).IsEntire) (hb : (ePowerSeries b).IsEntire) (z : K) :
    eFun (a + b) z = eFun a z + eFun b z := by
  rw [← evalAt_ePowerSeries, ePowerSeries_add, ha.evalAt_add hb, evalAt_ePowerSeries,
    evalAt_ePowerSeries]

/-- If `ePowerSeries a` is entire, `eFun a` admits a formal power series of infinite radius at
every center `z`, given by the Hasse derivatives of `ePowerSeries a` evaluated at `z`. -/
theorem hasFPowerSeriesOnBall_eFun_at (ha : (ePowerSeries a).IsEntire) (z : K) :
    HasFPowerSeriesOnBall (eFun a)
      (FormalMultilinearSeries.ofScalars K fun k ↦
        (PowerSeries.hasseDeriv k (ePowerSeries a)).evalAt z) z ⊤ := by
  have hrad : (FormalMultilinearSeries.ofScalars K fun k ↦
      coeff k ((ePowerSeries a).taylor z)).radius = ⊤ := by
    rw [← PowerSeries.radius_eq_radius_ofScalars, radius_eq_top_iff]
    exact ha.taylor z
  refine ⟨by simpa [coeff_taylor] using hrad.ge, ENNReal.zero_lt_top, fun {y} _ ↦ ?_⟩
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, evalAt_ePowerSeries,
    add_comm z y] using ha.hasSum_taylor z y

/-- If `ePowerSeries a` is entire, `eFun a` is analytic on all of `K`. -/
theorem analyticOnNhd_eFun (ha : (ePowerSeries a).IsEntire) :
    AnalyticOnNhd K (eFun a) Set.univ :=
  fun z _ ↦ (hasFPowerSeriesOnBall_eFun_at ha z).analyticAt

section CharZero

variable [CharZero K]

/-- Pointwise multiplication of `eFun` corresponds to `hurwitzMul` when both series are entire. -/
theorem eFun_hurwitzMul (ha : (ePowerSeries a).IsEntire) (hb : (ePowerSeries b).IsEntire) (z : K) :
    eFun (hurwitzMul a b) z = eFun a z * eFun b z := by
  rw [← evalAt_ePowerSeries, ePowerSeries_hurwitzMul, ha.evalAt_mul hb, evalAt_ePowerSeries,
    evalAt_ePowerSeries]

/-- If `ePowerSeries a` is entire, `eFun a` has formal power series
`∑ (aₙ / n!) zⁿ` on the whole space (`r = ⊤`) centered at `0`. -/
theorem hasFPowerSeriesOnBall_eFun (ha : (ePowerSeries a).IsEntire) :
    HasFPowerSeriesOnBall (eFun a)
      (FormalMultilinearSeries.ofScalars K fun k ↦ a k / k.factorial) 0 ⊤ := by
  convert hasFPowerSeriesOnBall_eFun_at ha 0 using 2
  ext k
  simp [hasseDeriv_ePowerSeries, div_eq_inv_mul]

/-- Termwise derivative of `eFun a` at `z`: shifting `a` differentiates `eFun a`. -/
theorem hasDerivAt_eFun (ha : (ePowerSeries a).IsEntire) (z : K) :
    HasDerivAt (eFun a) (eFun (fun n ↦ a (n + 1)) z) z := by
  have hd := (hasFPowerSeriesOnBall_eFun_at ha z).hasFPowerSeriesAt.hasDerivAt
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, pow_one, mul_one, smul_eq_mul,
    hasseDeriv_one_apply, derivative_ePowerSeries, evalAt_ePowerSeries] using hd

/-- If `ePowerSeries a` is entire, `eFun a` is everywhere differentiable. -/
theorem differentiable_eFun (ha : (ePowerSeries a).IsEntire) :
    Differentiable K (eFun a) :=
  fun z ↦ (hasDerivAt_eFun ha z).differentiableAt

/-- Derivative of `eFun a`: `deriv (eFun a) = eFun (fun n ↦ a (n + 1))`. -/
theorem deriv_eFun (ha : (ePowerSeries a).IsEntire) :
    deriv (eFun a) = eFun fun n ↦ a (n + 1) :=
  funext fun z ↦ (hasDerivAt_eFun ha z).deriv

/-- Iterated derivatives of `eFun a`: `iteratedDeriv k (eFun a) = eFun (fun n ↦ a (n + k))`. -/
theorem iteratedDeriv_eFun (ha : (ePowerSeries a).IsEntire) (k : ℕ) :
    iteratedDeriv k (eFun a) = eFun fun n ↦ a (n + k) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have ha' : (ePowerSeries fun n ↦ a (n + 1)).IsEntire := by
      rw [← derivative_ePowerSeries]
      exact ha.derivative
    rw [iteratedDeriv_succ', deriv_eFun ha, ih ha']
    simp only [add_assoc]

/-- The `k`-th derivative of `eFun a` at `0` recovers `a k`. -/
@[simp]
theorem iteratedDeriv_eFun_zero (ha : (ePowerSeries a).IsEntire) (k : ℕ) :
    iteratedDeriv k (eFun a) 0 = a k := by
  rw [iteratedDeriv_eFun ha k, eFun_apply_zero, zero_add]

end CharZero

end Entire

section GeometricGrowth

/-- Over `ℝ` or `ℂ` (`RCLike`), any sequence `a` with geometric bound `‖a n‖ ≤ C ^ (n + 1)` gives
an entire factorial-divided formal power series `ePowerSeries a`. -/
theorem isEntire_ePowerSeries_of_norm_le {K : Type*} [RCLike K] {a : ℕ → K} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) :
    (ePowerSeries a).IsEntire := by
  refine isEntire_iff_forall_pos.mpr fun r hr ↦ (isRestricted_iff' r _).mpr ?_
  have hlim : Filter.Tendsto (fun n : ℕ ↦ C * ((C * r) ^ n / n.factorial))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((Real.summable_pow_div_factorial (C * r)).tendsto_atTop_zero).const_mul C
  refine squeeze_zero (fun _ ↦ by positivity) (fun n ↦ ?_) hlim
  rw [coeff_ePowerSeries, norm_div, RCLike.norm_natCast]
  calc ‖a n‖ / n.factorial * r ^ n
      ≤ C ^ (n + 1) / n.factorial * r ^ n := by gcongr; exact ha n
    _ = C * ((C * r) ^ n / n.factorial) := by rw [pow_succ', mul_pow]; ring

end GeometricGrowth

end EFun

/-! ### Checks on small sequences -/

example : coeff 2 (ePowerSeries fun _ : ℕ ↦ (1 : ℂ)) = 1 / 2 := by
  norm_num [coeff_ePowerSeries, Nat.factorial]

example : ePowerSeries (Pi.single 2 (1 : ℂ)) = monomial 2 (1 / 2) := by
  rw [ePowerSeries_single]
  norm_num [Nat.factorial]

example (z : ℂ) : eFun (Pi.single 1 (1 : ℂ)) z = z := by
  simp

example (c z : ℂ) : eFun (Pi.single 0 c) z = c := by
  simp

example : hurwitzMul (Pi.single 1 (1 : ℕ)) (Pi.single 1 1) 2 = 2 := by
  decide

end TauCeti
