/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.Basic

/-!
# Factorial-divided formal power series and Hurwitz convolution

Purely formal algebra of Hurwitz (binomial) convolution `hurwitzMul` and the exponential generating
series `ePowerSeries a = ∑ₙ (aₙ / n!) Xⁿ`, with no analytic or arithmetic hypotheses.

## Main definitions

* `TauCeti.hurwitzMul`: binomial (Hurwitz) convolution `(a, b) ↦ (n ↦ ∑ k ≤ n, C(n, k) aₖ bₙ₋ₖ)`.
* `TauCeti.ePowerSeries`: the factorial-divided formal power series `∑ₙ (aₙ / n!) Xⁿ`.

## Main results

* `TauCeti.hurwitzMul_comm`, `TauCeti.hurwitzMul_assoc`, `TauCeti.hurwitzMul_succ`: commutativity,
  associativity, and the shift Leibniz rule for Hurwitz convolution.
* `TauCeti.single_hurwitzMul`, `TauCeti.hurwitzMul_single`: action of single-term sequences.
* `TauCeti.ePowerSeries_hurwitzMul`, `TauCeti.derivative_ePowerSeries`,
  `TauCeti.hasseDeriv_ePowerSeries`: compatibility of `ePowerSeries` with products, formal
  differentiation, and Hasse derivatives.

## References

* F. Beukers, *E-functions and G-functions*, Arizona Winter School, 2008, §3.1–3.2.
* A. B. Shidlovskii, *Transcendental Numbers*, de Gruyter, 1989, Chapter 3, §1.
-/

public section

open Finset PowerSeries

namespace TauCeti

/-! ### Hurwitz (binomial) convolution -/

section HurwitzMul

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The *Hurwitz* (binomial) product of `a, b : ℕ → R`:
`(hurwitzMul a b) n = ∑ k ∈ range (n + 1), n.choose k * a k * b (n - k)`. -/
def hurwitzMul (a b : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ range (n + 1), (n.choose k : R) * a k * b (n - k)

/-- Unfolding `hurwitzMul` at index `n`. -/
theorem hurwitzMul_apply (a b : ℕ → R) (n : ℕ) :
    hurwitzMul a b n = ∑ k ∈ range (n + 1), (n.choose k : R) * a k * b (n - k) := (rfl)

/-- Antidiagonal presentation of `hurwitzMul`. -/
theorem hurwitzMul_eq_sum_antidiagonal (a b : ℕ → R) (n : ℕ) :
    hurwitzMul a b n =
      ∑ ij ∈ antidiagonal n, ((ij.1 + ij.2).choose ij.1 : R) * a ij.1 * b ij.2 := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ ((i + j).choose i : R) * a i * b j) n,
    hurwitzMul_apply]
  exact sum_congr rfl fun k hk ↦ by rw [Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hk))]

/-- Left multiplication by the zero sequence gives zero. -/
@[simp] theorem zero_hurwitzMul (b : ℕ → R) : hurwitzMul 0 b = 0 := by
  ext n; simp [hurwitzMul_apply]

/-- Right multiplication by the zero sequence gives zero. -/
@[simp] theorem hurwitzMul_zero (a : ℕ → R) : hurwitzMul a 0 = 0 := by
  ext n; simp [hurwitzMul_apply]

/-- At `n = 0`, the Hurwitz product is `a 0 * b 0`. -/
@[simp] theorem hurwitzMul_apply_zero (a b : ℕ → R) : hurwitzMul a b 0 = a 0 * b 0 := by
  simp [hurwitzMul_apply]

/-- Left distributivity of `hurwitzMul` over addition. -/
theorem add_hurwitzMul (a₁ a₂ b : ℕ → R) :
    hurwitzMul (a₁ + a₂) b = hurwitzMul a₁ b + hurwitzMul a₂ b := by
  ext n; simp only [Pi.add_apply, hurwitzMul_apply, ← sum_add_distrib]
  exact sum_congr rfl fun k _ ↦ by rw [mul_add, add_mul]

/-- Right distributivity of `hurwitzMul` over addition. -/
theorem hurwitzMul_add (a b₁ b₂ : ℕ → R) :
    hurwitzMul a (b₁ + b₂) = hurwitzMul a b₁ + hurwitzMul a b₂ := by
  ext n; simp only [Pi.add_apply, hurwitzMul_apply, ← sum_add_distrib]
  exact sum_congr rfl fun k _ ↦ by rw [mul_add]

/-- Left Hurwitz multiplication by a sequence supported at a single index `k`. -/
@[simp]
theorem single_hurwitzMul (k : ℕ) (c : R) (b : ℕ → R) (n : ℕ) :
    hurwitzMul (Pi.single k c) b n = (n.choose k : R) * c * b (n - k) := by
  by_cases hkn : k ≤ n
  · rw [hurwitzMul_apply, sum_eq_single k (fun j _ hjk ↦ by simp [Pi.single_eq_of_ne hjk])
      (fun h ↦ absurd (mem_range.mpr (Nat.lt_succ_of_le hkn)) h)]
    simp
  · rw [hurwitzMul_apply, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkn), Nat.cast_zero,
      zero_mul, zero_mul]
    exact sum_eq_zero fun j hj ↦ by
      have := mem_range.mp hj; simp [Pi.single_eq_of_ne (by omega : j ≠ k)]

/-- Right Hurwitz multiplication by a sequence supported at a single index `k`. -/
@[simp]
theorem hurwitzMul_single (a : ℕ → R) (k : ℕ) (c : R) (n : ℕ) :
    hurwitzMul a (Pi.single k c) n = (n.choose k : R) * a (n - k) * c := by
  by_cases hkn : k ≤ n
  · rw [hurwitzMul_apply, sum_eq_single (n - k)
      (fun j hj hjnk ↦ by have := mem_range.mp hj; simp [Pi.single_eq_of_ne (by omega : n - j ≠ k)])
      (fun h ↦ absurd (mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n k))) h),
      Nat.sub_sub_self hkn, Pi.single_eq_same, Nat.choose_symm hkn]
  · rw [hurwitzMul_apply, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkn), Nat.cast_zero,
      zero_mul, zero_mul]
    exact sum_eq_zero fun j hj ↦ by
      have := mem_range.mp hj; simp [Pi.single_eq_of_ne (by omega : n - j ≠ k)]

/-- A sequence supported at `0` acts on the left by scalar multiplication. -/
theorem single_zero_hurwitzMul (c : R) (b : ℕ → R) (n : ℕ) :
    hurwitzMul (Pi.single 0 c) b n = c * b n := by simp

/-- A sequence supported at `0` acts on the right by scalar multiplication. -/
theorem hurwitzMul_single_zero (a : ℕ → R) (c : R) (n : ℕ) :
    hurwitzMul a (Pi.single 0 c) n = a n * c := by simp

/-- `Pi.single 0 1` is the left identity for `hurwitzMul`. -/
@[simp] theorem single_zero_one_hurwitzMul (b : ℕ → R) : hurwitzMul (Pi.single 0 1) b = b := by
  ext n; simp

/-- `Pi.single 0 1` is the right identity for `hurwitzMul`. -/
@[simp] theorem hurwitzMul_single_zero_one (a : ℕ → R) : hurwitzMul a (Pi.single 0 1) = a := by
  ext n; simp

/-- Ring homomorphisms commute with `hurwitzMul`. -/
theorem map_hurwitzMul (f : R →+* S) (a b : ℕ → R) (n : ℕ) :
    f (hurwitzMul a b n) = hurwitzMul (f ∘ a) (f ∘ b) n := by simp [hurwitzMul_apply]

/-- **Associativity of Hurwitz multiplication**, proved from the trinomial identity
`n.choose m * m.choose k = n.choose k * (n - k).choose (m - k)`. -/
theorem hurwitzMul_assoc (a b c : ℕ → R) :
    hurwitzMul (hurwitzMul a b) c = hurwitzMul a (hurwitzMul b c) := by
  ext n; simp only [hurwitzMul_apply]
  calc ∑ m ∈ range (n + 1), (n.choose m : R) *
          (∑ k ∈ range (m + 1), (m.choose k : R) * a k * b (m - k)) * c (n - m)
      = ∑ m ∈ range (n + 1), ∑ k ∈ range (m + 1),
          ((n.choose m * m.choose k : ℕ) : R) * a k * b (m - k) * c (n - m) :=
        sum_congr rfl fun m _ ↦ by
          rw [mul_sum, sum_mul]
          exact sum_congr rfl fun k _ ↦ by push_cast; simp only [mul_assoc]
    _ = ∑ k ∈ range (n + 1), ∑ j ∈ range (n - k + 1),
          ((n.choose k * (n - k).choose j : ℕ) : R) * a k * b j * c (n - k - j) := by
        -- Reindex `(m, k)` with `k ≤ m ≤ n` to `(k, j)` with `m = k + j` and `j ≤ n - k`.
        rw [sum_sigma', sum_sigma']
        refine sum_bij (fun p _ ↦ ⟨p.2, p.1 - p.2⟩) ?_ ?_ ?_ ?_
        · rintro ⟨m, k⟩ hp; simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at hp ⊢; omega
        · rintro ⟨m₁, k₁⟩ hp₁ ⟨m₂, k₂⟩ hp₂ heq
          simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at hp₁ hp₂
          simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
          obtain ⟨rfl, hsub⟩ := heq; congr; omega
        · rintro ⟨k, j⟩ hp; simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at hp
          exact ⟨⟨k + j, k⟩, by simp only [mem_sigma, mem_range, Nat.lt_succ_iff]; omega, by simp⟩
        · rintro ⟨m, k⟩ hp; simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at hp
          have hsub : n - m = n - k - (m - k) := by omega
          rw [Nat.choose_mul hp.2, hsub]
    _ = ∑ k ∈ range (n + 1), (n.choose k : R) * a k *
          ∑ j ∈ range (n - k + 1), ((n - k).choose j : R) * b j * c (n - k - j) :=
        sum_congr rfl fun k _ ↦ by
          rw [mul_sum]; refine sum_congr rfl fun j _ ↦ ?_
          push_cast; simp only [mul_assoc]
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
  have hsub : n - (k + 1) + 1 = n - k := by omega
  rw [hsub]

/-- Hurwitz product of two constant-one sequences: `(hurwitzMul 1 1) n = 2 ^ n`. -/
@[simp] theorem hurwitzMul_const_one (n : ℕ) :
    hurwitzMul (fun _ ↦ (1 : R)) (fun _ ↦ 1) n = 2 ^ n := by
  simp only [hurwitzMul_apply, mul_one, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow,
    Nat.cast_ofNat]

/-- Hurwitz multiplication is commutative over a commutative semiring. -/
theorem hurwitzMul_comm {R : Type*} [CommSemiring R] (a b : ℕ → R) :
    hurwitzMul a b = hurwitzMul b a := by
  ext n; rw [hurwitzMul_apply, ← sum_range_reflect]
  refine sum_congr rfl fun k hk ↦ ?_
  have hle : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, Nat.sub_sub_self hle, Nat.choose_symm hle]; ring

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
    ePowerSeries a = PowerSeries.mk fun n ↦ a n / n.factorial := (rfl)

/-- The `n`-th coefficient of `ePowerSeries a` is `a n / n!`. -/
@[simp] theorem coeff_ePowerSeries (a : ℕ → K) (n : ℕ) :
    coeff n (ePowerSeries a) = a n / n.factorial := coeff_mk n _

/-- The constant coefficient of `ePowerSeries a` is `a 0`. -/
@[simp] theorem constantCoeff_ePowerSeries (a : ℕ → K) :
    constantCoeff (ePowerSeries a) = a 0 := by simp [← coeff_zero_eq_constantCoeff_apply]

/-- Zero sequence gives the zero power series. -/
@[simp] theorem ePowerSeries_zero : ePowerSeries (0 : ℕ → K) = 0 := by ext n; simp

/-- `ePowerSeries` preserves addition. -/
theorem ePowerSeries_add (a b : ℕ → K) :
    ePowerSeries (a + b) = ePowerSeries a + ePowerSeries b := by ext n; simp [add_div]

/-- `ePowerSeries` preserves negation. -/
theorem ePowerSeries_neg (a : ℕ → K) : ePowerSeries (-a) = -ePowerSeries a := by
  ext n; simp [neg_div]

/-- `ePowerSeries` preserves subtraction. -/
theorem ePowerSeries_sub (a b : ℕ → K) :
    ePowerSeries (a - b) = ePowerSeries a - ePowerSeries b := by ext n; simp [sub_div]

/-- `ePowerSeries` commutes with scalar multiplication. -/
theorem ePowerSeries_smul (c : K) (a : ℕ → K) :
    ePowerSeries (c • a) = c • ePowerSeries a := by ext n; simp [mul_div_assoc]

/-- A sequence supported at a single index `k` gives the monomial `(c / k!) Xᵏ`. -/
theorem ePowerSeries_single (k : ℕ) (c : K) :
    ePowerSeries (Pi.single k c) = monomial k (c / k.factorial) := by
  ext n; rw [coeff_ePowerSeries, coeff_monomial]
  split_ifs with h <;> [subst h; skip] <;> simp [Pi.single_eq_of_ne, *]

/-- Field homomorphisms act coefficientwise on `ePowerSeries`. -/
theorem map_ePowerSeries {L : Type*} [Field L] (f : K →+* L) (a : ℕ → K) :
    PowerSeries.map f (ePowerSeries a) = ePowerSeries (f ∘ a) := by ext n; simp

/-- Rescaling the variable of `ePowerSeries a` by `c` multiplies `a n` by `c ^ n`. -/
theorem rescale_ePowerSeries (c : K) (a : ℕ → K) :
    rescale c (ePowerSeries a) = ePowerSeries fun n ↦ c ^ n * a n := by
  ext n; simp [coeff_rescale, mul_div_assoc]

section CharZero

variable [CharZero K]

/-- Over a field of characteristic zero, `ePowerSeries` is injective. -/
@[simp] theorem ePowerSeries_eq_iff {a b : ℕ → K} : ePowerSeries a = ePowerSeries b ↔ a = b := by
  refine ⟨fun h ↦ funext fun n ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hn : a n / n.factorial = b n / n.factorial := by
    simpa only [coeff_ePowerSeries] using congrArg (coeff n) h
  exact (div_left_inj₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))).mp hn

/-- Constant-one data give the formal exponential series `PowerSeries.exp K`. -/
@[simp] theorem ePowerSeries_one : ePowerSeries (fun _ ↦ (1 : K)) = PowerSeries.exp K := by
  ext n; simp

/-- Constant data `c` give `C c * exp K`. -/
theorem ePowerSeries_const (c : K) : ePowerSeries (fun _ ↦ c) = C c * PowerSeries.exp K := by
  ext n; simp [coeff_C_mul, div_eq_mul_inv]

/-- Formal differentiation of `ePowerSeries a` shifts the sequence by one step. -/
@[simp] theorem derivative_ePowerSeries (a : ℕ → K) :
    d⁄dX (ePowerSeries a) = ePowerSeries fun n ↦ a (n + 1) := by
  ext n
  rw [coeff_derivative, coeff_ePowerSeries, coeff_ePowerSeries, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hne : (n : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hfact : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

/-- The `k`-th formal derivative of `ePowerSeries a` shifts the sequence by `k`. -/
@[simp] theorem iterate_derivative_ePowerSeries (a : ℕ → K) (k : ℕ) :
    (d⁄dX)^[k] (ePowerSeries a) = ePowerSeries fun n ↦ a (n + k) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, derivative_ePowerSeries, ih]; simp [add_assoc]

/-- The `k`-th Hasse derivative of `ePowerSeries a` is `(k!)⁻¹` times the `k`-shifted series. -/
theorem hasseDeriv_ePowerSeries (a : ℕ → K) (k : ℕ) :
    PowerSeries.hasseDeriv k (ePowerSeries a) =
      (k.factorial : K)⁻¹ • ePowerSeries fun n ↦ a (n + k) := by
  ext n; rw [coeff_hasseDeriv, coeff_ePowerSeries, coeff_smul, coeff_ePowerSeries, smul_eq_mul]
  have hchoose : ((n + k).factorial : K) =
      ((n + k).choose k : K) * (n.factorial : K) * (k.factorial : K) := by
    exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial n k).symm
  have hc : ((n + k).choose k : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_left k n)).ne'
  have hk : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [hchoose]; field_simp

/-- **Cauchy product of factorial-divided series.** Hurwitz multiplication of coefficient sequences
corresponds to multiplication of `ePowerSeries`. -/
@[simp] theorem ePowerSeries_hurwitzMul (a b : ℕ → K) :
    ePowerSeries (hurwitzMul a b) = ePowerSeries a * ePowerSeries b := by
  ext n
  rw [coeff_ePowerSeries, coeff_mul, hurwitzMul_eq_sum_antidiagonal, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun ij hij ↦ ?_
  have hsum : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
  have hchoose : (n.factorial : K) =
      ((ij.1 + ij.2).choose ij.1 : K) * (ij.1.factorial : K) * (ij.2.factorial : K) := by
    rw [← hsum]
    have hnat := (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right ij.1 ij.2)).symm
    rw [Nat.add_sub_cancel_left] at hnat; exact_mod_cast hnat
  have hc : ((ij.1 + ij.2).choose ij.1 : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right ij.1 ij.2)).ne'
  have h1 : (ij.1.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (ij.2.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [coeff_ePowerSeries, coeff_ePowerSeries, hchoose]; field_simp

end CharZero

end EPowerSeries

/-! ### Checks on small sequences -/

example : coeff 2 (ePowerSeries fun _ : ℕ ↦ (1 : ℚ)) = 1 / 2 := by
  norm_num [coeff_ePowerSeries, Nat.factorial]
example : ePowerSeries (Pi.single 2 (1 : ℚ)) = monomial 2 (1 / 2) := by
  rw [ePowerSeries_single]; norm_num [Nat.factorial]
example : hurwitzMul (Pi.single 1 (1 : ℕ)) (Pi.single 1 1) 2 = 2 := by decide

end TauCeti
