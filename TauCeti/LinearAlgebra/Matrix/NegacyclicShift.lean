/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The negacyclic shift matrix

`TauCeti.negacyclicShift R n` is the `n × n` matrix of the linear map sending the standard basis
vector `eⱼ` to `eⱼ₊₁` for `j + 1 < n`, and the last one `e_{n-1}` to `-e₀`. For `n ≥ 1` it is
the companion matrix of `X ^ n + 1`: its `n`-th power is `-1`, and `e₀` is a cyclic vector, since
its first `n` images `e₀, …, e_{n-1}` are the standard basis. Consequently, for `n ≥ 1`, its
characteristic polynomial is `X ^ n + 1`, and, when moreover `-1 ≠ 1`, it has order `2 * n`.

It is the Coxeter element of the Weyl group of type `Bₙ` (or `Cₙ`) acting on the classical
lattice `ℤ ^ n`, a signed `n`-cycle.

## Main results

* `TauCeti.negacyclicShift_pow_apply`: the entries of the powers `negacyclicShift R n ^ i` with
  `i ≤ n`.
* `TauCeti.negacyclicShift_pow_self`: `negacyclicShift R n ^ n = -1`.
* `TauCeti.charpoly_negacyclicShift`: for `n ≥ 1`, the characteristic polynomial is `X ^ n + 1`.
* `TauCeti.orderOf_negacyclicShift`: for `n ≥ 1`, the order is `2 * n` when `2 ≠ 0` in `R`.
-/

public section

open Matrix Polynomial

namespace TauCeti

variable (R : Type*) (n : ℕ)

/-- The negacyclic shift: the matrix of `eⱼ ↦ eⱼ₊₁` for `j + 1 < n` and `e_{n-1} ↦ -e₀`. -/
def negacyclicShift [Ring R] : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun k j =>
    if (k : ℕ) = j + 1 then 1 else if (k : ℕ) = 0 ∧ (j : ℕ) + 1 = n then -1 else 0

variable {R n}

section Ring

variable [Ring R]

@[simp]
theorem negacyclicShift_apply (k j : Fin n) :
    negacyclicShift R n k j =
      if (k : ℕ) = j + 1 then 1 else if (k : ℕ) = 0 ∧ (j : ℕ) + 1 = n then -1 else 0 :=
  (rfl)

/-- An entry of the negacyclic shift vanishes unless `k = j + 1`, or `k = 0` and `j` is the last
index. -/
theorem negacyclicShift_apply_eq_zero {k j : Fin n} (h₁ : (k : ℕ) ≠ j + 1)
    (h₂ : ¬((k : ℕ) = 0 ∧ (j : ℕ) + 1 = n)) : negacyclicShift R n k j = 0 := by
  simp only [negacyclicShift_apply, h₁, h₂, ite_false]

/-- Multiplying on the right by the negacyclic shift moves column `j + 1` to column `j`, and the
negated column `0` to the last column. -/
theorem mul_negacyclicShift_apply {m : Type*} (M : Matrix m (Fin n) R) (k : m) (j : Fin n) :
    (M * negacyclicShift R n) k j =
      if h : (j : ℕ) + 1 < n then M k ⟨j + 1, h⟩ else -M k ⟨0, j.pos⟩ := by
  rw [Matrix.mul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j + 1, h⟩ (fun l _ hl => by
      rw [negacyclicShift_apply_eq_zero (fun h' => hl (Fin.ext h')) (by omega), mul_zero])
      (by simp)]
    simp [negacyclicShift_apply]
  · rw [Finset.sum_eq_single ⟨0, j.pos⟩ (fun l _ hl => by
      have hl' : (l : ℕ) ≠ 0 := fun h' => hl (Fin.ext h')
      rw [negacyclicShift_apply_eq_zero (by omega) (by omega), mul_zero]) (by simp)]
    simp [negacyclicShift_apply]
    omega

/-- The entries of the powers of the negacyclic shift, up to the `n`-th: `eⱼ ↦ eⱼ₊ᵢ` while
`j + i < n`, and `eⱼ ↦ -eⱼ₊ᵢ₋ₙ` after wrapping around once. -/
theorem negacyclicShift_pow_apply {i : ℕ} (hi : i ≤ n) (k j : Fin n) :
    (negacyclicShift R n ^ i) k j =
      if (j : ℕ) + i < n then (if (k : ℕ) = j + i then 1 else 0)
      else if (k : ℕ) + n = j + i then -1 else 0 := by
  induction i generalizing j with
  | zero => simp [Matrix.one_apply, Fin.ext_iff]
  | succ i ih =>
    rw [pow_succ, mul_negacyclicShift_apply]
    by_cases h : (j : ℕ) + 1 < n
    · rw [dite_eq_left h, ih (by omega)]
      simp only [show (j : ℕ) + 1 + i = j + (i + 1) by omega]
    · rw [dite_eq_right h, ih (by omega)]
      have := j.isLt
      simp only [zero_add, show i < n by omega, ite_true, show ¬(j : ℕ) + (i + 1) < n by omega,
        ite_false]
      split_ifs <;> grind

/-- The `n`-th power of the negacyclic shift is `-1`. -/
theorem negacyclicShift_pow_self : negacyclicShift R n ^ n = -1 := by
  ext k j
  rw [negacyclicShift_pow_apply le_rfl, Matrix.neg_apply, Matrix.one_apply]
  have hkj : (k : ℕ) + n = j + n ↔ k = j := by rw [Fin.ext_iff]; omega
  simp only [show ¬(j : ℕ) + n < n by omega, ite_false, hkj]
  split_ifs <;> simp

/-- `e₀` is a cyclic vector: for `i < n`, the `i`-th power of the negacyclic shift sends `e₀` to
`eᵢ`. -/
theorem negacyclicShift_pow_apply_zero {i : ℕ} (hi : i < n) (k : Fin n) :
    (negacyclicShift R n ^ i) k ⟨0, by omega⟩ = if (k : ℕ) = i then 1 else 0 := by
  rw [negacyclicShift_pow_apply hi.le]
  simp [hi]

end Ring

/-- **The characteristic polynomial of the negacyclic shift is `X ^ n + 1`.** -/
theorem charpoly_negacyclicShift [CommRing R] (hn : 0 < n) :
    (negacyclicShift R n).charpoly = X ^ n + 1 := by
  nontriviality R
  set N := negacyclicShift R n
  have hmonic : (X ^ n + 1 : R[X]).Monic := by
    rw [← C_1]
    exact monic_X_pow_add_C 1 hn.ne'
  -- The difference of two monic polynomials of degree `n` has degree less than `n`.
  set q := N.charpoly - (X ^ n + 1)
  have hdeg : q.degree < n := by
    have h := degree_sub_lt_left (p := N.charpoly) (q := X ^ n + 1)
      (by rw [charpoly_degree_eq_dim, Fintype.card_fin, ← C_1, degree_X_pow_add_C hn])
      (charpoly_monic N).ne_zero (by rw [(charpoly_monic N).leadingCoeff, hmonic.leadingCoeff])
    rwa [charpoly_degree_eq_dim, Fintype.card_fin] at h
  -- By Cayley–Hamilton, `q` annihilates `N`, and evaluating at the cyclic vector `e₀` reads off
  -- its coefficients.
  have hq : aeval N q = 0 := by
    simp [q, aeval_self_charpoly, N, negacyclicShift_pow_self]
  have hnat : q.natDegree < n := by
    by_cases hq0 : q = 0
    · simpa [hq0] using hn
    · exact (natDegree_lt_iff_degree_lt hq0).2 hdeg
  have hcoeff : ∀ m, q.coeff m = 0 := by
    intro m
    by_cases hm : m < n
    · have h := congr_fun₂ hq ⟨m, hm⟩ ⟨0, hn⟩
      rw [aeval_eq_sum_range' hnat, Matrix.sum_apply, Finset.sum_congr rfl fun i hi => by
        rw [Matrix.smul_apply, negacyclicShift_pow_apply_zero (Finset.mem_range.1 hi),
          smul_eq_mul]] at h
      simpa [hm] using h
    · exact coeff_eq_zero_of_degree_lt (hdeg.trans_le (by exact_mod_cast not_lt.1 hm))
  refine sub_eq_zero.1 ?_
  ext m
  rw [hcoeff m, coeff_zero]

/-- **The negacyclic shift has order `2 * n`** over a ring in which `2 ≠ 0`. -/
theorem orderOf_negacyclicShift [Ring R] [NeZero (2 : R)] (hn : 0 < n) :
    orderOf (negacyclicShift R n) = 2 * n := by
  have hne : (-1 : R) ≠ 1 := fun h => NeZero.ne (2 : R) (by
    rw [← one_add_one_eq_two]; nth_rw 1 [← h]; exact neg_add_cancel 1)
  refine (orderOf_eq_iff (by omega)).2 ⟨by rw [pow_mul', negacyclicShift_pow_self]; simp, ?_⟩
  intro d hd hd0 h
  have h00 := congr_fun₂ h ⟨0, hn⟩ ⟨0, hn⟩
  rw [one_apply_eq] at h00
  by_cases hdn : d ≤ n
  · rw [negacyclicShift_pow_apply hdn] at h00
    simp only [zero_add] at h00
    split_ifs at h00 <;> grind
  · rw [show d = n + (d - n) by omega, pow_add, negacyclicShift_pow_self, neg_one_mul,
      Matrix.neg_apply, negacyclicShift_pow_apply (by omega)] at h00
    simp only [zero_add] at h00
    split_ifs at h00 <;> grind

end TauCeti
