/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Positive definiteness of gcd matrices

The matrix indexed by the positive divisors of `N`, with entry `gcd(i,j)`, is positive
definite. Euler's identity `∑ d ∣ n, φ(d) = n` factors it as `Bᴴ diag(φ) B`, where
`B i j = 1` when `i ∣ j` and zero otherwise. The divisibility matrix is triangular with
diagonal entries one. The Schur product theorem then gives positive definiteness of every
positive integral entrywise power, including the squared-gcd matrix used to distinguish
cusp constant terms of corrected weight-two Eisenstein series.

## References

* H. J. S. Smith, *On the value of a certain arithmetical determinant*, Proceedings of the
  London Mathematical Society, s1-7 (1875), 208–213.
-/

public noncomputable section

open Finset
open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The gcd matrix on the positive divisors of `N` is positive definite, over either
the real or complex numbers. For `N = 0` the indexing finset is empty. -/
theorem posDef_gcd_divisors (N : ℕ) :
    PosDef (of fun i j : N.divisors ↦ (Nat.gcd i.val j.val : 𝕜)) := by
  classical
  let B : Matrix N.divisors N.divisors 𝕜 := of fun i j ↦ if i.val ∣ j.val then 1 else 0
  have hB : B.IsUpperTriangular := by
    intro i j hji
    apply ite_eq_right
    intro hij
    have := Nat.le_of_dvd (Nat.pos_of_mem_divisors j.property) hij
    exact (not_le_of_gt hji) this
  have hdet : B.det = 1 := by
    rw [det_of_isUpperTriangular hB]
    simp [B]
  have hdiag : (diagonal (fun i : N.divisors ↦ (Nat.totient i.val : 𝕜))).PosDef :=
    PosDef.diagonal fun i ↦ by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors i.property))
  have hfactor : Bᴴ * diagonal (fun i : N.divisors ↦ (Nat.totient i.val : 𝕜)) * B =
      (of fun i j : N.divisors ↦ (Nat.gcd i.val j.val : 𝕜)) := by
    ext i j
    rw [mul_apply]
    simp only [mul_diagonal, conjTranspose_apply]
    simp only [B, of_apply, apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_coe_sort N.divisors
      (fun d : ℕ ↦ if d ∣ j.val then if d ∣ i.val then (Nat.totient d : 𝕜) else 0 else 0)]
    have hfilter : N.divisors.filter (fun d ↦ d ∣ i.val ∧ d ∣ j.val) =
        (Nat.gcd i.val j.val).divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      have hN := Nat.ne_zero_of_mem_divisors i.property
      have hg : Nat.gcd i.val j.val ≠ 0 :=
        (Nat.gcd_pos_of_pos_left j.val (Nat.pos_of_mem_divisors i.property)).ne'
      constructor
      · tauto
      · intro hd
        exact ⟨⟨hd.1.1.trans (Nat.dvd_of_mem_divisors i.property), hN⟩, hd.1⟩
    simp_rw [← ite_and]
    simp_rw [and_comm]
    rw [← Finset.sum_filter, hfilter, ← Nat.cast_sum, Nat.sum_totient]
  rw [← hfactor]
  exact hdiag.conjTranspose_mul_mul_same
    (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det B).mpr (hdet ▸ isUnit_one)))

/-- Every positive integral entrywise power of the gcd matrix on the divisors of `N`
is positive definite. -/
theorem posDef_gcd_pow_divisors (N : ℕ) {r : ℕ} (hr : 0 < r) :
    PosDef (of fun i j : N.divisors ↦ (Nat.gcd i.val j.val : 𝕜) ^ r) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  clear hr
  induction r with
  | zero => simpa using (posDef_gcd_divisors (𝕜 := 𝕜) N)
  | succ r ih =>
    have hp : (of fun i j : N.divisors ↦ (Nat.gcd i.val j.val : 𝕜) ^ (r + 1).succ) =
        Matrix.hadamard (of fun i j : N.divisors ↦ (Nat.gcd i.val j.val : 𝕜) ^ r.succ)
          (of fun i j : N.divisors ↦ (Nat.gcd i.val j.val : 𝕜)) := by
      funext i j
      simp only [hadamard_apply, of_apply, pow_succ]
    rw [hp]
    exact ih.hadamard (posDef_gcd_divisors (𝕜 := 𝕜) N)

end Matrix
