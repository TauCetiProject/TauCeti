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
definite (`Matrix.posDef_gcd_divisors`). Euler's identity `∑ d ∣ n, φ(d) = n` factors it as
`Bᴴ diag(φ) B`, where `B i j = 1` when `i ∣ j` and zero otherwise. The divisibility matrix is
triangular with diagonal entries one.

The gcd matrix of any finite family of distinct positive integers is a principal submatrix of
such a divisor matrix, hence positive definite as well (`Matrix.posDef_gcd`). The Schur product
theorem then gives positive definiteness of every positive integral entrywise power
(`Matrix.posDef_gcd_pow`), including the squared-gcd matrix used to distinguish cusp constant
terms of corrected weight-two Eisenstein series.

## References

* H. J. S. Smith, *On the value of a certain arithmetical determinant*, Proceedings of the
  London Mathematical Society, s1-7 (1875), 208–213.
* S. Beslin and S. Ligh, *Greatest common divisor matrices*, Linear Algebra and its
  Applications 118 (1989), 69–76.
-/

public noncomputable section

open Finset
open scoped ComplexOrder

namespace Matrix

section StarOrderedRing

variable {R : Type*} [CommRing R] [IsDomain R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

/-- The gcd matrix on the positive divisors of `N` is positive definite, over the real or
complex numbers and more generally over any star-ordered commutative domain. For `N = 0` the
indexing finset is empty. -/
theorem posDef_gcd_divisors (N : ℕ) :
    PosDef (of fun i j : N.divisors ↦ (Nat.gcd i.val j.val : R)) := by
  classical
  let B : Matrix N.divisors N.divisors R := of fun i j ↦ if i.val ∣ j.val then 1 else 0
  have hB : B.IsUpperTriangular := fun i j hji ↦ ite_eq_right fun hij ↦
    (Nat.le_of_dvd (Nat.pos_of_mem_divisors j.property) hij).not_gt hji
  have hdet : B.det = 1 := by simp [det_of_isUpperTriangular hB, B]
  have hdiag : (diagonal fun i : N.divisors ↦ (Nat.totient i.val : R)).PosDef :=
    .diagonal fun i ↦ Nat.cast_pos'.mpr (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors i.property))
  have hfactor : Bᴴ * diagonal (fun i : N.divisors ↦ (Nat.totient i.val : R)) * B =
      of fun i j : N.divisors ↦ (Nat.gcd i.val j.val : R) := by
    ext i j
    have hfilter : {d ∈ N.divisors | d ∣ i.val ∧ d ∣ j.val} =
        (Nat.gcd i.val j.val).divisors := by
      simpa only [Nat.dvd_gcd_iff] using Nat.divisors_filter_dvd_of_dvd
        (Nat.ne_zero_of_mem_divisors i.property)
        ((Nat.gcd_dvd_left i.val j.val).trans (Nat.dvd_of_mem_divisors i.property))
    rw [Matrix.mul_apply]
    simp only [mul_diagonal, conjTranspose_apply, B, of_apply, apply_ite star,
      star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, ← ite_and]
    rw [sum_coe_sort N.divisors
      fun d ↦ if d ∣ j.val ∧ d ∣ i.val then (Nat.totient d : R) else 0]
    simp_rw [and_comm, ← sum_filter, hfilter, ← Nat.cast_sum, Nat.sum_totient]
  rw [← hfactor]
  exact hdiag.conjTranspose_mul_mul_same
    (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det B).mpr (hdet ▸ isUnit_one)))

/-- The gcd matrix of finitely many distinct positive integers `f i` is positive definite, over
the real or complex numbers and more generally over any star-ordered commutative domain. -/
theorem posDef_gcd {ι : Type*} [Finite ι] {f : ι → ℕ} (hf : Function.Injective f)
    (hf₀ : ∀ i, f i ≠ 0) : PosDef (of fun i j ↦ (Nat.gcd (f i) (f j) : R)) := by
  have := Fintype.ofFinite ι
  have hmem (i : ι) : f i ∈ (∏ i, f i).divisors :=
    Nat.mem_divisors.mpr
      ⟨dvd_prod_of_mem f (mem_univ i), prod_ne_zero_iff.mpr fun i _ ↦ hf₀ i⟩
  exact (posDef_gcd_divisors (∏ i, f i)).submatrix (e := fun i ↦ ⟨f i, hmem i⟩)
    fun i j hij ↦ hf (Subtype.ext_iff.mp hij)

end StarOrderedRing

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Every positive integral entrywise power of the gcd matrix of finitely many distinct
positive integers is positive definite, over either the real or complex numbers. -/
theorem posDef_gcd_pow {ι : Type*} [Finite ι] {f : ι → ℕ} (hf : Function.Injective f)
    (hf₀ : ∀ i, f i ≠ 0) {r : ℕ} (hr : r ≠ 0) :
    PosDef (of fun i j ↦ (Nat.gcd (f i) (f j) : 𝕜) ^ r) := by
  rw [← Nat.one_le_iff_ne_zero] at hr
  induction r, hr using Nat.le_induction with
  | base => simpa using posDef_gcd (R := 𝕜) hf hf₀
  | succ r _ ih =>
    convert ih.hadamard (posDef_gcd (R := 𝕜) hf hf₀) using 1
    ext i j
    simp [pow_succ]

end Matrix
