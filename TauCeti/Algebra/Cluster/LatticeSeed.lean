/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Ring

/-!
# Signed mutation of weighted mutable lattice families

A mutable family consists of vectors in a fixed submodule whose positive integer multiples
lie in a second fixed submodule. It can contain repetitions and need not span. For an
alternating rational pairing integral on the required pairs, signed mutation preserves these
conditions. The two signs give mutually inverse transformations, and two positive
mutations act on each vector by the integral transvection in the pivot direction.

## References

* M. Gross, P. Hacking and S. Keel, *Birational geometry of cluster algebras*,
  Algebraic Geometry 2 (2015), §2, equations (2.3)–(2.4).
-/

public section

namespace TauCeti

variable {K N : Type*} [AddCommGroup N]

/-- An indexed weighted mutable family in two fixed submodules. The weight times each vector
belongs to the integral submodule. -/
@[ext]
structure WeightedLatticeFamily (U L : Submodule ℤ N) (K : Type*) where
  /-- The mutable vectors, regarded as elements of the mutable submodule. -/
  vector : K → U
  /-- The integral weight in each direction. -/
  weight : K → ℤ
  /-- Each weight is positive. -/
  weight_pos : ∀ i, 0 < weight i
  /-- The weighted vectors belong to the integral submodule. -/
  weight_smul_mem : ∀ i, weight i • (vector i : N) ∈ L

namespace WeightedLatticeFamily

variable {U L : Submodule ℤ N}

/-- The integral pairing entry obtained by evaluating a vector against the weighted
mutable vector in direction `k`. -/
noncomputable def weightedPairing (s : WeightedLatticeFamily U L K)
    (B : N →ₗ[ℤ] N →ₗ[ℤ] ℚ)
    (hB : ∀ x y, y ∈ U ⊓ L → ∃ n : ℤ, B x y = n) (x : N) (k : K) : ℤ :=
  (hB x _ (Submodule.mem_inf.mpr
    ⟨U.smul_mem (s.weight k) (s.vector k).property, s.weight_smul_mem k⟩)).choose

/-- Casting the integral entry back to the rationals recovers the original pairing when the
pairing is integer-valued against the intersection of the two submodules. -/
@[simp]
theorem weightedPairing_intCast (s : WeightedLatticeFamily U L K)
    (B : N →ₗ[ℤ] N →ₗ[ℤ] ℚ)
    (hB : ∀ x y, y ∈ U ⊓ L → ∃ n : ℤ, B x y = n) (x : N) (k : K) :
    (s.weightedPairing B hB x k : ℚ) = B x (s.weight k • (s.vector k : N)) := by
  exact (hB x _ (Submodule.mem_inf.mpr
    ⟨U.smul_mem (s.weight k) (s.vector k).property, s.weight_smul_mem k⟩)).choose_spec.symm

variable (s : WeightedLatticeFamily U L K) (B : N →ₗ[ℤ] N →ₗ[ℤ] ℚ)
  (hB : ∀ x y, y ∈ U ⊓ L → ∃ n : ℤ, B x y = n)

/-- The positive weights skew-symmetrize the matrix of integral pairing entries, with
row index the unweighted vector and column index the weighted vector. -/
theorem weight_mul_weightedPairing (hAlt : B.IsAlt) (i k : K) :
    s.weight i * s.weightedPairing B hB (s.vector i) k =
      -(s.weight k * s.weightedPairing B hB (s.vector k) i) := by
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_mul, Int.cast_neg, s.weightedPairing_intCast B hB, map_zsmul,
    zsmul_eq_mul]
  rw [← hAlt.neg (s.vector i : N) (s.vector k : N)]
  ring

private theorem weight_smul_signedPositivePart_mem (hAlt : B.IsAlt) (sign : ℤ) (i k : K) :
    s.weight i • (max (sign * s.weightedPairing B hB (s.vector i) k) 0 •
      (s.vector k : N)) ∈ L := by
  have hm : s.weight i * (sign * s.weightedPairing B hB (s.vector i) k) =
      s.weight k * (-sign * s.weightedPairing B hB (s.vector k) i) := by
    calc
      _ = sign * (s.weight i * s.weightedPairing B hB (s.vector i) k) := by ring
      _ = _ := by rw [s.weight_mul_weightedPairing B hB hAlt i k]; ring
  rcases le_or_gt 0 (sign * s.weightedPairing B hB (s.vector i) k) with h | h
  · rw [max_eq_left h, ← mul_smul, hm, mul_comm (s.weight k), mul_smul]
    exact L.smul_mem _ (s.weight_smul_mem k)
  · rw [max_eq_right h.le, zero_smul, smul_zero]
    exact L.zero_mem

open scoped Classical in
/-- Mutate the family at `k`, negating the chosen vector and adding the positive part of
the signed pairing entry times that vector at other indices. The signs `1` and `-1`
give the positive and negative mutations. The weights are unchanged. -/
noncomputable def signedMutation (hAlt : B.IsAlt) (sign : ℤ) (k : K) :
    WeightedLatticeFamily U L K where
  vector i :=
    if i = k then -s.vector k
    else s.vector i + max (sign * s.weightedPairing B hB (s.vector i) k) 0 • s.vector k
  weight := s.weight
  weight_pos := s.weight_pos
  weight_smul_mem i := by
    by_cases hik : i = k
    · subst i
      simpa using L.neg_mem (s.weight_smul_mem k)
    · simp only [ite_eq_right hik, Submodule.coe_add, Submodule.coe_smul, smul_add]
      exact L.add_mem (s.weight_smul_mem i)
        (s.weight_smul_signedPositivePart_mem B hB hAlt sign i k)

/-- Signed mutation preserves every weight. -/
@[simp]
theorem signedMutation_weight (hAlt : B.IsAlt) (sign : ℤ) (k i : K) :
    (s.signedMutation B hB hAlt sign k).weight i = s.weight i := by
  simp [signedMutation]

/-- Signed mutation negates its pivot vector. -/
@[simp]
theorem signedMutation_vector_self (hAlt : B.IsAlt) (sign : ℤ) (k : K) :
    (s.signedMutation B hB hAlt sign k).vector k = -s.vector k := by
  simp [signedMutation]

/-- Away from the pivot, signed mutation adds a multiple of the pivot vector. -/
@[simp]
theorem signedMutation_vector_of_ne (hAlt : B.IsAlt) (sign : ℤ) {i k : K} (hik : i ≠ k) :
    (s.signedMutation B hB hAlt sign k).vector i =
      s.vector i + max (sign * s.weightedPairing B hB (s.vector i) k) 0 • s.vector k := by
  simp [signedMutation, hik]

/-- The entries paired against the pivot negate under mutation, since the correction is a
multiple of the alternating pairing's isotropic pivot. -/
@[simp]
theorem signedMutation_weightedPairing_pivot (hAlt : B.IsAlt) (sign : ℤ) (i k : K) :
    (s.signedMutation B hB hAlt sign k).weightedPairing B hB
      ((s.signedMutation B hB hAlt sign k).vector i) k =
      -s.weightedPairing B hB (s.vector i) k := by
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_neg, weightedPairing_intCast _ B hB, signedMutation_weight,
    signedMutation_vector_self, Submodule.coe_neg, smul_neg, map_neg]
  rcases eq_or_ne i k with rfl | hik
  · simp [map_neg, hAlt.self_eq_zero]
  · rw [s.signedMutation_vector_of_ne B hB hAlt sign hik]
    simp [map_add, LinearMap.add_apply, hAlt.self_eq_zero]

/-- Applying a signed mutation and then the opposite signed mutation at the same pivot
recovers the original weighted family. -/
@[simp]
theorem signedMutation_signedMutation_neg (hAlt : B.IsAlt) (sign : ℤ) (k : K) :
    (s.signedMutation B hB hAlt sign k).signedMutation B hB hAlt (-sign) k = s := by
  apply WeightedLatticeFamily.ext
  · funext i
    rcases eq_or_ne i k with rfl | hik
    · simp
    rw [(s.signedMutation B hB hAlt sign k).signedMutation_vector_of_ne B hB hAlt (-sign) hik,
      s.signedMutation_weightedPairing_pivot B hB hAlt sign i k,
      s.signedMutation_vector_self B hB hAlt sign k,
      s.signedMutation_vector_of_ne B hB hAlt sign hik]
    simp [smul_neg, add_assoc]
  · funext i
    simp

/-- Applying two positive mutations sends each vector `x` to the transvection
`x + B(x, dₖ eₖ) • eₖ` in the pivot direction, with the pairing read as an integer. -/
theorem signedMutation_one_signedMutation_one_vector (hAlt : B.IsAlt) (k i : K) :
    ((s.signedMutation B hB hAlt 1 k).signedMutation B hB hAlt 1 k).vector i =
      s.vector i + s.weightedPairing B hB (s.vector i) k • s.vector k := by
  rcases eq_or_ne i k with rfl | hik
  · have hz : s.weightedPairing B hB (s.vector i) i = 0 := by
      apply Int.cast_injective (α := ℚ)
      rw [s.weightedPairing_intCast B hB]
      simp [hAlt.self_eq_zero]
    simp [hz]
  · rw [(s.signedMutation B hB hAlt 1 k).signedMutation_vector_of_ne B hB hAlt 1 hik,
      s.signedMutation_weightedPairing_pivot B hB hAlt 1 i k,
      s.signedMutation_vector_self B hB hAlt 1 k,
      s.signedMutation_vector_of_ne B hB hAlt 1 hik]
    simp only [one_mul, smul_neg, add_assoc]
    rw [← sub_eq_add_neg, ← sub_smul, max_zero_sub_max_neg_zero_eq_self]

end WeightedLatticeFamily

end TauCeti
