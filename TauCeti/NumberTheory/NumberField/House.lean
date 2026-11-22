/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.Norm
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.NumberField.House
public import TauCeti.Analysis.Polynomial.L1Norm
public import TauCeti.Analysis.Polynomial.SupNorm.Basic
public import TauCeti.NumberTheory.NumberField.AdjoinPair

import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Bounds on the house of an algebraic number

This file collects upper bounds on Mathlib's `NumberField.house`, the largest absolute value of the
complex conjugates of an element of a number field, together with the common denominators that
make such bounds available for finitely many algebraic numbers.

Transcendence arguments measure an element `x` of a number field `K` by a *size* `(a, H)`: a
denominator `δ` such that `δ ^ a * x` is an algebraic integer whose house is at most `H`. Products
add exponents and multiply bounds (Mathlib's `NumberField.house_mul_le`, and
`NumberField.house_prod_le_prod_house` for indexed products), sums of elements of a common exponent
add bounds (`NumberField.house_add_le`, `NumberField.house_sum_le_sum_house`), and a `k`-th power
has size `(a k, H ^ k)` (`NumberField.house_pow`). Raising the exponent from `a` to `b` multiplies
the bound by `G ^ (b - a)` for any `G ≥ δ` (`NumberField.house_natCast_pow_mul_le_of_le`); the
integrality of `δ ^ b * x` is that of `δ ^ a * x` times the integer `δ ^ (b - a)`.

## Main results

* `NumberField.house_le_of_norm_embedding_eq`: if every complex conjugate of `γ` is, up to the
  factor `s ^ d`, the value of an integer polynomial `P` of degree `d` at the corresponding
  conjugate of `g`, then `house γ ≤ s ^ n * ((n + 1) * R ^ n) * H(P)`.
* `NumberField.house_prod_le_prod_house`: the house of a finite product is at most the product of
  the houses.
* `NumberField.house_natCast_pow_mul_le_of_le`: raising the exponent of a size.
* `NumberField.exists_natCast_mul_isIntegral_house_le`: finitely many elements of a number field
  have a common denominator `δ ≥ 1` and a bound `G ≥ δ` on the houses of their multiples by `δ`.
* `NumberField.exists_numberField_denominator`: finitely many algebraic numbers in a field of
  characteristic zero lie in a number field inside it, where they have such a common denominator.

## References

* M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, GTM 201, Part D.
* A. Baker, *Transcendental Number Theory*, Chapter 2.
-/

public section

namespace NumberField

open Finset Module Polynomial

/-- If every conjugate `σ γ` of `γ` has absolute value `s ^ d * ‖P(σ g)‖`, where `1 ≤ s` and `P` has
degree `d ≤ n`, and `max 1 ‖σ g‖ ≤ R` for every conjugate, then the house of `γ` is at most
`s ^ n * ((n + 1) * R ^ n) * H(P)`. -/
theorem house_le_of_norm_embedding_eq {F : Type*} [Field F] [NumberField F] {g γ : F}
    {R : ℝ} (hR : ∀ σ : F →+* ℂ, max 1 ‖σ g‖ ≤ R) {s : ℝ} (hs1 : 1 ≤ s) {n : ℕ}
    {P : ℤ[X]} (hP : P.natDegree ≤ n)
    (hγ : ∀ σ : F →+* ℂ, ‖σ γ‖ = s ^ P.natDegree * ‖aeval (σ g) P‖) :
    house γ ≤ s ^ n * ((n + 1) * R ^ n) * P.supNorm := by
  have hH := P.supNorm_nonneg
  obtain ⟨σ, -, hσ⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty fun φ : F →+* ℂ ↦ ‖φ γ‖₊
  rw [house_eq_sup', hσ, coe_nnNorm, hγ]
  calc s ^ P.natDegree * ‖aeval (σ g) P‖
      ≤ s ^ n * ((n + 1) * P.supNorm * max 1 ‖σ g‖ ^ n) := by
        gcongr
        rw [aeval_def, algebraMap_int_eq, ← eval_map, ← P.supNorm_map (Int.castRingHom ℂ)]
        exact norm_eval_le_add_one_mul_supNorm_mul (natDegree_map_le.trans hP) _
    _ ≤ s ^ n * ((n + 1) * P.supNorm * R ^ n) := by
        gcongr
        exact hR σ
    _ = s ^ n * ((n + 1) * R ^ n) * P.supNorm := by ring

section Size

variable {K : Type*} [Field K] [NumberField K]

/-- The house of a product over a finite index set is at most the product of the houses. Mathlib's
`NumberField.house_prod_le` is the case of the product of the elements of a finite subset of
`K`. -/
theorem house_prod_le_prod_house {ι : Type*} (s : Finset ι) (x : ι → K) :
    house (∏ i ∈ s, x i) ≤ ∏ i ∈ s, house (x i) := by
  simpa [house, map_prod] using norm_prod_le s fun i ↦ canonicalEmbedding K (x i)

/-- **Raising the exponent of a size.** If `δ ^ a * x` has house at most `H`, `a ≤ b` and `δ ≤ G`,
then `δ ^ b * x` has house at most `G ^ (b - a) * H`. -/
theorem house_natCast_pow_mul_le_of_le {δ a b : ℕ} (hab : a ≤ b) {G H : ℝ} (hδ : δ ≤ G)
    {x : K} (hx : house ((δ : K) ^ a * x) ≤ H) :
    house ((δ : K) ^ b * x) ≤ G ^ (b - a) * H := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.add_sub_cancel_left, pow_add, mul_comm ((δ : K) ^ a), mul_assoc, ← Nat.cast_pow,
    house_nat_mul, Nat.cast_pow]
  have := house_nonneg ((δ : K) ^ a * x)
  have := (Nat.cast_nonneg δ).trans hδ
  gcongr

/-- **Common denominators.** Finitely many elements `x i` of a number field have a common
denominator `δ ≥ 1`, so that every `δ * x i` is an algebraic integer, and a real bound `G ≥ δ` on
the houses of the `δ * x i`. -/
theorem exists_natCast_mul_isIntegral_house_le {ι : Type*} [Finite ι] (x : ι → K) :
    ∃ δ : ℕ, 1 ≤ δ ∧ ∃ G : ℝ, (δ : ℝ) ≤ G ∧
      ∀ i, IsIntegral ℤ ((δ : K) * x i) ∧ house ((δ : K) * x i) ≤ G := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := K) (univ.image x)
  have hδ (i : ι) : IsIntegral ℤ ((y.natAbs : K) * x i) := by
    have h := hint (x i) (mem_image_of_mem x (mem_univ i))
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with hy' | hy'
    · rwa [hy', Int.cast_natCast] at h
    · rw [hy', Int.cast_neg, Int.cast_natCast, neg_mul] at h
      simpa using h.neg
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, max y.natAbs (∑ i, house ((y.natAbs : K) * x i)),
    le_max_left _ _, fun i ↦ ⟨hδ i, le_max_of_le_right ?_⟩⟩
  exact single_le_sum (fun j _ ↦ house_nonneg ((y.natAbs : K) * x j)) (mem_univ i)

/-- **Algebraic numbers lie in a number field with a common denominator.** Finitely many algebraic
numbers `x i` of a field `Ω` of characteristic zero lie in a number field `F ⊆ Ω` (the proof takes
the field they generate), and as elements `x' i` of `F` they have a common denominator `δ ≥ 1`
and a bound `G ≥ δ` on the houses of the algebraic integers `δ * x' i`. -/
theorem exists_numberField_denominator {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type*} [Finite ι]
    (x : ι → Ω) (hx : ∀ i, IsAlgebraic ℚ (x i)) :
    ∃ (F : IntermediateField ℚ Ω) (_ : NumberField F) (x' : ι → F), (∀ i, (x' i : Ω) = x i) ∧
      ∃ δ : ℕ, 1 ≤ δ ∧ ∃ G : ℝ, (δ : ℝ) ≤ G ∧
        ∀ i, IsIntegral ℤ ((δ : F) * x' i) ∧ house ((δ : F) * x' i) ≤ G := by
  obtain ⟨F, hF, x', hx'⟩ := TauCeti.exists_numberField_comp hx
  exact ⟨F, hF, x', fun i ↦ congr_fun hx' i, exists_natCast_mul_isIntegral_house_le x'⟩

end Size

end NumberField
