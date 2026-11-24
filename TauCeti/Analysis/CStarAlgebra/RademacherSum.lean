/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.RademacherSum.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.CStarAlgebra.CauchySchwarz

/-!
# Rademacher sums in a C⋆-algebra: orthogonality and the fourth moment

This file proves two estimates for sums of C⋆-algebra elements weighted by Rademacher signs
`ε : ι → ℤˣ`, the expectation `𝔼` being the average over the finite sign cube.

**Orthogonality.** For any function `Φ` on the sign cube with values in a C⋆-algebra, its
Rademacher coefficients `yₖ = 𝔼 εₖ Φ(ε)` satisfy

`∑ k, yₖ⋆ yₖ ≤ 𝔼 Φ⋆Φ` and `∑ k, yₖ yₖ⋆ ≤ 𝔼 ΦΦ⋆`.

Indeed `Φ - ∑ k, εₖ yₖ` has no Rademacher coefficients, so `𝔼 Φ⋆Φ` is `∑ k, yₖ⋆ yₖ` plus the
positive element `𝔼 (Φ - ∑ k, εₖ yₖ)⋆ (Φ - ∑ k, εₖ yₖ)`.

**The fourth moment.** For a finite family `x` in a ring write `S(ε) = ∑ i, εᵢ xᵢ`. Averaging a
product of four signs keeps exactly the index patterns that match in pairs, so
`𝔼 S⁴ = A + B + C - 2 D` with

* `A = (∑ i, xᵢ²)²`,
* `B = ∑ i, xᵢ (∑ j, xⱼ²) xᵢ`,
* `C = ∑ i, ∑ j, xᵢ xⱼ xᵢ xⱼ`,
* `D = ∑ i, xᵢ⁴`.

This pairing expansion, `TauCeti.sum_sum_units_smul_mul_self_mul_mul_self`, holds in any
non-unital ring and lives with the other sign-cube averages in `RademacherSum/Basic.lean`.

The coefficients need not commute, so `A`, `B` and `C` differ in general. When the `xᵢ` are
self-adjoint elements of a C⋆-algebra, `D ≥ 0` and `𝔼 S⁴ ≥ 0`, so `‖𝔼 S⁴‖ ≤ ‖A + B + C‖`. Each of
`‖A‖` and `‖B‖` is at most `‖∑ i, xᵢ²‖²`, and the Cauchy–Schwarz bound for finite sums, applied to
the family `xᵢ xⱼ` indexed by pairs, gives `‖C‖ ≤ ‖B‖`. Hence

`‖𝔼 S⁴‖ ≤ 3 ‖∑ i, xᵢ²‖²`.

The constant `3` cannot be lowered: for `n` scalar coefficients equal to `1`,
`𝔼 S⁴ = 3 n² - 2 n` while `‖∑ i, xᵢ²‖² = n²`.

Together these are the C⋆-algebraic estimates behind the noncommutative Khintchine inequality in
the trace class with the constant `3^(-1/2)`: one truncates `S` at a level where the fourth moment
controls the discarded part, and orthogonality bounds the row and column norms of what the
truncation changes.

## Main declarations

* `TauCeti.sum_star_mul_le_card_inv_smul_sum_star_mul` and
  `TauCeti.sum_mul_star_le_card_inv_smul_sum_mul_star`: orthogonality of the Rademacher
  coefficients, in column and row form.
* `TauCeti.norm_sum_star_mul_le_of_norm_le` and `TauCeti.norm_sum_mul_star_le_of_norm_le`: their
  norm forms, `‖∑ k, yₖ⋆ yₖ‖ ≤ r²` and `‖∑ k, yₖ yₖ⋆‖ ≤ r²` when `‖Φ ε‖ ≤ r` for every `ε`.
* `TauCeti.norm_card_inv_smul_sum_sum_units_smul_mul_self_mul_mul_self_le`: for self-adjoint
  coefficients in a non-unital C⋆-algebra, `‖𝔼 S⁴‖ ≤ 3 ‖∑ i, xᵢ²‖²`.

## References

* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012), §9:
  the orthogonality (9.11) in the proof of Theorem 9.1, and Lemma 9.2 for the fourth moment,
  which it credits to G. Pisier, *Grothendieck's theorem for noncommutative C⋆-algebras*,
  J. Funct. Anal. 29 (1978), and U. Haagerup, *The Grothendieck inequality for bilinear forms on
  C⋆-algebras*, Adv. Math. 56 (1985).
* U. Haagerup and M. Musat, *On the best constants in noncommutative Khintchine-type
  inequalities*, J. Funct. Anal. 250 (2007), §2.
-/

public section

noncomputable section

open Finset
open scoped BigOperators

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [DecidableEq ι] in
/-- For self-adjoint `xᵢ` with `T = ∑ i, xᵢ²`, the three pairing terms of the fourth moment satisfy
`‖T² + ∑ i, xᵢ T xᵢ + ∑ i, ∑ j, xᵢ xⱼ xᵢ xⱼ‖ ≤ 3 ‖T‖²`. -/
private theorem norm_pairing_add_le {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) :
    ‖(∑ i, x i * x i) * (∑ i, x i * x i) + ∑ i, x i * (∑ j, x j * x j) * x i +
        ∑ i, ∑ j, x i * x j * (x i * x j)‖ ≤ 3 * ‖∑ i, x i * x i‖ ^ 2 := by
  set T := ∑ i, x i * x i
  set B := ∑ i, x i * T * x i
  have hT0 : 0 ≤ T := sum_nonneg fun i _ ↦ by
    simpa [(hx i).star_eq] using star_mul_self_nonneg (x i)
  -- `0 ≤ B ≤ ‖T‖ T`, so `‖B‖ ≤ ‖T‖²`.
  have hB0 : 0 ≤ B := sum_nonneg fun i _ ↦ by
    simpa [(hx i).star_eq] using star_left_conjugate_nonneg hT0 (x i)
  have hB : ‖B‖ ≤ ‖T‖ ^ 2 := by
    have hle : B ≤ ‖T‖ • T := by
      rw [smul_sum]
      refine sum_le_sum fun i _ ↦ ?_
      simpa [(hx i).star_eq] using CStarAlgebra.star_left_conjugate_le_norm_smul (x i) T
    refine (CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hB0).trans_eq ?_
    rw [norm_smul, norm_norm, sq]
  -- Cauchy–Schwarz for the family `xᵢ xⱼ`, whose row and column squares are both `B`.
  have hC : ‖∑ i, ∑ j, x i * x j * (x i * x j)‖ ≤ ‖B‖ := by
    have hrow : ∑ p : ι × ι, x p.1 * x p.2 * star (x p.1 * x p.2) = B := by
      simp [Fintype.sum_prod_type, star_mul, (hx _).star_eq, B, T, mul_sum, sum_mul, mul_assoc]
    have hcol : ∑ p : ι × ι, star (x p.1 * x p.2) * (x p.1 * x p.2) = B := by
      rw [Fintype.sum_prod_type, sum_comm]
      simp [star_mul, (hx _).star_eq, B, T, mul_sum, sum_mul, mul_assoc]
    have h := norm_sum_mul_sq_le univ (fun p : ι × ι ↦ x p.1 * x p.2) fun p ↦ x p.1 * x p.2
    rw [hrow, hcol, Fintype.sum_prod_type, ← sq] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
  calc _ ≤ ‖T‖ * ‖T‖ + ‖T‖ ^ 2 + ‖T‖ ^ 2 := by
        grw [norm_add₃_le, norm_mul_le, hC, hB]
    _ = 3 * ‖T‖ ^ 2 := by ring

/-- The fourth-moment estimate for Rademacher sums with self-adjoint coefficients in a C⋆-algebra:
`‖𝔼 (∑ i, εᵢ xᵢ)⁴‖ ≤ 3 ‖∑ i, xᵢ²‖²`, the expectation being the average over the sign cube. -/
theorem norm_card_inv_smul_sum_sum_units_smul_mul_self_mul_mul_self_le {x : ι → A}
    (hx : ∀ i, IsSelfAdjoint (x i)) :
    ‖(Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε : ι → ℤˣ,
        (∑ i, ε i • x i) * (∑ i, ε i • x i) * ((∑ i, ε i • x i) * (∑ i, ε i • x i))‖ ≤
      3 * ‖∑ i, x i * x i‖ ^ 2 := by
  -- `0 ≤ 𝔼 S⁴ = A + B + C - 2 D ≤ A + B + C`, since `S` and `D` are self-adjoint.
  have hD0 : 0 ≤ ∑ i, x i * x i * (x i * x i) := sum_nonneg fun i _ ↦ by
    simpa [star_mul, (hx i).star_eq] using star_mul_self_nonneg (x i * x i)
  have hE0 : 0 ≤ ∑ ε : ι → ℤˣ,
      (∑ i, ε i • x i) * (∑ i, ε i • x i) * ((∑ i, ε i • x i) * (∑ i, ε i • x i)) := by
    refine sum_nonneg fun ε _ ↦ ?_
    have hS : star (∑ i, ε i • x i) = ∑ i, ε i • x i := by
      simp [star_sum, Units.smul_def, (hx _).star_eq]
    simpa [star_mul, hS] using star_mul_self_nonneg ((∑ i, ε i • x i) * (∑ i, ε i • x i))
  have hcard : (Fintype.card (ι → ℤˣ) : ℝ) ≠ 0 := by positivity
  rw [sum_sum_units_smul_mul_self_mul_mul_self, ← Nat.cast_smul_eq_nsmul ℝ] at hE0 ⊢
  rw [inv_smul_smul₀ hcard]
  have hY0 := smul_nonneg (by positivity : (0 : ℝ) ≤ (Fintype.card (ι → ℤˣ) : ℝ)⁻¹) hE0
  rw [inv_smul_smul₀ hcard] at hY0
  exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_le_self _ (nsmul_nonneg hD0 2)) hY0).trans
    (norm_pairing_add_le hx)

omit [PartialOrder A] [StarOrderedRing A] in
/-- Expanding `∑ ε, (Φ ε - ∑ k, εₖ yₖ)⋆ (Φ ε - ∑ k, εₖ yₖ)` when `yₖ` is the sign-cube average of
`εₖ Φ`: the cross terms and the square of the Rademacher part each contribute `N ∑ k, yₖ⋆ yₖ`,
where `N` is the number of sign patterns. -/
private theorem sum_star_sub_mul_sub (Φ : (ι → ℤˣ) → A) (y : ι → A)
    (hy : ∀ k, y k = (Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, ε k • Φ ε) :
    ∑ ε : ι → ℤˣ, star (Φ ε - ∑ k, ((ε k : ℤ) : ℝ) • y k) * (Φ ε - ∑ k, ((ε k : ℤ) : ℝ) • y k) =
      ∑ ε, star (Φ ε) * Φ ε - (Fintype.card (ι → ℤˣ) : ℝ) • ∑ k, star (y k) * y k := by
  set N : ℝ := (Fintype.card (ι → ℤˣ) : ℝ)
  have hN : N ≠ 0 := by positivity
  have h1 (k : ι) : ∑ ε : ι → ℤˣ, ((ε k : ℤ) : ℝ) • Φ ε = N • y k := by
    simp [hy, smul_inv_smul₀ hN, Units.smul_def, Int.cast_smul_eq_zsmul]
  have h1' (k : ι) : ∑ ε : ι → ℤˣ, ((ε k : ℤ) : ℝ) • star (Φ ε) = N • star (y k) := by
    simpa [star_sum, star_smul] using congrArg star (h1 k)
  have h2 (k l : ι) :
      ∑ ε : ι → ℤˣ, ((ε k : ℤ) : ℝ) * (ε l : ℤ) = N * if k = l then 1 else 0 := by
    rw [← expect_units_apply_mul_apply k l, Fintype.expect_eq_sum_div_card, mul_div_cancel₀ _ hN]
  have e1 : ∑ ε : ι → ℤˣ, ∑ k, ((ε k : ℤ) : ℝ) • (star (y k) * Φ ε) =
      N • ∑ k, star (y k) * y k := by
    rw [sum_comm]
    simp_rw [← mul_smul_comm, ← mul_sum, h1, mul_smul_comm, smul_sum]
  have e2 : ∑ ε : ι → ℤˣ, ∑ k, ((ε k : ℤ) : ℝ) • (star (Φ ε) * y k) =
      N • ∑ k, star (y k) * y k := by
    rw [sum_comm]
    simp_rw [← smul_mul_assoc, ← sum_mul, h1', smul_mul_assoc, smul_sum]
  -- Distinct signs are orthogonal, so only the diagonal of the double sum survives.
  have e3 : ∑ ε : ι → ℤˣ, ∑ k, ((ε k : ℤ) : ℝ) • ∑ l, ((ε l : ℤ) : ℝ) • (star (y l) * y k) =
      N • ∑ k, star (y k) * y k := by
    simp_rw [smul_sum, smul_smul]
    rw [sum_comm]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [sum_comm]
    simp_rw [← sum_smul, h2, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, sum_ite_eq,
      mem_univ, ite_true]
  -- Expand the square into `Φ⋆Φ`, the two cross terms and the square of the Rademacher part.
  have hexp : ∑ ε : ι → ℤˣ,
      star (Φ ε - ∑ k, ((ε k : ℤ) : ℝ) • y k) * (Φ ε - ∑ k, ((ε k : ℤ) : ℝ) • y k) =
        ∑ ε, star (Φ ε) * Φ ε - ∑ ε : ι → ℤˣ, ∑ k, ((ε k : ℤ) : ℝ) • (star (Φ ε) * y k) -
          ∑ ε : ι → ℤˣ, ∑ k, ((ε k : ℤ) : ℝ) • (star (y k) * Φ ε) +
          ∑ ε : ι → ℤˣ, ∑ k, ((ε k : ℤ) : ℝ) • ∑ l, ((ε l : ℤ) : ℝ) • (star (y l) * y k) := by
    simp only [star_sub, star_sum, star_smul, star_trivial, sub_mul, mul_sub, sum_mul, mul_sum,
      smul_mul_assoc, mul_smul_comm, smul_sub, sum_sub_distrib]
    abel
  rw [hexp, e1, e2, e3]
  abel

/-- Orthogonality of the Rademacher coefficients of a C⋆-algebra-valued function on the sign
cube: if `yₖ = 𝔼 εₖ Φ(ε)`, then `∑ k, yₖ⋆ yₖ ≤ 𝔼 Φ⋆Φ`, the expectations being averages over the
sign cube. -/
theorem sum_star_mul_le_card_inv_smul_sum_star_mul (Φ : (ι → ℤˣ) → A) :
    ∑ k, star ((Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, ε k • Φ ε) *
        ((Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, ε k • Φ ε) ≤
      (Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, star (Φ ε) * Φ ε := by
  obtain ⟨y, hy⟩ : ∃ y : ι → A, ∀ k, y k = (Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, ε k • Φ ε :=
    ⟨_, fun _ ↦ rfl⟩
  simp_rw [← hy]
  have h0 : 0 ≤ (Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε : ι → ℤˣ,
      star (Φ ε - ∑ k, ((ε k : ℤ) : ℝ) • y k) * (Φ ε - ∑ k, ((ε k : ℤ) : ℝ) • y k) :=
    smul_nonneg (by positivity) (sum_nonneg fun ε _ ↦ star_mul_self_nonneg _)
  rwa [sum_star_sub_mul_sub Φ y hy, smul_sub, inv_smul_smul₀ (by positivity), sub_nonneg] at h0

/-- The row form of `sum_star_mul_le_card_inv_smul_sum_star_mul`: if `yₖ = 𝔼 εₖ Φ(ε)`, then
`∑ k, yₖ yₖ⋆ ≤ 𝔼 ΦΦ⋆`. -/
theorem sum_mul_star_le_card_inv_smul_sum_mul_star (Φ : (ι → ℤˣ) → A) :
    ∑ k, ((Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, ε k • Φ ε) *
        star ((Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, ε k • Φ ε) ≤
      (Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, Φ ε * star (Φ ε) := by
  simpa [star_sum, star_smul, Units.smul_def] using
    sum_star_mul_le_card_inv_smul_sum_star_mul fun ε ↦ star (Φ ε)

omit [PartialOrder A] [StarOrderedRing A] in
/-- A sign-cube average of elements of norm at most `c` has norm at most `c`. -/
private theorem norm_card_inv_smul_sum_le {z : (ι → ℤˣ) → A} {c : ℝ} (h : ∀ ε, ‖z ε‖ ≤ c) :
    ‖(Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, z ε‖ ≤ c := by
  have hcard : (0 : ℝ) < Fintype.card (ι → ℤˣ) := by positivity
  rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_le_iff₀ hcard]
  simpa using norm_sum_le_of_le univ fun ε _ ↦ h ε

/-- The norm form of `sum_star_mul_le_card_inv_smul_sum_star_mul`: if `‖Φ ε‖ ≤ r` for every sign
pattern `ε`, the Rademacher coefficients `yₖ = 𝔼 εₖ Φ(ε)` satisfy `‖∑ k, yₖ⋆ yₖ‖ ≤ r²`. -/
theorem norm_sum_star_mul_le_of_norm_le {Φ : (ι → ℤˣ) → A} {r : ℝ} (h : ∀ ε, ‖Φ ε‖ ≤ r) :
    ‖∑ k, star ((Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, ε k • Φ ε) *
        ((Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, ε k • Φ ε)‖ ≤ r ^ 2 := by
  refine (CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (sum_star_mul_le_card_inv_smul_sum_star_mul Φ)
    (sum_nonneg fun k _ ↦ star_mul_self_nonneg _)).trans (norm_card_inv_smul_sum_le fun ε ↦ ?_)
  rw [CStarRing.norm_star_mul_self, ← sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (h ε) 2

/-- The norm form of `sum_mul_star_le_card_inv_smul_sum_mul_star`: if `‖Φ ε‖ ≤ r` for every sign
pattern `ε`, the Rademacher coefficients `yₖ = 𝔼 εₖ Φ(ε)` satisfy `‖∑ k, yₖ yₖ⋆‖ ≤ r²`. -/
theorem norm_sum_mul_star_le_of_norm_le {Φ : (ι → ℤˣ) → A} {r : ℝ} (h : ∀ ε, ‖Φ ε‖ ≤ r) :
    ‖∑ k, ((Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, ε k • Φ ε) *
        star ((Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, ε k • Φ ε)‖ ≤ r ^ 2 := by
  refine (CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (sum_mul_star_le_card_inv_smul_sum_mul_star Φ)
    (sum_nonneg fun k _ ↦ mul_star_self_nonneg _)).trans (norm_card_inv_smul_sum_le fun ε ↦ ?_)
  rw [CStarRing.norm_self_mul_star, ← sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (h ε) 2

end CStarAlgebra

end TauCeti
