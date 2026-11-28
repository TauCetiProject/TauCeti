/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Slice
public import TauCeti.Analysis.SpecificLimits.TwoSidedGeometric
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Countable geometric models on Wenzl's continuous interval

For `q : ℂˣ` with `Q = q ^ 2 > 0` and `z = q * η - q⁻¹ * (1 - η)`, we construct countable
two-sided geometric models on `ℕ ⊕ₗ ℕᵒᵈ` realizing `η` in Wenzl's continuous interval
(`wenzlGtOneWeight` for `1 < Q`, `wenzlLtOneWeight` for `0 < Q < 1`). Cf. Wenzl (1988, §3),
Neretin (arXiv:2101.02133, §§1.6–1.7, §3.1).
-/

public section

open Filter Function Finsupp OrderDual
open scoped Topology

namespace TauCeti.TypeAHeckeAlgebra

/-- Sign predicate on `ℕ ⊕ₗ ℕᵒᵈ` for `1 < Q`: positive on `ℕ`, negative on `ℕᵒᵈ`. -/
def wenzlGtOnePos (a : ℕ ⊕ₗ ℕᵒᵈ) : Prop := (ofLex a).isLeft = true

instance : DecidablePred wenzlGtOnePos :=
  fun a ↦ inferInstanceAs (Decidable ((ofLex a).isLeft = true))

/-- Left-branch letters `Sum.inlₗ k` are positive in the `1 < Q` model. -/
@[simp] theorem wenzlGtOnePos_inl (k : ℕ) : wenzlGtOnePos (Sum.inlₗ k) := by simp [wenzlGtOnePos]

/-- Right-branch letters `Sum.inrₗ k` are negative in the `1 < Q` model. -/
@[simp] theorem not_wenzlGtOnePos_inr (k : ℕᵒᵈ) : ¬ wenzlGtOnePos (Sum.inrₗ k) := by
  simp [wenzlGtOnePos]

/-- Geometric weights on `ℕ ⊕ₗ ℕᵒᵈ` for `1 < Q`: `((1 + Q) * η - 1) / Q ^ (k + 1)` on `ℕ` and
`(Q - (1 + Q) * η) / Q ^ (k + 1)` on `ℕᵒᵈ`. -/
noncomputable def wenzlGtOneWeight (Q η : ℝ) : ℕ ⊕ₗ ℕᵒᵈ → ℝ :=
  twoSidedGeom (((1 + Q) * η - 1) * Q⁻¹) ((Q - (1 + Q) * η) * Q⁻¹) Q⁻¹

/-- Expressing `wenzlGtOneWeight` as a `twoSidedGeom` family. -/
theorem wenzlGtOneWeight_eq_twoSidedGeom (Q η : ℝ) : wenzlGtOneWeight Q η =
    twoSidedGeom (((1 + Q) * η - 1) * Q⁻¹) ((Q - (1 + Q) * η) * Q⁻¹) Q⁻¹ := (rfl)

/-- Value of `wenzlGtOneWeight` on a left-branch letter `Sum.inlₗ k`. -/
@[simp] theorem wenzlGtOneWeight_inl (Q η : ℝ) (k : ℕ) :
    wenzlGtOneWeight Q η (Sum.inlₗ k) = ((1 + Q) * η - 1) * Q⁻¹ * (Q⁻¹) ^ k := by
  simp [wenzlGtOneWeight]

/-- Value of `wenzlGtOneWeight` on a right-branch letter `Sum.inrₗ k`. -/
@[simp] theorem wenzlGtOneWeight_inr (Q η : ℝ) (k : ℕᵒᵈ) :
    wenzlGtOneWeight Q η (Sum.inrₗ k) = (Q - (1 + Q) * η) * Q⁻¹ * (Q⁻¹) ^ ofDual k := by
  simp [wenzlGtOneWeight]

/-- For `1 < Q` and `η ∈ [1 / (1 + Q), Q / (1 + Q)]`, `wenzlGtOneWeight Q η` is nonnegative. -/
theorem wenzlGtOneWeight_nonneg {Q : ℝ} (hQ : 1 < Q) {η : ℝ}
    (hη : η ∈ Set.Icc (1 / (1 + Q)) (Q / (1 + Q))) (a : ℕ ⊕ₗ ℕᵒᵈ) :
    0 ≤ wenzlGtOneWeight Q η a := by
  have h1Q : 0 < 1 + Q := by linarith
  have hQi : 0 ≤ Q⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hQ).le
  exact twoSidedGeom_nonneg (mul_nonneg (by linarith [(div_le_iff₀ h1Q).mp hη.1]) hQi)
    (mul_nonneg (by linarith [(le_div_iff₀ h1Q).mp hη.2]) hQi) hQi a

/-- For `1 < Q` and any `η : ℝ`, `wenzlGtOneWeight Q η` is absolutely summable. -/
theorem summable_norm_wenzlGtOneWeight {Q : ℝ} (hQ : 1 < Q) (η : ℝ) :
    Summable fun a ↦ ‖wenzlGtOneWeight Q η a‖ :=
  summable_norm_twoSidedGeom _ _ (inv_nonneg.mpr (zero_lt_one.trans hQ).le)
    (inv_lt_one_of_one_lt₀ hQ)

/-- For `1 < Q` and any `η : ℝ`, the total weight of `wenzlGtOneWeight Q η` is `1`. -/
theorem tsum_wenzlGtOneWeight {Q : ℝ} (hQ : 1 < Q) (η : ℝ) :
    (∑' a, wenzlGtOneWeight Q η a) = 1 := by
  have hQ0 : Q ≠ 0 := (zero_lt_one.trans hQ).ne'; have hQ1 : Q - 1 ≠ 0 := sub_ne_zero.mpr hQ.ne'
  rw [wenzlGtOneWeight_eq_twoSidedGeom, tsum_twoSidedGeom _ _
    (inv_nonneg.mpr (zero_lt_one.trans hQ).le) (inv_lt_one_of_one_lt₀ hQ)]; field_simp; ring

/-- Every left slice of `wenzlGtOneWeight Q η` equals `(1 + Q) * η - 1`. -/
theorem wenzlGtOneWeight_leftSlice {Q : ℝ} (hQ : 1 < Q) (η : ℝ) (b : ℕ ⊕ₗ ℕᵒᵈ) :
    (if wenzlGtOnePos b then Q else -1) * wenzlGtOneWeight Q η b +
      (Q - 1) * (∑' a, if a < b then wenzlGtOneWeight Q η a else 0) = (1 + Q) * η - 1 := by
  have hQ0 : Q ≠ 0 := (zero_lt_one.trans hQ).ne'
  rw [show Q - 1 = Q * (1 - Q⁻¹) by field_simp, mul_assoc]
  obtain ⟨m | m, rfl⟩ := toLex.surjective b
  · rw [wenzlGtOneWeight_inl, wenzlGtOneWeight_eq_twoSidedGeom, mul_tsum_lt_twoSidedGeom_inl]
    simp only [wenzlGtOnePos_inl, ↓reduceIte]; field_simp; ring
  · rw [← toDual_ofDual m, wenzlGtOneWeight_inr, wenzlGtOneWeight_eq_twoSidedGeom,
      mul_tsum_lt_twoSidedGeom_inr _ _ (inv_nonneg.mpr (zero_lt_one.trans hQ).le)
      (inv_lt_one_of_one_lt₀ hQ), pow_succ']
    simp only [not_wenzlGtOnePos_inr, ↓reduceIte, ofDual_toDual]; field_simp; ring

/-- **Countable geometric realization of the Ocneanu trace for `1 < Q`.** -/
theorem countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace {q : ℂˣ} {Q : ℝ} (hQ : 1 < Q)
    (hqQ : (q : ℂ) ^ 2 = Q) (η : ℝ) {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicTrace wenzlGtOnePos q (fun a ↦ (wenzlGtOneWeight Q η a : ℂ))
        ((summable_norm_wenzlGtOneWeight hQ η).congr fun _ ↦ (Complex.norm_real _).symm) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace ℂ q
        ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (toInfinite ℂ q n x) :=
  countableAtomicTrace_ofReal_eq_ocneanuTrace_of_leftSlice wenzlGtOnePos hqQ
    (summable_norm_wenzlGtOneWeight hQ η) η (tsum_wenzlGtOneWeight hQ η)
    (wenzlGtOneWeight_leftSlice hQ η) x

/-- Sign predicate on `ℕ ⊕ₗ ℕᵒᵈ` for `0 < Q < 1`: negative on `ℕ`, positive on `ℕᵒᵈ`. -/
def wenzlLtOnePos (a : ℕ ⊕ₗ ℕᵒᵈ) : Prop := (ofLex a).isRight = true

instance : DecidablePred wenzlLtOnePos :=
  fun a ↦ inferInstanceAs (Decidable ((ofLex a).isRight = true))

/-- Left-branch letters `Sum.inlₗ k` are negative in the `0 < Q < 1` model. -/
@[simp] theorem not_wenzlLtOnePos_inl (k : ℕ) : ¬ wenzlLtOnePos (Sum.inlₗ k) := by
  simp [wenzlLtOnePos]

/-- Right-branch letters `Sum.inrₗ k` are positive in the `0 < Q < 1` model. -/
@[simp] theorem wenzlLtOnePos_inr (k : ℕᵒᵈ) : wenzlLtOnePos (Sum.inrₗ k) := by simp [wenzlLtOnePos]

/-- Real geometric weights on `ℕ ⊕ₗ ℕᵒᵈ` for `0 < Q < 1` and projection parameter `η`. -/
noncomputable def wenzlLtOneWeight (Q η : ℝ) : ℕ ⊕ₗ ℕᵒᵈ → ℝ :=
  twoSidedGeom (1 - (1 + Q) * η) ((1 + Q) * η - Q) Q

/-- Expressing `wenzlLtOneWeight` as a `twoSidedGeom` family. -/
theorem wenzlLtOneWeight_eq_twoSidedGeom (Q η : ℝ) :
    wenzlLtOneWeight Q η = twoSidedGeom (1 - (1 + Q) * η) ((1 + Q) * η - Q) Q := (rfl)

/-- Value of `wenzlLtOneWeight` on a left-branch letter `Sum.inlₗ k`. -/
@[simp] theorem wenzlLtOneWeight_inl (Q η : ℝ) (k : ℕ) :
    wenzlLtOneWeight Q η (Sum.inlₗ k) = (1 - (1 + Q) * η) * Q ^ k := by simp [wenzlLtOneWeight]

/-- Value of `wenzlLtOneWeight` on a right-branch letter `Sum.inrₗ k`. -/
@[simp] theorem wenzlLtOneWeight_inr (Q η : ℝ) (k : ℕᵒᵈ) :
    wenzlLtOneWeight Q η (Sum.inrₗ k) = ((1 + Q) * η - Q) * Q ^ ofDual k := by
  simp [wenzlLtOneWeight]

/-- For `0 < Q < 1` and `η ∈ [Q / (1 + Q), 1 / (1 + Q)]`, `wenzlLtOneWeight Q η` is nonnegative. -/
theorem wenzlLtOneWeight_nonneg {Q : ℝ} (hQ0 : 0 < Q) {η : ℝ}
    (hη : η ∈ Set.Icc (Q / (1 + Q)) (1 / (1 + Q))) (a : ℕ ⊕ₗ ℕᵒᵈ) :
    0 ≤ wenzlLtOneWeight Q η a := by
  have h1Q : 0 < 1 + Q := by linarith
  exact twoSidedGeom_nonneg (by linarith [(le_div_iff₀ h1Q).mp hη.2]) (by
    linarith [(div_le_iff₀ h1Q).mp hη.1]) hQ0.le a

/-- For `0 < Q < 1` and any `η : ℝ`, `wenzlLtOneWeight Q η` is absolutely summable. -/
theorem summable_norm_wenzlLtOneWeight {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ) :
    Summable fun a ↦ ‖wenzlLtOneWeight Q η a‖ := summable_norm_twoSidedGeom _ _ hQ0.le hQ1

/-- For `0 < Q < 1` and any `η : ℝ`, the total weight of `wenzlLtOneWeight Q η` is `1`. -/
theorem tsum_wenzlLtOneWeight {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ) :
    (∑' a, wenzlLtOneWeight Q η a) = 1 := by
  rw [wenzlLtOneWeight_eq_twoSidedGeom, tsum_twoSidedGeom _ _ hQ0.le hQ1]
  have := sub_ne_zero.mpr hQ1.ne'; field_simp; ring

/-- Every left slice of `wenzlLtOneWeight Q η` equals `(1 + Q) * η - 1`. -/
theorem wenzlLtOneWeight_leftSlice {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ) (b : ℕ ⊕ₗ ℕᵒᵈ) :
    (if wenzlLtOnePos b then Q else -1) * wenzlLtOneWeight Q η b +
      (Q - 1) * (∑' a, if a < b then wenzlLtOneWeight Q η a else 0) = (1 + Q) * η - 1 := by
  rw [← neg_sub 1 Q, neg_mul]; obtain ⟨m | m, rfl⟩ := toLex.surjective b
  · rw [wenzlLtOneWeight_inl, wenzlLtOneWeight_eq_twoSidedGeom, mul_tsum_lt_twoSidedGeom_inl]
    simp only [not_wenzlLtOnePos_inl, ↓reduceIte]; ring
  · rw [← toDual_ofDual m, wenzlLtOneWeight_inr, wenzlLtOneWeight_eq_twoSidedGeom,
      mul_tsum_lt_twoSidedGeom_inr _ _ hQ0.le hQ1, pow_succ']; simp; ring

/-- **Countable geometric realization of the Ocneanu trace for `0 < Q < 1`.** -/
theorem countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace {q : ℂˣ} {Q : ℝ} (hQ0 : 0 < Q)
    (hQ1 : Q < 1) (hqQ : (q : ℂ) ^ 2 = Q) (η : ℝ) {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicTrace wenzlLtOnePos q (fun a ↦ (wenzlLtOneWeight Q η a : ℂ))
        ((summable_norm_wenzlLtOneWeight hQ0 hQ1 η).congr fun _ ↦ (Complex.norm_real _).symm) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace ℂ q
        ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (toInfinite ℂ q n x) :=
  countableAtomicTrace_ofReal_eq_ocneanuTrace_of_leftSlice wenzlLtOnePos hqQ
    (summable_norm_wenzlLtOneWeight hQ0 hQ1 η) η (tsum_wenzlLtOneWeight hQ0 hQ1 η) (
      wenzlLtOneWeight_leftSlice hQ0 hQ1 η) x

end TauCeti.TypeAHeckeAlgebra
