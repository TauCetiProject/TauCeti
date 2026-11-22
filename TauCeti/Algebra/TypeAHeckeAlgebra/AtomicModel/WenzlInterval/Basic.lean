/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Sum.Order
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Slice
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Ring.Units
import TauCeti.Analysis.SpecificLimits.TwoSidedGeometric

/-!
# Countable geometric models on Wenzl's continuous interval

For real nonzero `q : ℂˣ` with `Q = q ^ 2 > 0`, writing `z = q * η - q⁻¹ * (1 - η)` gives
`q * z = (1 + Q) * η - 1`. We construct the countable two-sided geometric atomic models on
`ℕ ⊕ₗ ℕᵒᵈ` realizing every parameter `η` in Wenzl's continuous interval:

* **For `1 < Q`** (`wenzlGtOnePos`, `wenzlGtOneWeight`): positive letters on `ℕ` followed by
  negative letters on `ℕᵒᵈ`, realizing the Ocneanu trace for any `η`
  (`countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace`), nonnegative on
  `[1 / (1 + Q), Q / (1 + Q)]` (`wenzlGtOneWeight_nonneg`).
* **For `0 < Q < 1`** (`wenzlLtOnePos`, `wenzlLtOneWeight`): negative letters on `ℕ` followed by
  positive letters on `ℕᵒᵈ`, realizing the Ocneanu trace for any `η`
  (`countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace`), nonnegative on
  `[Q / (1 + Q), 1 / (1 + Q)]` (`wenzlLtOneWeight_nonneg`).

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
-/

public section

open Filter Function Finsupp OrderDual
open scoped Topology

namespace TauCeti.TypeAHeckeAlgebra

section CountableGeometricModels

/-- Converting a real projection parameter `η` to the scaled Markov parameter `q * z` in `ℂ`:
`q * (q * η - q⁻¹ * (1 - η)) = ((1 + Q) * η - 1 : ℝ)`. -/
theorem mul_markovParam_proj_eq {q : ℂˣ} {Q : ℝ} (hqQ : (q : ℂ) ^ 2 = Q) (η : ℝ) :
    (q : ℂ) * ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) = (((1 + Q) * η - 1 : ℝ) : ℂ) := by
  simpa [← hqQ] using Units.mul_sub_val_inv_mul_one_sub q (η : ℂ)

/-- Real-weighted countable atomic model with left slice `(1 + Q) * η - 1` realizes the Ocneanu
trace at `z = q * η - q⁻¹ * (1 - η)`. -/
theorem countableAtomicTrace_ofReal_eq_ocneanuTrace_of_leftSlice {ι : Type*}
    [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] {q : ℂˣ} {Q : ℝ}
    (hqQ : (q : ℂ) ^ 2 = Q) {w : ι → ℝ} (hw : Summable fun a ↦ ‖w a‖) (η : ℝ)
    (hsum : (∑' a, w a) = 1)
    (hslice : ∀ b, (if pos b then Q else -1) * w b +
      (Q - 1) * (∑' a, if a < b then w a else 0) = (1 + Q) * η - 1)
    {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicTrace pos q (fun a ↦ (w a : ℂ))
        (hw.congr fun a ↦ (Complex.norm_real _).symm) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace ℂ q
        ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (toInfinite ℂ q n x) := by
  refine countableAtomicTrace_eq_ocneanuTrace_of_leftSlice pos q _ _
    (by rw [← Complex.ofReal_tsum, hsum, Complex.ofReal_one]) (fun b ↦ ?_) x
  have hsl := congrArg ((↑) : ℝ → ℂ) (hslice b)
  rw [← mul_markovParam_proj_eq hqQ η] at hsl
  push_cast [Complex.ofReal_tsum, apply_ite ((↑) : ℝ → ℂ)] at hsl
  rwa [← hqQ, ← Units.val_inv_eq_inv_val] at hsl

/-! ### The `1 < Q` countable model on `ℕ ⊕ₗ ℕᵒᵈ` -/

/-- Sign predicate on `ℕ ⊕ₗ ℕᵒᵈ` for Wenzl's continuous interval when `1 < Q`: positive letters on
the left (`ℕ`) followed by negative letters on the right (`ℕᵒᵈ`). -/
def wenzlGtOnePos (a : ℕ ⊕ₗ ℕᵒᵈ) : Prop := (ofLex a).isLeft = true

instance : DecidablePred wenzlGtOnePos :=
  fun a ↦ inferInstanceAs (Decidable ((ofLex a).isLeft = true))

/-- Left-branch letters `Sum.inlₗ k` are positive in the `1 < Q` model. -/
@[simp] theorem wenzlGtOnePos_inl (k : ℕ) : wenzlGtOnePos (Sum.inlₗ k) := by simp [wenzlGtOnePos]

/-- Right-branch letters `Sum.inrₗ k` are negative in the `1 < Q` model. -/
@[simp]
theorem not_wenzlGtOnePos_inr (k : ℕᵒᵈ) : ¬ wenzlGtOnePos (Sum.inrₗ k) := by simp [wenzlGtOnePos]

/-- Real geometric weights on `ℕ ⊕ₗ ℕᵒᵈ` for `1 < Q` and projection parameter `η`:
`((1 + Q) * η - 1) / Q ^ (k + 1)` on positive letters `Sum.inlₗ k` and
`(Q - (1 + Q) * η) / Q ^ (k + 1)` on negative letters `Sum.inrₗ (toDual k)`. -/
noncomputable def wenzlGtOneWeight (Q η : ℝ) (a : ℕ ⊕ₗ ℕᵒᵈ) : ℝ :=
  match ofLex a with
  | Sum.inl k => ((1 + Q) * η - 1) * Q⁻¹ * (Q⁻¹) ^ k
  | Sum.inr k => (Q - (1 + Q) * η) * Q⁻¹ * (Q⁻¹) ^ ofDual k

/-- Value of `wenzlGtOneWeight` on a left-branch letter `Sum.inlₗ k`. -/
@[simp]
theorem wenzlGtOneWeight_inl (Q η : ℝ) (k : ℕ) :
    wenzlGtOneWeight Q η (Sum.inlₗ k) = ((1 + Q) * η - 1) * Q⁻¹ * (Q⁻¹) ^ k := by
  simp [wenzlGtOneWeight]

/-- Value of `wenzlGtOneWeight` on a right-branch letter `Sum.inrₗ k`. -/
@[simp]
theorem wenzlGtOneWeight_inr (Q η : ℝ) (k : ℕᵒᵈ) :
    wenzlGtOneWeight Q η (Sum.inrₗ k) = (Q - (1 + Q) * η) * Q⁻¹ * (Q⁻¹) ^ ofDual k := by
  simp [wenzlGtOneWeight]

private theorem wenzlGtOneWeight_eq_twoSidedGeom (Q η : ℝ) :
    wenzlGtOneWeight Q η =
      twoSidedGeom (((1 + Q) * η - 1) * Q⁻¹) ((Q - (1 + Q) * η) * Q⁻¹) Q⁻¹ := by
  ext a
  obtain ⟨k | k, rfl⟩ := toLex.surjective a <;> simp

/-- For `1 < Q` and `η ∈ [1 / (1 + Q), Q / (1 + Q)]`, `wenzlGtOneWeight Q η` is nonnegative. -/
theorem wenzlGtOneWeight_nonneg {Q : ℝ} (hQ : 1 < Q) {η : ℝ}
    (hη : η ∈ Set.Icc (1 / (1 + Q)) (Q / (1 + Q))) (a : ℕ ⊕ₗ ℕᵒᵈ) :
    0 ≤ wenzlGtOneWeight Q η a := by
  have hr0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hQ).le
  have h1Q : 0 < 1 + Q := by linarith
  have hs : 0 ≤ (1 + Q) * η - 1 := by linarith [(div_le_iff₀ h1Q).mp hη.1]
  have hc : 0 ≤ Q - (1 + Q) * η := by linarith [(le_div_iff₀ h1Q).mp hη.2]
  rw [wenzlGtOneWeight_eq_twoSidedGeom]
  exact twoSidedGeom_nonneg (mul_nonneg hs hr0) (mul_nonneg hc hr0) hr0 a

/-- For `1 < Q` and any `η : ℝ`, `wenzlGtOneWeight Q η` is absolutely summable. -/
theorem summable_norm_wenzlGtOneWeight {Q : ℝ} (hQ : 1 < Q) (η : ℝ) :
    Summable fun a ↦ ‖wenzlGtOneWeight Q η a‖ := by
  rw [wenzlGtOneWeight_eq_twoSidedGeom]
  exact summable_norm_twoSidedGeom _ _ (inv_nonneg.mpr (zero_lt_one.trans hQ).le)
    (inv_lt_one_of_one_lt₀ hQ)

/-- For `1 < Q` and any `η : ℝ`, the total weight of `wenzlGtOneWeight Q η` is `1`. -/
theorem tsum_wenzlGtOneWeight {Q : ℝ} (hQ : 1 < Q) (η : ℝ) :
    (∑' a, wenzlGtOneWeight Q η a) = 1 := by
  have hQ0 : Q ≠ 0 := (zero_lt_one.trans hQ).ne'
  have hQ1 : Q - 1 ≠ 0 := sub_ne_zero.mpr hQ.ne'
  rw [wenzlGtOneWeight_eq_twoSidedGeom,
    tsum_twoSidedGeom _ _ (inv_nonneg.mpr (zero_lt_one.trans hQ).le) (inv_lt_one_of_one_lt₀ hQ)]
  field_simp; ring

/-- Every left slice of `wenzlGtOneWeight Q η` equals `(1 + Q) * η - 1`. -/
theorem wenzlGtOneWeight_leftSlice {Q : ℝ} (hQ : 1 < Q) (η : ℝ) (b : ℕ ⊕ₗ ℕᵒᵈ) :
    (if wenzlGtOnePos b then Q else -1) * wenzlGtOneWeight Q η b +
      (Q - 1) * (∑' a, if a < b then wenzlGtOneWeight Q η a else 0) = (1 + Q) * η - 1 := by
  have hQ0 : Q ≠ 0 := (zero_lt_one.trans hQ).ne'
  have hQsub : Q - 1 = Q * (1 - Q⁻¹) := by field_simp
  obtain ⟨m | m, rfl⟩ := toLex.surjective b
  · rw [hQsub, mul_assoc, wenzlGtOneWeight_inl, wenzlGtOneWeight_eq_twoSidedGeom,
      mul_tsum_lt_twoSidedGeom_inl]
    simp only [wenzlGtOnePos_inl, ↓reduceIte]; field_simp; ring
  · obtain ⟨m, rfl⟩ := toDual.surjective m
    rw [hQsub, mul_assoc, wenzlGtOneWeight_inr, wenzlGtOneWeight_eq_twoSidedGeom,
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

/-! ### The `0 < Q < 1` countable model on `ℕ ⊕ₗ ℕᵒᵈ` -/

/-- Sign predicate on `ℕ ⊕ₗ ℕᵒᵈ` for `0 < Q < 1`: negative on `ℕ`, positive on `ℕᵒᵈ`. -/
def wenzlLtOnePos (a : ℕ ⊕ₗ ℕᵒᵈ) : Prop :=
  (ofLex a).isRight = true

instance : DecidablePred wenzlLtOnePos :=
  fun a ↦ inferInstanceAs (Decidable ((ofLex a).isRight = true))

/-- Left-branch letters `Sum.inlₗ k` are negative in the `0 < Q < 1` model. -/
@[simp]
theorem not_wenzlLtOnePos_inl (k : ℕ) : ¬ wenzlLtOnePos (Sum.inlₗ k) := by simp [wenzlLtOnePos]

/-- Right-branch letters `Sum.inrₗ k` are positive in the `0 < Q < 1` model. -/
@[simp] theorem wenzlLtOnePos_inr (k : ℕᵒᵈ) : wenzlLtOnePos (Sum.inrₗ k) := by simp [wenzlLtOnePos]

/-- Real geometric weights on `ℕ ⊕ₗ ℕᵒᵈ` for `0 < Q < 1` and projection parameter `η`. -/
noncomputable def wenzlLtOneWeight (Q η : ℝ) (a : ℕ ⊕ₗ ℕᵒᵈ) : ℝ :=
  match ofLex a with
  | Sum.inl k => (1 - (1 + Q) * η) * Q ^ k
  | Sum.inr k => ((1 + Q) * η - Q) * Q ^ ofDual k

/-- Value of `wenzlLtOneWeight` on a left-branch letter `Sum.inlₗ k`. -/
@[simp]
theorem wenzlLtOneWeight_inl (Q η : ℝ) (k : ℕ) :
    wenzlLtOneWeight Q η (Sum.inlₗ k) = (1 - (1 + Q) * η) * Q ^ k := by simp [wenzlLtOneWeight]

/-- Value of `wenzlLtOneWeight` on a right-branch letter `Sum.inrₗ k`. -/
@[simp]
theorem wenzlLtOneWeight_inr (Q η : ℝ) (k : ℕᵒᵈ) :
    wenzlLtOneWeight Q η (Sum.inrₗ k) = ((1 + Q) * η - Q) * Q ^ ofDual k := by
  simp [wenzlLtOneWeight]

private theorem wenzlLtOneWeight_eq_twoSidedGeom (Q η : ℝ) :
    wenzlLtOneWeight Q η = twoSidedGeom (1 - (1 + Q) * η) ((1 + Q) * η - Q) Q := by
  ext a
  obtain ⟨k | k, rfl⟩ := toLex.surjective a <;> simp

/-- For `0 < Q < 1` and `η ∈ [Q / (1 + Q), 1 / (1 + Q)]`, `wenzlLtOneWeight Q η` is nonnegative. -/
theorem wenzlLtOneWeight_nonneg {Q : ℝ} (hQ0 : 0 < Q) {η : ℝ}
    (hη : η ∈ Set.Icc (Q / (1 + Q)) (1 / (1 + Q))) (a : ℕ ⊕ₗ ℕᵒᵈ) :
    0 ≤ wenzlLtOneWeight Q η a := by
  have h1Q : 0 < 1 + Q := by linarith
  rw [wenzlLtOneWeight_eq_twoSidedGeom]
  exact twoSidedGeom_nonneg (by linarith [(le_div_iff₀ h1Q).mp hη.2])
    (by linarith [(div_le_iff₀ h1Q).mp hη.1]) hQ0.le a

/-- For `0 < Q < 1` and any `η : ℝ`, `wenzlLtOneWeight Q η` is absolutely summable. -/
theorem summable_norm_wenzlLtOneWeight {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ) :
    Summable fun a ↦ ‖wenzlLtOneWeight Q η a‖ := by
  rw [wenzlLtOneWeight_eq_twoSidedGeom]
  exact summable_norm_twoSidedGeom _ _ hQ0.le hQ1

/-- For `0 < Q < 1` and any `η : ℝ`, the total weight of `wenzlLtOneWeight Q η` is `1`. -/
theorem tsum_wenzlLtOneWeight {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ) :
    (∑' a, wenzlLtOneWeight Q η a) = 1 := by
  have h1Q : 1 - Q ≠ 0 := sub_ne_zero.mpr hQ1.ne'
  rw [wenzlLtOneWeight_eq_twoSidedGeom, tsum_twoSidedGeom _ _ hQ0.le hQ1]
  field_simp; ring

/-- Every left slice of `wenzlLtOneWeight Q η` equals `(1 + Q) * η - 1`. -/
theorem wenzlLtOneWeight_leftSlice {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (η : ℝ)
    (b : ℕ ⊕ₗ ℕᵒᵈ) :
    (if wenzlLtOnePos b then Q else -1) * wenzlLtOneWeight Q η b +
      (Q - 1) * (∑' a, if a < b then wenzlLtOneWeight Q η a else 0) = (1 + Q) * η - 1 := by
  obtain ⟨m | m, rfl⟩ := toLex.surjective b
  · rw [← neg_sub 1 Q, neg_mul, wenzlLtOneWeight_inl,
      wenzlLtOneWeight_eq_twoSidedGeom, mul_tsum_lt_twoSidedGeom_inl]
    simp only [not_wenzlLtOnePos_inl, ↓reduceIte]; ring
  · obtain ⟨m, rfl⟩ := toDual.surjective m
    rw [← neg_sub 1 Q, neg_mul, wenzlLtOneWeight_inr,
      wenzlLtOneWeight_eq_twoSidedGeom, mul_tsum_lt_twoSidedGeom_inr _ _ hQ0.le hQ1, pow_succ']
    simp only [wenzlLtOnePos_inr, ↓reduceIte, ofDual_toDual]; ring

/-- **Countable geometric realization of the Ocneanu trace for `0 < Q < 1`.** -/
theorem countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace {q : ℂˣ} {Q : ℝ} (hQ0 : 0 < Q)
    (hQ1 : Q < 1) (hqQ : (q : ℂ) ^ 2 = Q) (η : ℝ) {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicTrace wenzlLtOnePos q (fun a ↦ (wenzlLtOneWeight Q η a : ℂ))
        ((summable_norm_wenzlLtOneWeight hQ0 hQ1 η).congr fun _ ↦ (Complex.norm_real _).symm) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace ℂ q
        ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (toInfinite ℂ q n x) :=
  countableAtomicTrace_ofReal_eq_ocneanuTrace_of_leftSlice wenzlLtOnePos hqQ
    (summable_norm_wenzlLtOneWeight hQ0 hQ1 η) η (tsum_wenzlLtOneWeight hQ0 hQ1 η)
    (wenzlLtOneWeight_leftSlice hQ0 hQ1 η) x

end CountableGeometricModels

end TauCeti.TypeAHeckeAlgebra
