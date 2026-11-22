/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Sum.Order
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic
import TauCeti.Analysis.SpecificLimits.TwoSidedGeometric

/-!
# Countable geometric models on Wenzl's continuous interval

For real nonzero `q : ℂˣ` with `Q = q ^ 2 > 0`, writing `z = q * η - q⁻¹ * (1 - η)` gives
`q * z = (1 + Q) * η - 1`. We construct the countable two-sided geometric atomic models on
`ℕ ⊕ₗ ℕᵒᵈ` realizing every parameter `η` in Wenzl's continuous interval:

* **For `1 < Q`** (`wenzlGtOnePos`, `wenzlGtOneWeight`): positive letters on `ℕ` followed by
  negative letters on `ℕᵒᵈ`, realizing the Ocneanu trace for any `η`
  (`countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace`), nonnegative on
  `[1 / (1 + Q), Q / (1 + Q)]` (`wenzlGtOneWeight_nonneg`), with telescoping cycle-trace product
  `(1 + (Q - (1 + Q) * η) * x) / (1 - ((1 + Q) * η - 1) * x)` on `Q * ‖x‖ < 1`
  (`wenzlGtOneWeight_cycleWord_hasProd`).
* **For `0 < Q < 1`** (`wenzlLtOnePos`, `wenzlLtOneWeight`): negative letters on `ℕ` followed by
  positive letters on `ℕᵒᵈ`, realizing the Ocneanu trace for any `η`
  (`countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace`), nonnegative on
  `[Q / (1 + Q), 1 / (1 + Q)]` (`wenzlLtOneWeight_nonneg`), with the same telescoping cycle-trace
  product on `‖x‖ < 1` (`wenzlLtOneWeight_cycleWord_hasProd`).

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

private theorem mul_markovParam_proj_eq {q : ℂˣ} {Q : ℝ} (hqQ : (q : ℂ) ^ 2 = Q) (η : ℝ) :
    (q : ℂ) * ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) = (((1 + Q) * η - 1 : ℝ) : ℂ) := by
  simpa [← hqQ] using mul_sub_val_inv_mul_one_sub q (η : ℂ)

private theorem countableAtomicTrace_ofReal_eq_ocneanuTrace_of_leftSlice {ι : Type*}
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

private theorem hasProd_ofReal_cycleWord {ι : Type*} [LinearOrder ι] (pos : ι → Prop)
    [DecidablePred pos] {q : ℂˣ} {Q : ℝ} (hqQ : (q : ℂ) ^ 2 = Q) {w : ι → ℝ}
    (hw : Summable fun a ↦ ‖w a‖) (hw0 : ∀ a, 0 ≤ w a) (hsum : (∑' a, w a) = 1)
    (η : ℝ) (hslice : ∀ b, (if pos b then Q else -1) * w b +
      (Q - 1) * (∑' a, if a < b then w a else 0) = (1 + Q) * η - 1)
    {x : ℂ} (hxM : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ‖x‖ < 1)
    (hsx : ‖(((1 + Q) * η - 1 : ℝ) : ℂ) * x‖ < 1) :
    HasProd (fun a : ι ↦
        if pos a then (1 - (w a : ℂ) * x) / (1 - (q : ℂ) ^ 2 * (w a : ℂ) * x)
        else (1 + (q : ℂ) ^ 2 * (w a : ℂ) * x) / (1 + (w a : ℂ) * x))
      ((1 + ((Q - (1 + Q) * η : ℝ) : ℂ) * x) /
        (1 - (((1 + Q) * η - 1 : ℝ) : ℂ) * x)) := by
  have hp : Summable fun a ↦ ‖(w a : ℂ)‖ := hw.congr fun _ ↦ (Complex.norm_real _).symm
  have hnorm_sum : (∑' a, ‖(w a : ℂ)‖) = 1 := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg (hw0 _)] using hsum
  have hprod := (countableAtomicTrace_cycleWord_hasProd pos q _ hp (by rwa [hnorm_sum, mul_one])).2
  set s : ℝ := (1 + Q) * η - 1
  have htr (m : ℕ) : countableAtomicTrace pos q (fun a ↦ (w a : ℂ))
      hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1) = x * ((s : ℂ) * x) ^ m := by
    rw [countableAtomicTrace_ofReal_eq_ocneanuTrace_of_leftSlice pos hqQ hw η hsum hslice,
      toInfinite_cycleWord,
      (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace _).map_cycleWord,
      Nat.add_sub_cancel, mul_markovParam_proj_eq hqQ η]
    ring
  have hne : 1 - (s : ℂ) * x ≠ 0 := fun h0 ↦ by
    have : ‖(s : ℂ) * x‖ = 1 := by simpa [sub_eq_zero.mp h0] using norm_one (α := ℂ)
    linarith
  convert hprod using 1
  simp_rw [htr]
  rw [(summable_geometric_of_norm_lt_one hsx).tsum_mul_left,
    tsum_geometric_of_norm_lt_one hsx, hqQ, eq_comm, eq_div_iff hne]
  have hmul : (1 - (s : ℂ) * x)⁻¹ * (1 - (s : ℂ) * x) = 1 := inv_mul_cancel₀ hne
  dsimp only [s] at hmul ⊢
  push_cast at hmul ⊢
  linear_combination ((Q : ℂ) - 1) * x * hmul

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

/-- **Telescoping infinite product for Wenzl's `1 < Q` countable model.** For `1 < Q`,
`η ∈ [1 / (1 + Q), Q / (1 + Q)]`, and `Q * ‖x‖ < 1`, the cycle-trace product converges to
`(1 + (Q - (1 + Q) * η) * x) / (1 - ((1 + Q) * η - 1) * x)`. -/
theorem wenzlGtOneWeight_cycleWord_hasProd {q : ℂˣ} {Q : ℝ} (hQ : 1 < Q) (hqQ : (q : ℂ) ^ 2 = Q)
    {η : ℝ} (hη : η ∈ Set.Icc (1 / (1 + Q)) (Q / (1 + Q))) {x : ℂ} (hx : Q * ‖x‖ < 1) :
    HasProd (fun a : ℕ ⊕ₗ ℕᵒᵈ ↦
        if wenzlGtOnePos a then
          (1 - (wenzlGtOneWeight Q η a : ℂ) * x) /
            (1 - (q : ℂ) ^ 2 * (wenzlGtOneWeight Q η a : ℂ) * x)
        else
          (1 + (q : ℂ) ^ 2 * (wenzlGtOneWeight Q η a : ℂ) * x) /
            (1 + (wenzlGtOneWeight Q η a : ℂ) * x))
      ((1 + ((Q - (1 + Q) * η : ℝ) : ℂ) * x) /
        (1 - (((1 + Q) * η - 1 : ℝ) : ℂ) * x)) := by
  have hmax : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) = Q := by
    rw [hqQ, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (zero_lt_one.trans hQ).le, Real.norm_of_nonneg (sub_nonneg.mpr hQ.le),
      max_eq_left (a := Q) (b := Q - 1) (by linarith), max_eq_right hQ.le]
  have hs0 : 0 ≤ (1 + Q) * η - 1 := by linarith [(div_le_iff₀ (by linarith : 0 < 1 + Q)).mp hη.1]
  have hsx : ‖(((1 + Q) * η - 1 : ℝ) : ℂ) * x‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
    exact (mul_le_mul_of_nonneg_right
      (by linarith [(le_div_iff₀ (by linarith : 0 < 1 + Q)).mp hη.2])
      (norm_nonneg x)).trans_lt hx
  exact hasProd_ofReal_cycleWord wenzlGtOnePos hqQ (summable_norm_wenzlGtOneWeight hQ η)
    (wenzlGtOneWeight_nonneg hQ hη) (tsum_wenzlGtOneWeight hQ η) η
    (wenzlGtOneWeight_leftSlice hQ η) (by rwa [hmax]) hsx

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

/-- **Telescoping infinite product for Wenzl's `0 < Q < 1` countable model.** For `0 < Q < 1`,
`η ∈ [Q / (1 + Q), 1 / (1 + Q)]`, and `‖x‖ < 1`, the cycle-trace product converges to
`(1 + (Q - (1 + Q) * η) * x) / (1 - ((1 + Q) * η - 1) * x)`. -/
theorem wenzlLtOneWeight_cycleWord_hasProd {q : ℂˣ} {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1)
    (hqQ : (q : ℂ) ^ 2 = Q) {η : ℝ} (hη : η ∈ Set.Icc (Q / (1 + Q)) (1 / (1 + Q)))
    {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun a : ℕ ⊕ₗ ℕᵒᵈ ↦
        if wenzlLtOnePos a then
          (1 - (wenzlLtOneWeight Q η a : ℂ) * x) /
            (1 - (q : ℂ) ^ 2 * (wenzlLtOneWeight Q η a : ℂ) * x)
        else
          (1 + (q : ℂ) ^ 2 * (wenzlLtOneWeight Q η a : ℂ) * x) /
            (1 + (wenzlLtOneWeight Q η a : ℂ) * x))
      ((1 + ((Q - (1 + Q) * η : ℝ) : ℂ) * x) /
        (1 - (((1 + Q) * η - 1 : ℝ) : ℂ) * x)) := by
  have hmax : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) = 1 := by
    rw [hqQ, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hQ0.le, Real.norm_of_nonpos (sub_nonpos.mpr hQ1.le), neg_sub]
    exact max_eq_left (max_le hQ1.le (by linarith))
  have hs0 : (1 + Q) * η - 1 ≤ 0 := by linarith [(le_div_iff₀ (by linarith : 0 < 1 + Q)).mp hη.2]
  have hs1 : -(1 - Q) ≤ (1 + Q) * η - 1 := by
    linarith [(div_le_iff₀ (by linarith : 0 < 1 + Q)).mp hη.1]
  have hs_le : -((1 + Q) * η - 1) ≤ 1 := by linarith
  have hsx : ‖(((1 + Q) * η - 1 : ℝ) : ℂ) * x‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonpos hs0]
    exact (mul_le_mul_of_nonneg_right hs_le (norm_nonneg x)).trans_lt (by simpa using hx)
  exact hasProd_ofReal_cycleWord wenzlLtOnePos hqQ (summable_norm_wenzlLtOneWeight hQ0 hQ1 η)
    (wenzlLtOneWeight_nonneg hQ0 hη) (tsum_wenzlLtOneWeight hQ0 hQ1 η) η
    (wenzlLtOneWeight_leftSlice hQ0 hQ1 η) (by rwa [hmax, one_mul]) hsx

end CountableGeometricModels

end TauCeti.TypeAHeckeAlgebra
