/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Sum.Order
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable
import Mathlib.Analysis.Complex.Order
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Zero

/-!
# Countable geometric models and positivity of positive-real Markov traces

For real nonzero `q : ℂˣ` (`IsSelfAdjoint (q : ℂ)`) with `Q = q ^ 2 > 0`, writing
`z = q * η - q⁻¹ * (1 - η)` gives `q * z = (1 + Q) * η - 1`. Over Wenzl's positive-real set
`TauCeti.wenzlPositiveSet Q` (defined in `TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam`), we prove
positivity of the Ocneanu trace
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg`, bundled as
`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuPositiveFunctional`) by combining:
1. **Two-sided geometric models on `ℕ ⊕ₗ ℕᵒᵈ` (`1 < Q` and `0 < Q < 1`)**: `wenzlGtOneWeight` and
   `wenzlLtOneWeight` realize the continuous interval, with telescoping cycle-trace product
   `(1 + c * x) / (1 - s * x)` for `1 < Q` (`wenzlGtOneWeight_cycleWord_hasProd`).
2. **The `z = 0` Ocneanu trace (`η = 1 / 2` at `Q = 1`)**: positive by
   `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_zero_star_mul_self_nonneg`.
3. **Finite positive/negative geometric atomic models (`d ≠ 0`, `Q > 0`)**.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
-/

public section

open Filter Function Finsupp OrderDual
open scoped Topology ComplexOrder

namespace TauCeti

namespace TypeAHeckeAlgebra

section CountableGeometricModels

private noncomputable def twoSidedGeom (a₁ a₂ r : ℝ) (a : ℕ ⊕ₗ ℕᵒᵈ) : ℝ :=
  match ofLex a with
  | Sum.inl k => a₁ * r ^ k
  | Sum.inr k => a₂ * r ^ ofDual k

private theorem twoSidedGeom_nonneg {a₁ a₂ r : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (hr : 0 ≤ r)
    (a : ℕ ⊕ₗ ℕᵒᵈ) : 0 ≤ twoSidedGeom a₁ a₂ r a := by
  cases ha : ofLex a <;> simp only [twoSidedGeom, ha] <;> positivity

private theorem summable_norm_twoSidedGeom (a₁ a₂ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun a ↦ ‖twoSidedGeom a₁ a₂ r a‖ := by
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  refine ((Equiv.sumCongr (Equiv.refl ℕ) toDual).trans toLex).summable_iff.mp <|
    Summable.sum _
      ((hgeom.mul_left ‖a₁‖).congr fun k ↦ by simp [twoSidedGeom, abs_of_nonneg hr0])
      ((hgeom.mul_left ‖a₂‖).congr fun k ↦ by simp [twoSidedGeom, abs_of_nonneg hr0])

private theorem tsum_twoSidedGeom (a₁ a₂ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' a, twoSidedGeom a₁ a₂ r a) = (a₁ + a₂) / (1 - r) := by
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  let e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ₗ ℕᵒᵈ) := (Equiv.sumCongr (Equiv.refl ℕ) toDual).trans toLex
  rw [(e.tsum_eq _).symm.trans (Summable.tsum_sum (f := twoSidedGeom a₁ a₂ r ∘ e)
    (hgeom.mul_left a₁) (hgeom.mul_left a₂))]
  simp only [e, comp_def, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl,
    Sum.map_inr, twoSidedGeom, ofLex_toLex, ofDual_toDual, hgeom.tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1]
  ring

private theorem mul_tsum_lt_twoSidedGeom_inl (a₁ a₂ r : ℝ) (m : ℕ) :
    (1 - r) * (∑' a : ℕ ⊕ₗ ℕᵒᵈ, if a < Sum.inlₗ m then twoSidedGeom a₁ a₂ r a else 0) =
      a₁ * (1 - r ^ m) := by
  have hpref : HasSum (fun k : ℕ ↦ if k < m then a₁ * r ^ k else 0)
      (∑ k ∈ Finset.range m, a₁ * r ^ k) := by
    convert hasSum_subtype_iff_indicator.mp ((Finset.range m).hasSum fun k ↦ a₁ * r ^ k) using 1
    ext k; simp [Set.indicator_apply]
  let e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ₗ ℕᵒᵈ) := (Equiv.sumCongr (Equiv.refl ℕ) toDual).trans toLex
  rw [(e.tsum_eq _).symm.trans (Summable.tsum_sum
    (f := (fun a : ℕ ⊕ₗ ℕᵒᵈ ↦ if a < Sum.inlₗ m then twoSidedGeom a₁ a₂ r a else 0) ∘ e)
    (by simpa [e, comp_def, twoSidedGeom] using hpref.summable) (by simp [e, comp_def]))]
  simp only [e, comp_def, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl,
    Sum.map_inr, twoSidedGeom, ofLex_toLex, Sum.Lex.inl_lt_inl_iff, Sum.Lex.not_inr_lt_inl,
    ↓reduceIte, tsum_zero, add_zero, hpref.tsum_eq, ← Finset.mul_sum]
  rw [mul_left_comm, mul_neg_geom_sum]

private theorem mul_tsum_lt_twoSidedGeom_inr (a₁ a₂ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m : ℕ) :
    (1 - r) * (∑' a : ℕ ⊕ₗ ℕᵒᵈ, if a < Sum.inrₗ (toDual m) then twoSidedGeom a₁ a₂ r a else 0) =
      a₁ + a₂ * r ^ (m + 1) := by
  have hgeom := summable_geometric_of_lt_one hr0 hr1; have h₂ := hgeom.mul_left a₂
  have htail_sum : Summable fun k : ℕ ↦ if m < k then a₂ * r ^ k else 0 := by
    convert (summable_subtype_iff_indicator (s := (Finset.range (m + 1) : Set ℕ)ᶜ)
      (f := fun k ↦ a₂ * r ^ k)).mp ((Finset.range (m + 1)).summable_compl_iff.mpr h₂) using 1
    ext k; simp [Set.indicator_apply]
  have htail : (∑' k : ℕ, if m < k then a₂ * r ^ k else 0) =
      (∑' k : ℕ, a₂ * r ^ k) - ∑ k ∈ Finset.range (m + 1), a₂ * r ^ k := by
    have hsplit := h₂.sum_add_tsum_compl (s := Finset.range (m + 1))
    rw [tsum_subtype (s := (Finset.range (m + 1) : Set ℕ)ᶜ) (fun k ↦ a₂ * r ^ k),
      tsum_congr (g := fun k ↦ if m < k then a₂ * r ^ k else 0) fun k ↦ by
        simp [Set.indicator_apply]] at hsplit
    linarith
  let e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ₗ ℕᵒᵈ) := (Equiv.sumCongr (Equiv.refl ℕ) toDual).trans toLex
  rw [(e.tsum_eq _).symm.trans (Summable.tsum_sum
    (f := (fun a : ℕ ⊕ₗ ℕᵒᵈ ↦ if a < Sum.inrₗ (toDual m) then twoSidedGeom a₁ a₂ r a else 0) ∘ e)
    (by simpa [e, comp_def, twoSidedGeom] using hgeom.mul_left a₁)
    (by simpa [e, comp_def, twoSidedGeom] using htail_sum))]
  simp only [e, comp_def, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl,
    Sum.map_inr, twoSidedGeom, ofLex_toLex, ofDual_toDual, Sum.Lex.inl_lt_inr,
    Sum.Lex.inr_lt_inr_iff, toDual_lt_toDual, ↓reduceIte, htail, hgeom.tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1, ← Finset.mul_sum]
  rw [mul_add, mul_sub, mul_left_comm (1 - r) a₂ (∑ _ ∈ _, _), mul_neg_geom_sum]
  have h1r : 1 - r ≠ 0 := sub_ne_zero.mpr hr1.ne'; field_simp; ring

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
  push_cast [Complex.ofReal_tsum, apply_ite ((↑) : ℝ → ℂ)] at hsl
  rw [← hqQ] at hsl
  have _ := q.ne_zero; rw [hsl, Units.val_inv_eq_inv_val]; field_simp; ring

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
      twoSidedGeom (((1 + Q) * η - 1) * Q⁻¹) ((Q - (1 + Q) * η) * Q⁻¹) Q⁻¹ := rfl

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
  have hp : Summable fun a ↦ ‖(wenzlGtOneWeight Q η a : ℂ)‖ :=
    (summable_norm_wenzlGtOneWeight hQ η).congr fun _ ↦ (Complex.norm_real _).symm
  have hnorm_sum : (∑' a, ‖(wenzlGtOneWeight Q η a : ℂ)‖) = 1 := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg (wenzlGtOneWeight_nonneg hQ hη _)] using
      tsum_wenzlGtOneWeight hQ η
  have hmax : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) = Q := by
    rw [hqQ, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (zero_lt_one.trans hQ).le, Real.norm_of_nonneg (sub_nonneg.mpr hQ.le),
      max_eq_left (a := Q) (b := Q - 1) (by linarith), max_eq_right hQ.le]
  have hprod := (countableAtomicTrace_cycleWord_hasProd wenzlGtOnePos q _ hp
    (by rwa [hmax, hnorm_sum, mul_one])).2
  set s : ℝ := (1 + Q) * η - 1
  have hs0 : 0 ≤ s := by linarith [(div_le_iff₀ (by linarith : 0 < 1 + Q)).mp hη.1]
  have hsx : ‖(s : ℂ) * x‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
    exact (mul_le_mul_of_nonneg_right
      (by linarith [(le_div_iff₀ (by linarith : 0 < 1 + Q)).mp hη.2])
      (norm_nonneg x)).trans_lt hx
  have htr (m : ℕ) : countableAtomicTrace wenzlGtOnePos q (fun a ↦ (wenzlGtOneWeight Q η a : ℂ))
      hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1) = x * ((s : ℂ) * x) ^ m := by
    rw [countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace hQ hqQ η, toInfinite_cycleWord,
      (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace _).map_cycleWord, Nat.add_sub_cancel,
      show (q : ℂ) * ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) = (s : ℂ) by
        have _ := q.ne_zero; dsimp only [s]; push_cast; rw [← hqQ]; field_simp; ring]
    ring
  have hne : 1 - (s : ℂ) * x ≠ 0 := fun h0 ↦ by
    have : ‖(s : ℂ) * x‖ = 1 := by simpa [sub_eq_zero.mp h0] using norm_one (α := ℂ)
    linarith
  convert hprod using 1
  simp_rw [htr]
  rw [(summable_geometric_of_norm_lt_one hsx).tsum_mul_left,
    tsum_geometric_of_norm_lt_one hsx, hqQ, eq_comm, eq_div_iff hne]
  have hmul : (1 - (s : ℂ) * x)⁻¹ * (1 - (s : ℂ) * x) = 1 := inv_mul_cancel₀ hne
  dsimp only [s] at hmul ⊢; push_cast at hmul ⊢; linear_combination ((Q : ℂ) - 1) * x * hmul

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
    wenzlLtOneWeight Q η = twoSidedGeom (1 - (1 + Q) * η) ((1 + Q) * η - Q) Q := rfl

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
  · rw [show Q - 1 = -(1 - Q) by ring, neg_mul, wenzlLtOneWeight_inl,
      wenzlLtOneWeight_eq_twoSidedGeom, mul_tsum_lt_twoSidedGeom_inl]
    simp only [not_wenzlLtOnePos_inl, ↓reduceIte]; ring
  · obtain ⟨m, rfl⟩ := toDual.surjective m
    rw [show Q - 1 = -(1 - Q) by ring, neg_mul, wenzlLtOneWeight_inr,
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

end TypeAHeckeAlgebra

/-! ### Positivity of `ocneanuTrace` across Wenzl's positive-real parameter set -/

namespace InfiniteTypeAHeckeAlgebra

private theorem ocneanuTrace_wenzlParam_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {Q : ℝ} (hQ0 : 0 < Q) (hQ : (Q : ℂ) = (q : ℂ) ^ 2) (b : Bool) (r : ℕ) {n : ℕ}
    (y : TypeAHeckeAlgebra ℂ q n) :
    let d : ℤ := if b then ((r + 1 : ℕ) : ℤ) else -((r + 1 : ℕ) : ℤ)
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * ((wenzlParam d Q : ℝ) : ℂ) -
        (↑q⁻¹ : ℂ) * (1 - ((wenzlParam d Q : ℝ) : ℂ)))
      (TypeAHeckeAlgebra.toInfinite ℂ q n (star y * y)) := by
  set Z : ℝ := ∑ a ∈ Finset.range (r + 1), Q ^ a
  have hZ0 : 0 < Z :=
    Finset.sum_pos (fun a _ ↦ pow_pos hQ0 a) (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero r))
  set c : ℝ := Z⁻¹
  have hcZ : (c : ℂ) * ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a = 1 := by
    simpa [c, Z, hQ] using congrArg ((↑) : ℝ → ℂ) (inv_mul_cancel₀ hZ0.ne')
  have h1Q : 1 + (q : ℂ) ^ 2 ≠ 0 := by
    rw [← hQ, ← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hZc := right_ne_zero_of_mul_eq_one hcZ
  have hq0 := q.ne_zero
  have hw (a : Fin (r + 1)) : (0 : ℂ) ≤ (c : ℂ) * ((q : ℂ) ^ 2) ^ (a : ℕ) := by
    simpa [hQ] using Complex.zero_le_real.mpr (show 0 ≤ c * Q ^ (a : ℕ) by positivity)
  have hmap (d : ℤ) : ((wenzlParam d Q : ℝ) : ℂ) = wenzlParam d (Q : ℂ) := by
    simpa using map_wenzlParam Complex.ofRealHom d Q
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hg : ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a =
        (q : ℂ) ^ 2 * ∑ a ∈ Finset.range r, ((q : ℂ) ^ 2) ^ a + 1 := by
      simp [Finset.sum_range_succ', pow_succ', ← Finset.mul_sum]
    have hz : (q : ℂ) * ((wenzlParam (-((r + 1 : ℕ) : ℤ)) Q : ℝ) : ℂ) -
        (↑q⁻¹ : ℂ) * (1 - ((wenzlParam (-((r + 1 : ℕ) : ℤ)) Q : ℝ) : ℂ)) = -((c : ℂ) * ↑q⁻¹) := by
      rw [hmap, hQ, wenzlParam_neg_natCast, Nat.add_sub_cancel, Units.val_inv_eq_inv_val]
      field_simp; linear_combination -((1 + (q : ℂ) ^ 2) * hg) + (1 + (q : ℂ) ^ 2) * hcZ
    rw [hz, ← TypeAHeckeAlgebra.atomicTrace_negGeometric_eq q hcZ (star y * y)]
    exact TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg _ q hw y
  · simp only [↓reduceIte]
    have hz : (q : ℂ) * ((wenzlParam ((r + 1 : ℕ) : ℤ) Q : ℝ) : ℂ) -
        (↑q⁻¹ : ℂ) * (1 - ((wenzlParam ((r + 1 : ℕ) : ℤ) Q : ℝ) : ℂ)) =
        (c : ℂ) * (q : ℂ) ^ (2 * r + 1) := by
      rw [hmap, hQ, wenzlParam_natCast, Units.val_inv_eq_inv_val, geom_sum_succ' (n := r + 1)]
      field_simp; linear_combination -((1 + (q : ℂ) ^ 2) * (q : ℂ) ^ (2 * r + 2)) * hcZ
    rw [hz, ← TypeAHeckeAlgebra.atomicTrace_geometric_eq q hcZ (star y * y)]
    exact TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg _ q hw y

/-- **Positivity of the Ocneanu trace across Wenzl's positive-real parameter set.** For real nonzero
`q : ℂˣ` with `(Q : ℂ) = (q : ℂ) ^ 2` and `η ∈ wenzlPositiveSet Q`, the Ocneanu trace at
`z = q * η - q⁻¹ * (1 - η)` is nonnegative on every `star x * x`. -/
theorem ocneanuTrace_star_mul_self_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (star x * x) := by
  have hQ0 : 0 < Q := by
    have hre : (q : ℂ) = ((q : ℂ).re : ℂ) :=
      (Complex.conj_eq_iff_re.mp (Fact.out : IsSelfAdjoint (q : ℂ)).star_eq).symm
    rw [Complex.ofReal_injective
      (hQ.trans ((congrArg (· ^ 2) hre).trans (Complex.ofReal_pow _ 2).symm))]
    exact sq_pos_of_ne_zero fun h0 ↦ q.ne_zero (by rw [hre, h0, Complex.ofReal_zero])
  obtain ⟨n, hx⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite, AlgHom.mem_range] at hx; obtain ⟨y, rfl⟩ := hx
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul]
  rcases mem_wenzlPositiveSet_iff.mp hη with hIcc | ⟨d, hd, rfl⟩
  · rcases lt_trichotomy Q 1 with hQ1 | rfl | hQ1
    · have hle : Q / (1 + Q) ≤ 1 / (1 + Q) := div_le_div_of_nonneg_right hQ1.le (by linarith)
      rw [min_eq_right hle, max_eq_left hle] at hIcc
      rw [← TypeAHeckeAlgebra.countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace hQ0 hQ1 hQ.symm]
      exact TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg _ q _
        (fun a ↦ Complex.zero_le_real.mpr (TypeAHeckeAlgebra.wenzlLtOneWeight_nonneg hQ0 hIcc a)) y
    · rw [show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num, min_self, max_self,
        Set.Icc_self, Set.mem_singleton_iff] at hIcc
      subst hIcc
      have hz0 : (q : ℂ) * ((1 / 2 : ℝ) : ℂ) - (↑q⁻¹ : ℂ) * (1 - ((1 / 2 : ℝ) : ℂ)) = 0 := by
        have _ := q.ne_zero; have hq2 : (q : ℂ) ^ 2 = 1 := by simpa using hQ.symm
        rw [Units.val_inv_eq_inv_val]; push_cast; field_simp; linear_combination hq2
      rw [hz0, map_mul, TypeAHeckeAlgebra.toInfinite_star]
      exact ocneanuTrace_zero_star_mul_self_nonneg _
    · have hle : 1 / (1 + Q) ≤ Q / (1 + Q) := div_le_div_of_nonneg_right hQ1.le (by linarith)
      rw [min_eq_left hle, max_eq_right hle] at hIcc
      rw [← TypeAHeckeAlgebra.countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace hQ1 hQ.symm]
      exact TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg _ q _
        (fun a ↦ Complex.zero_le_real.mpr (TypeAHeckeAlgebra.wenzlGtOneWeight_nonneg hQ1 hIcc a)) y
  · obtain ⟨_ | r, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · exact absurd rfl hd
    · simp at hd
    · exact ocneanuTrace_wenzlParam_nonneg hQ0 hQ true r y
    · exact ocneanuTrace_wenzlParam_nonneg hQ0 hQ false r y

/-- The complex Ocneanu trace on `InfiniteTypeAHeckeAlgebra ℂ q` bundled as a
`StarPositiveFunctional` for real nonzero `q : ℂˣ` and `η ∈ wenzlPositiveSet Q`. -/
noncomputable def ocneanuPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q) :
    StarPositiveFunctional (InfiniteTypeAHeckeAlgebra ℂ q) where
  toLinearMap := ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))
  square_nonneg := ocneanuTrace_star_mul_self_nonneg hQ hη

@[simp]
theorem ocneanuPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    ocneanuPositiveFunctional q hQ hη x =
      ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) x := (rfl)

end InfiniteTypeAHeckeAlgebra

end TauCeti
