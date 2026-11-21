/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Sum.Order
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Two-sided geometric series on `ℕ ⊕ₗ ℕᵒᵈ`

For real parameters `a₁, a₂, r : ℝ`, `TauCeti.twoSidedGeom a₁ a₂ r` defines the two-sided geometric
family on the lexicographic sum `ℕ ⊕ₗ ℕᵒᵈ` taking the value `a₁ * r ^ k` on `Sum.inlₗ k` and
`a₂ * r ^ ofDual k` on `Sum.inrₗ k`. When `0 ≤ r < 1`, the family is absolutely summable with sum
`(a₁ + a₂) / (1 - r)` (`TauCeti.summable_norm_twoSidedGeom`, `TauCeti.tsum_twoSidedGeom`), and its
initial-segment sums up to `Sum.inlₗ m` and `Sum.inrₗ (toDual m)` evaluate in closed form
(`TauCeti.mul_tsum_lt_twoSidedGeom_inl`, `TauCeti.mul_tsum_lt_twoSidedGeom_inr`).
-/

public section

open Function OrderDual

namespace TauCeti

/-- The two-sided geometric family on `ℕ ⊕ₗ ℕᵒᵈ` with values `a₁ * r ^ k` on the left branch
`Sum.inlₗ k` and `a₂ * r ^ ofDual k` on the right branch `Sum.inrₗ k`. -/
noncomputable def twoSidedGeom (a₁ a₂ r : ℝ) (a : ℕ ⊕ₗ ℕᵒᵈ) : ℝ :=
  match ofLex a with
  | Sum.inl k => a₁ * r ^ k
  | Sum.inr k => a₂ * r ^ ofDual k

/-- Value of `twoSidedGeom` on a left-branch index `Sum.inlₗ k`. -/
@[simp]
theorem twoSidedGeom_inl (a₁ a₂ r : ℝ) (k : ℕ) :
    twoSidedGeom a₁ a₂ r (Sum.inlₗ k) = a₁ * r ^ k := by simp [twoSidedGeom]

/-- Value of `twoSidedGeom` on a right-branch index `Sum.inrₗ k`. -/
@[simp]
theorem twoSidedGeom_inr (a₁ a₂ r : ℝ) (k : ℕᵒᵈ) :
    twoSidedGeom a₁ a₂ r (Sum.inrₗ k) = a₂ * r ^ ofDual k := by simp [twoSidedGeom]

/-- Nonnegativity of `twoSidedGeom a₁ a₂ r` when `a₁`, `a₂`, and `r` are nonnegative. -/
theorem twoSidedGeom_nonneg {a₁ a₂ r : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (hr : 0 ≤ r)
    (a : ℕ ⊕ₗ ℕᵒᵈ) : 0 ≤ twoSidedGeom a₁ a₂ r a := by
  cases ha : ofLex a <;> simp only [twoSidedGeom, ha] <;> positivity

/-- Absolute summability of `twoSidedGeom a₁ a₂ r` for `0 ≤ r < 1`. -/
theorem summable_norm_twoSidedGeom (a₁ a₂ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun a ↦ ‖twoSidedGeom a₁ a₂ r a‖ := by
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  refine ((Equiv.sumCongr (Equiv.refl ℕ) toDual).trans toLex).summable_iff.mp <|
    Summable.sum _
      ((hgeom.mul_left ‖a₁‖).congr fun k ↦ by simp [abs_of_nonneg hr0])
      ((hgeom.mul_left ‖a₂‖).congr fun k ↦ by simp [abs_of_nonneg hr0])

/-- Total sum `(a₁ + a₂) / (1 - r)` of `twoSidedGeom a₁ a₂ r` for `0 ≤ r < 1`. -/
theorem tsum_twoSidedGeom (a₁ a₂ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' a, twoSidedGeom a₁ a₂ r a) = (a₁ + a₂) / (1 - r) := by
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  let e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ₗ ℕᵒᵈ) := (Equiv.sumCongr (Equiv.refl ℕ) toDual).trans toLex
  rw [(e.tsum_eq _).symm.trans (Summable.tsum_sum (f := twoSidedGeom a₁ a₂ r ∘ e)
    (hgeom.mul_left a₁) (hgeom.mul_left a₂))]
  simp only [e, comp_def, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl,
    Sum.map_inr, twoSidedGeom, ofLex_toLex, ofDual_toDual, hgeom.tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1]
  ring

/-- Initial-segment sum of `twoSidedGeom a₁ a₂ r` strictly below `Sum.inlₗ m`. -/
theorem mul_tsum_lt_twoSidedGeom_inl (a₁ a₂ r : ℝ) (m : ℕ) :
    (1 - r) * (∑' a : ℕ ⊕ₗ ℕᵒᵈ, if a < Sum.inlₗ m then twoSidedGeom a₁ a₂ r a else 0) =
      a₁ * (1 - r ^ m) := by
  have hpref : HasSum (fun k : ℕ ↦ if k < m then a₁ * r ^ k else 0)
      (∑ k ∈ Finset.range m, a₁ * r ^ k) := by
    convert hasSum_subtype_iff_indicator.mp ((Finset.range m).hasSum fun k ↦ a₁ * r ^ k) using 1
    ext k; simp [Set.indicator_apply]
  let e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ₗ ℕᵒᵈ) := (Equiv.sumCongr (Equiv.refl ℕ) toDual).trans toLex
  rw [(e.tsum_eq _).symm.trans (Summable.tsum_sum
    (f := (fun a : ℕ ⊕ₗ ℕᵒᵈ ↦ if a < Sum.inlₗ m then twoSidedGeom a₁ a₂ r a else 0) ∘ e)
    (by simpa [e, comp_def] using hpref.summable) (by simp [e, comp_def]))]
  simp only [e, comp_def, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl,
    Sum.map_inr, twoSidedGeom, ofLex_toLex, Sum.Lex.inl_lt_inl_iff, Sum.Lex.not_inr_lt_inl,
    ↓reduceIte, tsum_zero, add_zero, hpref.tsum_eq, ← Finset.mul_sum]
  rw [mul_left_comm, mul_neg_geom_sum]

/-- Initial-segment sum of `twoSidedGeom a₁ a₂ r` strictly below `Sum.inrₗ (toDual m)`. -/
theorem mul_tsum_lt_twoSidedGeom_inr (a₁ a₂ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m : ℕ) :
    (1 - r) * (∑' a : ℕ ⊕ₗ ℕᵒᵈ, if a < Sum.inrₗ (toDual m) then twoSidedGeom a₁ a₂ r a else 0) =
      a₁ + a₂ * r ^ (m + 1) := by
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  have h₂ := hgeom.mul_left a₂
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
    (by simpa [e, comp_def] using hgeom.mul_left a₁)
    (by simpa [e, comp_def] using htail_sum))]
  simp only [e, comp_def, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl,
    Sum.map_inr, twoSidedGeom, ofLex_toLex, ofDual_toDual, Sum.Lex.inl_lt_inr,
    Sum.Lex.inr_lt_inr_iff, toDual_lt_toDual, ↓reduceIte, htail, hgeom.tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1, ← Finset.mul_sum]
  rw [mul_add, mul_sub, mul_left_comm (1 - r) a₂ (∑ _ ∈ _, _), mul_neg_geom_sum]
  have h1r : 1 - r ≠ 0 := sub_ne_zero.mpr hr1.ne'
  field_simp; ring

end TauCeti
