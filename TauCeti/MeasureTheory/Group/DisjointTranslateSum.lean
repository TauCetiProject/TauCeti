/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Bounding sums over disjoint translates by a group integral

Let `G` be a measurable group with a left-invariant measure `μ`, `B ⊆ G` a measurable set, and
`y : I → G` a countable family whose right translates `y i * B` are pairwise disjoint. If a
nonnegative function `f : G → ℝ≥0∞` satisfies the local Harnack bound `f x ≤ c * f (x * z)` for
all `z ∈ B` (with `c ≠ ⊤`), then

`(∑' i, f (y i)) * μ B ≤ c * ∫⁻ x, f x ∂μ`

(`TauCeti.tsum_mul_measure_le_lintegral`). We also prove the dual statement for a right-invariant
measure and left translates `B * y i` (`TauCeti.tsum_mul_measure_le_lintegral_right`), and the
divided form when `0 < μ B < ⊤` (`TauCeti.tsum_le_mul_lintegral_div`).

## Main results

* `TauCeti.tsum_mul_measure_le_lintegral`: left-invariant bound for disjoint translates `y i * B`.
* `TauCeti.tsum_mul_measure_le_lintegral_right`: right-invariant bound for disjoint translates
  `B * y i`.
* `TauCeti.tsum_le_mul_lintegral_div`: divided bound `∑' i, f (y i) ≤ c * (∫⁻ f ∂μ) / μ B`.

## References

* Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0),
  `src/Lib/Adelic/TraceFormula/KernelBound.lean` (`New.tsum_mul_measure_le_lintegral`).
-/

public section

open MeasureTheory ENNReal

namespace TauCeti

/-- If `μ` is left-invariant on `G`, the right translates `y i * B` of a measurable set `B` are
pairwise disjoint, and `f x ≤ c * f (x * z)` for all `z ∈ B`, then
`(∑' i, f (y i)) * μ B ≤ c * ∫⁻ x, f x ∂μ`. -/
theorem tsum_mul_measure_le_lintegral {G I : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [Countable I] {y : I → G}
    {B : Set G} (hB : MeasurableSet B)
    (hdisj : ∀ i j : I, ∀ z ∈ B, ∀ z' ∈ B, y i * z = y j * z' → i = j)
    {f : G → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hle : ∀ x : G, ∀ z ∈ B, f x ≤ c * f (x * z)) :
    (∑' i : I, f (y i)) * μ B ≤ c * ∫⁻ x : G, f x ∂μ := by
  let S (i : I) : Set G := (fun x ↦ (y i)⁻¹ * x) ⁻¹' B
  have hS (i : I) : MeasurableSet (S i) := measurable_const_mul _ hB
  have hS_disj : Pairwise (Function.onFun Disjoint S) := fun i j hij ↦
    Set.disjoint_left.mpr fun x hi hj ↦ hij (hdisj i j _ hi _ hj (by simp))
  have hterm (i : I) : f (y i) * μ B ≤ ∫⁻ x in S i, c * f x ∂μ := by
    rw [← measure_preimage_mul μ (y i)⁻¹ B, ← setLIntegral_const]
    exact setLIntegral_mono' (hS i) fun x hx ↦ by simpa using hle (y i) _ hx
  calc (∑' i : I, f (y i)) * μ B
      ≤ ∑' i : I, ∫⁻ x in S i, c * f x ∂μ := ENNReal.tsum_mul_right.ge.trans (tsum_le_tsum hterm)
    _ = ∫⁻ x in ⋃ i : I, S i, c * f x ∂μ := (lintegral_iUnion hS hS_disj _).symm
    _ ≤ ∫⁻ x, c * f x ∂μ := setLIntegral_le_lintegral _ _
    _ = c * ∫⁻ x, f x ∂μ := lintegral_const_mul' _ _ hc

/-- If `μ` is right-invariant on `G`, the left translates `B * y i` of a measurable set `B` are
pairwise disjoint, and `f x ≤ c * f (z * x)` for all `z ∈ B`, then
`(∑' i, f (y i)) * μ B ≤ c * ∫⁻ x, f x ∂μ`. -/
theorem tsum_mul_measure_le_lintegral_right {G I : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant] [Countable I] {y : I → G}
    {B : Set G} (hB : MeasurableSet B)
    (hdisj : ∀ i j : I, ∀ z ∈ B, ∀ z' ∈ B, z * y i = z' * y j → i = j)
    {f : G → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hle : ∀ x : G, ∀ z ∈ B, f x ≤ c * f (z * x)) :
    (∑' i : I, f (y i)) * μ B ≤ c * ∫⁻ x : G, f x ∂μ := by
  let S (i : I) : Set G := (fun x ↦ x * (y i)⁻¹) ⁻¹' B
  have hS (i : I) : MeasurableSet (S i) := measurable_mul_const _ hB
  have hS_disj : Pairwise (Function.onFun Disjoint S) := fun i j hij ↦
    Set.disjoint_left.mpr fun x hi hj ↦ hij (hdisj i j _ hi _ hj (by simp))
  have hterm (i : I) : f (y i) * μ B ≤ ∫⁻ x in S i, c * f x ∂μ := by
    rw [← measure_preimage_mul_right μ (y i)⁻¹ B, ← setLIntegral_const]
    exact setLIntegral_mono' (hS i) fun x hx ↦ by simpa using hle (y i) _ hx
  calc (∑' i : I, f (y i)) * μ B
      ≤ ∑' i : I, ∫⁻ x in S i, c * f x ∂μ := ENNReal.tsum_mul_right.ge.trans (tsum_le_tsum hterm)
    _ = ∫⁻ x in ⋃ i : I, S i, c * f x ∂μ := (lintegral_iUnion hS hS_disj _).symm
    _ ≤ ∫⁻ x, c * f x ∂μ := setLIntegral_le_lintegral _ _
    _ = c * ∫⁻ x, f x ∂μ := lintegral_const_mul' _ _ hc

/-- Divided form of `tsum_mul_measure_le_lintegral` when `0 < μ B < ⊤`:
`∑' i, f (y i) ≤ c * (∫⁻ x, f x ∂μ) / μ B`. -/
theorem tsum_le_mul_lintegral_div {G I : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [Countable I] {y : I → G} {B : Set G}
    (hB : MeasurableSet B) (hB_pos : μ B ≠ 0) (hB_fin : μ B ≠ ⊤)
    (hdisj : ∀ i j : I, ∀ z ∈ B, ∀ z' ∈ B, y i * z = y j * z' → i = j)
    {f : G → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hle : ∀ x : G, ∀ z ∈ B, f x ≤ c * f (x * z)) :
    ∑' i : I, f (y i) ≤ c * (∫⁻ x : G, f x ∂μ) / μ B := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hB_pos) (Or.inl hB_fin)]
  exact tsum_mul_measure_le_lintegral μ hB hdisj hc hle

end TauCeti
