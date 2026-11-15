/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Topology.MetricSpace.CoveringExponent
public import Mathlib.Topology.MetricSpace.CoveringNumbers
-- Private: `Nat.floor` and extended floor lemmas are used only in proofs.
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Packing numbers, separated sets, and covering exponents of intervals

Metric facts about `ε`-separated sets, isometric invariance and uniform scale bounds for
`Metric.HasCoveringExponent`, and explicit covering exponents (`d = 1`) for bounded intervals in
`ℝ≥0` and `ℝ`.

## Main results

* `TauCeti.packingNumber_le_of_forall_finset_card_le`: a finite bound on the sizes of the finite
  `ε`-separated subsets of a set bounds its packing number.
* `Metric.IsSeparated.pairwiseDisjoint_closedBall`: the closed balls of radius `ε / 2` around
  the points of an `ε`-separated set are pairwise disjoint.
* `Isometry.hasCoveringExponent_image_iff'`, `Isometry.hasCoveringExponent_image_iff`,
  `Metric.hasCoveringExponent_univ_subtype_iff`: invariance of `Metric.HasCoveringExponent` under
  isometries and passage to subtypes.
* `Metric.HasCoveringExponent.coveringNumber_le_max_one_mul`: uniform bound
  `coveringNumber ε A ≤ max 1 c * ε⁻¹ ^ d` for all `ε ≤ 1` when `0 ≤ d`.
* `TauCeti.hasCoveringExponent_Icc_nnreal`, `TauCeti.hasCoveringExponent_Iio_nnreal`,
  `TauCeti.hasCoveringExponent_Icc_real`: intervals in `ℝ≥0` and `ℝ` have covering exponent `1`.
-/

public section

open Metric Set
open scoped ENNReal NNReal

namespace TauCeti

/-- If every finite `ε`-separated subset of `A` has at most `B ≠ ∞` elements, then the packing
number of `A` at scale `ε` is at most `B`. -/
theorem packingNumber_le_of_forall_finset_card_le {X : Type*} [PseudoEMetricSpace X] {ε : ℝ≥0}
    {A : Set X} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (h : ∀ s : Finset X, (s : Set X) ⊆ A → IsSeparated ε (s : Set X) → (s.card : ℝ≥0∞) ≤ B) :
    (packingNumber ε A : ℝ≥0∞) ≤ B := by
  rw [packingNumber]
  simp only [ENat.toENNReal_iSup]
  refine iSup₂_le fun C hCA ↦ iSup_le fun hC ↦ ?_
  rcases C.finite_or_infinite with hCf | hCi
  · rw [hCf.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
    exact h hCf.toFinset (by simpa using hCA) (by simpa using hC)
  · -- An infinite separated subset would contain finite separated subsets of every size.
    exfalso
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hB
    obtain ⟨s, hsC, rfl⟩ := hCi.exists_subset_card_eq n
    exact (h s (hsC.trans hCA) (hC.subset hsC)).not_gt hn

end TauCeti

section Isometry

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- An isometry injective on `A` preserves `Metric.HasCoveringExponent`. -/
theorem Isometry.hasCoveringExponent_image_iff' {f : X → Y} (hf : Isometry f) {A : Set X}
    (hinj : A.InjOn f) {c : ℝ≥0∞} {d : ℝ} :
    HasCoveringExponent (f '' A) c d ↔ HasCoveringExponent A c d := by
  have hdiam : ediam (f '' A) = ediam A := hf.ediam_image A
  have hcov (ε : ℝ≥0) : coveringNumber ε (f '' A) = coveringNumber ε A :=
    hf.coveringNumber_image' hinj
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨hdiam ▸ h1, fun ε hε ↦ hcov ε ▸ h2 ε (hdiam.symm ▸ hε)⟩,
    fun ⟨h1, h2⟩ ↦ ⟨hdiam.symm ▸ h1, fun ε hε ↦ (hcov ε).symm ▸ h2 ε (hdiam ▸ hε)⟩⟩

/-- An isometry out of an `EMetricSpace` preserves `Metric.HasCoveringExponent`. -/
theorem Isometry.hasCoveringExponent_image_iff {X : Type*} [EMetricSpace X] {f : X → Y}
    (hf : Isometry f) {A : Set X} {c : ℝ≥0∞} {d : ℝ} :
    HasCoveringExponent (f '' A) c d ↔ HasCoveringExponent A c d :=
  hf.hasCoveringExponent_image_iff' hf.injective.injOn

end Isometry

namespace Metric

/-- The closed balls of radius `ε / 2` around the points of an `ε`-separated set are pairwise
disjoint. -/
theorem IsSeparated.pairwiseDisjoint_closedBall {X : Type*} [PseudoMetricSpace X] {ε : ℝ≥0}
    {C : Set X} (hC : IsSeparated ε C) : C.PairwiseDisjoint fun x ↦ closedBall x (ε / 2) := by
  intro x hx y hy hxy
  refine closedBall_disjoint_closedBall ?_
  have h : (ε : ℝ≥0∞) < edist x y := hC hx hy hxy
  rw [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nndist] at h
  linarith

/-- `univ` in the subtype `A` has covering exponent `(c, d)` if and only if `A` does in the ambient
space. -/
theorem hasCoveringExponent_univ_subtype_iff {X : Type*} [PseudoEMetricSpace X] {A : Set X}
    {c : ℝ≥0∞} {d : ℝ} :
    HasCoveringExponent (univ : Set A) c d ↔ HasCoveringExponent A c d := by
  simpa using (Isometry.hasCoveringExponent_image_iff' (f := (Subtype.val : A → X)) (A := univ)
    (fun _ _ ↦ rfl) Subtype.val_injective.injOn).symm

/-- When `0 ≤ d`, `HasCoveringExponent A c d` bounds `coveringNumber ε A` by `max 1 c * ε⁻¹ ^ d`
for every scale `ε ≤ 1`, even above `ediam A`. -/
theorem HasCoveringExponent.coveringNumber_le_max_one_mul {X : Type*} [PseudoEMetricSpace X]
    {A : Set X} {c : ℝ≥0∞} {d : ℝ} (h : HasCoveringExponent A c d) (hd : 0 ≤ d) {ε : ℝ≥0}
    (hε : ε ≤ 1) :
    (coveringNumber ε A : ℝ≥0∞) ≤ max 1 c * (ε : ℝ≥0∞)⁻¹ ^ d := by
  by_cases hle : (ε : ℝ≥0∞) ≤ ediam A
  · exact (h.coveringNumber_le ε hle).trans (by gcongr; exact le_max_right 1 c)
  · have hone_cov : (coveringNumber ε A : ℝ≥0∞) ≤ 1 :=
      mod_cast coveringNumber_le_one_of_ediam_le (not_le.mp hle).le
    have hone_inv : (1 : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_le_inv.mp (by simpa using hε)
    have hone_rpow : (1 : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ d := by
      rw [← ENNReal.one_rpow (x := d)]
      exact ENNReal.rpow_le_rpow hone_inv hd
    exact hone_cov.trans (one_le_mul_of_one_le_of_one_le (le_max_left 1 c) hone_rpow)

end Metric

namespace TauCeti

/-- For `R ≠ 0`, the closed interval `Icc (0 : ℝ≥0) R` has covering exponent `1` with constant
`2 * R`. -/
theorem hasCoveringExponent_Icc_nnreal_of_ne_zero {R : ℝ≥0} (hR : R ≠ 0) :
    HasCoveringExponent (Icc (0 : ℝ≥0) R) (2 * R) 1 := by
  have hdiam : ediam (Icc (0 : ℝ≥0) R) ≤ R := by
    refine ediam_le_iff.mpr fun x hx y hy ↦ ?_
    rw [edist_nndist, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nndist, NNReal.dist_eq, abs_le]
    exact ⟨by linarith [x.coe_nonneg, NNReal.coe_le_coe.mpr hy.2],
      by linarith [y.coe_nonneg, NNReal.coe_le_coe.mpr hx.2]⟩
  refine ⟨hdiam.trans_lt ENNReal.coe_lt_top, fun ε hε_diam ↦ ?_⟩
  rcases eq_or_ne ε 0 with rfl | hε₀
  · have htop : (2 : ℝ≥0∞) * R * (0 : ℝ≥0∞)⁻¹ ^ (1 : ℝ) = ∞ := by
      rw [ENNReal.inv_zero, ENNReal.rpow_one,
        ENNReal.mul_top (mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr hR))]
    exact htop ▸ le_top
  · have hε_pos : 0 < ε := pos_iff_ne_zero.mpr hε₀
    have hεR : ε ≤ R := ENNReal.coe_le_coe.mp (hε_diam.trans hdiam)
    let N : ℕ := ⌊R / ε⌋₊ + 1
    let C : Finset ℝ≥0 := (Finset.range N).image fun k : ℕ ↦ min R ((k : ℝ≥0) * ε)
    have hC_sub : (C : Set ℝ≥0) ⊆ Icc 0 R := by
      rintro z hz
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
      exact ⟨zero_le, min_le_left _ _⟩
    have hC_cov : IsCover ε (Icc (0 : ℝ≥0) R) (C : Set ℝ≥0) := by
      intro x hx
      let k : ℕ := ⌊x / ε⌋₊
      have hk_lt : k < N :=
        Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right hx.2 hε_pos.le))
      have hk_le_x : (k : ℝ≥0) * ε ≤ x :=
        (le_div_iff₀ hε_pos).mp (Nat.floor_le zero_le)
      have hx_le_succ : x ≤ ((k : ℝ≥0) + 1) * ε :=
        (div_le_iff₀ hε_pos).mp (Nat.lt_floor_add_one (x / ε)).le
      refine ⟨min R ((k : ℝ≥0) * ε),
        Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hk_lt)), ?_⟩
      change edist x (min R ((k : ℝ≥0) * ε)) ≤ ε
      rw [min_eq_right (hk_le_x.trans hx.2), edist_nndist, ENNReal.coe_le_coe,
        ← NNReal.coe_le_coe, coe_nndist, NNReal.dist_eq]
      have hk_real : (k : ℝ) * ε ≤ x := by exact_mod_cast hk_le_x
      have hx_real : (x : ℝ) ≤ (k + 1) * ε := by exact_mod_cast hx_le_succ
      push_cast
      rw [abs_of_nonneg (sub_nonneg.mpr hk_real)]
      linarith
    have hN_le : (N : ℝ≥0) ≤ 2 * R * ε⁻¹ := by
      have h1 : (1 : ℝ≥0) ≤ R / ε := (one_le_div hε_pos).mpr hεR
      have hfl : (⌊R / ε⌋₊ : ℝ≥0) ≤ R / ε := Nat.floor_le zero_le
      calc (N : ℝ≥0)
        _ = (⌊R / ε⌋₊ : ℝ≥0) + 1 := by simp [N]
        _ ≤ R / ε + R / ε := add_le_add hfl h1
        _ = 2 * R * ε⁻¹ := by rw [← two_mul, div_eq_mul_inv, mul_assoc]
    calc (coveringNumber ε (Icc (0 : ℝ≥0) R) : ℝ≥0∞)
      _ ≤ ((C : Set ℝ≥0).encard : ℝ≥0∞) :=
        ENat.toENNReal_le.mpr (hC_cov.coveringNumber_le_encard hC_sub)
      _ = (C.card : ℝ≥0∞) := by simp
      _ ≤ (N : ℝ≥0∞) := by
        exact_mod_cast Finset.card_image_le.trans (by simp)
      _ ≤ ((2 * R * ε⁻¹ : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hN_le
      _ = 2 * (R : ℝ≥0∞) * (ε : ℝ≥0∞)⁻¹ ^ (1 : ℝ) := by
        rw [ENNReal.rpow_one, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_ofNat,
          ENNReal.coe_inv hε₀]

/-- For every `R : ℝ≥0`, the closed interval `Icc (0 : ℝ≥0) R` has covering exponent `1` with
constant `max 1 (2 * R)`. -/
theorem hasCoveringExponent_Icc_nnreal (R : ℝ≥0) :
    HasCoveringExponent (Icc (0 : ℝ≥0) R) (max 1 (2 * R)) 1 := by
  rcases eq_or_ne R 0 with rfl | hR
  · have h0 : Icc (0 : ℝ≥0) 0 = {0} := Icc_self 0
    rw [h0]
    refine ⟨by simp, fun ε hε ↦ ?_⟩
    have hε0 : ε = 0 := by simpa using hε
    subst hε0
    simp
  · obtain ⟨h1, h2⟩ := hasCoveringExponent_Icc_nnreal_of_ne_zero hR
    exact ⟨h1, fun ε hε ↦ (h2 ε hε).trans (by gcongr; exact le_max_right 1 _)⟩

/-- For every `R : ℝ≥0`, the open ray segment `Iio R` in `ℝ≥0` has covering exponent `1` with
constant `4 * R`. -/
theorem hasCoveringExponent_Iio_nnreal (R : ℝ≥0) :
    HasCoveringExponent (Iio R) (4 * R) 1 := by
  rcases eq_or_ne R 0 with rfl | hR
  · have hempty : Iio (0 : ℝ≥0) = ∅ := by ext x; simp
    rw [hempty]
    exact ⟨by simp, fun ε _ ↦ by simp⟩
  · have h := (hasCoveringExponent_Icc_nnreal_of_ne_zero hR).subset (B := Iio R)
      (fun _ hx ↦ ⟨zero_le, le_of_lt hx⟩) zero_le_one
    convert h using 1
    rw [ENNReal.rpow_one, ← mul_assoc]
    norm_num

/-- For `a ≤ b` in `ℝ`, the closed interval `Icc a b` has covering exponent `1` with constant
`max 1 (2 * ENNReal.ofReal (b - a))`. -/
theorem hasCoveringExponent_Icc_real {a b : ℝ} (hab : a ≤ b) :
    HasCoveringExponent (Icc a b) (max 1 (2 * ENNReal.ofReal (b - a))) 1 := by
  let R : ℝ≥0 := (b - a).toNNReal
  have hR_coe : (R : ℝ) = b - a := Real.coe_toNNReal _ (sub_nonneg.mpr hab)
  let f : ℝ≥0 → ℝ := fun x ↦ a + (x : ℝ)
  have hf : Isometry f := Isometry.of_dist_eq fun x y ↦ by
    change |(a + (x : ℝ)) - (a + (y : ℝ))| = |(x : ℝ) - (y : ℝ)|
    congr 1
    ring
  have himg : f '' Icc 0 R = Icc a b := by
    ext z
    simp only [mem_image, mem_Icc, f]
    constructor
    · rintro ⟨x, ⟨_, hxR⟩, rfl⟩
      have hxR' : (x : ℝ) ≤ b - a := hR_coe ▸ NNReal.coe_le_coe.mpr hxR
      exact ⟨by linarith [x.coe_nonneg], by linarith⟩
    · rintro ⟨haz, hzb⟩
      refine ⟨(z - a).toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal (by linarith)⟩, ?_⟩
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr haz)]
      ring
  have hofReal : ENNReal.ofReal (b - a) = (R : ℝ≥0∞) := by
    rw [ENNReal.ofReal]
  rw [← himg, hofReal]
  exact hf.hasCoveringExponent_image_iff.mpr (hasCoveringExponent_Icc_nnreal R)

end TauCeti
