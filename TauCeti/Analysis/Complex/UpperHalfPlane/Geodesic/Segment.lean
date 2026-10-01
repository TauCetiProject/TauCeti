/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Semicircle

/-!
# Geodesic segments and the convexity of half-planes

`UpperHalfPlane.geodesicSegment z w` is the geodesic segment from `z` to `w`: the image of
`[0, dist z w]` under the geodesic line `geodesicBetween z w`. The point-keyed API lives in the
`UpperHalfPlane` namespace (`UpperHalfPlane.mem_geodesicSegment_iff`,
`UpperHalfPlane.geodesicSegment_comm`, `UpperHalfPlane.isCompact_geodesicSegment`, …), and
segments transform naturally under `PSL(2, ℝ)` (`smul_geodesicSegment`).

Along any geodesic line the real part is monotone or antitone
(`monotone_re_geodesicLine_or_antitone`); the set of parameters at which a geodesic line lies in
a given half-plane or its closure is an interval
(`ordConnected_preimage_geodesicLine_rightHalfPlane` and companions); and half-planes and
their closures are convex: they contain the segment between any two of their points
(`geodesicSegment_subset_rightHalfPlane`, …, `geodesicSegment_subset_closure_leftHalfPlane`).
Convexity is what makes the triangles and polygons bounded by such half-planes convex.

Source: Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §7.1 (the
segment `[z, w]`) and Solution 14.1 (half-planes are convex); Katok, *Fuchsian groups,
geodesic flows…*, Clay Math. Proc. 10 (2010), Theorem 3.1 p. 10 (geodesics are semicircles and
vertical rays).
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace UpperHalfPlane

open TauCeti.UpperHalfPlane

/-! ### Segments -/

/-- The geodesic segment from `z` to `w`. -/
def geodesicSegment (z w : ℍ) : Set ℍ :=
  geodesicLine (geodesicBetween z w) '' Icc 0 (dist z w)

-- The body of `geodesicSegment` is not `@[expose]`d, so downstream modules rewrite with this.
/-- The geodesic segment from `z` to `w`, unfolded: the image of `[0, dist z w]` under the geodesic
line from `z` to `w`. -/
theorem geodesicSegment_def (z w : ℍ) :
    geodesicSegment z w = geodesicLine (geodesicBetween z w) '' Icc 0 (dist z w) := by
  rfl

/-- Membership in `geodesicSegment z w`. -/
@[simp]
theorem mem_geodesicSegment_iff (z w u : ℍ) :
    u ∈ geodesicSegment z w ↔ ∃ t ∈ Icc 0 (dist z w), geodesicLine (geodesicBetween z w) t = u :=
  Iff.rfl

/-- `z` lies on the segment from `z` to `w`. -/
@[simp]
theorem left_mem_geodesicSegment (z w : ℍ) : z ∈ geodesicSegment z w :=
  ⟨0, ⟨le_rfl, dist_nonneg⟩, geodesicLine_geodesicBetween_zero z w⟩

/-- `w` lies on the segment from `z` to `w`. -/
@[simp]
theorem right_mem_geodesicSegment (z w : ℍ) : w ∈ geodesicSegment z w :=
  ⟨dist z w, ⟨dist_nonneg, le_rfl⟩, geodesicLine_geodesicBetween_dist z w⟩

/-- The segment from a point to itself is that point. -/
@[simp]
theorem geodesicSegment_self (z : ℍ) : geodesicSegment z z = {z} := by
  rw [geodesicSegment, dist_self, Icc_self, image_singleton, geodesicLine_geodesicBetween_zero]

/-- A segment lies on the geodesic line through its endpoints. -/
theorem geodesicSegment_subset_range_geodesicLine (z w : ℍ) :
    geodesicSegment z w ⊆ Set.range (geodesicLine (geodesicBetween z w)) :=
  image_subset_range _ _

/-- The segment does not depend on the order of its endpoints. -/
theorem geodesicSegment_comm (z w : ℍ) : geodesicSegment w z = geodesicSegment z w := by
  rcases eq_or_ne z w with rfl | hzw
  · rfl
  have key : ∀ t, geodesicLine (geodesicBetween w z) t =
      geodesicLine (geodesicBetween z w) (dist z w - t) := fun t ↦ by
    rw [geodesicBetween_swap hzw, geodesicLine_mul_pslS, geodesicLine_mul_dilation, sub_eq_add_neg]
  rw [geodesicSegment, geodesicSegment, dist_comm w z, funext key,
    ← image_image (geodesicLine (geodesicBetween z w)) (fun t ↦ dist z w - t),
    ← uIcc_of_le dist_nonneg, image_const_sub_uIcc, sub_zero, sub_self, uIcc_of_ge dist_nonneg,
    uIcc_of_le dist_nonneg]

/-- Segments are compact. -/
theorem isCompact_geodesicSegment (z w : ℍ) : IsCompact (geodesicSegment z w) :=
  isCompact_Icc.image (isometry_geodesicLine _).continuous

/-- Segments are closed. -/
theorem isClosed_geodesicSegment (z w : ℍ) : IsClosed (geodesicSegment z w) :=
  (isCompact_geodesicSegment z w).isClosed

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- Segments transform naturally under the action. -/
theorem smul_geodesicSegment (h : PSL(2, ℝ)) (z w : ℍ) :
    h • geodesicSegment z w = geodesicSegment (h • z) (h • w) := by
  rcases eq_or_ne z w with rfl | hzw
  · rw [geodesicSegment_self, geodesicSegment_self, smul_set_singleton]
  rw [geodesicSegment, geodesicSegment, geodesicBetween_smul h hzw, (isometry_smul ℍ h).dist_eq,
    ← image_smul, image_image]
  simp only [smul_geodesicLine]

/-! ### The real part is monotone along a geodesic line -/

/-- The real part of `geodesicLine ↑A t`, in the entries of a representative `A ∈ SL(2, ℝ)`. -/
private theorem re_geodesicLine_mk (A : SL(2, ℝ)) (t : ℝ) :
    (geodesicLine (↑A : PSL(2, ℝ)) t).re =
      (A 0 0 * A 1 0 * Real.exp t ^ 2 + A 0 1 * A 1 1) /
        (A 1 0 ^ 2 * Real.exp t ^ 2 + A 1 1 ^ 2) := by
  rw [geodesicLine_def, UpperHalfPlane.pslMk_smul, ← UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply]
  rw [Complex.div_re, ← add_div]
  congr 1 <;>
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im] <;>
    ring

/-- The denominator of `re_geodesicLine_mk` is positive, as `(c, d) ≠ (0, 0)`. -/
private theorem denom_pos {a b c d : ℝ} (h : a * d - b * c = 1) {s : ℝ} (hs : 0 < s) :
    0 < c ^ 2 * s + d ^ 2 := by
  rcases eq_or_ne d 0 with rfl | hd
  · have hc : c ≠ 0 := by rintro rfl; simp at h
    positivity
  · positivity

/-- The difference of the values of `s ↦ (a c s + b d) / (c² s + d²)` at `s₂` and `s₁`, when
`a d - b c = 1`. -/
private theorem sub_re_eq {a b c d : ℝ} (h : a * d - b * c = 1) {s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (hs₂ : 0 < s₂) :
    (a * c * s₂ + b * d) / (c ^ 2 * s₂ + d ^ 2) - (a * c * s₁ + b * d) / (c ^ 2 * s₁ + d ^ 2) =
      c * d * (s₂ - s₁) / ((c ^ 2 * s₁ + d ^ 2) * (c ^ 2 * s₂ + d ^ 2)) := by
  have h₁ := (denom_pos h hs₁).ne'
  have h₂ := (denom_pos h hs₂).ne'
  field_simp
  linear_combination (c * d * (s₂ - s₁)) * h

/-- Along a geodesic line the real part is monotone or antitone: the line is a vertical ray or a
semicircle centred on the real axis, traversed once.
Source: Katok, *Fuchsian groups, geodesic flows…* (Clay Math. Proc. 10), Theorem 3.1 p. 10. -/
theorem monotone_re_geodesicLine_or_antitone (g : PSL(2, ℝ)) :
    Monotone (fun t ↦ (geodesicLine g t).re) ∨ Antitone (fun t ↦ (geodesicLine g t).re) := by
  induction g using QuotientGroup.induction_on with
  | _ A =>
  have hdet := A.det_coe
  rw [Matrix.det_fin_two] at hdet
  have key (s t : ℝ) : (geodesicLine (↑A : PSL(2, ℝ)) t).re - (geodesicLine (↑A : PSL(2, ℝ)) s).re =
      A 1 0 * A 1 1 * (Real.exp t ^ 2 - Real.exp s ^ 2) /
        ((A 1 0 ^ 2 * Real.exp s ^ 2 + A 1 1 ^ 2) * (A 1 0 ^ 2 * Real.exp t ^ 2 + A 1 1 ^ 2)) := by
    rw [re_geodesicLine_mk, re_geodesicLine_mk, sub_re_eq hdet (by positivity) (by positivity)]
  have hexp {s t : ℝ} (hst : s ≤ t) : 0 ≤ Real.exp t ^ 2 - Real.exp s ^ 2 :=
    sub_nonneg.2 (pow_le_pow_left₀ (Real.exp_pos s).le (Real.exp_le_exp.2 hst) 2)
  have hden (s t : ℝ) := (mul_pos (denom_pos hdet (pow_pos (Real.exp_pos s) 2))
    (denom_pos hdet (pow_pos (Real.exp_pos t) 2))).le
  rcases le_or_gt 0 (A 1 0 * A 1 1) with hcd | hcd
  · refine Or.inl fun s t hst ↦ sub_nonneg.1 ?_
    rw [key s t]
    exact div_nonneg (mul_nonneg hcd (hexp hst)) (hden s t)
  · refine Or.inr fun s t hst ↦ sub_nonpos.1 ?_
    rw [key s t]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hcd.le (hexp hst))
      (hden s t)

/-- The preimage of an interval under the real part along a geodesic line is an interval. -/
private theorem ordConnected_preimage_re_geodesicLine (g : PSL(2, ℝ)) {S : Set ℝ}
    (hS : S.OrdConnected) : ((fun t ↦ (geodesicLine g t).re) ⁻¹' S).OrdConnected :=
  (monotone_re_geodesicLine_or_antitone g).elim hS.preimage_mono hS.preimage_anti

/-- The parameters at which a geodesic line lies in an open right half-plane form an interval. -/
theorem ordConnected_preimage_geodesicLine_rightHalfPlane (g k : PSL(2, ℝ)) :
    (geodesicLine g ⁻¹' rightHalfPlane k).OrdConnected := by
  simpa only [preimage, mem_rightHalfPlane_iff, smul_geodesicLine, mem_Ioi] using
    ordConnected_preimage_re_geodesicLine (k⁻¹ * g) ordConnected_Ioi

/-- The parameters at which a geodesic line lies in the closure of a right half-plane form an
interval. -/
theorem ordConnected_preimage_geodesicLine_closure_rightHalfPlane (g k : PSL(2, ℝ)) :
    (geodesicLine g ⁻¹' closure (rightHalfPlane k)).OrdConnected := by
  simpa only [preimage, mem_closure_rightHalfPlane_iff, smul_geodesicLine, mem_Ici] using
    ordConnected_preimage_re_geodesicLine (k⁻¹ * g) ordConnected_Ici

/-- The parameters at which a geodesic line lies in an open left half-plane form an interval. -/
theorem ordConnected_preimage_geodesicLine_leftHalfPlane (g k : PSL(2, ℝ)) :
    (geodesicLine g ⁻¹' leftHalfPlane k).OrdConnected := by
  simpa only [preimage, mem_leftHalfPlane_iff, smul_geodesicLine, mem_Iio] using
    ordConnected_preimage_re_geodesicLine (k⁻¹ * g) ordConnected_Iio

/-- The parameters at which a geodesic line lies in the closure of a left half-plane form an
interval. -/
theorem ordConnected_preimage_geodesicLine_closure_leftHalfPlane (g k : PSL(2, ℝ)) :
    (geodesicLine g ⁻¹' closure (leftHalfPlane k)).OrdConnected := by
  simpa only [preimage, mem_closure_leftHalfPlane_iff, smul_geodesicLine, mem_Iic] using
    ordConnected_preimage_re_geodesicLine (k⁻¹ * g) ordConnected_Iic

/-! ### Half-planes are convex -/

/-- A set containing `z` and `w` whose trace on the line from `z` to `w` is an interval of
parameters contains the segment from `z` to `w`. -/
private theorem geodesicSegment_subset_of_ordConnected {S : Set ℍ} {z w : ℍ}
    (h : (geodesicLine (geodesicBetween z w) ⁻¹' S).OrdConnected) (hz : z ∈ S) (hw : w ∈ S) :
    geodesicSegment z w ⊆ S := by
  rintro _ ⟨t, ht, rfl⟩
  refine h.out ?_ ?_ ht
  · simpa only [mem_preimage, geodesicLine_geodesicBetween_zero] using hz
  · simpa only [mem_preimage, geodesicLine_geodesicBetween_dist] using hw

/-- Open right half-planes are convex.
Source: Walkden, *Hyperbolic geometry* (MATH32051), Solution 14.1. -/
theorem geodesicSegment_subset_rightHalfPlane {k : PSL(2, ℝ)} {z w : ℍ}
    (hz : z ∈ rightHalfPlane k) (hw : w ∈ rightHalfPlane k) :
    geodesicSegment z w ⊆ rightHalfPlane k :=
  geodesicSegment_subset_of_ordConnected (ordConnected_preimage_geodesicLine_rightHalfPlane _ k)
    hz hw

/-- Closed right half-planes are convex. -/
theorem geodesicSegment_subset_closure_rightHalfPlane {k : PSL(2, ℝ)} {z w : ℍ}
    (hz : z ∈ closure (rightHalfPlane k)) (hw : w ∈ closure (rightHalfPlane k)) :
    geodesicSegment z w ⊆ closure (rightHalfPlane k) :=
  geodesicSegment_subset_of_ordConnected
    (ordConnected_preimage_geodesicLine_closure_rightHalfPlane _ k) hz hw

/-- Open left half-planes are convex. -/
theorem geodesicSegment_subset_leftHalfPlane {k : PSL(2, ℝ)} {z w : ℍ}
    (hz : z ∈ leftHalfPlane k) (hw : w ∈ leftHalfPlane k) :
    geodesicSegment z w ⊆ leftHalfPlane k :=
  geodesicSegment_subset_of_ordConnected (ordConnected_preimage_geodesicLine_leftHalfPlane _ k)
    hz hw

/-- Closed left half-planes are convex. -/
theorem geodesicSegment_subset_closure_leftHalfPlane {k : PSL(2, ℝ)} {z w : ℍ}
    (hz : z ∈ closure (leftHalfPlane k)) (hw : w ∈ closure (leftHalfPlane k)) :
    geodesicSegment z w ⊆ closure (leftHalfPlane k) :=
  geodesicSegment_subset_of_ordConnected
    (ordConnected_preimage_geodesicLine_closure_leftHalfPlane _ k) hz hw

end TauCeti.UpperHalfPlane
