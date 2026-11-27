/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.FromTo
public import TauCeti.Analysis.Complex.UpperHalfPlane.IdealBoundary

/-!
# Ideal boundaries of geodesic lines and half-planes

The ideal boundary of a geodesic line consists of its two endpoints. The ideal boundary of
its closed left half-plane is the corresponding closed arc. These identities relate the
orbit-closure definition of ideal boundary to the endpoint tests for extended geodesic segments.
-/

public section

open Set UpperHalfPlane
open scoped MatrixGroups OnePoint Pointwise

namespace TauCeti.UpperHalfPlane

private theorem coe_mem_idealBoundary_preimage_re_iff (s : Set ℝ) {x : ℝ} :
    (x : OnePoint ℝ) ∈ idealBoundary (UpperHalfPlane.re ⁻¹' s) ↔ x ∈ closure s := by
  rw [coe_mem_idealBoundary_iff, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨z, hz, hd⟩ := h ε hε
    refine ⟨z.re, hz, ?_⟩
    rw [Complex.dist_eq] at hd
    have hr := Complex.abs_re_le_norm ((z : ℂ) - (x : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, UpperHalfPlane.coe_re] at hr
    rw [dist_comm, Real.dist_eq]
    exact hr.trans_lt hd
  · intro h ε hε
    obtain ⟨y, hy, hd⟩ := h (ε / 2) (half_pos hε)
    let z : ℍ := ⟨⟨y, ε / 2⟩, half_pos hε⟩
    refine ⟨z, hy, (dist_triangle _ (y : ℂ) _).trans_lt ?_⟩
    have hz : dist (z : ℂ) (y : ℂ) = ε / 2 := by
      rw [Complex.dist_of_re_eq (by simp [z])]
      simp [z, abs_of_pos hε]
    have hxy : dist (y : ℂ) (x : ℂ) < ε / 2 := by
      rw [Complex.dist_of_im_eq (by simp)]
      simpa [dist_comm] using hd
    linarith

private theorem infty_mem_idealBoundary_range_geodesicLine_one :
    (∞ : OnePoint ℝ) ∈ idealBoundary (range (geodesicLine 1)) := by
  rw [infty_mem_idealBoundary_iff, range_geodesicLine_one]
  intro r
  let z : ℍ := ⟨⟨0, max r 0 + 1⟩, by positivity⟩
  refine ⟨z, rfl, ?_⟩
  calc
    r < z.im := by dsimp [z]; linarith [le_max_left r 0]
    _ ≤ ‖(z : ℂ)‖ := by simpa [abs_of_pos z.im_pos] using Complex.abs_im_le_norm (z : ℂ)

/-- The ideal boundary of a geodesic line is the pair of its backward and forward endpoints. -/
theorem idealBoundary_range_geodesicLine (g : PSL(2, ℝ)) :
    idealBoundary (range (geodesicLine g)) = {g • ((0 : ℝ) : OnePoint ℝ), g • ∞} := by
  have h : idealBoundary (range (geodesicLine 1)) = {((0 : ℝ) : OnePoint ℝ), ∞} := by
    ext ξ
    induction ξ using OnePoint.rec with
    | infty => simp [infty_mem_idealBoundary_range_geodesicLine_one]
    | coe x =>
      simp only [mem_insert_iff, mem_singleton_iff, OnePoint.coe_eq_coe, OnePoint.coe_ne_infty,
        or_false]
      have haxis : range (geodesicLine 1) = UpperHalfPlane.re ⁻¹' ({0} : Set ℝ) := by
        rw [range_geodesicLine_one]
        ext z
        simp
      rw [haxis, coe_mem_idealBoundary_preimage_re_iff, closure_singleton, mem_singleton_iff]
  rw [← mul_one g, ← smul_range_geodesicLine, idealBoundary_smul, h]
  rw [Set.smul_set_insert, Set.smul_set_singleton, mul_one]

/-- The closed left half-plane has the closed left ideal arc as its ideal boundary. -/
theorem mem_idealBoundary_closure_leftHalfPlane_iff {g : PSL(2, ℝ)} {ξ : OnePoint ℝ} :
    ξ ∈ idealBoundary (closure (leftHalfPlane g)) ↔
      Sum.inr ξ ∈ extClosedLeftHalfPlane g := by
  have h (η : OnePoint ℝ) : η ∈ idealBoundary (closure (leftHalfPlane 1)) ↔
      Sum.inr η ∈ extClosedLeftHalfPlane 1 := by
    induction η using OnePoint.rec with
    | infty =>
      have hsub := idealBoundary_mono
        (subset_union_right : range (geodesicLine 1) ⊆
          leftHalfPlane 1 ∪ range (geodesicLine 1))
      rw [← closure_leftHalfPlane] at hsub
      exact iff_of_true (hsub infty_mem_idealBoundary_range_geodesicLine_one) (by simp)
    | coe x =>
      have hclosure : closure (leftHalfPlane 1) = UpperHalfPlane.re ⁻¹' Iic 0 := by
        ext z
        simp only [mem_closure_leftHalfPlane_iff, inv_one, one_smul, mem_preimage, mem_Iic]
      rw [hclosure, coe_mem_idealBoundary_preimage_re_iff, isClosed_Iic.closure_eq,
        inr_mem_extClosedLeftHalfPlane_iff]
      simp [coe_mem_boundaryLeftHalfPlane_iff, sideForm_one, le_iff_eq_or_lt]
  rw [← mul_one g, ← smul_leftHalfPlane, closure_smul, idealBoundary_smul,
    ← smul_extClosedLeftHalfPlane, Set.mem_smul_set_iff_inv_smul_mem,
    Set.mem_smul_set_iff_inv_smul_mem, Sum.smul_inr, h]

/-- For a geodesic from `a` to `b` with `a < b`, the closed left half-plane has the
complement of the open real interval `(a,b)` as its ideal boundary. -/
theorem idealBoundary_closure_leftHalfPlane_eq_compl_Ioo {g : PSL(2, ℝ)} {a b : ℝ}
    (hab : a < b) (ha : g • ((0 : ℝ) : OnePoint ℝ) = a) (hb : g • (∞ : OnePoint ℝ) = b) :
    idealBoundary (closure (leftHalfPlane g)) = (((↑) : ℝ → OnePoint ℝ) '' Ioo a b)ᶜ := by
  ext ξ
  rw [mem_idealBoundary_closure_leftHalfPlane_iff, inr_mem_extClosedLeftHalfPlane_iff, ha, hb]
  induction ξ using OnePoint.rec with
  | infty => simp [(infty_mem_boundaryLeftHalfPlane_iff ha hb).2 hab]
  | coe x =>
    obtain ⟨κ, hκ, hform⟩ := exists_sideForm_eq_of_smul_zero_of_smul_infty ha hb
    have hpos := mul_pos hκ (sub_pos.2 hab)
    simp only [OnePoint.coe_eq_coe, mem_compl_iff, mem_image, exists_eq_right, mem_Ioo,
      coe_mem_boundaryLeftHalfPlane_iff, hform, mul_neg_iff, hpos, hpos.not_gt, true_and,
      false_and, or_false]
    have h : ((b - a) / 2) ^ 2 - Complex.normSq ((x : ℂ) - ((a + b) / 2 : ℝ)) =
        -((x - a) * (x - b)) := by
      rw [← Complex.ofReal_sub, Complex.normSq_ofReal]
      ring
    rw [h, neg_lt_zero, sub_mul_sub_pos_iff x hab.le]
    grind

end TauCeti.UpperHalfPlane
