/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Ray
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Short secants across a corner

Let `γ₁` and `γ₂` be two curves in a real normed space, `C¹` near `0`, which meet at
`γ₁ 0 = γ₂ 0`: think of `γ₁` as the arc arriving at a corner and of `γ₂` as the arc leaving it.
Suppose that their tangent vectors `γ₁' 0` and `γ₂' 0` do not point in opposite directions,
`¬SameRay ℝ (γ₁' 0) (-γ₂' 0)`, so that the corner is not a cusp; straight joins and corners of
either sign are allowed. Then a single continuous linear functional `L` is positive on both
tangent vectors and on every short secant `γ₂ (t + r) - γ₁ t`, `-r ≤ t ≤ 0`, from the arriving
arc to the leaving one across the corner: all these secants lie in one open half-space.

This is the local input of Hopf's secant proof of the theorem of turning tangents for curves
with corners: the argument of the short secants across a corner has a continuous branch.

## Main results

* `TauCeti.exists_strongDual_pos_of_not_sameRay_neg`: two vectors that do not point in
  opposite directions are both positive for some continuous linear functional.
* `TauCeti.exists_strongDual_pos_secant_of_not_sameRay_neg`: the short secants across a corner
  lie in an open half-space containing both tangent vectors.

## References

* H. Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2
  (1935), 50–62.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two vectors `u` and `v` that do not point in opposite directions, `¬SameRay ℝ u (-v)`, are
both positive for some continuous linear functional. The hypothesis says that `0` is not on the
segment `[u, v]`, which Hahn–Banach separates from `0`. -/
theorem exists_strongDual_pos_of_not_sameRay_neg {u v : E} (h : ¬SameRay ℝ u (-v)) :
    ∃ L : StrongDual ℝ E, 0 < L u ∧ 0 < L v := by
  have h0 : (0 : E) ∉ segment ℝ u v := by
    rwa [mem_segment_iff_sameRay, zero_sub, sub_zero, sameRay_neg_swap]
  have hclosed : IsClosed (segment ℝ u v) := by
    rw [← convexHull_pair]
    exact ((toFinite _).isCompact_convexHull ℝ).isClosed
  obtain ⟨L, c, hc, hL⟩ := geometric_hahn_banach_point_closed (convex_segment u v) hclosed h0
  rw [map_zero] at hc
  exact ⟨L, hc.trans (hL u (left_mem_segment ℝ u v)), hc.trans (hL v (right_mem_segment ℝ u v))⟩

/-- A real function that is `C¹` near `0` with positive derivative at `0` is strictly increasing
on a closed interval around `0`. -/
private lemma exists_pos_strictMonoOn_Icc_of_deriv_pos {f : ℝ → ℝ} (hf : ContDiffAt ℝ 1 f 0)
    (hpos : 0 < deriv f 0) : ∃ δ > 0, StrictMonoOn f (Icc (-δ) δ) := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hcont : ContinuousOn (deriv f) (Metric.ball 0 ε) :=
    (hfu.mono hball).continuousOn_deriv_of_isOpen Metric.isOpen_ball le_rfl
  obtain ⟨η, hη, hd⟩ := Metric.eventually_nhds_iff.mp
    ((hcont.continuousAt (Metric.ball_mem_nhds 0 hε)).eventually (Ioi_mem_nhds hpos))
  have hsub : Icc (-(min ε η / 2)) (min ε η / 2) ⊆ Metric.ball 0 (min ε η) := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2, lt_min hε hη]
  refine ⟨min ε η / 2, by positivity, strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_⟩
  · exact (hfu.continuousOn.mono hball).mono
      (hsub.trans (Metric.ball_subset_ball (min_le_left _ _)))
  · intro t ht
    exact hd (Metric.ball_subset_ball (min_le_right _ _) (hsub (interior_subset ht)))

/-- **Short secants across a corner lie in an open half-space.** Let `γ₁` and `γ₂` be `C¹` near
`0`, with `γ₁ 0 = γ₂ 0`, and with tangent vectors `γ₁' 0` and `γ₂' 0` not pointing in opposite
directions. Then there are `δ > 0` and a continuous linear functional `L`, positive on both
tangent vectors, such that `0 < L (γ₂ (t + r) - γ₁ t)` whenever `0 < r < δ` and `-r ≤ t ≤ 0`. -/
theorem exists_strongDual_pos_secant_of_not_sameRay_neg {γ₁ γ₂ : ℝ → E}
    (h₁ : ContDiffAt ℝ 1 γ₁ 0) (h₂ : ContDiffAt ℝ 1 γ₂ 0) (h₀ : γ₁ 0 = γ₂ 0)
    (hne : ¬SameRay ℝ (deriv γ₁ 0) (-deriv γ₂ 0)) :
    ∃ δ > 0, ∃ L : StrongDual ℝ E, 0 < L (deriv γ₁ 0) ∧ 0 < L (deriv γ₂ 0) ∧
      ∀ r ∈ Ioo (0 : ℝ) δ, ∀ t ∈ Icc (-r) 0, 0 < L (γ₂ (t + r) - γ₁ t) := by
  obtain ⟨L, hL₁, hL₂⟩ := exists_strongDual_pos_of_not_sameRay_neg hne
  have hd₁ : deriv (L ∘ γ₁) 0 = L (deriv γ₁ 0) :=
    (L.hasFDerivAt.comp_hasDerivAt 0 (h₁.differentiableAt one_ne_zero).hasDerivAt).deriv
  have hd₂ : deriv (L ∘ γ₂) 0 = L (deriv γ₂ 0) :=
    (L.hasFDerivAt.comp_hasDerivAt 0 (h₂.differentiableAt one_ne_zero).hasDerivAt).deriv
  obtain ⟨a, ha, hma⟩ := exists_pos_strictMonoOn_Icc_of_deriv_pos
    (L.contDiff.contDiffAt.comp 0 h₁) (hd₁ ▸ hL₁)
  obtain ⟨b, hb, hmb⟩ := exists_pos_strictMonoOn_Icc_of_deriv_pos
    (L.contDiff.contDiffAt.comp 0 h₂) (hd₂ ▸ hL₂)
  refine ⟨min a b, lt_min ha hb, L, hL₁, hL₂, fun r hr t ht => ?_⟩
  have hra : r < a := hr.2.trans_le (min_le_left _ _)
  have hrb : r < b := hr.2.trans_le (min_le_right _ _)
  have hta : t ∈ Icc (-a) a := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htrb : t + r ∈ Icc (-b) b := ⟨by linarith [ht.1, hr.1], by linarith [ht.2]⟩
  have h0a : (0 : ℝ) ∈ Icc (-a) a := ⟨by linarith, ha.le⟩
  have h0b : (0 : ℝ) ∈ Icc (-b) b := ⟨by linarith, hb.le⟩
  have hle₁ : L (γ₁ t) ≤ L (γ₁ 0) := hma.monotoneOn hta h0a ht.2
  have hle₂ : L (γ₂ 0) ≤ L (γ₂ (t + r)) := hmb.monotoneOn h0b htrb (by linarith [ht.1])
  have hL₀ : L (γ₁ 0) = L (γ₂ 0) := by rw [h₀]
  rw [map_sub]
  rcases ht.2.lt_or_eq with htlt | rfl
  · have hlt : L (γ₁ t) < L (γ₁ 0) := hma hta h0a htlt
    linarith
  · have hlt : L (γ₂ 0) < L (γ₂ (0 + r)) := hmb h0b htrb (by linarith [hr.1])
    linarith

end TauCeti
