/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Order.Filter.Extr

import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
import TauCeti.Topology.Semicontinuity.Sequences
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Minimizers of strongly convex functions

Strong convexity gives sharp quadratic growth at every minimizer. On a nonempty complete
subset of a real normed space, a lower semicontinuous strongly convex function with positive
modulus has a unique minimizer. The midpoint inequality controls the distance between points
by their objective gaps, making minimizing sequences Cauchy.

The real-valued estimates use `TauCeti.ConvexAlong.apply_add_le_of_forall_le` and
`TauCeti.iInf_ne_bot_of_lowerSemicontinuousAt` along affine segments. For the metric
interpolation estimates, see Ambrosio, Gigli and Savaré, *Gradient Flows in Metric Spaces
and in the Space of Probability Measures*, 2nd ed., Section 2.4.
-/

public section

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} {f : E → ℝ} {μ : ℝ} {x y : E}

-- Express strong convexity in the affine-segment and distance conventions of the metric lemmas.
private theorem lineMap_le (hf : StrongConvexOn s μ f) (hx : x ∈ s) (hy : y ∈ s)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    f (AffineMap.lineMap x y t) ≤
      (1 - t) * f x + t * f y - μ / 2 * t * (1 - t) * dist x y ^ 2 := by
  rw [AffineMap.lineMap_apply_module, dist_eq_norm]
  have h := hf.2 hx hy (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
  simp only [smul_eq_mul] at h
  linarith

/-- Sharp quadratic growth at a constrained minimizer. The modulus may have either sign. -/
theorem StrongConvexOn.add_mul_norm_sub_sq_le_of_isMinOn (hf : StrongConvexOn s μ f) (hx : x ∈ s)
    (hmin : IsMinOn f s x) (hy : y ∈ s) :
    f x + μ / 2 * ‖x - y‖ ^ 2 ≤ f y := by
  have hcurve : TauCeti.ConvexAlong μ (fun z ↦ (f z : EReal))
      (AffineMap.lineMap x y) := by
    rw [TauCeti.convexAlong_def]
    intro t ht
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, ← EReal.coe_mul,
      ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff] using lineMap_le hf hx hy ht
  have h := hcurve.apply_add_le_of_forall_le (fun t ht ↦ by
    simp only [AffineMap.lineMap_apply_zero, EReal.coe_le_coe_iff]
    exact hmin (hf.1.segment_subset hx hy (lineMap_mem_segment ℝ x y ht)))
  simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, dist_eq_norm,
    ← EReal.coe_add, EReal.coe_le_coe_iff] using h

/-- The average objective gap above a common lower bound is at least `μ / 8` times the
squared distance between two points. -/
theorem StrongConvexOn.mul_norm_sub_sq_le_sub (hf : StrongConvexOn s μ f)
    {a : ℝ} (hlower : ∀ z ∈ s, a ≤ f z) (hx : x ∈ s) (hy : y ∈ s) :
    μ / 8 * ‖x - y‖ ^ 2 ≤ (f x + f y) / 2 - a := by
  have hm := hlower _ (hf.1 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hc := hf.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hc
  linarith

/-- A minimizing sequence for a strongly convex function with positive modulus is Cauchy. -/
theorem StrongConvexOn.cauchySeq_of_tendsto (hf : StrongConvexOn s μ f) (hμ : 0 < μ)
    {a : ℝ} (hlower : ∀ z ∈ s, a ≤ f z) {u : ℕ → E} (hu : ∀ n, u n ∈ s)
    (hlim : Tendsto (f ∘ u) atTop (𝓝 a)) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hμ8 : 0 < μ / 8 := by positivity
  have hgap : 0 < μ / 8 * ε ^ 2 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (lt_add_of_pos_right a hgap)))
  simp only [Function.comp_def] at hN
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have hbound := hf.mul_norm_sub_sq_le_sub hlower (hu m) (hu n)
  have hsq : ‖u m - u n‖ ^ 2 < ε ^ 2 :=
    (mul_lt_mul_iff_right₀ hμ8).1 (by linarith [hN m hm, hN n hn])
  rw [dist_eq_norm]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 hsq

/-- A strongly convex function with positive modulus is bounded below on its domain if it is
lower semicontinuous within the domain at one of its points. -/
theorem StrongConvexOn.bddBelow_image_of_lowerSemicontinuousWithinAt
    (hf : StrongConvexOn s μ f) (hμ : 0 < μ) (hx : x ∈ s)
    (hlsc : LowerSemicontinuousWithinAt f s x) : BddBelow (f '' s) := by
  let g : s → EReal := (fun z : E ↦ (f z : EReal)) ∘ Subtype.val
  let x₀ : s := ⟨x, hx⟩
  have hcoe : LowerSemicontinuousWithinAt (fun z ↦ (f z : EReal)) s x :=
    continuous_coe_real_ereal.continuousAt.comp_lowerSemicontinuousWithinAt hlsc
      EReal.coe_strictMono.monotone
  have hg : LowerSemicontinuousAt g x₀ :=
    lowerSemicontinuousWithinAt_univ_iff.mp
      (LowerSemicontinuousWithinAt.comp (g := ((↑) : s → E))
        (f := fun z : E ↦ (f z : EReal)) (t := Set.univ) (x := x₀) hcoe
        continuous_subtypeVal.continuousWithinAt (fun z _ ↦ z.property))
  have hb := TauCeti.iInf_ne_bot_of_lowerSemicontinuousAt hg (EReal.coe_ne_top _)
    (EReal.coe_ne_bot _) hμ (fun y _ ↦ ?_)
  · obtain ⟨a, _, ha⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hb)
    refine ⟨a, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact EReal.coe_le_coe_iff.1 (ha.le.trans (iInf_le g ⟨y, hy⟩))
  · refine ⟨dist x (y : E), fun t ht ↦ ?_⟩
    let z : s := ⟨AffineMap.lineMap x (y : E) t,
      hf.1.segment_subset hx y.property (lineMap_mem_segment ℝ x (y : E) ht)⟩
    refine ⟨z, ?_, ?_⟩
    · simpa only [x₀, z, Subtype.dist_eq, Real.norm_of_nonneg ht.1] using
        (dist_left_lineMap x (y : E) t).le
    · simpa only [g, x₀, z, Function.comp_apply, ← EReal.coe_mul, ← EReal.coe_add,
        ← EReal.coe_sub, EReal.coe_le_coe_iff] using lineMap_le hf hx y.property ht

/-- A lower semicontinuous strongly convex function with positive modulus on a nonempty
complete set has a unique constrained minimizer. -/
theorem StrongConvexOn.existsUnique_isMinOn (hf : StrongConvexOn s μ f) (hμ : 0 < μ)
    (hs : IsComplete s) (hne : s.Nonempty) (hlsc : LowerSemicontinuousOn f s) :
    ∃! x, x ∈ s ∧ IsMinOn f s x := by
  have hbdd : BddBelow (f '' s) := by
    obtain ⟨z, hz⟩ := hne
    exact hf.bddBelow_image_of_lowerSemicontinuousWithinAt hμ hz (hlsc z hz)
  obtain ⟨v, _, hvlim, hv⟩ := exists_seq_tendsto_sInf (hne.image f) hbdd
  choose u hu huv using hv
  have hulim : Tendsto (f ∘ u) atTop (𝓝 (sInf (f '' s))) := by
    simpa only [Function.comp_def, huv] using hvlim
  have hcauchy := hf.cauchySeq_of_tendsto hμ (fun z hz ↦ csInf_le hbdd ⟨z, hz, rfl⟩)
    hu hulim
  obtain ⟨x, hx, hux⟩ := cauchySeq_tendsto_of_isComplete hs hu hcauchy
  have hfx := hlsc.seqLowerSemicontinuousOn.le_of_tendsto hx hu hux hulim
  have hmin : IsMinOn f s x :=
    isMinOn_iff.2 (fun y hy ↦ hfx.trans (csInf_le hbdd ⟨y, hy, rfl⟩))
  exact ⟨x, ⟨hx, hmin⟩, fun y hy ↦
    (hf.strictConvexOn hμ).eq_of_isMinOn hy.2 hmin hy.1 hx⟩
