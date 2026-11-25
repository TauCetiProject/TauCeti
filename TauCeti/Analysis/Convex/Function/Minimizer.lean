/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Function.Uniform

import Mathlib.Analysis.Normed.Affine.AddTorsor
import TauCeti.Topology.Order.IsLUB
import TauCeti.Topology.Semicontinuity.Sequences

/-!
# Minimizers of uniformly and strongly convex functions

At every minimizer, strong convexity gives a quadratic lower bound, which is sharp
quadratic growth when the modulus is positive. A lower semicontinuous strongly convex
function with positive modulus attains its minimum uniquely on a nonempty complete set.

The Cauchy and attainment arguments also apply to bounded-below uniformly convex
functions whose modulus is bounded away from zero off every neighborhood of zero.
They use the same midpoint estimate as the resolvent proof
`TauCeti.moreauYosidaResolvent_nonempty_of_convexAlong`. See Ambrosio, Gigli and
Savaré, *Gradient Flows in Metric Spaces and in the Space of Probability Measures*,
2nd ed., Section 2.4, Lemma 4.1.1 and Theorem 4.1.2.
-/

public section

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} {f : E → ℝ} {μ : ℝ} {x y : E}

/-- A quadratic lower bound at a constrained minimizer, with sharp quadratic growth
when the modulus is positive. -/
theorem StrongConvexOn.add_mul_norm_sub_sq_le_of_isMinOn (hf : StrongConvexOn s μ f) (hx : x ∈ s)
    (hmin : IsMinOn f s x) (hy : y ∈ s) :
    f x + μ / 2 * ‖x - y‖ ^ 2 ≤ f y :=
  UniformConvexOn.add_le_of_isMinOn hf hx hmin hy

/-- A sequence whose objective values tend to a common lower bound is Cauchy when the
uniform modulus is bounded away from zero off every neighborhood of zero. -/
theorem UniformConvexOn.cauchySeq_of_tendsto_comp {φ : ℝ → ℝ} (hf : UniformConvexOn s φ f)
    (hφ : ∀ ε > 0, ∃ c > 0, ∀ r ≥ ε, c ≤ φ r)
    {a : ℝ} (hlower : ∀ z ∈ s, a ≤ f z) {u : ℕ → E} (hu : ∀ n, u n ∈ s)
    (hlim : Tendsto (f ∘ u) atTop (𝓝 a)) : CauchySeq u := by
  refine TauCeti.cauchySeq_of_le_average_sub hφ (fun n k ↦ ?_) hlim
  simpa only [dist_eq_norm, Function.comp_apply] using hf.div_four_le_sub hlower (hu n) (hu k)

/-- A bounded-below uniformly convex function attains its minimum on a nonempty complete
domain if it is lower semicontinuous there and its modulus is bounded away from zero
off every neighborhood of zero. -/
theorem UniformConvexOn.exists_isMinOn_of_bddBelow {φ : ℝ → ℝ} (hf : UniformConvexOn s φ f)
    (hφ : ∀ ε > 0, ∃ c > 0, ∀ r ≥ ε, c ≤ φ r)
    (hs : IsComplete s) (hne : s.Nonempty) (hlsc : LowerSemicontinuousOn f s)
    (hbdd : BddBelow (f '' s)) : ∃ x ∈ s, IsMinOn f s x := by
  obtain ⟨u, hu, -, hulim⟩ := TauCeti.exists_seq_forall_mem_and_tendsto_sInf hne hbdd
  have hlower : ∀ z ∈ s, sInf (f '' s) ≤ f z := fun z hz ↦ csInf_le hbdd ⟨z, hz, rfl⟩
  have hcauchy := hf.cauchySeq_of_tendsto_comp hφ hlower hu hulim
  obtain ⟨x, hx, hux⟩ := cauchySeq_tendsto_of_isComplete hs hu hcauchy
  have hfx := hlsc.seqLowerSemicontinuousOn.le_of_tendsto hx hu hux hulim
  exact ⟨x, hx, isMinOn_iff.2 (fun y hy ↦ hfx.trans (hlower y hy))⟩

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
      hf.1.lineMap_mem hx y.property ht⟩
    refine ⟨z, ?_, ?_⟩
    · simpa only [x₀, z, Subtype.dist_eq, Real.norm_of_nonneg ht.1] using
        (dist_left_lineMap x (y : E) t).le
    · have hcurve := hf.convexAlong_lineMap hx y.property
      simpa only [g, x₀, z, Function.comp_apply, AffineMap.lineMap_apply_zero,
        AffineMap.lineMap_apply_one] using TauCeti.convexAlong_def.mp hcurve t ht

/-- A lower semicontinuous strongly convex function with positive modulus on a nonempty
complete set has a unique constrained minimizer. -/
theorem StrongConvexOn.existsUnique_isMinOn (hf : StrongConvexOn s μ f) (hμ : 0 < μ)
    (hs : IsComplete s) (hne : s.Nonempty) (hlsc : LowerSemicontinuousOn f s) :
    ∃! x, x ∈ s ∧ IsMinOn f s x := by
  have hbdd : BddBelow (f '' s) := by
    obtain ⟨z, hz⟩ := hne
    exact hf.bddBelow_image_of_lowerSemicontinuousWithinAt hμ hz (hlsc z hz)
  have hu : UniformConvexOn s (fun r ↦ μ / 2 * r ^ 2) f := hf
  have hmod : ∀ ε > (0 : ℝ), ∃ c > (0 : ℝ), ∀ r ≥ ε, c ≤ μ / 2 * r ^ 2 := by
    intro ε hε
    exact ⟨μ / 2 * ε ^ 2, by positivity, fun r hr ↦ by gcongr⟩
  obtain ⟨x, hx, hmin⟩ := hu.exists_isMinOn_of_bddBelow hmod hs hne hlsc hbdd
  exact ⟨x, ⟨hx, hmin⟩, fun y hy ↦
    (hf.strictConvexOn hμ).eq_of_isMinOn hy.2 hmin hy.1 hx⟩
