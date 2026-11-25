/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Function.Coercivity

import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Topology.MetricSpace.Cauchy
import TauCeti.Topology.Order.IsLUB
import TauCeti.Topology.Semicontinuity.Sequences

/-!
# Minimizers of uniformly and strongly convex functions

A lower semicontinuous strongly convex function with positive modulus attains its
minimum uniquely on a nonempty complete set.

The Cauchy and attainment arguments also apply to bounded-below uniformly convex
functions whose modulus is positive at every positive radius.
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

/-- A sequence in the domain whose objective values tend to a lower bound on that
domain is Cauchy if the uniform modulus is positive at every positive radius. -/
theorem UniformConvexOn.cauchySeq_of_tendsto_comp {φ : ℝ → ℝ} (hf : UniformConvexOn s φ f)
    (hφ : ∀ r > 0, 0 < φ r)
    {a : ℝ} (hlower : ∀ z ∈ s, a ≤ f z) {u : ℕ → E} (hu : ∀ n, u n ∈ s)
    (hlim : Tendsto (f ∘ u) atTop (𝓝 a)) : CauchySeq u := by
  refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
  have hcut : a < a + φ ε / 4 := by linarith [hφ ε hε]
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hcut))
  simp only [Function.comp_apply] at hN
  have hgap {x y : E} (hx : x ∈ s) (hy : y ∈ s) (hd : ε ≤ dist x y)
      (hxy : f x ≤ f y) : φ ε / 4 ≤ f y - a := by
    have hdpos : 0 < dist x y := hε.trans_le hd
    let t := ε / dist x y
    have ht : t ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hε.le hdpos.le, (div_le_one hdpos).2 hd⟩
    let z := AffineMap.lineMap x y t
    have hz : z ∈ s := hf.1.lineMap_mem hx hy ht
    have hnorm : ‖x - z‖ = ε := by
      rw [← dist_eq_norm, dist_left_lineMap, Real.norm_of_nonneg ht.1]
      exact div_mul_cancel₀ ε hdpos.ne'
    have hpen : 0 ≤ t * (1 - t) * φ ‖x - y‖ := by
      apply mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2))
      exact (hφ _ (by simpa only [dist_eq_norm] using hdpos)).le
    have hzle : f z ≤ f y := by
      have hseg := hf.map_lineMap_le hx hy ht
      have hweighted := mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 hxy)
      dsimp only [z]
      nlinarith
    have hmid := hf.div_four_le_sub hlower hx hz
    rw [hnorm] at hmid
    linarith
  refine ⟨N, fun n hn k hk ↦ lt_of_not_ge fun hd ↦ ?_⟩
  rcases le_total (f (u n)) (f (u k)) with hnk | hkn
  · linarith [hgap (hu n) (hu k) hd hnk, hN k hk]
  · have hd' : ε ≤ dist (u k) (u n) := by simpa only [dist_comm] using hd
    linarith [hgap (hu k) (hu n) hd' hkn, hN n hn]

/-- A bounded-below uniformly convex function attains its minimum on a nonempty complete
domain if it is lower semicontinuous there and its modulus is positive at every
positive radius. -/
theorem UniformConvexOn.exists_isMinOn_of_bddBelow {φ : ℝ → ℝ} (hf : UniformConvexOn s φ f)
    (hφ : ∀ r > 0, 0 < φ r)
    (hs : IsComplete s) (hne : s.Nonempty) (hlsc : LowerSemicontinuousOn f s)
    (hbdd : BddBelow (f '' s)) : ∃ x ∈ s, IsMinOn f s x := by
  obtain ⟨u, hu, -, hulim⟩ := TauCeti.exists_seq_forall_mem_and_tendsto_sInf hne hbdd
  have hlower : ∀ z ∈ s, sInf (f '' s) ≤ f z := fun z hz ↦ csInf_le hbdd ⟨z, hz, rfl⟩
  have hcauchy := hf.cauchySeq_of_tendsto_comp hφ hlower hu hulim
  obtain ⟨x, hx, hux⟩ := cauchySeq_tendsto_of_isComplete hs hu hcauchy
  refine ⟨x, hx, hlsc.seqLowerSemicontinuousOn.isMinOn_of_tendsto hx hu hux ?_⟩
  exact fun v hv c hc ↦ hulim.eventually (gt_mem_nhds ((hlower v hv).trans_lt hc))

/-- A lower semicontinuous strongly convex function with positive modulus on a nonempty
complete set has a unique constrained minimizer. -/
theorem StrongConvexOn.existsUnique_isMinOn (hf : StrongConvexOn s μ f) (hμ : 0 < μ)
    (hs : IsComplete s) (hne : s.Nonempty) (hlsc : LowerSemicontinuousOn f s) :
    ∃! x, x ∈ s ∧ IsMinOn f s x := by
  have hbdd : BddBelow (f '' s) := by
    obtain ⟨z, hz⟩ := hne
    exact hf.bddBelow_image_of_lowerSemicontinuousWithinAt hμ hz (hlsc z hz)
  have hmod : ∀ r > (0 : ℝ), 0 < μ / 2 * r ^ 2 := by
    intro r hr
    positivity
  obtain ⟨x, hx, hmin⟩ := hf.uniformConvexOn.exists_isMinOn_of_bddBelow hmod hs hne hlsc hbdd
  exact ⟨x, ⟨hx, hmin⟩, fun y hy ↦
    (hf.strictConvexOn hμ).eq_of_isMinOn hy.2 hmin hy.1 hx⟩
