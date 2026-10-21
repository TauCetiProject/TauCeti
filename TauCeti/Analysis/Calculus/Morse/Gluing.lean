/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Passage
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Gluing transverse discs through the split hyperbolic box

Let `b` be a critical point at which the flow is the split hyperbolic flow
`φ t (x, y) = (e^{-t} x, e^t y)` (`TauCeti.splitQuadraticFlow`) on the box `‖x‖ ≤ ε, ‖y‖ ≤ ε`, and
let a broken trajectory enter the box along the stable set at `(x₀, 0)` and leave it along the
unstable set at `(0, y₀)`. In the gluing step of Morse homology, the unbroken trajectories near
the broken one are those starting on a disc `S` in the entrance face that passes through
`(x₀, 0)` transversally to the stable set, such as the trace there of the unstable manifold of
the starting critical point, and ending on a disc `T` in the exit face that passes through
`(0, y₀)` transversally to the unstable set, such as the trace there of the stable manifold of the
final critical point. Near these two points, transversality makes `S` a graph `y ↦ (g y, y)` over
the expanding factor and `T` a graph `x ↦ (x, k x)` over the contracting factor.

This file proves that such orbits form a single continuous family converging to the broken
trajectory. Write a point of the entrance face off the stable set as `(g (r • w), r • w)` with
`‖w‖ = ε`; the number `0 < r ≤ 1` is the gluing parameter. By
`TauCeti.splitPassage_toLp_smul` its exit point is `(r • g (r • w), w)`, so it lies on `T` exactly
when `w = k (r • g (r • w))`. When `g` and `k` are Lipschitz, the right-hand side is a contraction
of `w` with constant `Kk * Kg * r ^ 2`. For small `r`, Banach's fixed-point theorem gives one
solution `w r`, depending continuously on `r`. At `r = 0` the equation reads `w = k 0 = y₀`, so as
`r → 0` the entrance points `(g (r • w r), r • w r)` tend to `(x₀, 0)` and the exit points
`(r • g (r • w r), w r)` tend to `(0, y₀)`.

This is the nonlinear form of the linear gluing statement
`TauCeti.setOf_mem_splitPassage_source_eq_image`, which is the case of constant `g` and `k`.

## Main results

* `TauCeti.exists_setOf_mem_splitPassage_source_graph_eq_image`: the points of the graph of `g` in
  the entrance face whose passage lies on the graph of `k` form the image of the gluing parameter
  interval under `r ↦ (g (r • w r), r • w r)`, for a map `w` continuous on `[0, r₀]` with
  `w 0 = k 0` and `‖w r‖ = ε`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
-/

public section

open Metric Set
open scoped NNReal

namespace TauCeti

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [NormedSpace ℝ Eₛ]
  [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ]
  {ε r₀ : ℝ} {Kg Kk : ℝ≥0} {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ}

/-- A gluing parameter `r ∈ [0, r₀]` scales the closed ball of radius `ε` into the closed ball of
radius `r₀ * ε`. -/
private theorem smul_mem_closedBall_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : r ∈ Icc 0 r₀) {v : E} (hv : ‖v‖ ≤ ε) :
    r • v ∈ closedBall (0 : E) (r₀ * ε) := by
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hr.1]
  exact mul_le_mul hr.2 hv (norm_nonneg v) (hr.1.trans hr.2)

/-- The gluing map `w ↦ k (r • g (r • w))` sends the closed ball of radius `ε` to the sphere of
radius `ε`. -/
private theorem norm_gluing_eq (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε) {r : ℝ} (hr : r ∈ Icc 0 r₀) {w : Eᵤ}
    (hw : ‖w‖ ≤ ε) : ‖k (r • g (r • w))‖ = ε :=
  hkε _ (smul_mem_closedBall_mul hr (hgε _ (smul_mem_closedBall_mul hr hw)).le)

/-- The gluing map `w ↦ k (r • g (r • w))` is Lipschitz with constant `Kk * Kg * r₀` on the
closed ball of radius `ε`. -/
private theorem dist_gluing_le (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hr₀ : r₀ ≤ 1) {r : ℝ} (hr : r ∈ Icc 0 r₀) {v v' : Eᵤ} (hv : ‖v‖ ≤ ε) (hv' : ‖v'‖ ≤ ε) :
    dist (k (r • g (r • v))) (k (r • g (r • v'))) ≤ Kk * Kg * r₀ * dist v v' := by
  have hrv := smul_mem_closedBall_mul hr hv
  have hrv' := smul_mem_closedBall_mul hr hv'
  have hrr : r * r ≤ r₀ := by nlinarith [hr.1, hr.2]
  calc dist (k (r • g (r • v))) (k (r • g (r • v')))
      ≤ Kk * dist (r • g (r • v)) (r • g (r • v')) :=
        hk.dist_le_mul _ (smul_mem_closedBall_mul hr (hgε _ hrv).le) _
          (smul_mem_closedBall_mul hr (hgε _ hrv').le)
    _ = Kk * (r * dist (g (r • v)) (g (r • v'))) := by
        rw [dist_smul₀, Real.norm_of_nonneg hr.1]
    _ ≤ Kk * (r * (Kg * dist (r • v) (r • v'))) := by
        gcongr
        · exact hr.1
        · exact hg.dist_le_mul _ hrv _ hrv'
    _ = Kk * Kg * (r * r) * dist v v' := by
        rw [dist_smul₀, Real.norm_of_nonneg hr.1]
        ring
    _ ≤ Kk * Kg * r₀ * dist v v' := by gcongr

/-- The gluing map `w ↦ k (r • g (r • w))` depends Lipschitz-continuously on the gluing parameter,
uniformly on the closed ball of radius `ε`. -/
private theorem dist_gluing_le_dist (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hr₀ : r₀ ≤ 1) {r s : ℝ} (hr : r ∈ Icc 0 r₀) (hs : s ∈ Icc 0 r₀) {v : Eᵤ} (hv : ‖v‖ ≤ ε) :
    dist (k (r • g (r • v))) (k (s • g (s • v))) ≤ Kk * ((1 + Kg) * ε) * dist r s := by
  have hrv := smul_mem_closedBall_mul hr hv
  have hsv := smul_mem_closedBall_mul hs hv
  have hs1 : s ≤ 1 := hs.2.trans hr₀
  have hε : 0 ≤ ε := (norm_nonneg v).trans hv
  calc dist (k (r • g (r • v))) (k (s • g (s • v)))
      ≤ Kk * dist (r • g (r • v)) (s • g (s • v)) :=
        hk.dist_le_mul _ (smul_mem_closedBall_mul hr (hgε _ hrv).le) _
          (smul_mem_closedBall_mul hs (hgε _ hsv).le)
    _ ≤ Kk * (dist (r • g (r • v)) (s • g (r • v)) + dist (s • g (r • v)) (s • g (s • v))) := by
        gcongr
        exact dist_triangle _ _ _
    _ ≤ Kk * (dist r s * ε + s * dist (g (r • v)) (g (s • v))) := by
        rw [dist_smul₀, Real.norm_of_nonneg hs.1]
        gcongr
        simpa [hgε _ hrv] using dist_pair_smul r s (g (r • v))
    _ ≤ Kk * (dist r s * ε + 1 * (Kg * (dist r s * ε))) := by
        gcongr
        calc dist (g (r • v)) (g (s • v)) ≤ Kg * dist (r • v) (s • v) :=
              hg.dist_le_mul _ hrv _ hsv
          _ ≤ Kg * (dist r s * ε) := by
              gcongr
              exact (dist_pair_smul r s v).trans (by rw [dist_zero_right]; gcongr)
    _ = Kk * ((1 + Kg) * ε) * dist r s := by ring

/-- **Gluing transverse discs through the split hyperbolic box.** Let `y ↦ (g y, y)` be a disc in
the entrance face `‖x‖ = ε` over the closed ball of radius `r₀ * ε` of the expanding factor, and
`x ↦ (x, k x)` a disc in the exit face `‖y‖ = ε` over the closed ball of radius `r₀ * ε` of the
contracting factor, with `g` and `k` Lipschitz with constants `Kg` and `Kk`. If `r₀ ≤ 1` and
`Kk * Kg * r₀ < 1`, then the points `z` of the first disc with `‖z.snd‖ ≤ r₀ * ε` whose passage
through the box lies on the second disc are exactly the points `(g (r • w r), r • w r)` for
`0 < r ≤ r₀`, where `w` is continuous on `[0, r₀]`, has norm `ε` there, and starts at `w 0 = k 0`.

So these orbits form one continuous family, indexed by the gluing parameter `r = ‖z.snd‖ / ε`. By
`TauCeti.splitPassage_toLp_smul`, the exit point of the orbit with parameter `r` is
`(r • g (r • w r), w r)`. Since `w` is continuous at `0` with `w 0 = k 0` and `g` is Lipschitz,
as `r → 0` the entrance points tend to `(g 0, 0)` and the exit points to `(0, k 0)`: the family
converges to the broken orbit through these two points. -/
theorem exists_setOf_mem_splitPassage_source_graph_eq_image [CompleteSpace Eᵤ]
    (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε)
    (hε : 0 < ε) (hr₀ : r₀ ≤ 1) (hK : Kk * Kg * r₀ < 1) :
    ∃ w : ℝ → Eᵤ, ContinuousOn w (Icc 0 r₀) ∧ w 0 = k 0 ∧ (∀ r ∈ Icc 0 r₀, ‖w r‖ = ε) ∧
      {z | z ∈ (splitPassage ε).source ∧ ‖z.snd‖ ≤ r₀ * ε ∧ z.fst = g z.snd ∧
          (splitPassage ε z).snd = k (splitPassage ε z).fst} =
        (fun r ↦ WithLp.toLp 2 (g (r • w r), r • w r)) '' Ioc 0 r₀ := by
  rcases lt_or_ge r₀ 0 with hr₀0 | hr₀0
  · -- With a negative radius both sides are empty.
    refine ⟨fun _ ↦ k 0, continuousOn_const, rfl, fun r hr ↦ absurd (hr.1.trans hr.2) hr₀0.not_ge,
      ?_⟩
    rw [Ioc_eq_empty hr₀0.not_gt, image_empty, eq_empty_iff_forall_notMem]
    rintro z ⟨-, hz, -⟩
    exact (norm_nonneg _).not_gt (hz.trans_lt (mul_neg_of_neg_of_pos hr₀0 hε))
  set s : Set Eᵤ := closedBall 0 ε
  have hnorm {r : ℝ} (hr : r ∈ Icc 0 r₀) {v : Eᵤ} (hv : v ∈ s) : ‖k (r • g (r • v))‖ = ε :=
    norm_gluing_eq hgε hkε hr (mem_closedBall_zero_iff.1 hv)
  have hmaps {r : ℝ} (hr : r ∈ Icc 0 r₀) : MapsTo (fun v ↦ k (r • g (r • v))) s s :=
    fun v hv ↦ mem_closedBall_zero_iff.2 (hnorm hr hv).le
  have hcontr {r : ℝ} (hr : r ∈ Icc 0 r₀) {v v' : Eᵤ} (hv : v ∈ s) (hv' : v' ∈ s) :
      dist (k (r • g (r • v))) (k (r • g (r • v'))) ≤ Kk * Kg * r₀ * dist v v' :=
    dist_gluing_le hg hgε hk hr₀ hr (mem_closedBall_zero_iff.1 hv) (mem_closedBall_zero_iff.1 hv')
  -- Banach's fixed-point theorem on the closed ball of radius `ε`.
  have hex (r : ℝ) (hr : r ∈ Icc 0 r₀) : ∃ v ∈ s, k (r • g (r • v)) = v := by
    set K : ℝ≥0 := Kk * Kg * r₀.toNNReal
    have hKr : (K : ℝ) = Kk * Kg * r₀ := by simp [K, Real.coe_toNNReal _ hr₀0]
    have hf : ContractingWith K ((hmaps hr).restrict _ s s) := by
      refine ⟨by rw [← NNReal.coe_lt_coe, hKr]; exact hK, LipschitzWith.of_dist_le_mul ?_⟩
      rintro ⟨v, hv⟩ ⟨v', hv'⟩
      rw [hKr]
      exact hcontr hr hv hv'
    have h0 : (0 : Eᵤ) ∈ s := mem_closedBall_self hε.le
    obtain ⟨v, hv, hfix, -⟩ :=
      hf.exists_fixedPoint' isClosed_closedBall.isComplete (hmaps hr) h0 (edist_ne_top _ _)
    exact ⟨v, hv, hfix⟩
  have huniq {r : ℝ} (hr : r ∈ Icc 0 r₀) {v v' : Eᵤ} (hv : v ∈ s) (hv' : v' ∈ s)
      (hfv : k (r • g (r • v)) = v) (hfv' : k (r • g (r • v')) = v') : v = v' := by
    have h := hcontr hr hv hv'
    rw [hfv, hfv'] at h
    have : dist v v' ≤ 0 := by nlinarith [dist_nonneg (x := v) (y := v')]
    exact dist_le_zero.1 this
  have hchoice (r : ℝ) : ∃ v, r ∈ Icc 0 r₀ → v ∈ s ∧ k (r • g (r • v)) = v := by
    by_cases hr : r ∈ Icc 0 r₀
    · obtain ⟨v, hv, hfv⟩ := hex r hr
      exact ⟨v, fun _ ↦ ⟨hv, hfv⟩⟩
    · exact ⟨0, fun h ↦ absurd h hr⟩
  choose w hw using hchoice
  have hwnorm (r : ℝ) (hr : r ∈ Icc 0 r₀) : ‖w r‖ = ε := by
    rw [← (hw r hr).2]
    exact hnorm hr (hw r hr).1
  refine ⟨w, ?_, ?_, hwnorm, ?_⟩
  · -- The fixed point depends Lipschitz-continuously on the gluing parameter.
    set C : ℝ := Kk * ((1 + Kg) * ε) / (1 - Kk * Kg * r₀)
    have hpos : 0 < 1 - Kk * Kg * r₀ := sub_pos.2 hK
    refine (LipschitzOnWith.of_dist_le_mul (K := C.toNNReal) fun r hr r' hr' ↦ ?_).continuousOn
    have h₁ := hcontr hr (hw r hr).1 (hw r' hr').1
    have h₂ := dist_gluing_le_dist hg hgε hk hr₀ hr hr' (mem_closedBall_zero_iff.1 (hw r' hr').1)
    have htri := dist_triangle (k (r • g (r • w r))) (k (r • g (r • w r')))
      (k (r' • g (r' • w r')))
    rw [(hw r hr).2, (hw r' hr').2] at htri
    rw [(hw r hr).2] at h₁
    rw [(hw r' hr').2] at h₂
    have hle : dist (w r) (w r') ≤ C * dist r r' := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      nlinarith
    exact hle.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) dist_nonneg)
  · have h := (hw 0 (left_mem_Icc.2 hr₀0)).2
    simp only [zero_smul] at h
    exact h.symm
  · ext z
    constructor
    · rintro ⟨hsrc, hzr₀, hzg, hzk⟩
      have hy : 0 < ‖z.snd‖ := norm_pos_iff.2 (mem_splitPassage_source.1 hsrc).2.1
      set r := ‖z.snd‖ / ε with hr_def
      have hr : r ∈ Ioc 0 r₀ := ⟨div_pos hy hε, (div_le_iff₀ hε).2 hzr₀⟩
      have hr' : r ∈ Icc 0 r₀ := Ioc_subset_Icc_self hr
      obtain ⟨v, hv_def⟩ : ∃ v, (splitPassage ε z).snd = v := ⟨_, rfl⟩
      rw [hv_def] at hzk
      have hvz : r • v = z.snd := by
        rw [← hv_def, snd_splitPassage hsrc, smul_smul, hr_def, div_mul_div_cancel₀ hε.ne',
          div_self hy.ne', one_smul]
      have hv : v ∈ s := by
        rw [← hv_def]
        exact mem_closedBall_zero_iff.2
          (mem_splitPassage_target.1 ((splitPassage ε).map_source hsrc)).1.le
      have hfv : k (r • g (r • v)) = v := by
        rw [hvz, ← hzg, hzk, fst_splitPassage hsrc]
      have hvw : v = w r := huniq hr' hv (hw r hr').1 hfv (hw r hr').2
      refine ⟨r, hr, ?_⟩
      apply WithLp.ofLp_injective
      ext
      · simp [← hvw, hvz, hzg]
      · simp [← hvw, hvz]
    · rintro ⟨r, hr, rfl⟩
      have hr' : r ∈ Icc 0 r₀ := Ioc_subset_Icc_self hr
      have hwr := hwnorm r hr'
      have hgr : ‖g (r • w r)‖ = ε := hgε _ (smul_mem_closedBall_mul hr' hwr.le)
      have hpass := splitPassage_toLp_smul (g (r • w r)) hwr hε hr.1
      refine ⟨toLp_smul_mem_splitPassage_source hgr hwr hε ⟨hr.1, hr.2.trans hr₀⟩, ?_, by simp,
        ?_⟩
      · simpa [norm_smul, Real.norm_of_nonneg hr.1.le, hwr] using
          mul_le_mul_of_nonneg_right hr.2 hε.le
      · rw [hpass]
        simpa using (hw r hr').2.symm

end TauCeti
