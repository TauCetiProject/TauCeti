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
solution `w r`, depending Lipschitz-continuously on `r`. At `r = 0` the equation reads
`w = k 0 = y₀`, so as `r → 0` the entrance points `(g (r • w r), r • w r)` tend to `(x₀, 0)` and
the exit points `(r • g (r • w r), w r)` tend to `(0, y₀)`.

This is the nonlinear form of the linear gluing statement
`TauCeti.setOf_mem_splitPassage_source_eq_image`, which is the case of constant `g` and `k`.

**Families of discs.** When the Morse indices of the three critical points of the broken
trajectory are not consecutive, the trace of the unstable manifold of the starting critical point
on the entrance face is no longer a single graph over the expanding factor, but a family of
graphs `y ↦ (g p y, y)`; likewise the trace of the stable manifold of the final critical point on
the exit face is a family of graphs `x ↦ (x, k p x)`. Here `p` ranges over pairs of a trajectory
into the middle critical point and a trajectory out of it, with `g p` depending on the first and
`k p` on the second. If the families are Lipschitz with uniform constants and depend continuously on
`p`, the gluing parametrizations `w r p` of the pairs of discs `g p` and `k p` can be chosen to
depend continuously on `(r, p)` jointly
(`TauCeti.exists_continuousOn_and_forall_setOf_mem_splitPassage_source_graph_eq_image`): the
gluing maps contract with a constant independent of `(r, p)`, so their fixed points move
continuously with the maps.

## Main results

* `TauCeti.exists_setOf_mem_splitPassage_source_graph_eq_image`: the points of the graph of `g` in
  the entrance face whose passage lies on the graph of `k` form the image of the gluing parameter
  interval under `r ↦ (g (r • w r), r • w r)`, for a map `w` Lipschitz on `[0, r₀]` with
  `w 0 = k 0` and `‖w r‖ = ε`.
* `TauCeti.exists_continuousOn_and_forall_setOf_mem_splitPassage_source_graph_eq_image`: for
  families of discs depending continuously on a parameter `p`, the same parametrizations, chosen
  jointly continuous in the gluing parameter and in `p`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
-/

public section

open Filter Metric Set Topology
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

/-- The gluing map `w ↦ k (r • g (r • w))` sends the closed ball of radius `ε` to itself. -/
private theorem mapsTo_gluing (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε) {r : ℝ} (hr : r ∈ Icc 0 r₀) :
    MapsTo (fun v ↦ k (r • g (r • v))) (closedBall 0 ε) (closedBall 0 ε) := fun _ hv ↦
  mem_closedBall_zero_iff.2 (norm_gluing_eq hgε hkε hr (mem_closedBall_zero_iff.1 hv)).le

/-- The contraction constant `Kk * Kg * r₀ ^ 2` of the gluing map, as a real number. -/
private theorem coe_mul_mul_toNNReal_sq (hr₀ : 0 ≤ r₀) :
    ((Kk * Kg * r₀.toNNReal ^ 2 : ℝ≥0) : ℝ) = Kk * Kg * r₀ ^ 2 := by
  simp [Real.coe_toNNReal _ hr₀]

/-- The gluing map `w ↦ k (r • g (r • w))` is Lipschitz with constant `Kk * Kg * r₀ ^ 2` on the
closed ball of radius `ε`. -/
private theorem dist_gluing_le (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    {r : ℝ} (hr : r ∈ Icc 0 r₀) {v v' : Eᵤ} (hv : ‖v‖ ≤ ε) (hv' : ‖v'‖ ≤ ε) :
    dist (k (r • g (r • v))) (k (r • g (r • v'))) ≤ Kk * Kg * r₀ ^ 2 * dist v v' := by
  have hrv := smul_mem_closedBall_mul hr hv
  have hrv' := smul_mem_closedBall_mul hr hv'
  have hrr : r * r ≤ r₀ ^ 2 := pow_two r₀ ▸ mul_le_mul hr.2 hr.2 hr.1 (hr.1.trans hr.2)
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
    _ ≤ Kk * Kg * r₀ ^ 2 * dist v v' := by gcongr

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

/-- For `r ∈ [0, r₀]`, the gluing map `w ↦ k (r • g (r • w))` restricts to a contraction of the
closed ball of radius `ε`, with constant `Kk * Kg * r₀ ^ 2`. -/
private theorem contractingWith_gluing (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε))) (hK : Kk * Kg * r₀ ^ 2 < 1) {r : ℝ}
    (hr : r ∈ Icc 0 r₀) (hmaps : MapsTo (fun v ↦ k (r • g (r • v))) (closedBall 0 ε)
      (closedBall 0 ε)) :
    ContractingWith (Kk * Kg * r₀.toNNReal ^ 2) (hmaps.restrict _ _ _) := by
  have hKr := coe_mul_mul_toNNReal_sq (Kk := Kk) (Kg := Kg) (hr.1.trans hr.2)
  refine ⟨by rw [← NNReal.coe_lt_coe, hKr]; exact hK, LipschitzWith.of_dist_le_mul ?_⟩
  rintro ⟨v, hv⟩ ⟨v', hv'⟩
  rw [hKr]
  exact dist_gluing_le hg hgε hk hr (mem_closedBall_zero_iff.1 hv) (mem_closedBall_zero_iff.1 hv')

/-- A family of fixed points of the gluing maps `w ↦ k (r • g (r • w))` in the closed ball of
radius `ε`, one for each gluing parameter `r ∈ [0, r₀]`, is Lipschitz in `r`. -/
private theorem lipschitzOnWith_gluing_fixedPt
    (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε) (hr₀ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1)
    {w : ℝ → Eᵤ} (hw : ∀ r ∈ Icc 0 r₀, w r ∈ closedBall 0 ε ∧ k (r • g (r • w r)) = w r) :
    LipschitzOnWith (Kk * ((1 + Kg) * ε) / (1 - Kk * Kg * r₀ ^ 2)).toNNReal w (Icc 0 r₀) := by
  refine LipschitzOnWith.of_dist_le_mul fun r hr r' hr' ↦ ?_
  have hle := (contractingWith_gluing hg hgε hk hK hr (mapsTo_gluing hgε hkε hr))
    |>.dist_fixedPoint_fixedPoint_of_dist_le' ((mapsTo_gluing hgε hkε hr').restrict _ _ _)
      (x := ⟨w r, (hw r hr).1⟩) (y := ⟨w r', (hw r' hr').1⟩) (Subtype.ext (hw r hr).2)
      (Subtype.ext (hw r' hr').2) fun v ↦
        dist_gluing_le_dist hg hgε hk hr₀ hr hr' (mem_closedBall_zero_iff.1 v.property)
  rw [Subtype.dist_eq, coe_mul_mul_toNNReal_sq (hr.1.trans hr.2), ← div_mul_eq_mul_div] at hle
  exact hle.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg)

/-- A point `z` of the graph of `g` in the entrance face whose passage lies on the graph of `k` has
gluing parameter `r = ‖z.snd‖ / ε`: its exit coordinate `v` satisfies `r • v = z.snd` and is a
fixed point of the gluing map `v ↦ k (r • g (r • v))`. -/
private theorem isFixedPt_gluing_snd_splitPassage {z : WithLp 2 (Eₛ × Eᵤ)}
    (hsrc : z ∈ (splitPassage ε).source) (hzg : z.fst = g z.snd)
    (hzk : (splitPassage ε z).snd = k (splitPassage ε z).fst) :
    Function.IsFixedPt (fun v ↦ k ((‖z.snd‖ / ε) • g ((‖z.snd‖ / ε) • v)))
        (splitPassage ε z).snd ∧
      (‖z.snd‖ / ε) • (splitPassage ε z).snd = z.snd := by
  have hε := pos_of_mem_splitPassage_source hsrc
  have hvz : (‖z.snd‖ / ε) • (splitPassage ε z).snd = z.snd := by
    rw [snd_splitPassage hsrc, smul_smul, div_mul_div_cancel₀ hε.ne',
      div_self (norm_ne_zero_iff.2 (mem_splitPassage_source.1 hsrc).2.1), one_smul]
  refine ⟨?_, hvz⟩
  rw [Function.IsFixedPt, hvz, ← hzg, ← fst_splitPassage hsrc]
  exact hzk.symm

/-- For `0 < ε` and `Kk * Kg * r₀ ^ 2 < 1`, Banach's fixed-point theorem gives, for each gluing
parameter `r ∈ [0, r₀]`, a fixed point `w r` of the gluing map `v ↦ k (r • g (r • v))` in the closed
ball of radius `ε`. -/
private theorem exists_fixedPt_gluing [CompleteSpace Eᵤ]
    (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε) (hε : 0 < ε) (hK : Kk * Kg * r₀ ^ 2 < 1) :
    ∃ w : ℝ → Eᵤ, ∀ r ∈ Icc 0 r₀, w r ∈ closedBall 0 ε ∧ k (r • g (r • w r)) = w r := by
  have hchoice (r : ℝ) : ∃ v, r ∈ Icc 0 r₀ → v ∈ closedBall 0 ε ∧ k (r • g (r • v)) = v := by
    by_cases hr : r ∈ Icc 0 r₀
    · obtain ⟨v, hv, hfv, -⟩ := (contractingWith_gluing hg hgε hk hK hr
        (mapsTo_gluing hgε hkε hr)).exists_fixedPoint' isClosed_closedBall.isComplete
        (mapsTo_gluing hgε hkε hr) (mem_closedBall_self hε.le) (edist_ne_top _ _)
      exact ⟨v, fun _ ↦ ⟨hv, hfv⟩⟩
    · exact ⟨0, fun h ↦ absurd h hr⟩
  choose w hw using hchoice
  exact ⟨w, hw⟩

/-- A point `z` of the graph of `g` in the entrance face with `‖z.snd‖ ≤ r₀ * ε` whose passage lies
on the graph of `k` is `(g (r • w r), r • w r)` for the gluing parameter `r = ‖z.snd‖ / ε`, where
`w r` is the fixed point of the gluing map: the exit coordinate of `z` is a fixed point, hence
equals `w r`. -/
private theorem toLp_mem_image_of_mem_graph
    (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε) (hε : 0 < ε) (hK : Kk * Kg * r₀ ^ 2 < 1)
    {w : ℝ → Eᵤ} (hw : ∀ r ∈ Icc 0 r₀, w r ∈ closedBall 0 ε ∧ k (r • g (r • w r)) = w r)
    {z : WithLp 2 (Eₛ × Eᵤ)} (hsrc : z ∈ (splitPassage ε).source) (hzr₀ : ‖z.snd‖ ≤ r₀ * ε)
    (hzg : z.fst = g z.snd) (hzk : (splitPassage ε z).snd = k (splitPassage ε z).fst) :
    z ∈ (fun r ↦ WithLp.toLp 2 (g (r • w r), r • w r)) '' Ioc 0 r₀ := by
  have hy : 0 < ‖z.snd‖ := norm_pos_iff.2 (mem_splitPassage_source.1 hsrc).2.1
  have hr : ‖z.snd‖ / ε ∈ Ioc 0 r₀ := ⟨div_pos hy hε, (div_le_iff₀ hε).2 hzr₀⟩
  have hr' := Ioc_subset_Icc_self hr
  obtain ⟨hfv, hvz⟩ := isFixedPt_gluing_snd_splitPassage hsrc hzg hzk
  have hv : (splitPassage ε z).snd ∈ closedBall 0 ε := mem_closedBall_zero_iff.2
    (mem_splitPassage_target.1 ((splitPassage ε).map_source hsrc)).1.le
  have hf := contractingWith_gluing hg hgε hk hK hr' (mapsTo_gluing hgε hkε hr')
  have hvw : (splitPassage ε z).snd = w (‖z.snd‖ / ε) :=
    Subtype.ext_iff.1 (hf.fixedPoint_unique' (x := ⟨_, hv⟩) (y := ⟨_, (hw _ hr').1⟩)
      (Subtype.ext hfv) (Subtype.ext (hw _ hr').2))
  refine ⟨_, hr, ?_⟩
  apply WithLp.ofLp_injective
  ext
  · simp only [← hvw, hvz]
    simpa using hzg.symm
  · simpa [← hvw] using hvz

/-- **Gluing transverse discs through the split hyperbolic box.** Let `y ↦ (g y, y)` be a disc in
the entrance face `‖x‖ = ε` over the closed ball of radius `r₀ * ε` of the expanding factor, and
`x ↦ (x, k x)` a disc in the exit face `‖y‖ = ε` over the closed ball of radius `r₀ * ε` of the
contracting factor, with `g` and `k` Lipschitz with constants `Kg` and `Kk`. If `r₀ ≤ 1` and
`Kk * Kg * r₀ ^ 2 < 1`, then the points `z` of the first disc with `‖z.snd‖ ≤ r₀ * ε` whose passage
through the box lies on the second disc are exactly the points `(g (r • w r), r • w r)` for
`0 < r ≤ r₀`, where `w` is Lipschitz on `[0, r₀]`, has norm `ε` there, starts at `w 0 = k 0`,
and satisfies the matching equation `k (r • g (r • w r)) = w r` throughout that interval.

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
    (hε : 0 < ε) (hr₀ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1) :
    ∃ w : ℝ → Eᵤ, LipschitzOnWith (Kk * ((1 + Kg) * ε) / (1 - Kk * Kg * r₀ ^ 2)).toNNReal w
        (Icc 0 r₀) ∧ w 0 = k 0 ∧ (∀ r ∈ Icc 0 r₀, ‖w r‖ = ε) ∧
      (∀ r ∈ Icc 0 r₀, k (r • g (r • w r)) = w r) ∧
      {z | z ∈ (splitPassage ε).source ∧ ‖z.snd‖ ≤ r₀ * ε ∧ z.fst = g z.snd ∧
          (splitPassage ε z).snd = k (splitPassage ε z).fst} =
        (fun r ↦ WithLp.toLp 2 (g (r • w r), r • w r)) '' Ioc 0 r₀ := by
  rcases lt_or_ge r₀ 0 with hr₀0 | hr₀0
  · -- With a negative radius both sides are empty.
    refine ⟨fun _ ↦ k 0, by rw [Icc_eq_empty hr₀0.not_ge]; exact lipschitzOnWith_empty _ _, rfl,
      fun r hr ↦ absurd (hr.1.trans hr.2) hr₀0.not_ge,
      fun r hr ↦ absurd (hr.1.trans hr.2) hr₀0.not_ge, ?_⟩
    rw [Ioc_eq_empty hr₀0.not_gt, image_empty, eq_empty_iff_forall_notMem]
    rintro z ⟨-, hz, -⟩
    exact (norm_nonneg _).not_gt (hz.trans_lt (mul_neg_of_neg_of_pos hr₀0 hε))
  obtain ⟨w, hw⟩ := exists_fixedPt_gluing hg hgε hk hkε hε hK
  have hwnorm (r : ℝ) (hr : r ∈ Icc 0 r₀) : ‖w r‖ = ε := by
    rw [← (hw r hr).2]
    exact norm_gluing_eq hgε hkε hr (mem_closedBall_zero_iff.1 (hw r hr).1)
  refine ⟨w, lipschitzOnWith_gluing_fixedPt hg hgε hk hkε hr₀ hK hw, ?_, hwnorm,
    fun r hr ↦ (hw r hr).2, ?_⟩
  · have h := (hw 0 (left_mem_Icc.2 hr₀0)).2
    simp only [zero_smul] at h
    exact h.symm
  · ext z
    constructor
    · rintro ⟨hsrc, hzr₀, hzg, hzk⟩
      exact toLp_mem_image_of_mem_graph hg hgε hk hkε hε hK hw hsrc hzr₀ hzg hzk
    · -- Conversely, the point with gluing parameter `r` exits the box at `(r • g (r • w r), w r)`,
      -- which lies on the graph of `k` because `w r` is a fixed point.
      rintro ⟨r, hr, rfl⟩
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


/-! ### Families of discs -/

/-- A fixed point `v` of the gluing map `F w = k (r • g (r • w))` in the closed ball of radius `ε`
is within `dist (F v') v' / (1 - Kk * Kg * r₀ ^ 2)` of every `v'` of that ball, since `F` contracts
the ball with constant `Kk * Kg * r₀ ^ 2`. -/
private theorem dist_le_of_isFixedPt_gluing (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε) (hK : Kk * Kg * r₀ ^ 2 < 1) {r : ℝ}
    (hr : r ∈ Icc 0 r₀) {v v' : Eᵤ} (hv : v ∈ closedBall 0 ε) (hv' : v' ∈ closedBall 0 ε)
    (hfix : k (r • g (r • v)) = v) :
    dist v v' ≤ dist (k (r • g (r • v'))) v' / (1 - Kk * Kg * r₀ ^ 2) := by
  have h := (contractingWith_gluing hg hgε hk hK hr (mapsTo_gluing hgε hkε hr))
    |>.dist_le_of_fixedPoint ⟨v', hv'⟩ (y := ⟨v, hv⟩) (Subtype.ext hfix)
  rw [Subtype.dist_eq, Subtype.dist_eq, coe_mul_mul_toNNReal_sq (hr.1.trans hr.2)] at h
  simpa only [dist_comm, MapsTo.val_restrict_apply] using h

/-- For families of discs `g p` and `k p`, Lipschitz with uniform constants and continuous in the
parameter `p ∈ S`, the value of the gluing map `w ↦ k p (r • g p (r • w))` at a fixed `v` depends
continuously on the gluing parameter `r` and on `p` jointly. -/
private theorem continuousOn_gluing_family {P : Type*} [TopologicalSpace P] {S : Set P}
    {g : P → Eᵤ → Eₛ} {k : P → Eₛ → Eᵤ}
    (hg : ∀ p ∈ S, LipschitzOnWith Kg (g p) (closedBall 0 (r₀ * ε)))
    (hgε : ∀ p ∈ S, ∀ y ∈ closedBall 0 (r₀ * ε), ‖g p y‖ = ε)
    (hk : ∀ p ∈ S, LipschitzOnWith Kk (k p) (closedBall 0 (r₀ * ε)))
    (hgc : ∀ y ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ g p y) S)
    (hkc : ∀ x ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ k p x) S) {v : Eᵤ}
    (hv : ‖v‖ ≤ ε) :
    ContinuousOn (fun q : ℝ × P ↦ k q.2 (q.1 • g q.2 (q.1 • v))) (Icc 0 r₀ ×ˢ S) := by
  -- Uniformly Lipschitz families that are continuous in the parameter are jointly continuous.
  have hG : ContinuousOn (fun q : P × Eᵤ ↦ g q.1 q.2) (S ×ˢ closedBall 0 (r₀ * ε)) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith' _ Kg hg hgc
  have hH : ContinuousOn (fun q : P × Eₛ ↦ k q.1 q.2) (S ×ˢ closedBall 0 (r₀ * ε)) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith' _ Kk hk hkc
  have hin : ContinuousOn (fun q : ℝ × P ↦ g q.2 (q.1 • v)) (Icc 0 r₀ ×ˢ S) :=
    hG.comp (continuousOn_snd.prodMk (continuousOn_fst.smul continuousOn_const))
      fun q hq ↦ ⟨hq.2, smul_mem_closedBall_mul hq.1 hv⟩
  exact hH.comp (continuousOn_snd.prodMk (continuousOn_fst.smul hin)) fun q hq ↦
    ⟨hq.2, smul_mem_closedBall_mul hq.1 (hgε _ hq.2 _ (smul_mem_closedBall_mul hq.1 hv)).le⟩

/-- **Gluing families of transverse discs through the split hyperbolic box.** Let
`y ↦ (g p y, y)` and `x ↦ (x, k p x)`, for `p` in a set `S` of a topological space, be families of
discs in the entrance and exit faces satisfying the hypotheses of
`TauCeti.exists_setOf_mem_splitPassage_source_graph_eq_image` with uniform constants, and depending
continuously on `p` at every point of their domains. Then the gluing parametrizations of that
theorem can be chosen to depend continuously on the gluing parameter `r` and on `p` jointly: there
is `w` with `(r, p) ↦ w r p` continuous on `[0, r₀] × S`, such that for each `p ∈ S` the map
`r ↦ w r p` has all the properties of the parametrization of the single discs `g p` and `k p`.

In the gluing of broken trajectories `p` ranges over pairs of a trajectory into the middle
critical point and a trajectory out of it: the trace of the unstable manifold of the starting
critical point on the entrance face is a family of graphs over the expanding factor, `g p`
depending on the first trajectory, and likewise on the exit face, `k p` depending on the second.
The points `(g p (r • w r p), r • w r p)` then sweep out all orbits running from the first family
to the second, continuously in `(r, p)`. -/
theorem exists_continuousOn_and_forall_setOf_mem_splitPassage_source_graph_eq_image
    [CompleteSpace Eᵤ] {P : Type*} [TopologicalSpace P] {S : Set P}
    {g : P → Eᵤ → Eₛ} {k : P → Eₛ → Eᵤ}
    (hg : ∀ p ∈ S, LipschitzOnWith Kg (g p) (closedBall 0 (r₀ * ε)))
    (hgε : ∀ p ∈ S, ∀ y ∈ closedBall 0 (r₀ * ε), ‖g p y‖ = ε)
    (hk : ∀ p ∈ S, LipschitzOnWith Kk (k p) (closedBall 0 (r₀ * ε)))
    (hkε : ∀ p ∈ S, ∀ x ∈ closedBall 0 (r₀ * ε), ‖k p x‖ = ε)
    (hgc : ∀ y ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ g p y) S)
    (hkc : ∀ x ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ k p x) S)
    (hε : 0 < ε) (hr₀ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1) :
    ∃ w : ℝ → P → Eᵤ, ContinuousOn (fun q : ℝ × P ↦ w q.1 q.2) (Icc 0 r₀ ×ˢ S) ∧
      ∀ p ∈ S, LipschitzOnWith (Kk * ((1 + Kg) * ε) / (1 - Kk * Kg * r₀ ^ 2)).toNNReal
          (fun r ↦ w r p) (Icc 0 r₀) ∧ w 0 p = k p 0 ∧ (∀ r ∈ Icc 0 r₀, ‖w r p‖ = ε) ∧
        (∀ r ∈ Icc 0 r₀, k p (r • g p (r • w r p)) = w r p) ∧
        {z | z ∈ (splitPassage ε).source ∧ ‖z.snd‖ ≤ r₀ * ε ∧ z.fst = g p z.snd ∧
            (splitPassage ε z).snd = k p (splitPassage ε z).fst} =
          (fun r ↦ WithLp.toLp 2 (g p (r • w r p), r • w r p)) '' Ioc 0 r₀ := by
  -- Choose the parametrization of each pair of discs separately.
  have hex (p : P) : ∃ w : ℝ → Eᵤ, p ∈ S →
      LipschitzOnWith (Kk * ((1 + Kg) * ε) / (1 - Kk * Kg * r₀ ^ 2)).toNNReal w (Icc 0 r₀) ∧
        w 0 = k p 0 ∧ (∀ r ∈ Icc 0 r₀, ‖w r‖ = ε) ∧
        (∀ r ∈ Icc 0 r₀, k p (r • g p (r • w r)) = w r) ∧
        {z | z ∈ (splitPassage ε).source ∧ ‖z.snd‖ ≤ r₀ * ε ∧ z.fst = g p z.snd ∧
            (splitPassage ε z).snd = k p (splitPassage ε z).fst} =
          (fun r ↦ WithLp.toLp 2 (g p (r • w r), r • w r)) '' Ioc 0 r₀ := by
    by_cases hp : p ∈ S
    · obtain ⟨w, hw⟩ := exists_setOf_mem_splitPassage_source_graph_eq_image (hg p hp)
        (hgε p hp) (hk p hp) (hkε p hp) hε hr₀ hK
      exact ⟨w, fun _ ↦ hw⟩
    · exact ⟨0, fun h ↦ absurd h hp⟩
  choose w hw using hex
  refine ⟨fun r p ↦ w p r, ?_, fun p hp ↦ hw p hp⟩
  -- Joint continuity: the fixed point `w p r` is within a constant times
  -- `dist (F_{r, p} v') v'` of the fixed point `v'` at `(r', p')`, and `F_{r, p} v' → v'`.
  rintro ⟨r', p'⟩ ⟨hr', hp'⟩
  obtain ⟨-, -, hnorm', hfix', -⟩ := hw p' hp'
  have hv' : ‖w p' r'‖ ≤ ε := (hnorm' r' hr').le
  have hF := (continuousOn_gluing_family hg hgε hk hgc hkc hv' (r', p') ⟨hr', hp'⟩).tendsto
  simp only [hfix' r' hr'] at hF
  have hlim : Tendsto (fun q : ℝ × P ↦ dist (k q.2 (q.1 • g q.2 (q.1 • w p' r'))) (w p' r') /
      (1 - Kk * Kg * r₀ ^ 2)) (𝓝[Icc 0 r₀ ×ˢ S] (r', p')) (𝓝 0) := by
    simpa using (tendsto_iff_dist_tendsto_zero.1 hF).div_const (1 - Kk * Kg * r₀ ^ 2)
  refine tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hlim)
  filter_upwards [self_mem_nhdsWithin] with q hq
  obtain ⟨-, -, hnorm, hfix, -⟩ := hw q.2 hq.2
  exact dist_le_of_isFixedPt_gluing (hg _ hq.2) (hgε _ hq.2) (hk _ hq.2) (hkε _ hq.2) hK hq.1
    (mem_closedBall_zero_iff.2 (hnorm _ hq.1).le) (mem_closedBall_zero_iff.2 hv') (hfix _ hq.1)

end TauCeti
