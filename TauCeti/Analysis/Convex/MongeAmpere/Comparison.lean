/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Basic
public import TauCeti.Analysis.Convex.Extrema
import TauCeti.Analysis.Convex.FunctionTopology
import TauCeti.Analysis.Convex.MongeAmpere.Affine
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.Frontier

/-!
# The comparison principle for the Monge–Ampère equation

Let `Ω` be a bounded open convex subset of a finite-dimensional real inner product space `E`,
and let `u` and `v` be convex on `Ω` and continuous on its closure, with Aleksandrov
Monge–Ampère measures `MA_u` and `MA_v` (of `u` and `v` extended by `⊤` off `Ω`).

* If `u ≤ v` on `Ω` and `v ≤ u` on the frontier of `Ω`, then every subgradient of `v` relative
  to `Ω` is a subgradient of `u` relative to `Ω`, so `MA_v(Ω) ≤ MA_u(Ω)`: the lower function
  carries more Monge–Ampère mass.
* **The comparison principle.** If `MA_u ≤ MA_v` and `v ≤ u` on the frontier of `Ω`, then
  `v ≤ u` on `Ω`. Hence a convex function on `Ω`, continuous on the closure, is determined by
  its Monge–Ampère measure and its boundary values; this is the uniqueness half of the
  Dirichlet problem for the Monge–Ampère equation.

The comparison principle is proved by contradiction. If `u x₀ < v x₀`, then for small `ε > 0`
the function `w = (1 + ε) v - c` lies above `u` at `x₀` and strictly below `u` on the frontier,
so the open set `G = {u < w}` has closure inside `Ω`, and `w ≤ u` on its frontier. By
`TauCeti.exists_forall_add_inner_add_le_of_forall_frontier_le`, the subgradients of `w` on `G`,
are subgradients of `u` on `G`, as are their small perturbations, which form an open ball.
The scaling law gives `MA_w(G) = (1 + ε)^n MA_v(G)`. Comparing measures,
`(1 + ε) ^ n MA_v(G) ≤ MA_u(G) ≤ MA_v(G)` with `0 < MA_u(G)` and `MA_v(G) < ∞`, which is
impossible.

## Main statements

* `TauCeti.mongeAmpereMeasure_le_of_le_of_le_frontier` — a convex function lying below
  another, with the reverse inequality on the frontier, has larger Monge–Ampère mass;
* `TauCeti.le_of_mongeAmpereMeasure_le_of_le_frontier` — **the comparison principle**;
* `TauCeti.eqOn_of_mongeAmpereMeasure_eq_of_eqOn_frontier` — two convex functions with the same
  Monge–Ampère measure and the same boundary values agree.
* `TauCeti.abs_sub_le_of_smul_le_mongeAmpereMeasure_le_smul` — two-sided measure bounds give a
  quantitative comparison with a zero-boundary reference.

## References

* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.4.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, Chapter 2.
* G. De Philippis and A. Figalli, [The Monge–Ampère equation and its link to optimal
  transportation](https://arxiv.org/abs/1310.6167v1), §2.4, the perturbation argument.
* The density bracketing follows the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/9cde7938fc09cd017519c7c8a498bee99c12f717/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov/Comparison.lean#L404).
-/

public section

namespace TauCeti

open MeasureTheory Measure Set Filter Metric Module

open scoped Topology ENNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Set E} [DecidablePred (· ∈ Ω)] {u v : E → ℝ}

/-- **A lower convex function with the reverse boundary inequality has more Monge–Ampère mass.**
Let `Ω` be a bounded open set, and let `u` and `v` be convex on `Ω` and continuous on its
closure, with `u ≤ v` on `Ω` and `v ≤ u` on the frontier of `Ω`. Then `MA_v(Ω) ≤ MA_u(Ω)` for
the Monge–Ampère measures of `u` and `v` (extended by `⊤` off `Ω`) with respect to any measure
`μ` absolutely continuous with respect to an additive Haar measure. -/
theorem mongeAmpereMeasure_le_of_le_of_le_frontier (μ : Measure E) {ν : Measure E}
    [ν.IsAddHaarMeasure] (hμ : μ ≪ ν) (hΩo : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
    (hu : ConvexOn ℝ Ω u) (hv : ConvexOn ℝ Ω v) (huc : ContinuousOn u (closure Ω))
    (hvc : ContinuousOn v (closure Ω)) (hle : ∀ x ∈ Ω, u x ≤ v x)
    (hfr : ∀ x ∈ frontier Ω, v x ≤ u x) :
    mongeAmpereMeasure μ (fun x => if x ∈ Ω then (v x : EReal) else ⊤) Ω ≤
      mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) Ω := by
  rw [mongeAmpereMeasure_ite_apply μ hΩo hv hμ hΩo.measurableSet,
    mongeAmpereMeasure_ite_apply μ hΩo hu hμ hΩo.measurableSet]
  refine measure_mono (iUnion₂_subset fun x hx p hp => ?_)
  obtain ⟨x₁, hx₁, h⟩ := exists_forall_add_inner_add_le_of_forall_frontier_le (q := 0)
    hΩ.isCompact_closure huc hvc
    hfr hx.1 hp (by simpa using hle x hx.1)
  exact mem_biUnion ⟨hx₁, hx₁⟩ (by simpa using h)

omit [MeasurableSpace E] [BorelSpace E] [DecidablePred (· ∈ Ω)] in
/-- Let `u` be convex on `Ω`, and let `G ⊆ Ω` be a bounded open set on whose closure `u` and `w`
are continuous, with `w ≤ u` on the frontier of `G`. If `p` is a subgradient of `w` relative to
`G` at `y ∈ G` and `‖q‖ * diam G ≤ w y - u y`, then `p + q` is a subgradient of `u` relative to
`Ω` at some point of `G`. -/
private theorem add_mem_biUnion_of_forall_frontier_le (hu : ConvexOn ℝ Ω u) {w : E → ℝ}
    {G : Set E} (hGo : IsOpen G) (hGΩ : G ⊆ Ω) (hGb : Bornology.IsBounded G)
    (huc : ContinuousOn u (closure G)) (hwc : ContinuousOn w (closure G))
    (hfr : ∀ y ∈ frontier G, w y ≤ u y) {y : E} (hy : y ∈ G) {p q : E}
    (hp : ∀ x ∈ G, w y + inner ℝ (x - y) p ≤ w x) (hq : ‖q‖ * diam G ≤ w y - u y) :
    p + q ∈ ⋃ x ∈ G ∩ Ω, {z | ∀ x' ∈ Ω, u x + inner ℝ (x' - x) z ≤ u x'} := by
  obtain ⟨x₁, hx₁, h⟩ :=
    exists_forall_add_inner_add_le_of_forall_frontier_le hGb.isCompact_closure huc hwc hfr hy hp hq
  -- A subgradient relative to the open neighbourhood `G` of `x₁` is one relative to `Ω`.
  have h' := hu.add_le_of_eventually_add_le (hGΩ hx₁) ((innerₗ E).flip (p + q)) (by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hGo.mem_nhds hx₁)] with x' hx'
    simpa only [LinearMap.flip_apply, innerₗ_apply_apply] using h x' hx')
  exact mem_biUnion ⟨hx₁, hGΩ hx₁⟩ fun x' hx' => by
    simpa only [LinearMap.flip_apply, innerₗ_apply_apply] using h' x' hx'

omit [DecidablePred (· ∈ Ω)] in
/-- A convex function on an open set `Ω` has a subgradient relative to `Ω` at some point of every
nonempty open subset `G` of `Ω`: by Rademacher's theorem it is differentiable at some point of
`G`, and its gradient there is a subgradient. -/
private theorem exists_mem_forall_add_inner_le (hv : ConvexOn ℝ Ω v) {G : Set E} (hGo : IsOpen G)
    (hGΩ : G ⊆ Ω) (hG : G.Nonempty) :
    ∃ x ∈ G, ∃ p, ∀ x' ∈ Ω, v x + inner ℝ (x' - x) p ≤ v x' := by
  classical
  have hae := ae_eventually_ne_top_and_differentiableAt_toReal (μ := addHaar)
    (convex_epigraph_ite hv) ite_ne_bot
  have : (ae (addHaar.restrict G)).NeBot := ae_restrict_neBot.2 (hGo.measure_ne_zero _ hG)
  have hae' : ∀ᵐ y ∂addHaar.restrict G, y ∈ G ∧
      DifferentiableAt ℝ (fun x' => (if x' ∈ Ω then (v x' : EReal) else ⊤).toReal) y := by
    filter_upwards [ae_restrict_mem hGo.measurableSet, ae_restrict_of_ae hae] with y hyG h
    exact ⟨hyG, (h (by simp [hGΩ hyG])).2⟩
  obtain ⟨x, hx, hd⟩ := hae'.exists
  have hp := (mem_subdifferential_ite_iff (innerₗ E) (hGΩ hx)).1
    (gradient_toReal_mem_subdifferential (convex_epigraph_ite hv) ite_ne_bot (by simp [hGΩ hx]) hd)
  exact ⟨x, hx, _, by simpa only [innerₗ_apply_apply] using hp⟩

variable [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [Nontrivial E] in
/-- Let `w ≤ u` on the frontier of a bounded open subset `G` of `Ω` on which `u < w`, with `u`, `w`
convex on `Ω` and continuous on its closure. Then the subgradient images of `u` and `w` over `G`
(whose measures are the Monge–Ampère measures of `G`) satisfy `S_w ⊆ S_u`, and `S_u` contains a
ball. -/
private theorem exists_measure_eq_subset_ball (hΩo : IsOpen Ω) (hu : ConvexOn ℝ Ω u) {w : E → ℝ}
    (hwconv : ConvexOn ℝ Ω w) (huc : ContinuousOn u (closure Ω)) (hwc : ContinuousOn w (closure Ω))
    {G : Set E} (hGo : IsOpen G) (hGΩ : G ⊆ Ω) (hGb : Bornology.IsBounded G)
    (hfrG : ∀ y ∈ frontier G, w y ≤ u y) (hpos : ∀ y ∈ G, 0 < w y - u y) (hG : G.Nonempty) :
    ∃ Su Sw : Set E,
      mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) G = μ Su ∧
      mongeAmpereMeasure μ (fun x => if x ∈ Ω then (w x : EReal) else ⊤) G = μ Sw ∧
      Sw ⊆ Su ∧ ∃ c, ∃ η > 0, ball c η ⊆ Su := by
  -- The subgradients of `w` on `G` and their small perturbations belong to the image for `u`.
  set Su := ⋃ y ∈ G ∩ Ω, {p | ∀ x' ∈ Ω, u y + inner ℝ (x' - y) p ≤ u x'}
  set Sw := ⋃ y ∈ G ∩ Ω, {p | ∀ x' ∈ Ω, w y + inner ℝ (x' - y) p ≤ w x'}
  have key : ∀ y ∈ G, ∀ p, (∀ x' ∈ Ω, w y + inner ℝ (x' - y) p ≤ w x') →
      ∀ q : E, ‖q‖ * diam G ≤ w y - u y → p + q ∈ Su := fun y hy p hp q hq =>
    add_mem_biUnion_of_forall_frontier_le hu hGo hGΩ hGb (huc.mono (closure_mono hGΩ))
      (hwc.mono (closure_mono hGΩ)) hfrG hy (fun x' hx' => hp x' (hGΩ hx')) hq
  have hsub : Sw ⊆ Su := by
    intro p hp
    obtain ⟨y, hy, hp⟩ := mem_iUnion₂.1 hp
    simpa using key y hy.1 p hp 0 (by simpa using (hpos y hy.1).le)
  -- A subgradient of `w` at some point of `G` gives a ball of subgradients of `u`.
  have hball : ∃ c, ∃ η > 0, ball c η ⊆ Su := by
    obtain ⟨x₁, hx₁, p₁, hp₁⟩ := exists_mem_forall_add_inner_le hwconv hGo hGΩ hG
    have hκ : 0 < w x₁ - u x₁ := hpos x₁ hx₁
    refine ⟨p₁, (w x₁ - u x₁) / (diam G + 1), by positivity, fun z hz => ?_⟩
    have hz' : ‖z - p₁‖ * diam G ≤ w x₁ - u x₁ := by
      rw [mem_ball, dist_eq_norm] at hz
      calc ‖z - p₁‖ * diam G ≤ (w x₁ - u x₁) / (diam G + 1) * (diam G + 1) :=
            mul_le_mul hz.le (by linarith) diam_nonneg (by positivity)
        _ = w x₁ - u x₁ := div_mul_cancel₀ _ (by positivity)
    simpa using key x₁ hx₁ _ hp₁ _ hz'
  exact ⟨Su, Sw, mongeAmpereMeasure_ite_apply μ hΩo hu AbsolutelyContinuous.rfl hGo.measurableSet,
    mongeAmpereMeasure_ite_apply μ hΩo hwconv AbsolutelyContinuous.rfl hGo.measurableSet,
    hsub, hball⟩

/-- **The comparison principle for the Monge–Ampère equation.** Let `Ω` be a bounded open subset
of a real inner product space `E` of finite dimension `n ≥ 1`, and let `u` and `v` be convex on
`Ω` and continuous on its closure. If `MA_u ≤ MA_v` for their Aleksandrov Monge–Ampère measures
(of `u` and `v` extended by `⊤` off `Ω`, with respect to an additive Haar measure `μ`) and
`v ≤ u` on the frontier of `Ω`, then `v ≤ u` on `Ω`. -/
theorem le_of_mongeAmpereMeasure_le_of_le_frontier (hΩo : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) (hu : ConvexOn ℝ Ω u) (hv : ConvexOn ℝ Ω v)
    (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v (closure Ω))
    (hMA : mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) ≤
      mongeAmpereMeasure μ (fun x => if x ∈ Ω then (v x : EReal) else ⊤))
    (hfr : ∀ x ∈ frontier Ω, v x ≤ u x) {x₀ : E} (hx₀ : x₀ ∈ Ω) : v x₀ ≤ u x₀ := by
  by_contra! hlt
  -- Replace `v` by `w = (1 + ε) v + b`: then `u < w` at `x₀` and `w < u` on the frontier of `Ω`.
  obtain ⟨ε, hε, b, hwc, hwconv, hfrw, hx₀w⟩ :=
    exists_convexOn_lt_frontier_of_lt hΩ hv hvc hfr hx₀ hlt
  set w : E → ℝ := fun y => (1 + ε) * v y + b with hw
  -- The open set `G = {u < w}` contains `x₀`, and `w ≤ u` on its frontier.
  obtain ⟨G, hGo, hGΩ, hGc, hx₀G, hpos, hfrG⟩ :=
    exists_isOpen_subset_pos_forall_frontier_le hΩo huc hwc hfrw hx₀ hx₀w
  have hGb : Bornology.IsBounded G := hΩ.subset hGΩ
  obtain ⟨Su, Sw, hSu, hSw, hsub, hball⟩ := exists_measure_eq_subset_ball μ hΩo hu hwconv huc hwc
    hGo hGΩ hGb hfrG hpos ⟨x₀, hx₀G⟩
  -- Compare `(1 + ε) ^ n MA_v(G) ≤ MA_u(G) ≤ MA_v(G)` with `0 < MA_u(G)` and `MA_v(G) < ∞`.
  have hεpos : 0 < 1 + ε := by positivity
  refine false_of_subset_of_ball_subset μ ?_ hMA
    (mongeAmpereMeasure_ite_mul_add_of_pos μ hεpos b) hSu hSw hsub hball ?_
  · rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact one_lt_pow₀ (by linarith) finrank_pos.ne'
  · refine ((measure_mono subset_closure).trans_lt ?_).ne
    refine mongeAmpereMeasure_lt_top μ (convex_epigraph_ite hv) ite_ne_bot
      AbsolutelyContinuous.rfl hGb.isCompact_closure ?_
    rwa [setOf_ite_ne_top, hΩo.interior_eq]

/-- **Uniqueness for the Dirichlet problem for the Monge–Ampère equation.** Let `Ω` be a bounded
open subset of a real inner product space of finite dimension `n ≥ 1`, and let `u` and `v` be
convex on `Ω` and continuous on its closure. If `u` and `v` have the same Aleksandrov
Monge–Ampère measure (extended by `⊤` off `Ω`, with respect to an additive Haar measure `μ`) and
agree on the frontier of `Ω`, then they agree on `Ω`. -/
theorem eqOn_of_mongeAmpereMeasure_eq_of_eqOn_frontier (hΩo : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) (hu : ConvexOn ℝ Ω u) (hv : ConvexOn ℝ Ω v)
    (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v (closure Ω))
    (hMA : mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) =
      mongeAmpereMeasure μ (fun x => if x ∈ Ω then (v x : EReal) else ⊤))
    (hfr : EqOn u v (frontier Ω)) : EqOn u v Ω := fun _ hx =>
  le_antisymm
    (le_of_mongeAmpereMeasure_le_of_le_frontier μ hΩo hΩ hv hu hvc huc hMA.ge
      (fun _ hy => (hfr hy).le) hx)
    (le_of_mongeAmpereMeasure_le_of_le_frontier μ hΩo hΩ hu hv huc hvc hMA.le
      (fun _ hy => (hfr hy).ge) hx)

/-- **Quantitative comparison.** On a bounded open set, suppose the convex potentials `u`
and `v` are continuous on the closure and vanish on the frontier. If the Monge–Ampère
measure of `v` is `ν` and that of `u` lies between `(1 - ε)^n • ν` and `(1 + ε)^n • ν`
for `0 ≤ ε < 1`, then `|u - v| ≤ ε |v|` pointwise. -/
theorem abs_sub_le_of_smul_le_mongeAmpereMeasure_le_smul
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hu : ConvexOn ℝ Ω u) (hv : ConvexOn ℝ Ω v)
    (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v (closure Ω))
    (hu0 : ∀ x ∈ frontier Ω, u x = 0) (hv0 : ∀ x ∈ frontier Ω, v x = 0)
    {ν : Measure E} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hlo : ENNReal.ofReal ((1 - ε) ^ finrank ℝ E) • ν ≤
      mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤))
    (hhi : mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) ≤
      ENNReal.ofReal ((1 + ε) ^ finrank ℝ E) • ν)
    (href : mongeAmpereMeasure μ (fun x => if x ∈ Ω then (v x : EReal) else ⊤) = ν) :
    ∀ x ∈ Ω, |u x - v x| ≤ ε * |v x| := by
  have hscaled (c : ℝ) (hc : 0 < c) :
      mongeAmpereMeasure μ (fun x => if x ∈ Ω then ((c * v x : ℝ) : EReal) else ⊤) =
        ENNReal.ofReal (c ^ finrank ℝ E) • ν := by
    rw [mongeAmpereMeasure_ite_mul_of_pos μ hc, href]
  have hconv (c : ℝ) (hc : 0 ≤ c) : ConvexOn ℝ Ω (fun x => c * v x) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hv.smul hc
  have hfront (c : ℝ) (x : E) (hx : x ∈ frontier Ω) : c * v x = u x := by
    rw [hu0 x hx, hv0 x hx, mul_zero]
  intro x hx
  have hl : (1 + ε) * v x ≤ u x :=
    le_of_mongeAmpereMeasure_le_of_le_frontier μ hΩ hΩb hu
      (hconv (1 + ε) (by positivity)) huc (continuousOn_const.mul hvc)
      (by simpa only [hscaled (1 + ε) (by positivity)] using hhi)
      (fun y hy => (hfront _ y hy).le) hx
  have hh : u x ≤ (1 - ε) * v x :=
    le_of_mongeAmpereMeasure_le_of_le_frontier μ hΩ hΩb
      (hconv (1 - ε) (sub_nonneg.mpr hε1.le)) hu (continuousOn_const.mul hvc) huc
      (by simpa only [hscaled (1 - ε) (sub_pos.mpr hε1)] using hlo)
      (fun y hy => (hfront _ y hy).ge) hx
  have hbound := mul_le_mul_of_nonneg_left (neg_abs_le (v x)) hε
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TauCeti
