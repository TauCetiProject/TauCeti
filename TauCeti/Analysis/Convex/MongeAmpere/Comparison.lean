/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Basic
public import TauCeti.Analysis.Convex.Extrema

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
which are the `(1 + ε)`-multiples of those of `v`, are subgradients of `u` on `G`; so are their
small perturbations, which form an open ball. Comparing measures,
`(1 + ε) ^ n MA_v(G) ≤ MA_u(G) ≤ MA_v(G)` with `0 < MA_u(G)` and `MA_v(G) < ∞`, which is
impossible.

## Main statements

* `TauCeti.mongeAmpereMeasure_le_of_le_of_le_frontier` — a convex function lying below
  another with the same boundary values has larger Monge–Ampère mass;
* `TauCeti.le_of_mongeAmpereMeasure_le_of_le_frontier` — **the comparison principle**;
* `TauCeti.eqOn_of_mongeAmpereMeasure_eq_of_eqOn_frontier` — two convex functions with the same
  Monge–Ampère measure and the same boundary values agree.

## References

* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.4.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, Chapter 2.
-/

public section

namespace TauCeti

open MeasureTheory Measure Set Filter Metric Module

open scoped Topology ENNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Set E} [DecidablePred (· ∈ Ω)] {u v : E → ℝ}

/-- **A lower convex function with the same boundary values has more Monge–Ampère mass.** Let
`Ω` be a bounded open set, and let `u` and `v` be convex on `Ω` and continuous on its closure,
with `u ≤ v` on `Ω` and `v ≤ u` on the frontier of `Ω`. Then `MA_v(Ω) ≤ MA_u(Ω)` for the
Monge–Ampère measures of `u` and `v` (extended by `⊤` off `Ω`) with respect to any measure `μ`
absolutely continuous with respect to an additive Haar measure. -/
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
  obtain ⟨x₁, hx₁, h⟩ := exists_forall_add_inner_add_le_of_forall_frontier_le (q := 0) hΩ huc hvc
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
    exists_forall_add_inner_add_le_of_forall_frontier_le hGb huc hwc hfr hy hp hq
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
  -- Choose `ε > 0` with `ε |v| ≤ a / 4` on the closure of `Ω`, where `a = v x₀ - u x₀ > 0`, and
  -- set `w = (1 + ε) v - a / 2`. Then `u < w` at `x₀` and `w < u` on the frontier of `Ω`.
  set a := v x₀ - u x₀
  have ha : 0 < a := sub_pos.2 hlt
  obtain ⟨M, hM⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hvc
  set ε := a / (4 * (|M| + 1))
  have hε : 0 < ε := by positivity
  have hεv : ∀ y ∈ closure Ω, |ε * v y| ≤ a / 4 := fun y hy => by
    rw [abs_mul, abs_of_pos hε]
    calc ε * |v y| ≤ ε * (|M| + 1) := by
          gcongr
          exact (hM y hy).trans ((le_abs_self M).trans (le_add_of_nonneg_right zero_le_one))
      _ = a / 4 := by
          simp only [ε]
          field_simp
  set w : E → ℝ := fun y => (1 + ε) * v y - a / 2 with hw
  have hwc : ContinuousOn w (closure Ω) := (continuousOn_const.mul hvc).sub continuousOn_const
  have hfrw : ∀ y ∈ frontier Ω, w y < u y := fun y hy => by
    have := (abs_le.1 (hεv y (frontier_subset_closure hy))).2
    simp only [hw]
    linarith [hfr y hy]
  -- The open set `G = {u < w}` contains `x₀`, its closure lies in `Ω`, and `w ≤ u` on its
  -- frontier.
  set G := Ω ∩ (fun y => w y - u y) ⁻¹' Ioi 0
  have hGo : IsOpen G := ((hwc.sub huc).mono subset_closure).isOpen_inter_preimage hΩo isOpen_Ioi
  have hGΩ : G ⊆ Ω := inter_subset_left
  have hx₀G : x₀ ∈ G := by
    refine ⟨hx₀, ?_⟩
    have := (abs_le.1 (hεv x₀ (subset_closure hx₀))).1
    simp only [mem_preimage, mem_Ioi, hw]
    linarith
  have hGc : closure G ⊆ Ω := by
    have hT : closure G ⊆ closure Ω ∩ (fun y => w y - u y) ⁻¹' Ici 0 :=
      closure_minimal (fun y hy => ⟨subset_closure hy.1, le_of_lt hy.2⟩)
        ((hwc.sub huc).preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici)
    intro y hy
    obtain ⟨hy₁, hy₂⟩ := hT hy
    by_contra hyΩ
    have := hfrw y (by rw [hΩo.frontier_eq]; exact ⟨hy₁, hyΩ⟩)
    simp only [mem_preimage, mem_Ici] at hy₂
    linarith
  have hfrG : ∀ y ∈ frontier G, w y ≤ u y := fun y hy => by
    rw [hGo.frontier_eq] at hy
    have : ¬0 < w y - u y := fun h => hy.2 ⟨hGc hy.1, h⟩
    linarith [not_lt.1 this]
  have hGb : Bornology.IsBounded G := hΩ.subset hGΩ
  -- The `(1 + ε)`-multiples of the subgradients of `v` at points of `G`, and their perturbations
  -- by `q` with `‖q‖ * diam G ≤ w - u`, are subgradients of `u` at points of `G`.
  set Su := ⋃ y ∈ G ∩ Ω, {p | ∀ x' ∈ Ω, u y + inner ℝ (x' - y) p ≤ u x'}
  set Sv := ⋃ y ∈ G ∩ Ω, {p | ∀ x' ∈ Ω, v y + inner ℝ (x' - y) p ≤ v x'}
  have key : ∀ y ∈ G, ∀ p, (∀ x' ∈ Ω, v y + inner ℝ (x' - y) p ≤ v x') →
      ∀ q : E, ‖q‖ * diam G ≤ w y - u y → (1 + ε) • p + q ∈ Su := fun y hy p hp q hq =>
    add_mem_biUnion_of_forall_frontier_le hu hGo hGΩ hGb (huc.mono (closure_mono hGΩ))
      (hwc.mono (closure_mono hGΩ)) hfrG hy (fun x' hx' => by
        have := mul_le_mul_of_nonneg_left (hp x' (hGΩ hx')) (by positivity : (0 : ℝ) ≤ 1 + ε)
        simp only [hw, real_inner_smul_right]
        linarith) hq
  have hscale : (1 + ε) • Sv ⊆ Su := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨y, hy, hp⟩ := mem_iUnion₂.1 hp
    simpa using key y hy.1 p hp 0 (by simpa using hy.1.2.le)
  -- `v` has a subgradient `p₁` at some `x₁ ∈ G`, so a ball about `(1 + ε) • p₁` consists of
  -- subgradients of `u`, and `MA_u(G) > 0`.
  have hball : ∃ c, ∃ η > 0, ball c η ⊆ Su := by
    obtain ⟨x₁, hx₁, p₁, hp₁⟩ := exists_mem_forall_add_inner_le hv hGo hGΩ ⟨x₀, hx₀G⟩
    have hκ : 0 < w x₁ - u x₁ := hx₁.2
    refine ⟨(1 + ε) • p₁, (w x₁ - u x₁) / (diam G + 1), by positivity, fun z hz => ?_⟩
    have hz' : ‖z - (1 + ε) • p₁‖ * diam G ≤ w x₁ - u x₁ := by
      rw [mem_ball, dist_eq_norm] at hz
      calc ‖z - (1 + ε) • p₁‖ * diam G ≤ (w x₁ - u x₁) / (diam G + 1) * (diam G + 1) :=
            mul_le_mul hz.le (by linarith) diam_nonneg (by positivity)
        _ = w x₁ - u x₁ := div_mul_cancel₀ _ (by positivity)
    simpa using key x₁ hx₁ _ hp₁ _ hz'
  obtain ⟨c, η, hη, hcη⟩ := hball
  -- Compare `(1 + ε) ^ n MA_v(G) ≤ MA_u(G) ≤ MA_v(G)` with `0 < MA_u(G)` and `MA_v(G) < ∞`.
  have hSu : mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) G = μ Su :=
    mongeAmpereMeasure_ite_apply μ hΩo hu AbsolutelyContinuous.rfl hGo.measurableSet
  have hSv : mongeAmpereMeasure μ (fun x => if x ∈ Ω then (v x : EReal) else ⊤) G = μ Sv :=
    mongeAmpereMeasure_ite_apply μ hΩo hv AbsolutelyContinuous.rfl hGo.measurableSet
  have h₁ : ENNReal.ofReal |(1 + ε) ^ finrank ℝ E| * μ Sv ≤ μ Su := by
    rw [← addHaar_smul]
    exact measure_mono hscale
  have h₂ : μ Su ≤ μ Sv := hSu ▸ hSv ▸ Measure.le_iff'.1 hMA G
  have h₃ : 0 < μ Su := (measure_ball_pos μ c hη).trans_le (measure_mono hcη)
  have h₄ : μ Sv ≠ ∞ := by
    rw [← hSv]
    refine ((measure_mono subset_closure).trans_lt ?_).ne
    refine mongeAmpereMeasure_lt_top μ (convex_epigraph_ite hv) ite_ne_bot
      AbsolutelyContinuous.rfl hGb.isCompact_closure ?_
    rwa [setOf_ite_ne_top, hΩo.interior_eq]
  have h₅ : 1 < ENNReal.ofReal |(1 + ε) ^ finrank ℝ E| := by
    rw [abs_of_pos (by positivity), ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff
      (by positivity)]
    exact one_lt_pow₀ (by linarith) finrank_pos.ne'
  have := ENNReal.mul_lt_mul_left (h₃.trans_le h₂).ne' h₄ h₅
  rw [one_mul] at this
  exact (this.trans_le (h₁.trans h₂)).false

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

end TauCeti
