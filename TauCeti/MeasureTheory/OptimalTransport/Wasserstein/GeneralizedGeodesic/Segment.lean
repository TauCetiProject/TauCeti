/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.GeneralizedGeodesic.Stability

/-!
# Restricting and reparameterizing generalized geodesics

Let `γ` be a measure on `E × E × E`, read as the joint law of a triple `(x, y₀, y₁)`, and write
`y_t = (1 - t) • y₀ + t • y₁`. The *segment plan* `TauCeti.segmentPlan γ s r` is the law of
`(x, y_s, y_r)` under `γ`. Its generalized geodesic is that of `γ` run affinely from time `s` to
time `r`:

`generalizedGeodesic (segmentPlan γ s r) u = generalizedGeodesic γ ((1 - u) * s + u * r)`,

and its endpoint coupling has `(r - s) ^ 2` times the quadratic cost of that of `γ`, since
`y_s - y_r = (r - s) • (y₀ - y₁)`. Taking `s ≤ r` restricts a generalized geodesic to a
subinterval; taking `s = 1` and `r = 0` reverses it.

The substance is that this operation preserves generalized-geodesic plans. In a real inner
product space, let `γ` be a quadratic generalized-geodesic plan from `ν₀` to `ν₁` based at `μ`,
with finite second moments, and let `s ∈ [0, 1]`. Then the law of `(x, y_s)` under `γ` is an
optimal coupling of `μ` and `ν_s` (`TauCeti.IsGeneralizedGeodesicPlan.isOptimalCoupling_map`).
Indeed, the supports of the optimal couplings `(x, y₀)` and `(x, y₁)` are cyclically monotone,
and cyclical monotonicity for the quadratic cost is linear in the targets over a fixed family of
sources, so the closure of the set of pairs `(x, (1 - s) • y₀ + s • y₁)` is cyclically monotone
as well and carries the law of `(x, y_s)`. Cyclically monotone plans between laws with finite
second moments are optimal. No regularity of the base law `μ` is needed: when `μ` is absolutely
continuous the two plans are induced by gradients of convex functions and the statement is the
familiar convexity of Brenier potentials, but the cyclical-monotonicity argument does not use it.

Consequently, for `s, r ∈ [0, 1]`, the segment plan of a quadratic generalized-geodesic plan is a
generalized-geodesic plan from `ν_s` to `ν_r` based at `μ`
(`TauCeti.IsGeneralizedGeodesicPlan.segmentPlan`). An energy convex along every generalized
geodesic based at `μ` is therefore convex along every restriction and reparameterization of one,
with the remainder scaled by `(r - s) ^ 2`
(`TauCeti.ConvexAlongGeneralizedGeodesics.convexAlongGeneralizedGeodesicPlan_segmentPlan` and
`TauCeti.ConvexAlongGeneralizedGeodesics.apply_le_of_eq_generalizedGeodesic`).

## Main definitions

* `TauCeti.segmentPlan γ s r`: the law of `(x, y_s, y_r)` under `γ`.

## Main statements

* `TauCeti.generalizedGeodesic_segmentPlan`: the generalized geodesic of a segment plan is the
  affinely reparameterized generalized geodesic of the plan.
* `TauCeti.integral_norm_sub_sq_snd_segmentPlan`: the endpoint cost of a segment plan.
* `TauCeti.IsGeneralizedGeodesicPlan.isOptimalCoupling_map`: interpolating the targets of a
  quadratic generalized-geodesic plan gives an optimal coupling out of the base law.
* `TauCeti.IsGeneralizedGeodesicPlan.segmentPlan`: segment plans of quadratic
  generalized-geodesic plans are generalized-geodesic plans.
* `TauCeti.ConvexAlongGeneralizedGeodesics.apply_le_of_eq_generalizedGeodesic`: convexity along
  every generalized geodesic restricts to subintervals and reparameterizations.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §9.2, Definition 9.2.2 and Definition 9.2.4.
* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24, for cyclically
  monotone sets and sums of subdifferentials.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

section Segment

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]

/-- The *segment plan* of a measure `γ` on `E × E × E`, read as the joint law of `(x, y₀, y₁)`,
between the times `s` and `r`: the law under `γ` of `(x, y_s, y_r)`, where
`y_t = (1 - t) • y₀ + t • y₁`. Its generalized geodesic is that of `γ` run from time `s` to time
`r` (`TauCeti.generalizedGeodesic_segmentPlan`). -/
def segmentPlan (γ : Measure (E × E × E)) (s r : ℝ) : Measure (E × E × E) :=
  γ.map fun w ↦ (w.1, (1 - s) • w.2.1 + s • w.2.2, (1 - r) • w.2.1 + r • w.2.2)

/-- The segment plan is the pushforward of `γ` along `(x, y₀, y₁) ↦ (x, y_s, y_r)`. -/
theorem segmentPlan_def (γ : Measure (E × E × E)) (s r : ℝ) :
    segmentPlan γ s r =
      γ.map fun w ↦ (w.1, (1 - s) • w.2.1 + s • w.2.2, (1 - r) • w.2.1 + r • w.2.2) := by
  rw [segmentPlan]

/-- The segment plan over the whole time interval is the plan itself. -/
@[simp]
theorem segmentPlan_zero_one (γ : Measure (E × E × E)) : segmentPlan γ 0 1 = γ := by
  simp [segmentPlan_def]

variable [MeasurableAdd₂ E] [MeasurableConstSMul ℝ E]

/-- The segment plan of a probability measure is a probability measure. -/
instance isProbabilityMeasure_segmentPlan (γ : Measure (E × E × E)) [IsProbabilityMeasure γ]
    (s r : ℝ) : IsProbabilityMeasure (segmentPlan γ s r) := by
  rw [segmentPlan_def]
  infer_instance

/-- The generalized geodesic of the segment plan between times `s` and `r` is the generalized
geodesic of `γ`, reparameterized affinely so that it runs from time `s` to time `r`. -/
@[simp]
theorem generalizedGeodesic_segmentPlan (γ : Measure (E × E × E)) (s r t : ℝ) :
    generalizedGeodesic (segmentPlan γ s r) t = generalizedGeodesic γ ((1 - t) * s + t * r) := by
  rw [generalizedGeodesic_def, generalizedGeodesic_def, segmentPlan_def,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext w
  simp only [Function.comp_apply]
  module

/-- Segment plans compose: a segment of a segment plan is a segment plan of `γ`, between the
reparameterized times. -/
@[simp]
theorem segmentPlan_segmentPlan (γ : Measure (E × E × E)) (s r s' r' : ℝ) :
    segmentPlan (segmentPlan γ s r) s' r' =
      segmentPlan γ ((1 - s') * s + s' * r) ((1 - r') * s + r' * r) := by
  rw [segmentPlan_def, segmentPlan_def, segmentPlan_def,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext w
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  constructor <;> module

/-- The first coordinate of a segment plan has the same law as under `γ`. -/
@[simp]
theorem fst_segmentPlan (γ : Measure (E × E × E)) (s r : ℝ) : (segmentPlan γ s r).fst = γ.fst := by
  rw [segmentPlan_def, Measure.fst, Measure.fst, Measure.map_map measurable_fst (by fun_prop)]
  rfl

/-- The projection of a segment plan to its first two coordinates is the law of `(x, y_s)` under
`γ`. -/
theorem map_prodMap_fst_segmentPlan (γ : Measure (E × E × E)) (s r : ℝ) :
    (segmentPlan γ s r).map (Prod.map id Prod.fst) =
      γ.map fun w ↦ (w.1, (1 - s) • w.2.1 + s • w.2.2) := by
  rw [segmentPlan_def, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The projection of a segment plan to its first and last coordinates is the law of `(x, y_r)`
under `γ`. -/
theorem map_prodMap_snd_segmentPlan (γ : Measure (E × E × E)) (s r : ℝ) :
    (segmentPlan γ s r).map (Prod.map id Prod.snd) =
      γ.map fun w ↦ (w.1, (1 - r) • w.2.1 + r • w.2.2) := by
  rw [segmentPlan_def, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end Segment

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The quadratic cost of the endpoint coupling of a segment plan between times `s` and `r` is
`(r - s) ^ 2` times that of `γ`, since `y_s - y_r = (r - s) • (y₀ - y₁)`. -/
theorem integral_norm_sub_sq_snd_segmentPlan (γ : Measure (E × E × E)) (s r : ℝ) :
    ∫ z, ‖z.1 - z.2‖ ^ 2 ∂(segmentPlan γ s r).snd =
      (r - s) ^ 2 * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd := by
  rw [Measure.snd, Measure.snd, segmentPlan_def, Measure.map_map measurable_snd (by fun_prop),
    integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
    ← integral_const_mul]
  congr 1
  funext w
  have : (1 - s) • w.2.1 + s • w.2.2 - ((1 - r) • w.2.1 + r • w.2.2) =
      (r - s) • (w.2.1 - w.2.2) := by
    module
  simp only [Function.comp_apply, this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

end Normed

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {γ : Measure (E × E × E)} {μ ν₀ ν₁ : Measure E}

/-- An optimal coupling for squared distance between laws with finite second moments has a
cyclically monotone support for the half-squared cost. -/
private theorem isCyclicallyMonotone_support_of_eLpNorm_eq [IsFiniteMeasure μ] {ν : Measure E}
    {π : Measure (E × E)} (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) (hπ : IsCoupling π μ ν)
    (hW : eLpNorm (fun z : E × E ↦ edist z.1 z.2) 2 π = wassersteinEDist 2 μ ν) :
    IsCyclicallyMonotone (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2 / 2) π.support := by
  have hopt : IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν :=
    isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two (by
      simpa only [ENNReal.toReal_ofNat] using
        (isOptimalCoupling_edist_rpow_iff measurable_edist two_ne_zero ENNReal.ofNat_ne_top).2
          ⟨hπ, hW⟩)
  refine (isCyclicallyMonotone_ofReal_iff fun _ ↦ by positivity).1
    (hopt.isCyclicallyMonotone_support continuous_ofReal_norm_sub_sq_div_two ?_)
  refine ne_top_of_le_ne_top ?_ (transportCost_le_lintegral hπ _)
  rw [hπ.lintegral_norm_sub_sq_div_two hμ hν]
  exact ENNReal.ofReal_ne_top

/-- The generalized geodesic of a plan whose middle and last coordinates have laws `ν₀` and `ν₁`
with finite second moments has finite second moment at every time. -/
private theorem memLp_id_generalizedGeodesic (hγ : IsGeneralizedGeodesicPlan 2 γ μ ν₀ ν₁)
    (hν₀ : MemLp id 2 ν₀) (hν₁ : MemLp id 2 ν₁) (s : ℝ) :
    MemLp id 2 (generalizedGeodesic γ s) := by
  have h₀ : γ.map (fun w ↦ w.2.1) = ν₀ := by
    rw [← hγ.isCoupling_snd.fst_eq, Measure.fst, Measure.snd,
      Measure.map_map measurable_fst measurable_snd]
    rfl
  have h₁ : γ.map (fun w ↦ w.2.2) = ν₁ := by
    rw [← hγ.isCoupling_snd.snd_eq, Measure.snd, Measure.snd,
      Measure.map_map measurable_snd measurable_snd]
    rfl
  have hm₀ : MemLp (fun w : E × E × E ↦ w.2.1) 2 γ := (h₀ ▸ hν₀).comp_of_map (by fun_prop)
  have hm₁ : MemLp (fun w : E × E × E ↦ w.2.2) 2 γ := (h₁ ▸ hν₁).comp_of_map (by fun_prop)
  rw [generalizedGeodesic_def, memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)]
  exact (hm₀.const_smul (1 - s)).add (hm₁.const_smul s)

/-- **Interpolated targets of a generalized-geodesic plan are optimally coupled with the base.**
Let `γ` be a quadratic generalized-geodesic plan from `ν₀` to `ν₁` based at a finite measure `μ`,
the three measures having finite second moments. For `s ∈ [0, 1]`, the law of
`(x, (1 - s) • y₀ + s • y₁)` under `γ` is an optimal coupling of `μ` and the generalized geodesic
at time `s` for the cost `‖x - y‖ ^ 2 / 2`. -/
theorem IsGeneralizedGeodesicPlan.isOptimalCoupling_map [IsFiniteMeasure μ]
    (hγ : IsGeneralizedGeodesicPlan 2 γ μ ν₀ ν₁) (hμ : MemLp id 2 μ) (hν₀ : MemLp id 2 ν₀)
    (hν₁ : MemLp id 2 ν₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (γ.map fun w ↦ (w.1, (1 - s) • w.2.1 + s • w.2.2)) μ (generalizedGeodesic γ s) := by
  set π₀ := γ.map (Prod.map id Prod.fst)
  set π₁ := γ.map (Prod.map id Prod.snd)
  -- The supports of the two optimal projections are cyclically monotone, hence so is the closure
  -- of the set of interpolated pairs over a common source.
  set S := closure {z : E × E | ∃ y₀ y₁, (z.1, y₀) ∈ π₀.support ∧ (z.1, y₁) ∈ π₁.support ∧
    z.2 = (1 - s) • y₀ + s • y₁}
  have hS : IsCyclicallyMonotone (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2 / 2) S := by
    refine IsCyclicallyMonotone.closure (by fun_prop) ?_
    have h₀ := isCyclicallyMonotone_support_of_eLpNorm_eq hμ hν₀ hγ.isCoupling_left
      hγ.eLpNorm_left
    have h₁ := isCyclicallyMonotone_support_of_eLpNorm_eq hμ hν₁ hγ.isCoupling_right
      hγ.eLpNorm_right
    rw [isCyclicallyMonotone_norm_sub_sq_div_two_iff] at h₀ h₁ ⊢
    exact h₀.pairingCost_smul_add_smul h₁ (sub_nonneg.2 hs.2) hs.1
  -- Almost every triple projects into both supports, so the interpolated coupling lives on `S`.
  have hf : Measurable fun w : E × E × E ↦ (w.1, (1 - s) • w.2.1 + s • w.2.2) := by fun_prop
  have hae : ∀ᵐ z ∂γ.map (fun w ↦ (w.1, (1 - s) • w.2.1 + s • w.2.2)), z ∈ S := by
    refine (ae_map_iff hf.aemeasurable (p := (· ∈ S)) isClosed_closure.measurableSet).2 ?_
    filter_upwards [ae_of_ae_map (by fun_prop) (Measure.support_mem_ae (μ := π₀)),
      ae_of_ae_map (by fun_prop) (Measure.support_mem_ae (μ := π₁))] with w hw₀ hw₁
    exact subset_closure ⟨w.2.1, w.2.2, hw₀, hw₁, rfl⟩
  have hcoup : IsCoupling (γ.map fun w ↦ (w.1, (1 - s) • w.2.1 + s • w.2.2)) μ
      (generalizedGeodesic γ s) := by
    constructor
    · rw [← hγ.fst_eq, Measure.fst, Measure.fst, Measure.map_map measurable_fst (by fun_prop)]
      rfl
    · rw [generalizedGeodesic_def, Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
      rfl
  exact hcoup.isOptimalCoupling_of_isCyclicallyMonotone_norm_sub_sq_div_two hμ
    (memLp_id_generalizedGeodesic hγ hν₀ hν₁ s) hS hae

/-- **Segments of generalized geodesics are generalized geodesics.** Let `γ` be a quadratic
generalized-geodesic plan from `ν₀` to `ν₁` based at a finite measure `μ`, the three measures
having finite second moments. For `s, r ∈ [0, 1]`, the segment plan of `γ` between `s` and `r` is
a quadratic generalized-geodesic plan from the generalized geodesic at time `s` to that at time
`r`, based at `μ`. -/
theorem IsGeneralizedGeodesicPlan.segmentPlan [IsFiniteMeasure μ]
    (hγ : IsGeneralizedGeodesicPlan 2 γ μ ν₀ ν₁) (hμ : MemLp id 2 μ) (hν₀ : MemLp id 2 ν₀)
    (hν₁ : MemLp id 2 ν₁) {s r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    IsGeneralizedGeodesicPlan 2 (TauCeti.segmentPlan γ s r) μ (generalizedGeodesic γ s)
      (generalizedGeodesic γ r) := by
  have key {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      IsCoupling (γ.map fun w ↦ (w.1, (1 - t) • w.2.1 + t • w.2.2)) μ (generalizedGeodesic γ t) ∧
        eLpNorm (fun z : E × E ↦ edist z.1 z.2) 2
            (γ.map fun w ↦ (w.1, (1 - t) • w.2.1 + t • w.2.2)) =
          wassersteinEDist 2 μ (generalizedGeodesic γ t) :=
    (isOptimalCoupling_edist_rpow_iff measurable_edist two_ne_zero ENNReal.ofNat_ne_top).1 (by
      simpa only [ENNReal.toReal_ofNat] using
        isOptimalCoupling_edist_rpow_two_of_norm_sub_sq_div_two
          (hγ.isOptimalCoupling_map hμ hν₀ hν₁ ht))
  obtain ⟨hcs, hWs⟩ := key hs
  obtain ⟨hcr, hWr⟩ := key hr
  rw [← map_prodMap_fst_segmentPlan γ s r] at hcs hWs
  rw [← map_prodMap_snd_segmentPlan γ s r] at hcr hWr
  exact ⟨hcs, hWs, hcr, hWr⟩

section Convexity

variable {m : ℝ} {φ : WassersteinSpace 2 E → EReal} {μ ν₀ ν₁ νs νr : WassersteinSpace 2 E}
  {s r : ℝ}

/-- **Convexity along generalized geodesics passes to their segments.** If `φ` is `m`-convex
along every quadratic generalized geodesic based at `μ`, and `γ` is a generalized-geodesic plan
based at `μ` between laws of finite energy, then `φ` is `m`-convex along the segment plan of `γ`
between any two times `s, r ∈ [0, 1]`. -/
theorem ConvexAlongGeneralizedGeodesics.convexAlongGeneralizedGeodesicPlan_segmentPlan
    (h : ConvexAlongGeneralizedGeodesics m φ μ)
    (hγ : IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
      ((ν₀ : ProbabilityMeasure E) : Measure E) ((ν₁ : ProbabilityMeasure E) : Measure E))
    (h₀ : φ ν₀ ≠ ⊤) (h₁ : φ ν₁ ≠ ⊤) (hs : s ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1)
    (hνs : ((νs : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ s)
    (hνr : ((νr : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ r) :
    ConvexAlongGeneralizedGeodesicPlan m φ νs νr (segmentPlan γ s r) := by
  refine convexAlongGeneralizedGeodesics_def.1 h (h.apply_ne_top h₀ h₁ hγ hs hνs)
    (h.apply_ne_top h₀ h₁ hγ hr hνr) ?_
  rw [hνs, hνr]
  exact hγ.segmentPlan μ.hasFiniteMoment.memLp_id ν₀.hasFiniteMoment.memLp_id
    ν₁.hasFiniteMoment.memLp_id hs hr

/-- **Convexity along generalized geodesics restricts to subintervals.** If `φ` is `m`-convex along
every quadratic generalized geodesic based at `μ`, and `ν_t` is the generalized geodesic of a
generalized-geodesic plan `γ` based at `μ` between laws of finite energy, then for
`s, r, u ∈ [0, 1]`,
`φ ν_{(1 - u) s + u r} ≤ (1 - u) φ ν_s + u φ ν_r - (m / 2) u (1 - u) (r - s)² ∫ ‖y₀ - y₁‖² dγ`. -/
theorem ConvexAlongGeneralizedGeodesics.apply_le_of_eq_generalizedGeodesic
    (h : ConvexAlongGeneralizedGeodesics m φ μ)
    (hγ : IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
      ((ν₀ : ProbabilityMeasure E) : Measure E) ((ν₁ : ProbabilityMeasure E) : Measure E))
    (h₀ : φ ν₀ ≠ ⊤) (h₁ : φ ν₁ ≠ ⊤) (hs : s ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1)
    (hνs : ((νs : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ s)
    (hνr : ((νr : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ r)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) {ν : WassersteinSpace 2 E}
    (hν : ((ν : ProbabilityMeasure E) : Measure E) =
      generalizedGeodesic γ ((1 - u) * s + u * r)) :
    φ ν ≤ ((1 - u : ℝ) : EReal) * φ νs + (u : EReal) * φ νr -
      ((m / 2 * u * (1 - u) * ((r - s) ^ 2 * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd) : ℝ) : EReal) := by
  have := convexAlongGeneralizedGeodesicPlan_def.1
    (h.convexAlongGeneralizedGeodesicPlan_segmentPlan hγ h₀ h₁ hs hr hνs hνr) u hu ν
    (by rw [hν, generalizedGeodesic_segmentPlan])
  rwa [integral_norm_sub_sq_snd_segmentPlan] at this

end Convexity

end InnerProductSpace

end TauCeti

end
