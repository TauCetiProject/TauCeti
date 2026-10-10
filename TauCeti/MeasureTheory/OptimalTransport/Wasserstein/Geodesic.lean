/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.DynamicPlan
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Infinity.Basic

/-!
# Wasserstein geodesics from optimal dynamic plans

Let `η` be a dynamic plan on a metric space `X`, concentrated on geodesic paths, whose endpoint
law is an optimal coupling of its laws `μ = η_0` and `ν = η_1` at times `0` and `1`, at finite
cost. Its laws at intermediate times then form a constant-speed geodesic for the `p`-Wasserstein
distance, for every exponent `1 ≤ p ≤ ∞`:

`W_p (η_s, η_t) = |s - t| * W_p (μ, ν)`.

The bound `≤` holds for any plan concentrated on geodesics
(`TauCeti.wassersteinEDist_timeMarginal_le`). The reverse bound follows from the triangle
inequality: `W_p (μ, ν)` is at most the sum of the three distances along `0 ≤ s ≤ t ≤ 1`, each of
which is bounded by its share of `W_p (μ, ν)`, so none of the three bounds can be strict. In the
same way, the joint law of the path at times `s` and `t` is an optimal coupling of `η_s` and `η_t`:
every two-time projection of such a plan is optimal.

On a Polish geodesic space, every pair of finite measures at finite Wasserstein distance is the
pair of endpoint laws of such a plan, obtained by lifting an optimal coupling to geodesic paths.
Consequently the space `P_p (X)` of probability measures with finite `p`-th moment is itself a
geodesic space.

## Main results

* `TauCeti.wassersteinEDist_timeMarginal_eq`: the laws at intermediate times of a dynamic plan
  concentrated on geodesics, with optimal endpoint law of finite cost, form a constant-speed
  Wasserstein geodesic.
* `TauCeti.eLpNorm_edist_map_eq_wassersteinEDist_timeMarginal` and
  `TauCeti.isOptimalCoupling_map_timeMarginal`: every two-time projection of such a plan is an
  optimal coupling of its laws at those times.
* `TauCeti.exists_ae_mem_geodesicPaths_wassersteinEDist_timeMarginal_eq`: on a Polish geodesic
  space, two finite measures at finite `p`-Wasserstein distance are joined by such a plan.
* `TauCeti.WassersteinSpace.instIsGeodesicSpace`: on a Polish geodesic space, `P_p (X)` is a
  geodesic space for every `1 ≤ p ≤ ∞`.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §7.2.
* S. Lisini, *Characterization of absolutely continuous curves in Wasserstein spaces*, Calc. Var.
  Partial Differential Equations 28 (2007), 85--120.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 7.
-/

public section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace TauCeti

variable {p : ℝ≥0∞}

section Interpolation

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X]

/-- The three pieces into which times `s ≤ t` cut the unit interval add up to the whole. -/
private theorem edist_zero_mul_add_edist_mul_add_edist_one_mul {s t : I} (hst : s ≤ t)
    (a : ℝ≥0∞) : edist 0 s * a + edist s t * a + edist t 1 * a = a := by
  have hst' : (s : ℝ) ≤ t := hst
  simp only [edist_dist, Subtype.dist_eq, Real.dist_eq, Icc.coe_zero, Icc.coe_one, zero_sub,
    abs_neg, abs_of_nonneg s.2.1, abs_of_nonpos (sub_nonpos.2 hst'),
    abs_of_nonpos (sub_nonpos.2 t.2.2), neg_sub, ← add_mul]
  rw [← ENNReal.ofReal_add s.2.1 (sub_nonneg.2 hst'), add_sub_cancel,
    ← ENNReal.ofReal_add t.2.1 (sub_nonneg.2 t.2.2), add_sub_cancel, ENNReal.ofReal_one, one_mul]

/-- **Wasserstein geodesics from optimal dynamic plans.** Let `η` be a finite dynamic plan
concentrated on geodesic paths whose endpoint law is an optimal coupling, at finite cost, of its
laws at times `0` and `1`. For `1 ≤ p`, its laws at times `s` and `t` are at `p`-Wasserstein
distance exactly `|s - t|` times that between its laws at times `0` and `1`. -/
theorem wassersteinEDist_timeMarginal_eq {η : Measure C(I, X)} [IsFiniteMeasure η]
    (hη : ∀ᵐ γ ∂η, γ ∈ geodesicPaths X) (hp : 1 ≤ p)
    (hopt : eLpNorm (fun z : X × X ↦ edist z.1 z.2) p η.endpointLaw =
      wassersteinEDist p (η.timeMarginal 0) (η.timeMarginal 1))
    (hfin : wassersteinEDist p (η.timeMarginal 0) (η.timeMarginal 1) ≠ ∞) (s t : I) :
    wassersteinEDist p (η.timeMarginal s) (η.timeMarginal t) =
      edist s t * wassersteinEDist p (η.timeMarginal 0) (η.timeMarginal 1) := by
  have hd : Measurable fun z : X × X ↦ edist z.1 z.2 := measurable_edist
  -- By symmetry of both sides it suffices to treat `s ≤ t`.
  wlog hst : s ≤ t generalizing s t
  · rw [wassersteinEDist_comm hd, edist_comm]
    exact this t s (le_of_not_ge hst)
  set W := wassersteinEDist p (η.timeMarginal 0) (η.timeMarginal 1)
  have hle (u v : I) : wassersteinEDist p (η.timeMarginal u) (η.timeMarginal v) ≤ edist u v * W :=
    hopt ▸ wassersteinEDist_timeMarginal_le hη p u v
  refine le_antisymm (hle s t) ?_
  -- The triangle inequality along `0 ≤ s ≤ t ≤ 1` leaves no room in the middle bound.
  have htri : W ≤ edist 0 s * W + wassersteinEDist p (η.timeMarginal s) (η.timeMarginal t) +
      edist t 1 * W := calc
    W ≤ wassersteinEDist p (η.timeMarginal 0) (η.timeMarginal s) +
        wassersteinEDist p (η.timeMarginal s) (η.timeMarginal 1) :=
      wassersteinEDist_triangle hd hp _ _ _
    _ ≤ wassersteinEDist p (η.timeMarginal 0) (η.timeMarginal s) +
        (wassersteinEDist p (η.timeMarginal s) (η.timeMarginal t) +
          wassersteinEDist p (η.timeMarginal t) (η.timeMarginal 1)) := by
      gcongr
      exact wassersteinEDist_triangle hd hp _ _ _
    _ ≤ edist 0 s * W + (wassersteinEDist p (η.timeMarginal s) (η.timeMarginal t) +
          edist t 1 * W) := by
      gcongr
      exacts [hle 0 s, hle t 1]
    _ = _ := (add_assoc ..).symm
  have hfin' (u v : I) : edist u v * W ≠ ∞ := ENNReal.mul_ne_top (edist_ne_top u v) hfin
  exact (ENNReal.add_le_add_iff_left (hfin' 0 s)).1 ((ENNReal.add_le_add_iff_right (hfin' t 1)).1
    ((edist_zero_mul_add_edist_mul_add_edist_one_mul hst W).trans_le htri))

/-- **Two-time projections are optimal.** For a dynamic plan as in
`TauCeti.wassersteinEDist_timeMarginal_eq`, the joint law at times `s` and `t` realizes the
`p`-Wasserstein distance between the laws at those times. -/
theorem eLpNorm_edist_map_eq_wassersteinEDist_timeMarginal {η : Measure C(I, X)}
    [IsFiniteMeasure η] (hη : ∀ᵐ γ ∂η, γ ∈ geodesicPaths X) (hp : 1 ≤ p)
    (hopt : eLpNorm (fun z : X × X ↦ edist z.1 z.2) p η.endpointLaw =
      wassersteinEDist p (η.timeMarginal 0) (η.timeMarginal 1))
    (hfin : wassersteinEDist p (η.timeMarginal 0) (η.timeMarginal 1) ≠ ∞) (s t : I) :
    eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (η.map fun γ ↦ (γ s, γ t)) =
      wassersteinEDist p (η.timeMarginal s) (η.timeMarginal t) := by
  rw [eLpNorm_edist_map_eq hη, hopt, wassersteinEDist_timeMarginal_eq hη hp hopt hfin s t]

/-- **Two-time projections are optimal**, in the language of optimal couplings: for a finite
exponent, the joint law at times `s` and `t` of a dynamic plan as in
`TauCeti.wassersteinEDist_timeMarginal_eq` is an optimal coupling of its laws at those times for
the cost `d ^ p`. -/
theorem isOptimalCoupling_map_timeMarginal {η : Measure C(I, X)} [IsFiniteMeasure η]
    (hη : ∀ᵐ γ ∂η, γ ∈ geodesicPaths X) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hopt : eLpNorm (fun z : X × X ↦ edist z.1 z.2) p η.endpointLaw =
      wassersteinEDist p (η.timeMarginal 0) (η.timeMarginal 1))
    (hfin : wassersteinEDist p (η.timeMarginal 0) (η.timeMarginal 1) ≠ ∞) (s t : I) :
    IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) (η.map fun γ ↦ (γ s, γ t))
      (η.timeMarginal s) (η.timeMarginal t) :=
  (isOptimalCoupling_edist_rpow_iff measurable_edist (zero_lt_one.trans_le hp).ne' hp').2
    ⟨η.isCoupling_map_timeMarginal s t,
      eLpNorm_edist_map_eq_wassersteinEDist_timeMarginal hη hp hopt hfin s t⟩

end Interpolation

section Polish

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Existence of Wasserstein geodesics.** On a Polish geodesic space and for `1 ≤ p`, two finite
measures `μ` and `ν` at finite `p`-Wasserstein distance are the laws at times `0` and `1` of a
finite dynamic plan concentrated on geodesic paths, whose endpoint law is an optimal coupling of
`μ` and `ν` and whose laws at times `s` and `t` are at distance exactly
`|s - t| * W_p (μ, ν)`. -/
theorem exists_ae_mem_geodesicPaths_wassersteinEDist_timeMarginal_eq [IsGeodesicSpace X]
    (hp : 1 ≤ p) (μ ν : Measure X) [IsFiniteMeasure μ] (hfin : wassersteinEDist p μ ν ≠ ∞) :
    ∃ η : Measure C(I, X), IsFiniteMeasure η ∧ (∀ᵐ γ ∂η, γ ∈ geodesicPaths X) ∧
      η.timeMarginal 0 = μ ∧ η.timeMarginal 1 = ν ∧
      eLpNorm (fun z : X × X ↦ edist z.1 z.2) p η.endpointLaw = wassersteinEDist p μ ν ∧
      ∀ s t : I, wassersteinEDist p (η.timeMarginal s) (η.timeMarginal t) =
        edist s t * wassersteinEDist p μ ν := by
  have hcoup := exists_isCoupling_of_wassersteinEDist_ne_top hfin
  obtain ⟨π, hπ, hπopt⟩ : ∃ π, IsCoupling π μ ν ∧
      eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π = wassersteinEDist p μ ν := by
    rcases eq_or_ne p ∞ with rfl | hp'
    · exact exists_isCoupling_eLpNorm_top_eq_wassersteinEDist μ ν hcoup
    · exact exists_isCoupling_eLpNorm_eq_wassersteinEDist (zero_lt_one.trans_le hp).ne' hp' μ ν
        hcoup
  have : IsFiniteMeasure π := hπ.isFiniteMeasure
  obtain ⟨η, -, hη, hηπ⟩ := π.exists_ae_mem_geodesicPaths_endpointLaw_eq
    (.of_forall fun z ↦ IsGeodesicSpace.exists_mem_geodesicPaths z.1 z.2)
  have : IsFiniteMeasure (η.map fun γ ↦ (γ 0, γ 1)) := by
    rw [← Measure.endpointLaw_def, hηπ]
    infer_instance
  have : IsFiniteMeasure η := Measure.isFiniteMeasure_of_map (μ := η)
    (f := fun γ ↦ (γ 0, γ 1))
    ((ContinuousMap.measurable_eval 0).prodMk (ContinuousMap.measurable_eval 1)).aemeasurable
  have h0 : η.timeMarginal 0 = μ := by rw [← Measure.fst_endpointLaw, hηπ, hπ.fst_eq]
  have h1 : η.timeMarginal 1 = ν := by rw [← Measure.snd_endpointLaw, hηπ, hπ.snd_eq]
  have hopt : eLpNorm (fun z : X × X ↦ edist z.1 z.2) p η.endpointLaw =
      wassersteinEDist p (η.timeMarginal 0) (η.timeMarginal 1) := by rw [hηπ, hπopt, h0, h1]
  refine ⟨η, inferInstance, hη, h0, h1, hηπ ▸ hπopt, fun s t ↦ ?_⟩
  rw [wassersteinEDist_timeMarginal_eq hη hp hopt (h0 ▸ h1 ▸ hfin), h0, h1]

namespace WassersteinSpace

variable [Fact (1 ≤ p)]

/-- **`P_p (X)` is a geodesic space.** On a Polish geodesic space, the space of probability
measures with finite `p`-th moment, with the `p`-Wasserstein distance, is a geodesic space for
every `1 ≤ p ≤ ∞`: the laws at intermediate times of a dynamic plan lifting an optimal coupling
to geodesic paths form a geodesic segment. -/
instance instIsGeodesicSpace [IsGeodesicSpace X] : IsGeodesicSpace (WassersteinSpace p X) where
  exists_isGeodesicSegment μ ν := by
    have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
    have hμν := wassersteinEDist_ne_top measurable_edist μ ν
    obtain ⟨η, -, hη, h0, h1, -, hW⟩ :=
      exists_ae_mem_geodesicPaths_wassersteinEDist_timeMarginal_eq hp _ _ hμν
    have : IsProbabilityMeasure η := by
      rw [← Measure.isProbabilityMeasure_map_iff (ContinuousMap.measurable_eval 0).aemeasurable,
        ← Measure.timeMarginal_def, h0]
      infer_instance
    -- The law at time `t` has finite moment, being at finite distance from `μ`.
    have hmom (t : I) :
        HasFiniteMoment p ((η.timeMarginal t).toProbabilityMeasure : Measure X) := by
      rw [Measure.coe_toProbabilityMeasure]
      refine (hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment measurable_edist
        (hasFiniteMoment μ)).2 ?_
      rw [← h0, hW]
      exact ENNReal.mul_ne_top (edist_ne_top 0 t) hμν
    obtain ⟨γ, hγ⟩ : ∃ γ : I → WassersteinSpace p X,
        ∀ t, ((γ t : ProbabilityMeasure X) : Measure X) = η.timeMarginal t :=
      ⟨fun t ↦ mk (η.timeMarginal t).toProbabilityMeasure (hmom t),
        fun t ↦ by simp⟩
    have hγ0 : γ 0 = μ := ext (ProbabilityMeasure.toMeasure_injective ((hγ 0).trans h0))
    have hγ1 : γ 1 = ν := ext (ProbabilityMeasure.toMeasure_injective ((hγ 1).trans h1))
    have hdist (s t : I) : dist (γ s) (γ t) = |(s : ℝ) - t| * dist (γ 0) (γ 1) := by
      rw [hγ0, hγ1, dist_def, dist_def, hγ, hγ, hW, ENNReal.toReal_mul, edist_dist,
        ENNReal.toReal_ofReal dist_nonneg, Subtype.dist_eq, Real.dist_eq]
    -- The curve is Lipschitz, hence a path; it is then a geodesic path by `hdist`.
    have hc : (⟨γ, (LipschitzWith.of_dist_le_mul (K := (dist (γ 0) (γ 1)).toNNReal)
        fun s t ↦ by rw [hdist, Real.coe_toNNReal _ dist_nonneg, Subtype.dist_eq, Real.dist_eq,
          mul_comm]).continuous⟩ : C(I, WassersteinSpace p X)) ∈ geodesicPaths _ :=
      mem_geodesicPaths_iff.2 hdist
    have hseg := mem_geodesicPaths_iff_isGeodesicSegment.1 hc
    simp only [ContinuousMap.coe_mk, hγ0, hγ1] at hseg
    exact ⟨_, hseg⟩

end WassersteinSpace

end Polish

end TauCeti
