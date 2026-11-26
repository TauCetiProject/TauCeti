/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Convex.Conjugate
public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Monge
import TauCeti.Analysis.Convex.Superlinear
import TauCeti.MeasureTheory.OptimalTransport.Cost.Mixture
import TauCeti.MeasureTheory.OptimalTransport.CTransform.CyclicalMonotonicity
import TauCeti.MeasureTheory.OptimalTransport.CTransform.Regularity
import TauCeti.MeasureTheory.OptimalTransport.Existence.CyclicalMonotonicity
import TauCeti.MeasureTheory.OptimalTransport.Twist.StrictConvex

/-!
# Gangbo–McCann's theorem for strictly convex displacement costs

For a strictly convex superlinear displacement cost `c (x, y) = h (x - y)` on a finite-dimensional
real inner product space `E` (so that the Legendre–Fenchel conjugate `h⋆` of `h` is finite and
`C¹`), `TauCeti.gradient_fenchelConjugate_eq_sub_of_mem_contactSet` identifies any contact partner
`(x, y)` of a `c`-concave potential `φ` at a point `x` where `φ` avoids `⊥` nearby and has
differentiable real representative as `y = x - ∇h⋆(∇φ x)`. Under superlinear growth `h z / ‖z‖ → ∞`
and the cone condition (H2) at infinity,
`TauCeti.ae_eventually_ne_bot_and_differentiableAt_toReal_cTransformSymm` (in
`TauCeti.MeasureTheory.OptimalTransport.CTransform.Regularity`) shows that every `c`-concave
potential avoids `⊥` on a neighbourhood and has differentiable real representative at Haar-almost
every point of `{x | φ x ≠ ⊥}` (its finiteness domain whenever `φ ≢ ⊤`).

When `0 ≤ h`, wrapping the displacement cost as `(x, y) ↦ ENNReal.ofReal (h (x - y))` and combining
this potential regularity with `TauCeti.exists_isOptimalCoupling_isCyclicallyMonotone_support` and
Rockafellar–Rüschendorf (`TauCeti.IsCyclicallyMonotone.exists_isCConcave_subset_cSuperdifferential`)
yields Gangbo and McCann's Theorem 1.2: for finite measures `μ` and `ν` of equal mass with `μ`
absolutely continuous with respect to Haar measure, there is a `c`-concave potential `φ` such that
`T x = x - ∇h⋆(∇φ x)` is a Kantorovich-optimal transport map for `ENNReal.ofReal (h (x - y))` whose
graph plan has `c`-cyclically monotone support
(`TauCeti.exists_isCConcave_and_isKantorovichOptimalTransportMap_of_strictConvexOn`), even when the
optimal transport cost is `∞`. When the optimal cost for `ENNReal.ofReal (h (x - y))` is finite,
both the optimal coupling and the optimal transport map are unique
(`TauCeti.IsOptimalCoupling.unique_of_strictConvexOn`,
`TauCeti.exists_isKantorovichOptimalTransportMap_of_strictConvexOn`). When `h` is also
differentiable, `∇h⋆` is the two-sided inverse of `∇h` by
`TauCeti.leftInverse_gradient_fenchelConjugate_of_superlinear` and
`TauCeti.rightInverse_gradient_fenchelConjugate_of_superlinear`.

## Main statements

* `TauCeti.eq_graphPlan_of_ae_mem_cSuperdifferential_of_strictConvexOn` — any plan with Haar-regular
  first marginal concentrated on `cSuperdifferential c φ` is the graph plan of
  `x ↦ x - ∇h⋆(∇φ x)`;
* `TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_strictConvexOn` and
  `TauCeti.IsOptimalCoupling.unique_of_strictConvexOn` — for `0 ≤ h`, map representation and
  uniqueness of finite-cost optimal plans for `(x, y) ↦ ENNReal.ofReal (h (x - y))`;
* `TauCeti.exists_isCConcave_and_isKantorovichOptimalTransportMap_of_strictConvexOn` — for `0 ≤ h`,
  unconditional existence of a `c`-concave potential and cyclically/Kantorovich-optimal map
  `x ↦ x - ∇h⋆(∇φ x)` between finite equal-mass measures for `(x, y) ↦ ENNReal.ofReal (h (x - y))`;
* `TauCeti.exists_isKantorovichOptimalTransportMap_of_strictConvexOn` — for `0 ≤ h`, finite-cost
  existence and uniqueness of the Kantorovich-optimal transport map and optimal plan for
  `(x, y) ↦ ENNReal.ofReal (h (x - y))`.

## References

* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113--161, Theorem 1.2.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 10.28.
-/

public section

noncomputable section

open Filter MeasureTheory Metric ProbabilityTheory Set
open scoped ENNReal Gradient RealInnerProductSpace Topology

namespace TauCeti

section TransportMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]
  {h : E → ℝ} {μ ν : Measure E} {π : Measure (E × E)}

/-- **A plan on the `c`-superdifferential is induced by the Gangbo–McCann map.** Let `π` be a
measure on `E × E` with first marginal `μ ≪ ρ`, where `ρ` is an additive Haar measure, and let `h`
be strictly convex, superlinear, and satisfy the cone condition (H2). If `φ` is `c`-concave for
`c (x, y) = h (x - y)` and `π`-almost every point lies in `cSuperdifferential c φ`, then `φ` avoids
`⊥` near `μ`-almost every point and has differentiable real representative there, and `π` is the
graph plan over `μ` of `x ↦ x - ∇h⋆(∇φ x)`. -/
theorem eq_graphPlan_of_ae_mem_cSuperdifferential_of_strictConvexOn (hπ : π.fst = μ) (hμ : μ ≪ ρ)
    (h_strict : StrictConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∃ r θ R : ℝ, 0 < r ∧ 0 < θ ∧ θ < Real.pi ∧ ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    {φ : E → EReal} (hφ : IsCConcave (fun z : E × E ↦ h (z.1 - z.2)) φ)
    (hcon : ∀ᵐ z ∂π, z ∈ cSuperdifferential (fun z : E × E ↦ h (z.1 - z.2)) φ) :
    (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧ DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x) ∧
      π = graphPlan (fun x ↦ x -
        ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
          (∇ (fun x' ↦ (φ x').toReal) x)) μ := by
  set c : E × E → ℝ := fun z ↦ h (z.1 - z.2)
  have hc : Continuous h := h_strict.convexOn.locallyLipschitz.continuous
  have hsuper_cc : Tendsto (fun x ↦ h x / ‖x‖) (cocompact E) atTop :=
    Metric.cobounded_eq_cocompact (α := E) ▸ h_superlinear
  rw [cSuperdifferential_def] at hcon
  have hφ_eq : φ = cTransformSymm c (cTransform c φ) := hφ.cTransformSymm_cTransform.symm
  have hφ_meas : Measurable φ :=
    hφ_eq ▸ measurable_cTransformSymm_of_upperSemicontinuous
      (fun y ↦ (hc.comp (continuous_id.sub continuous_const)).upperSemicontinuous) (cTransform c φ)
  have hdom : ∀ᵐ x ∂μ, φ x ≠ ⊥ := by
    rw [← hπ]
    refine (ae_map_iff measurable_fst.aemeasurable
      (hφ_meas (measurableSet_singleton ⊥).compl)).2 ?_
    filter_upwards [hcon] with z hz using ne_bot_left_of_mem_contactSet (x := z.1) (y := z.2) hz
  have hdiff : ∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧
      DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x := by
    rw [hφ_eq]
    filter_upwards [hμ.ae_le (ae_eventually_ne_bot_and_differentiableAt_toReal_cTransformSymm ρ
      h_strict.convexOn h_superlinear h_cone (cTransform c φ)), hφ_eq ▸ hdom] with x hx hx'
      using hx hx'
  have hconj_top : ∀ q, fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q ≠ ⊤ := fun q ↦ by
    obtain ⟨w, hw⟩ := exists_fenchelConjugate_eq_of_superlinear hc hsuper_cc q
    exact hw ▸ EReal.coe_ne_top _
  have hconj_diff : Differentiable ℝ
      (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal) :=
    (contDiff_fenchelConjugate_toReal_of_superlinear h_strict hsuper_cc).differentiable one_ne_zero
  set T : E → E := fun x ↦ x -
    ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
      (∇ (fun x' ↦ (φ x').toReal) x)
  have hT_meas : Measurable T :=
    measurable_id.sub ((measurable_gradient _).comp (measurable_gradient _))
  have hgraph : ∀ᵐ z ∂π, z.2 = T z.1 := by
    rw [← hπ] at hdiff
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hdiff, hcon] with z ⟨hfin, hd⟩ hz
    have heq := gradient_fenchelConjugate_eq_sub_of_mem_contactSet (x := z.1) (y := z.2)
      h_strict.convexOn (Eventually.of_forall fun x' ↦ add_cTransform_le c φ x' z.2) hfin hz hd
      (Eventually.of_forall hconj_top) (hconj_diff _)
    simp only [T, heq, sub_sub_cancel]
  refine ⟨hdiff, ?_⟩
  rw [eq_graphPlan_of_ae_snd_eq hT_meas.aemeasurable hgraph, hπ]

private theorem exists_eq_graphPlan_of_isCyclicallyMonotone_support (hπ : π.fst = μ) (hμ : μ ≪ ρ)
    (h_strict : StrictConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∃ r θ R : ℝ, 0 < r ∧ 0 < θ ∧ θ < Real.pi ∧ ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (hcm : IsCyclicallyMonotone (fun z : E × E ↦ h (z.1 - z.2)) π.support) :
    ∃ φ : E → EReal, IsCConcave (fun z : E × E ↦ h (z.1 - z.2)) φ ∧
      (∀ x, φ x ≠ ⊤) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧ DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x) ∧
      (∀ᵐ x ∂μ, (x, x -
        ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
          (∇ (fun x' ↦ (φ x').toReal) x)) ∈
        cSuperdifferential (fun z : E × E ↦ h (z.1 - z.2)) φ) ∧
      π = graphPlan (fun x ↦ x -
        ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
          (∇ (fun x' ↦ (φ x').toReal) x)) μ := by
  set c : E × E → ℝ := fun z ↦ h (z.1 - z.2)
  obtain ⟨φ, hφ, hφ_top, hsub⟩ :
      ∃ φ : E → EReal, IsCConcave c φ ∧ (∀ x, φ x ≠ ⊤) ∧
        π.support ⊆ cSuperdifferential c φ := by
    rcases π.support.eq_empty_or_nonempty with hemp | ⟨z₀, hz₀⟩
    · exact ⟨cTransformSymm c 0, isCConcave_cTransformSymm c 0,
        fun x ↦ (cTransformSymm_lt_top_of_ne_bot c (y := (0 : E)) EReal.zero_ne_bot x).ne,
        hemp ▸ empty_subset _⟩
    · obtain ⟨φ, hφ, hsub⟩ := hcm.exists_isCConcave_subset_cSuperdifferential
      have hhz₀ : (z₀.1, z₀.2) ∈ contactSet c φ (cTransform c φ) := by
        simpa only [cSuperdifferential_def] using hsub hz₀
      exact ⟨φ, hφ, ne_top_of_cTransform_ne_bot (ne_bot_right_of_mem_contactSet hhz₀), hsub⟩
  have hcon : ∀ᵐ z ∂π, z ∈ cSuperdifferential c φ := by
    filter_upwards [π.support_mem_ae] with z hz using hsub hz
  obtain ⟨hdiff, hgraph⟩ := eq_graphPlan_of_ae_mem_cSuperdifferential_of_strictConvexOn
    hπ hμ h_strict h_superlinear h_cone hφ hcon
  have hT_meas : Measurable fun x ↦ x -
      ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
        (∇ (fun x' ↦ (φ x').toReal) x) :=
    measurable_id.sub ((measurable_gradient _).comp (measurable_gradient _))
  exact ⟨φ, hφ, hφ_top, hdiff, ae_of_ae_graphPlan hT_meas.aemeasurable (hgraph ▸ hcon), hgraph⟩

/-- **An optimal finite-cost plan is the graph plan of a Gangbo–McCann map.** Between finite
measures on a finite-dimensional real inner product space with `μ ≪ ρ`, any optimal coupling of
finite cost for a nonnegative strictly convex superlinear displacement cost `h (x - y)` satisfying
the cone condition (H2) is the graph plan of `x ↦ x - ∇h⋆(∇φ x)` for a `c`-concave potential `φ`
that never takes `⊤`, avoids `⊥` near `μ`-almost every point, and has differentiable real
representative there. -/
theorem IsOptimalCoupling.exists_eq_graphPlan_of_strictConvexOn [IsFiniteMeasure μ] (hμ : μ ≪ ρ)
    (h_nonneg : ∀ x, 0 ≤ h x) (h_strict : StrictConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∃ r θ R : ℝ, 0 < r ∧ 0 < θ ∧ θ < Real.pi ∧ ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (hopt : IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) π μ ν)
    (hfin : transportCost (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν ≠ ∞) :
    ∃ φ : E → EReal, IsCConcave (fun z : E × E ↦ h (z.1 - z.2)) φ ∧
      (∀ x, φ x ≠ ⊤) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧ DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x) ∧
      π = graphPlan (fun x ↦ x -
        ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
          (∇ (fun x' ↦ (φ x').toReal) x)) μ := by
  have hc_prod : Continuous fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2)) :=
    ENNReal.continuous_ofReal.comp
      (h_strict.convexOn.locallyLipschitz.continuous.comp (continuous_fst.sub continuous_snd))
  obtain ⟨φ, hφ, hφ_top, hdiff, -, hgraph⟩ :=
    exists_eq_graphPlan_of_isCyclicallyMonotone_support hopt.fst_eq hμ h_strict h_superlinear
      h_cone ((isCyclicallyMonotone_ofReal_iff fun _ ↦ h_nonneg _).1
        (hopt.isCyclicallyMonotone_support hc_prod hfin))
  exact ⟨φ, hφ, hφ_top, hdiff, hgraph⟩

/-- **Uniqueness of the optimal plan for a strictly convex displacement cost**
(Gangbo–McCann, Theorem 1.2). Between finite measures on a finite-dimensional real inner product
space with `μ ≪ ρ`, if `h` is nonnegative, strictly convex, superlinear, and satisfies the cone
condition (H2), and the optimal cost for `h (x - y)` is finite, then any two optimal couplings are
equal. -/
theorem IsOptimalCoupling.unique_of_strictConvexOn [IsFiniteMeasure μ] (hμ : μ ≪ ρ)
    {π' : Measure (E × E)} (h_nonneg : ∀ x, 0 ≤ h x) (h_strict : StrictConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∃ r θ R : ℝ, 0 < r ∧ 0 < θ ∧ θ < Real.pi ∧ ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (hopt : IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) π μ ν)
    (hopt' : IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) π' μ ν)
    (hfin : transportCost (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν ≠ ∞) :
    π = π' :=
  hopt.eq_of_add_eq_graphPlan hopt' fun hsum ↦ by
    obtain ⟨φ, -, -, -, hgraph⟩ := hsum.exists_eq_graphPlan_of_strictConvexOn
      (hμ.add_left hμ) h_nonneg h_strict h_superlinear h_cone
      (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin, hfin⟩) (transportCost_add_le _ _ _ _ _))
    exact ⟨_, (measurable_id.sub
      ((measurable_gradient _).comp (measurable_gradient _))).aemeasurable, hgraph⟩

/-- **Gangbo–McCann's theorem, unconditional potential and map form**
(Gangbo–McCann, Theorem 1.2). For finite measures `μ` and `ν` of equal mass on a
finite-dimensional real inner product space with `μ ≪ ρ`, and a nonnegative strictly convex
superlinear function `h` satisfying the cone condition (H2), there exists a `c`-concave potential
`φ` for `c (x, y) = h (x - y)` that never takes `⊤`, avoids `⊥` near `μ`-almost every point and has
differentiable real representative there, such that `T x = x - ∇h⋆(∇φ x)` satisfies
`(x, T x) ∈ cSuperdifferential c φ` `μ`-almost everywhere, `(graphPlan T μ).support` is
`c`-cyclically monotone, and `T` is a Kantorovich-optimal transport map from `μ` to `ν`. No
finiteness assumption on `transportCost` is required, and no uniqueness claim is made when the
optimal cost is `∞`. -/
theorem exists_isCConcave_and_isKantorovichOptimalTransportMap_of_strictConvexOn
    [IsFiniteMeasure μ] (hmass : μ univ = ν univ) (hμ : μ ≪ ρ)
    (h_nonneg : ∀ x, 0 ≤ h x) (h_strict : StrictConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∃ r θ R : ℝ, 0 < r ∧ 0 < θ ∧ θ < Real.pi ∧ ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p) :
    ∃ φ : E → EReal, IsCConcave (fun z : E × E ↦ h (z.1 - z.2)) φ ∧
      (∀ x, φ x ≠ ⊤) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧ DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x) ∧
      (∀ᵐ x ∂μ, (x, x -
        ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
          (∇ (fun x' ↦ (φ x').toReal) x)) ∈
        cSuperdifferential (fun z : E × E ↦ h (z.1 - z.2)) φ) ∧
      IsCyclicallyMonotone (fun z : E × E ↦ h (z.1 - z.2))
        (graphPlan (fun x ↦ x -
          ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
            (∇ (fun x' ↦ (φ x').toReal) x)) μ).support ∧
      IsKantorovichOptimalTransportMap (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν
        (fun x ↦ x -
          ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
            (∇ (fun x' ↦ (φ x').toReal) x)) := by
  have hc : Continuous fun z : E × E ↦ h (z.1 - z.2) :=
    h_strict.convexOn.locallyLipschitz.continuous.comp (continuous_fst.sub continuous_snd)
  obtain ⟨π, hopt, hcm⟩ :=
    exists_isOptimalCoupling_isCyclicallyMonotone_support hmass hc fun _ ↦ h_nonneg _
  obtain ⟨φ, hφ, hφ_top, hdiff, hcon_T, hgraph⟩ :=
    exists_eq_graphPlan_of_isCyclicallyMonotone_support hopt.fst_eq hμ h_strict h_superlinear
      h_cone hcm
  have hT_meas : Measurable fun x ↦ x -
      ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
        (∇ (fun x' ↦ (φ x').toReal) x) :=
    measurable_id.sub ((measurable_gradient _).comp (measurable_gradient _))
  exact ⟨φ, hφ, hφ_top, hdiff, hcon_T, hgraph ▸ hcm,
    isKantorovichOptimalTransportMap_of_isOptimalCoupling_graphPlan hT_meas.aemeasurable
      (ENNReal.continuous_ofReal.comp hc).measurable.aemeasurable (hgraph ▸ hopt)⟩

/-- **Gangbo–McCann's theorem for strictly convex costs** (Gangbo–McCann, Theorem 1.2). Let `μ` be
a finite measure and `ν` a measure on a finite-dimensional real inner product space `E`, with `μ`
absolutely continuous with respect to an additive Haar measure `ρ`, and let `h : E → [0, ∞)` be
strictly convex, superlinear, and satisfy the cone condition `h_cone`: for some height `r > 0`,
aperture `θ ∈ (0, π)` and radius `R`, every `p` with `R < ‖p‖` is the vertex of a truncated cone
on which `h ≤ h p`. This is one instance of Gangbo–McCann's condition (H2), which asks it for
every `r` and `θ` (with `R` depending on them). If the optimal transport cost of
`c (x, y) = h (x - y)` from `μ` to `ν` is finite (so `μ` and `ν` have the same finite mass), then
there exists a transport map `T : E → E` that:

* is a Kantorovich-optimal transport map from `μ` to `ν`;
* induces the unique optimal coupling: `γ` is optimal if and only if `γ = graphPlan T μ`;
* is the unique Kantorovich-optimal transport map up to `μ`-almost everywhere equality. -/
theorem exists_isKantorovichOptimalTransportMap_of_strictConvexOn [IsFiniteMeasure μ]
    (hμ : μ ≪ ρ) (h_nonneg : ∀ x, 0 ≤ h x) (h_strict : StrictConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∃ r θ R : ℝ, 0 < r ∧ 0 < θ ∧ θ < Real.pi ∧ ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (hfin : transportCost (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν ≠ ∞) :
    ∃ T : E → E,
      IsKantorovichOptimalTransportMap (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν T ∧
      (∀ γ, IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) γ μ ν ↔
        γ = graphPlan T μ) ∧
      ∀ S : E → E,
        IsKantorovichOptimalTransportMap (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν S →
          S =ᵐ[μ] T := by
  have hc : Continuous fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2)) :=
    ENNReal.continuous_ofReal.comp
      (h_strict.convexOn.locallyLipschitz.continuous.comp (continuous_fst.sub continuous_snd))
  have hmass : μ univ = ν univ :=
    (exists_isCoupling_of_transportCost_ne_top hfin).choose_spec.measure_univ_eq
  obtain ⟨φ, -, -, -, -, -, hT_opt⟩ :=
    exists_isCConcave_and_isKantorovichOptimalTransportMap_of_strictConvexOn hmass hμ h_nonneg
      h_strict h_superlinear h_cone
  have hπ : IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2)))
      (graphPlan _ μ) μ ν :=
    (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hT_opt.toHasLaw
      hc.measurable.aemeasurable).1 hT_opt
  refine ⟨_, hT_opt,
    fun γ ↦ ⟨fun hγ ↦ hγ.unique_of_strictConvexOn hμ h_nonneg h_strict h_superlinear
      h_cone hπ hfin, fun hγ ↦ hγ ▸ hπ⟩,
    fun S hS ↦ hS.ae_eq_of_isOptimalCoupling_eq_graphPlan hT_opt.toHasLaw.aemeasurable
      hc.measurable.aemeasurable fun hS_opt ↦
        hS_opt.unique_of_strictConvexOn hμ h_nonneg h_strict h_superlinear h_cone hπ hfin⟩

end TransportMap

end TauCeti
