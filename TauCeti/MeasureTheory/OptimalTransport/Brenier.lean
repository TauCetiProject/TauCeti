/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Convex.Differentiability
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Quadratic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Mixture
public import TauCeti.MeasureTheory.OptimalTransport.Existence
public import TauCeti.MeasureTheory.OptimalTransport.Monge
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space

/-!
# Brenier's theorem

Let `E` be a finite-dimensional real inner product space, such as `ℝⁿ`, and consider the quadratic
transport cost `c (x, y) = ‖x - y‖ ^ 2 / 2`. **Brenier's theorem** says that when the source law
`μ` is absolutely continuous with respect to Lebesgue measure and the optimal cost is finite, the
optimal transport plan is unique and is induced by the gradient of a convex function: there is a
proper lower semicontinuous convex `u : E → EReal`, finite and differentiable `μ`-almost
everywhere, such that `x ↦ ∇ u (x)` pushes `μ` to `ν` and is the unique optimal transport map.

The proof avoids Kantorovich duality. The support of an optimal plan of finite cost is
`c`-cyclically monotone (`TauCeti.IsOptimalCoupling.isCyclicallyMonotone_support`), so by
Rockafellar's theorem it lies in the subdifferential graph of a Legendre–Fenchel conjugate `u`
(`TauCeti.IsCyclicallyMonotone.exists_fenchelConjugate_innerₗ_subset_subdifferential`). By
Rademacher's theorem for convex functions
(`TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal`), `u` is differentiable at almost
every point of its effective domain, which contains `μ`-almost every point because the plan has
first marginal `μ`; there the subgradient is the gradient
(`TauCeti.gradient_toReal_eq_of_mem_subdifferential`). So the plan is the graph plan of `∇ u`.
Uniqueness follows by applying this to the sum of two optimal plans, which is again optimal.

Absolute continuity is taken with respect to an arbitrary additive Haar measure `ρ` on `E`, which
for `E = ℝⁿ` covers Lebesgue measure. The real representative `x ↦ (u x).toReal` is the function
whose gradient is taken; where `u` is finite near `x` it agrees with `u` near `x`. The cost
`‖x - y‖ ^ 2 / 2` is the normalisation of the convex-analysis bridges; its optimal plans and maps
are those of `‖x - y‖ ^ 2`, whose transport cost is twice as large
(`TauCeti.transportCost_const_mul`).

## Main statements

* `TauCeti.IsOptimalCoupling.exists_support_subset_subdifferential` — on any real inner product
  space, the support of an optimal quadratic plan of finite cost lies in the subdifferential graph
  of a proper lower semicontinuous convex function;
* `TauCeti.IsOptimalCoupling.exists_eq_graphPlan_gradient` — for an absolutely continuous source,
  an optimal quadratic plan of finite cost is the graph plan of the gradient of such a function,
  differentiable almost everywhere;
* `TauCeti.IsOptimalCoupling.unique` — for an absolutely continuous source and finite optimal
  cost, the optimal quadratic plan is unique;
* `TauCeti.exists_isKantorovichOptimalTransportMap_gradient` — **Brenier's theorem**: the gradient
  of a convex function is the almost everywhere unique optimal transport map, and its graph plan is
  the unique optimal plan;
* `TauCeti.transportCost_norm_sub_sq_div_two_ne_top` — laws with finite second moment have finite
  quadratic transport cost, so Brenier's theorem applies to them.

## References

* Y. Brenier, *Polar factorization and monotone rearrangement of vector-valued functions*, Comm.
  Pure Appl. Math. 44 (1991), 375--417.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  Theorem 2.12.
* R. J. McCann, *Existence and uniqueness of monotone measure-preserving maps*, Duke Math. J. 80
  (1995), 309--323, for the route through cyclical monotonicity of the support.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology Gradient

namespace TauCeti

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace (E × E)] {μ ν : Measure E} {π : Measure (E × E)}

/-- **The support of an optimal quadratic plan lies in a subdifferential graph.** On a real inner
product space, if `π` is an optimal plan of finite cost for `‖x - y‖ ^ 2 / 2` between finite
measures, there is a convex, lower semicontinuous `u : E → EReal` that never takes the value `⊥`
such that every `(x, y)` in the support of `π` has `y ∈ ∂u(x)`. -/
theorem IsOptimalCoupling.exists_support_subset_subdifferential [IsFiniteMeasure μ]
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧ π.support ⊆ {p | p.2 ∈ subdifferential (innerₗ E) u p.1} := by
  -- The function is a Legendre–Fenchel conjugate `g⋆`; it is proper because some point of the
  -- support carries a subgradient, or, for an empty support, because `g` is chosen finite.
  obtain ⟨g, hsub, hbot⟩ : ∃ g : E → EReal,
      π.support ⊆ {p | p.2 ∈ subdifferential (innerₗ E) (fenchelConjugate (innerₗ E) g) p.1} ∧
        ∀ x, fenchelConjugate (innerₗ E) g x ≠ ⊥ := by
    rcases π.support.eq_empty_or_nonempty with hπ | ⟨z, hz⟩
    · exact ⟨fun _ => 0, by simp [hπ],
        fenchelConjugate_ne_bot (innerₗ E) (x := 0) EReal.zero_ne_top⟩
    · have hcm : IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) π.support :=
        (isCyclicallyMonotone_ofReal_iff fun _ => by positivity).1
          (h.isCyclicallyMonotone_support (ENNReal.continuous_ofReal.comp
            (((continuous_fst.sub continuous_snd).norm.pow 2).div_const 2)) hfin)
      obtain ⟨g, hg⟩ := hcm.exists_fenchelConjugate_innerₗ_subset_subdifferential
      exact ⟨g, hg, apply_ne_bot_of_mem_subdifferential (innerₗ E) (hg hz)⟩
  have hcont (x : E) : Continuous (innerₗ E x) :=
    (continuous_const.inner continuous_id).congr fun y => (innerₗ_apply_apply x y).symm
  exact ⟨_, convex_epigraph_fenchelConjugate (innerₗ E) g,
    lowerSemicontinuous_fenchelConjugate (innerₗ E) hcont g, hbot, hsub⟩

end InnerProduct

section SecondMoment

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- Laws with finite second moment have finite transport cost for `‖x - y‖ ^ 2 / 2`: the cost is
at most `‖x - y‖ ^ 2`, whose transport cost is the square of their finite `2`-Wasserstein
distance. -/
theorem transportCost_norm_sub_sq_div_two_ne_top (μ ν : WassersteinSpace 2 E) :
    transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ (transportCost_mono (c' := fun z : E × E ↦ edist z.1 z.2 ^
    (2 : ℝ≥0∞).toReal) fun z => ?_)
  · rw [← wassersteinEDist_rpow_eq_transportCost measurable_edist two_ne_zero
      ENNReal.ofNat_ne_top]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
      (WassersteinSpace.wassersteinEDist_ne_top measurable_edist μ ν)
  · beta_reduce
    rw [ENNReal.toReal_ofNat, edist_dist, dist_eq_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two, Real.rpow_two]
    exact ENNReal.ofReal_le_ofReal (half_le_self (by positivity))

end SecondMoment

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]
  {μ ν : Measure E} {π : Measure (E × E)}

/-- **An optimal quadratic plan is induced by the gradient of a convex function.** Let `π` be an
optimal plan of finite cost for `‖x - y‖ ^ 2 / 2` between finite measures `μ` and `ν` on a
finite-dimensional real inner product space, with `μ` absolutely continuous with respect to an
additive Haar measure. Then there is a convex, lower semicontinuous `u : E → EReal` that never
takes the value `⊥`, is finite near `μ`-almost every point and has differentiable real
representative there, such that `π` is the graph plan of the gradient of that real representative.
-/
theorem IsOptimalCoupling.exists_eq_graphPlan_gradient [IsFiniteMeasure μ] (hμ : μ ≪ ρ)
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      π = graphPlan (∇ fun x => (u x).toReal) μ := by
  obtain ⟨u, hconv, hlsc, hbot, hsub⟩ := h.exists_support_subset_subdifferential hfin
  -- The effective domain of `u` contains the first coordinate of every point of the support,
  -- hence `μ`-almost every point, since `π` has first marginal `μ`.
  have hdom : ∀ᵐ x ∂μ, u x ≠ ⊤ := by
    rw [← h.fst_eq]
    refine (ae_map_iff measurable_fst.aemeasurable
      (hlsc.measurable (measurableSet_singleton ⊤).compl)).2 ?_
    filter_upwards [π.support_mem_ae] with z hz
    exact ne_top_of_mem_subdifferential (innerₗ E) (hsub hz)
  -- Rademacher's theorem holds `ρ`-almost everywhere on the effective domain, hence `μ`-almost
  -- everywhere.
  have hdiff : ∀ᵐ x ∂μ,
      (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x := by
    filter_upwards [hμ.ae_le (ae_eventually_ne_top_and_differentiableAt_toReal hconv hbot), hdom]
      with x hx hx' using hx hx'
  -- Almost every point of `π` lies in its support, so its second coordinate is a subgradient at
  -- the first, which is then the gradient.
  have hgraph : ∀ᵐ z ∂π, z.2 = ∇ (fun x => (u x).toReal) z.1 := by
    rw [← h.fst_eq] at hdiff
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hdiff, π.support_mem_ae]
      with z ⟨hdom, hd⟩ hzs
    exact (gradient_toReal_eq_of_mem_subdifferential (hsub hzs) hdom hd).symm
  refine ⟨u, hconv, hlsc, hbot, hdiff, ?_⟩
  rw [eq_graphPlan_of_ae_snd_eq (measurable_gradient _).aemeasurable hgraph, h.fst_eq]

/-- **Uniqueness of the optimal quadratic plan.** Between finite measures on a finite-dimensional
real inner product space, if the source `μ` is absolutely continuous with respect to an additive
Haar measure and the optimal cost for `‖x - y‖ ^ 2 / 2` is finite, any two optimal plans are
equal. -/
theorem IsOptimalCoupling.unique [IsFiniteMeasure μ] (hμ : μ ≪ ρ) {π' : Measure (E × E)}
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (h' : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π' μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    π = π' := by
  -- The sum `π + π'` is an optimal plan between `μ + μ` and `ν + ν`, so it is carried by the
  -- graph of a single map, and so are `π` and `π'`, which lie below it.
  have hsum := h.add h'
  have hfin' : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (μ + μ) (ν + ν) ≠ ∞ := by
    rw [← hsum.lintegral_eq, lintegral_add_measure, h.lintegral_eq, h'.lintegral_eq]
    exact ENNReal.add_ne_top.2 ⟨hfin, hfin⟩
  obtain ⟨u, -, -, -, -, hgraph⟩ := hsum.exists_eq_graphPlan_gradient (hμ.add_left hμ) hfin'
  have hT := measurable_gradient fun x => (u x).toReal
  have hae : ∀ᵐ z ∂(π + π'), z.2 = ∇ (fun x => (u x).toReal) z.1 :=
    hgraph ▸ ae_snd_eq_graphPlan hT.aemeasurable
  rw [eq_graphPlan_of_ae_snd_eq hT.aemeasurable (ae_mono (Measure.le_add_right le_rfl) hae),
    eq_graphPlan_of_ae_snd_eq hT.aemeasurable (ae_mono (Measure.le_add_left le_rfl) hae),
    h.fst_eq, h'.fst_eq]

/-- **Brenier's theorem.** Let `μ` and `ν` be probability measures on a finite-dimensional real
inner product space `E`, with `μ` absolutely continuous with respect to an additive Haar measure,
and suppose the optimal cost for `‖x - y‖ ^ 2 / 2` is finite, as it is for laws with finite second
moment (`TauCeti.transportCost_norm_sub_sq_div_two_ne_top`). Then there is a convex, lower
semicontinuous `u : E → EReal` that never takes the value `⊥`, is finite near `μ`-almost every
point and has differentiable real representative there, such that the gradient
`T = ∇ (fun x => (u x).toReal)`:

* is an optimal transport map from `μ` to `ν`, attaining the Kantorovich value;
* induces the unique optimal plan: a plan is optimal exactly when it is the graph plan of `T`;
* is the unique optimal transport map up to `μ`-almost everywhere equality. -/
theorem exists_isKantorovichOptimalTransportMap_gradient [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : μ ≪ ρ)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        μ ν (∇ fun x => (u x).toReal) ∧
      (∀ π, IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν ↔
        π = graphPlan (∇ fun x => (u x).toReal) μ) ∧
      ∀ S : E → E,
        IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
          μ ν S → S =ᵐ[μ] ∇ fun x => (u x).toReal := by
  have hc : Continuous fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
    ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const 2)
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling μ ν hc.lowerSemicontinuous
  obtain ⟨u, hconv, hlsc, hbot, hdiff, hgraph⟩ := hπ.exists_eq_graphPlan_gradient hμ hfin
  have hT := measurable_gradient fun x => (u x).toReal
  have hlaw : HasLaw (∇ fun x => (u x).toReal) ν μ :=
    (isCoupling_graphPlan_iff hT.aemeasurable).1 (hgraph ▸ hπ.toIsCoupling)
  have hiff : ∀ S : E → E, HasLaw S ν μ →
      (IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        μ ν S ↔ IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
          (graphPlan S μ) μ ν) := fun S hS =>
    isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hS
      hc.measurable.aemeasurable
  refine ⟨u, hconv, hlsc, hbot, hdiff, (hiff _ hlaw).2 (hgraph ▸ hπ),
    fun σ => ⟨fun hσ => (hσ.unique hμ hπ hfin).trans hgraph, fun hσ => hσ ▸ hgraph ▸ hπ⟩,
    fun S hS => ?_⟩
  exact (graphPlan_eq_graphPlan_iff hS.toHasLaw.aemeasurable hT.aemeasurable).1
    ((((hiff S hS.toHasLaw).1 hS).unique hμ hπ hfin).trans hgraph)

end FiniteDimensional

end TauCeti
