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

When the target `ν` is absolutely continuous as well, the same argument applies to the plan with
exchanged coordinates, which lies in the subdifferential graph of the Legendre–Fenchel conjugate
`u⋆` by conjugate-subgradient reciprocity. So `∇ u⋆` is the optimal transport map from `ν` back to
`μ`, and the two maps are inverse to each other almost everywhere: conjugate potentials give
inverse maps.

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
* `TauCeti.eq_graphPlan_gradient_of_ae_mem_subdifferential` — for an absolutely continuous
  source, a plan concentrated on the subdifferential graph of a proper lower
  semicontinuous convex function is the graph plan of its gradient, differentiable almost
  everywhere;
* `TauCeti.IsOptimalCoupling.exists_eq_graphPlan_gradient` — for an absolutely continuous source,
  an optimal quadratic plan of finite cost is the graph plan of the gradient of such a function,
  differentiable almost everywhere;
* `TauCeti.map_swap_eq_graphPlan_gradient_fenchelConjugate`,
  `TauCeti.IsCoupling.gradient_fenchelConjugate_comp_gradient_ae_eq_id` and
  `TauCeti.IsCoupling.gradient_comp_gradient_fenchelConjugate_ae_eq_id` — for an absolutely
  continuous target, the exchanged plan is the graph plan of the gradient of the conjugate
  potential, and the two gradients are inverse to each other almost everywhere;
* `TauCeti.IsOptimalCoupling.unique` — for an absolutely continuous source and finite optimal
  cost, the optimal quadratic plan is unique;
* `TauCeti.exists_isKantorovichOptimalTransportMap_gradient` — **Brenier's theorem**: the gradient
  of a convex function is the almost everywhere unique optimal transport map, and its graph plan is
  the unique optimal plan;
* `TauCeti.exists_isKantorovichOptimalTransportMap_gradient_and_gradient_fenchelConjugate` —
  **Brenier's theorem with the inverse map**: when both laws are absolutely continuous, the
  gradients of a convex potential and of its conjugate are the optimal transport maps in the two
  directions, and they are inverse to each other almost everywhere;
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
  exact ⟨_, convex_epigraph_fenchelConjugate (innerₗ E) g,
    lowerSemicontinuous_fenchelConjugate_innerₗ g, hbot, hsub⟩

omit [OpensMeasurableSpace (E × E)] in
/-- **Reciprocity along a plan.** If `y ∈ ∂u(x)` for `π`-almost every `(x, y)`, then
`x ∈ ∂u⋆(y)` for almost every `(y, x)` of the plan with exchanged coordinates, where `u⋆` is the
Legendre–Fenchel conjugate of `u` for the inner product. -/
theorem ae_mem_subdifferential_fenchelConjugate_map_swap {u : E → EReal}
    (h : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    ∀ᵐ z ∂π.map Prod.swap,
      z.2 ∈ subdifferential (innerₗ E) (fenchelConjugate (innerₗ E) u) z.1 := by
  -- Read `h` against `(π.map swap).map swap` and pull it back along the outer exchange.
  have hπ : (π.map Prod.swap).map Prod.swap = π :=
    MeasurableEquiv.map_map_symm (ν := π) MeasurableEquiv.prodComm
  rw [← hπ] at h
  filter_upwards [ae_of_ae_map measurable_swap.aemeasurable h] with z hz
  simpa only [flip_innerₗ, Prod.fst_swap, Prod.snd_swap] using
    mem_subdifferential_fenchelConjugate_of_mem_subdifferential (innerₗ E) hz

end InnerProduct

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]
  {μ ν : Measure E} {π : Measure (E × E)}

/-- **A plan on a subdifferential graph is the graph plan of the gradient.** Let `π` be a plan
with first marginal `μ` on a finite-dimensional real inner product space, with `μ` absolutely
continuous with respect to an additive Haar measure, and let `u : E → EReal` be convex, lower
semicontinuous and never `⊥`. If `y ∈ ∂u(x)` for `π`-almost every `(x, y)`, then `u` is finite
near `μ`-almost every point with differentiable real representative there, and `π` is the graph
plan of the gradient of that real representative. -/
theorem eq_graphPlan_gradient_of_ae_mem_subdifferential (hπ : π.fst = μ) (hμ : μ ≪ ρ)
    {u : E → EReal} (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hlsc : LowerSemicontinuous u) (hbot : ∀ x, u x ≠ ⊥)
    (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      π = graphPlan (∇ fun x => (u x).toReal) μ := by
  -- The effective domain of `u` contains the first coordinate of almost every point of `π`,
  -- hence `μ`-almost every point, since `π` has first marginal `μ`.
  have hdom : ∀ᵐ x ∂μ, u x ≠ ⊤ := by
    rw [← hπ]
    refine (ae_map_iff measurable_fst.aemeasurable
      (hlsc.measurable (measurableSet_singleton ⊤).compl)).2 ?_
    filter_upwards [hsub] with z hz
    exact ne_top_of_mem_subdifferential (innerₗ E) hz
  -- Rademacher's theorem holds `ρ`-almost everywhere on the effective domain, hence `μ`-almost
  -- everywhere.
  have hdiff : ∀ᵐ x ∂μ,
      (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x := by
    filter_upwards [hμ.ae_le (ae_eventually_ne_top_and_differentiableAt_toReal hconv hbot), hdom]
      with x hx hx' using hx hx'
  -- At almost every point of `π` the second coordinate is a subgradient at the first, which is
  -- then the gradient.
  have hgraph : ∀ᵐ z ∂π, z.2 = ∇ (fun x => (u x).toReal) z.1 := by
    rw [← hπ] at hdiff
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hdiff, hsub] with z ⟨hdom, hd⟩ hz
    exact (gradient_toReal_eq_of_mem_subdifferential hz hdom hd).symm
  refine ⟨hdiff, ?_⟩
  rw [eq_graphPlan_of_ae_snd_eq (measurable_gradient _).aemeasurable hgraph, hπ]

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
  -- Almost every point of `π` lies in its support, so it lies in the subdifferential graph.
  have hsub' : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1 := by
    filter_upwards [π.support_mem_ae] with z hz using hsub hz
  obtain ⟨hdiff, hgraph⟩ :=
    eq_graphPlan_gradient_of_ae_mem_subdifferential h.fst_eq hμ hconv hlsc hbot hsub'
  exact ⟨u, hconv, hlsc, hbot, hdiff, hgraph⟩

/-- **The exchanged plan is the graph plan of the gradient of the conjugate.** Let `π` be a plan
with second marginal `ν` on a finite-dimensional real inner product space, with `ν` absolutely
continuous with respect to an additive Haar measure, and let `u : E → EReal` be any function such
that `y ∈ ∂u(x)` for `π`-almost every `(x, y)`. Then the Legendre–Fenchel conjugate `u⋆` of `u`
for the inner product is finite near `ν`-almost every point with differentiable real
representative there, and the plan with exchanged coordinates is the graph plan over `ν` of the
gradient of that real representative. -/
theorem map_swap_eq_graphPlan_gradient_fenchelConjugate (hπ : π.snd = ν) (hν : ν ≪ ρ)
    {u : E → EReal} (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    (∀ᵐ y ∂ν, (∀ᶠ y' in 𝓝 y, fenchelConjugate (innerₗ E) u y' ≠ ⊤) ∧
        DifferentiableAt ℝ (fun y' => (fenchelConjugate (innerₗ E) u y').toReal) y) ∧
      π.map Prod.swap = graphPlan (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) ν := by
  rcases eq_zero_or_neZero π with rfl | hne
  · obtain rfl : ν = 0 := hπ.symm.trans Measure.snd_zero
    simp
  -- `u` is finite somewhere since `π` is not zero, so `u⋆` never takes the value `⊥`.
  have := ae_neBot.2 hne.out
  obtain ⟨z, hz⟩ := hsub.exists
  exact eq_graphPlan_gradient_of_ae_mem_subdifferential (Measure.fst_map_swap.trans hπ) hν
    (convex_epigraph_fenchelConjugate (innerₗ E) u) (lowerSemicontinuous_fenchelConjugate_innerₗ u)
    (fenchelConjugate_ne_bot (innerₗ E) (ne_top_of_mem_subdifferential (innerₗ E) hz))
    (ae_mem_subdifferential_fenchelConjugate_map_swap hsub)

/-- **Conjugate potentials give inverse maps.** Let `π` couple `μ` and `ν`, both absolutely
continuous with respect to an additive Haar measure on a finite-dimensional real inner product
space, and let `u : E → EReal` be convex, lower semicontinuous and never `⊥`, with `y ∈ ∂u(x)`
for `π`-almost every `(x, y)`. Then the gradient of the conjugate `u⋆` is a left inverse of the
gradient of `u`, `μ`-almost everywhere. -/
theorem IsCoupling.gradient_fenchelConjugate_comp_gradient_ae_eq_id (hπ : IsCoupling π μ ν)
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) {u : E → EReal} (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hlsc : LowerSemicontinuous u) (hbot : ∀ x, u x ≠ ⊥)
    (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) ∘ (∇ fun x => (u x).toReal) =ᵐ[μ] id := by
  have h₁ :=
    (eq_graphPlan_gradient_of_ae_mem_subdifferential hπ.fst_eq hμ hconv hlsc hbot hsub).2
  have h₂ := (map_swap_eq_graphPlan_gradient_fenchelConjugate hπ.snd_eq hν hsub).2
  rw [h₁] at h₂
  exact (comp_ae_eq_id_of_map_swap_graphPlan_eq (measurable_gradient _).aemeasurable
    (measurable_gradient _).aemeasurable h₂).1

/-- **Conjugate potentials give inverse maps.** Let `π` couple `μ` and `ν`, both absolutely
continuous with respect to an additive Haar measure on a finite-dimensional real inner product
space, and let `u : E → EReal` be convex, lower semicontinuous and never `⊥`, with `y ∈ ∂u(x)`
for `π`-almost every `(x, y)`. Then the gradient of `u` is a left inverse of the gradient of the
conjugate `u⋆`, `ν`-almost everywhere. -/
theorem IsCoupling.gradient_comp_gradient_fenchelConjugate_ae_eq_id (hπ : IsCoupling π μ ν)
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) {u : E → EReal} (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hlsc : LowerSemicontinuous u) (hbot : ∀ x, u x ≠ ⊥)
    (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    (∇ fun x => (u x).toReal) ∘ (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) =ᵐ[ν] id := by
  have h₁ :=
    (eq_graphPlan_gradient_of_ae_mem_subdifferential hπ.fst_eq hμ hconv hlsc hbot hsub).2
  have h₂ := (map_swap_eq_graphPlan_gradient_fenchelConjugate hπ.snd_eq hν hsub).2
  rw [h₁] at h₂
  exact (comp_ae_eq_id_of_map_swap_graphPlan_eq (measurable_gradient _).aemeasurable
    (measurable_gradient _).aemeasurable h₂).2

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

/-- **Brenier's theorem with the inverse map.** Let `μ` and `ν` be probability measures on a
finite-dimensional real inner product space `E`, both absolutely continuous with respect to an
additive Haar measure, and suppose the optimal cost for `‖x - y‖ ^ 2 / 2` is finite. Then there is
a convex, lower semicontinuous `u : E → EReal` that never takes the value `⊥` such that `u` is
finite near `μ`-almost every point and its Legendre–Fenchel conjugate `u⋆` is finite near
`ν`-almost every point, both with differentiable real representatives there, and:

* the gradient `∇ u` is an optimal transport map from `μ` to `ν`;
* the gradient `∇ u⋆` is an optimal transport map from `ν` to `μ`;
* the two maps are inverse to each other, `∇ u⋆ ∘ ∇ u = id` `μ`-almost everywhere and
  `∇ u ∘ ∇ u⋆ = id` `ν`-almost everywhere.

The almost everywhere uniqueness of the optimal maps and plans in each direction is recorded
separately, in `TauCeti.exists_isKantorovichOptimalTransportMap_gradient` and
`TauCeti.IsOptimalCoupling.unique`. -/
theorem exists_isKantorovichOptimalTransportMap_gradient_and_gradient_fenchelConjugate
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμ : μ ≪ ρ) (hν : ν ≪ ρ)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      (∀ᵐ y ∂ν, (∀ᶠ y' in 𝓝 y, fenchelConjugate (innerₗ E) u y' ≠ ⊤) ∧
        DifferentiableAt ℝ (fun y' => (fenchelConjugate (innerₗ E) u y').toReal) y) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        μ ν (∇ fun x => (u x).toReal) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        ν μ (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) ∧
      (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) ∘ (∇ fun x => (u x).toReal)
        =ᵐ[μ] id ∧
      (∇ fun x => (u x).toReal) ∘ (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal)
        =ᵐ[ν] id := by
  have hc : Continuous fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
    ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const 2)
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling μ ν hc.lowerSemicontinuous
  obtain ⟨u, hconv, hlsc, hbot, hsub⟩ := hπ.exists_support_subset_subdifferential hfin
  have hsub' : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1 := by
    filter_upwards [π.support_mem_ae] with z hz using hsub hz
  obtain ⟨hdiff, hgraph⟩ :=
    eq_graphPlan_gradient_of_ae_mem_subdifferential hπ.fst_eq hμ hconv hlsc hbot hsub'
  obtain ⟨hdiff', hgraph'⟩ :=
    map_swap_eq_graphPlan_gradient_fenchelConjugate hπ.snd_eq hν hsub'
  -- The quadratic cost is symmetric, so the exchanged plan is optimal from `ν` to `μ`.
  have hswap : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (π.map Prod.swap) ν μ := by
    have hcs : (fun z : E × E => ENNReal.ofReal (‖z.swap.1 - z.swap.2‖ ^ 2 / 2)) =
        fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) := by
      ext z
      rw [Prod.fst_swap, Prod.snd_swap, norm_sub_rev]
    exact hcs ▸ hπ.swap hc.measurable
  have hT := measurable_gradient fun x => (u x).toReal
  have hS := measurable_gradient fun y => (fenchelConjugate (innerₗ E) u y).toReal
  have hlaw : HasLaw (∇ fun x => (u x).toReal) ν μ :=
    (isCoupling_graphPlan_iff hT.aemeasurable).1 (hgraph ▸ hπ.toIsCoupling)
  have hlaw' : HasLaw (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) μ ν :=
    (isCoupling_graphPlan_iff hS.aemeasurable).1 (hgraph' ▸ hπ.toIsCoupling.swap)
  refine ⟨u, hconv, hlsc, hbot, hdiff, hdiff',
    (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hlaw
      hc.measurable.aemeasurable).2 (hgraph ▸ hπ),
    (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hlaw'
      hc.measurable.aemeasurable).2 (hgraph' ▸ hswap),
    hπ.toIsCoupling.gradient_fenchelConjugate_comp_gradient_ae_eq_id hμ hν hconv hlsc hbot hsub',
    hπ.toIsCoupling.gradient_comp_gradient_fenchelConjugate_ae_eq_id hμ hν hconv hlsc hbot hsub'⟩

end FiniteDimensional

end TauCeti
