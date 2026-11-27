/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Convex.CCHypersurface.Regular.Basic
public import TauCeti.Analysis.Convex.Differentiability
public import TauCeti.Analysis.Convex.MongeAmpere.Transport
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Mixture
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Quadratic.Optimality
public import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Monge
import TauCeti.Analysis.Convex.CCHypersurface.Regular.Differentiability
import TauCeti.Analysis.Convex.CCHypersurface.Regular.SufficientConditions
import TauCeti.Analysis.Convex.FenchelMoreau
import TauCeti.Analysis.Convex.MongeAmpere.Decomposition
import TauCeti.Analysis.Convex.MongeAmpere.Interpolation
import TauCeti.MeasureTheory.Constructions.BorelSpace.Prod
import TauCeti.MeasureTheory.OptimalTransport.Existence.Finite

/-!
# Brenier's theorem

Let `E` be a finite-dimensional real inner product space, such as `ℝⁿ`, and consider the quadratic
transport cost `c (x, y) = ‖x - y‖ ^ 2 / 2`. **Brenier's theorem** says that when the source law
`μ` is finite and `c - c`-regular (`TauCeti.IsCCRegular`, e.g. a.c.) and the optimal cost is
finite, the optimal transport plan is unique and is induced by the gradient of a convex function:
there is a lower semicontinuous convex `u : E → EReal` never taking `⊥`, finite and differentiable
`μ`-almost everywhere, such that `x ↦ ∇ u (x)` pushes `μ` to `ν` and is the `μ`-almost everywhere
unique optimal transport map.

The proof avoids Kantorovich duality. The support of an optimal plan of finite cost is
`c`-cyclically monotone (`TauCeti.IsOptimalCoupling.isCyclicallyMonotone_support`), so by
Rockafellar's theorem it lies in the subdifferential graph of a Legendre–Fenchel conjugate `u`
(`TauCeti.IsCyclicallyMonotone.exists_fenchelConjugate_innerₗ_subset_subdifferential`). By
Zajíček's differentiability theorem for convex functions
(`TauCeti.IsCCRegular.ae_eventually_ne_top_and_differentiableAt_toReal`), `u` is differentiable at
`μ`-almost
every point of its effective domain, which contains `μ`-almost every point because the plan has
first marginal `μ`; there the subgradient is the gradient
(`TauCeti.gradient_toReal_eq_of_mem_subdifferential`). So the plan is the graph plan of `∇ u`.
Uniqueness follows by applying this to the sum of two optimal plans, which is again optimal.

When the target `ν` is `c - c`-regular as well, the same argument applies to the plan with
exchanged coordinates, which lies in the subdifferential graph of the Legendre–Fenchel conjugate
`u⋆` by conjugate-subgradient reciprocity. So `∇ u⋆` is the optimal transport map from `ν` back to
`μ`, and the two maps are inverse to each other almost everywhere: conjugate potentials give
inverse maps.

Conversely, between finite measures with finite second moments on a real inner product space with
open sets measurable, every plan concentrated on the subdifferential graph of a function
`u : E → EReal` is optimal (`TauCeti.MeasureTheory.OptimalTransport.Cost.Quadratic.Optimality`,
requiring open sets in `E × E` to be measurable for support and a.e. concentration results), and so
is every transport map selecting a subgradient of `u` almost everywhere — in particular, on a
Hilbert space with open sets measurable, the gradient `∇ u` of a convex function `u` that never
takes `⊥`, is finite source-almost everywhere, and has differentiable real representative
`u.toReal` there.
Expanding the square, the quadratic cost of a plan is a fixed second-moment term minus its
correlation `∫ ⟪x, y⟫`, and on the subdifferential graph of a Legendre–Fenchel conjugate the
Fenchel–Young inequality `⟪x, y⟫ ≤ u x + u⋆ y` is an equality. The real representatives of `u` and
`u⋆` are integrable, being squeezed between affine functions and the correlation, so integrating
Fenchel–Young against any other coupling bounds its correlation by that of the given plan. A
general `u` is first replaced, through Rockafellar's theorem, by a conjugate whose subdifferential
graph contains its own. With the forward direction this gives the Knott–Smith optimality criterion
on second-countable spaces (where open sets in both `E` and `E × E` are measurable).

For Monge–Ampère results, absolute continuity uses an arbitrary additive Haar measure `ρ`, which
for `E = ℝⁿ` covers Lebesgue measure. The real representative `x ↦ (u x).toReal` is the function
whose gradient is taken; where `u` is finite near `x` it agrees with `u` near `x`. The cost
`‖x - y‖ ^ 2 / 2` is the normalisation of the convex-analysis bridges; its optimal plans and maps
are those of `‖x - y‖ ^ 2`, whose transport cost is twice as large
(`TauCeti.transportCost_const_mul`).

## Main statements

* `TauCeti.eq_graphPlan_gradient_of_ae_mem_subdifferential_of_ae_differentiableAt` — on a real
  Hilbert space, a plan concentrated on the subdifferential graph of a function `u` that avoids
  `⊤` near `μ`-almost every point with differentiable real representative there is the graph plan
  of `∇ u`;
* `TauCeti.eq_graphPlan_gradient_of_ae_mem_subdifferential` — for a `c - c`-regular
  source, a plan concentrated on the subdifferential graph of a convex function
  `u : E → EReal` (without assuming lower semicontinuity) is the graph plan of its gradient,
  differentiable almost everywhere;
* `TauCeti.IsOptimalCoupling.exists_eq_graphPlan_gradient` — for a finite `c - c`-regular source,
  an optimal quadratic plan of finite cost is the graph plan of the gradient of a lower
  semicontinuous convex function never taking `⊥`, differentiable almost everywhere;
* `TauCeti.map_swap_eq_graphPlan_gradient_fenchelConjugate` — for a `c - c`-regular target `ν`,
  when a plan `π` with second marginal `ν` is concentrated on the subdifferential graph of `u`, the
  exchanged plan is the graph plan of the gradient of the conjugate potential `u⋆`;
* `TauCeti.IsCoupling.gradient_fenchelConjugate_comp_gradient_ae_eq_id` and
  `TauCeti.IsCoupling.gradient_comp_gradient_fenchelConjugate_ae_eq_id` — when a coupling `π`
  between `c - c`-regular marginals is concentrated on the subdifferential graph of `u` and `u` has
  convex real epigraph, the gradients of `u` and its conjugate `u⋆` are inverse to each other
  almost everywhere;
* `TauCeti.IsOptimalCoupling.unique` — for a finite `c - c`-regular source and finite optimal
  cost, the optimal quadratic plan is unique;
* `TauCeti.IsCCRegular.isOptimalCoupling_graphPlan_gradient` — for a finite `c - c`-regular
  source and a finite target, both with finite second moments, if a convex potential avoids `⊤`
  source-a.e. and the gradient of its real representative has the prescribed target law, its graph
  plan is optimal without assuming `u ≠ ⊥` or a.e. differentiability;
* `TauCeti.gradient_ae_eq_gradient_of_hasLaw` — **uniqueness of the monotone rearrangement**:
  two gradients of convex functions (with `u, v ≠ ⊤` a.e.) pushing a finite `c - c`-regular `μ` to
  the same law agree `μ`-almost everywhere, when both laws have finite second moments;
* `TauCeti.exists_isKantorovichOptimalTransportMap_gradient` — **Brenier's theorem**: for a finite
  `c - c`-regular `μ` and a target `ν` at finite quadratic transport cost, the gradient of a convex
  function is the almost everywhere unique optimal transport map, and its graph plan is the unique
  optimal plan;
* `TauCeti.exists_isKantorovichOptimalTransportMap_gradient_and_gradient_fenchelConjugate` —
  **Brenier's theorem with the inverse map**: when both finite marginals are `c - c`-regular and the
  quadratic transport cost is finite, the gradients of a convex potential and of its conjugate are
  the optimal transport maps in the two directions, and they are inverse to each other almost
  everywhere;
* `TauCeti.IsCCRegular.transportCost_smul_add_smul_lt` — strict convexity of the quadratic transport
  cost on targets at finite quadratic transport cost from a finite `c - c`-regular source;
* `TauCeti.exists_isKantorovichOptimalTransportMap_gradient_and_mongeAmpereMeasure_eq` — when `μ`
  is a probability measure, both `μ` and `ν` are absolutely continuous with respect to an additive
  Haar measure, and the optimal quadratic cost is finite, the Brenier potential `u` is a weak
  solution of its transport equation: its Monge–Ampère measure weighted by `ν` is `μ`, and `ν` is
  carried by the subgradient image of the interior of its effective domain;
* `TauCeti.exists_isKantorovichOptimalTransportMap_gradient_and_mongeAmpereMeasure_eq_withDensity` —
  for a `c - c`-regular source probability measure at finite optimal cost, when the target has
  density `g` positive almost everywhere on a closed convex set `K` carrying it, there is a
  Brenier potential `u` with all its slopes in `K`, and it is an Aleksandrov solution:
  `MA_u = (g ∘ ∇u)⁻¹ μ`;
* `TauCeti.exists_isKantorovichOptimalTransportMap_gradient_and_rnDeriv_ae_eq` — when `μ` is a
  probability measure, both `μ` and `ν` are absolutely continuous with respect to an additive Haar
  measure `ρ` with densities `g₀` and `g₁`, and the optimal quadratic cost is finite, the Brenier
  potential `u` solves the Monge–Ampère equation `g₀ x = g₁ (∇ u x) det (D²u x)` for `ρ`-almost
  every `x` in the interior of the effective domain of `u`, with `g₀ x = 0` for `ρ`-almost every
  `x` outside it and `D²u` the Alexandrov Hessian;
* `exists_isKantorovichOptimalTransportMap_gradient_and_rnDeriv_ae_eq_map_smul_add_smul_gradient` —
  when `μ` is a probability measure absolutely continuous with respect to an additive Haar measure
  `ρ` with density `g₀` and the optimal quadratic cost is finite (with arbitrary target `ν`), the
  interpolating maps `Tₜ x = (1 - t) • x + t • ∇ u x` push `μ`, for `0 ≤ t < 1`, to absolutely
  continuous laws with densities `gₜ`, and the Jacobian equation
  `g₀ x = det ((1 - t) • 1 + t • D²u x) gₜ (Tₜ x)` holds for `ρ`-almost every `x` in the interior
  of the effective domain of `u`, with `g₀ x = 0` for `ρ`-almost every `x` outside it;
* `TauCeti.isKantorovichOptimalTransportMap_of_ae_mem_subdifferential` and
  `TauCeti.isKantorovichOptimalTransportMap_gradient` — the converse of Brenier's theorem: when
  open sets in `E` are measurable, a transport map selecting subgradients of a function almost
  everywhere — such as the gradient `∇ u` of a convex function never taking `⊥` that is finite
  source-almost everywhere and has differentiable real representative `u.toReal` there — is an
  optimal transport map;
* `TauCeti.IsCoupling.isOptimalCoupling_iff_exists_ae_mem_subdifferential` — the **Knott–Smith
  optimality criterion**: on a second-countable space (so open sets in `E × E` are measurable), a
  plan between marginals with finite second moments is optimal exactly when it is concentrated on
  the subdifferential graph of a proper lower semicontinuous convex function.

## References

* M. Knott and C. S. Smith, *On the optimal mapping of distributions*, J. Optim. Theory Appl. 43
  (1984), 39--49, for the optimality criterion.
* Y. Brenier, *Polar factorization and monotone rearrangement of vector-valued functions*, Comm.
  Pure Appl. Math. 44 (1991), 375--417.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  Theorem 2.12, whose proof of the converse direction is followed here.
* R. J. McCann, *Existence and uniqueness of monotone measure-preserving maps*, Duke Math. J. 80
  (1995), 309--323, for the route through cyclical monotonicity of the support.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology Gradient RealInnerProductSpace

namespace TauCeti

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace (E × E)] {μ ν : Measure E} {π σ : Measure (E × E)}

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

omit [OpensMeasurableSpace (E × E)] in
/-- **Subgradient selections are optimal transport maps for the quadratic cost.** Let `μ` and `ν`
be finite measures with finite second moments on a real inner product space with open sets
measurable, `u : E → EReal` any function, and `T` a transport map from `μ` to `ν` with
`T x ∈ ∂u(x)` for `μ`-almost every `x`. Then `T` is an optimal transport map for the cost
`‖x - y‖ ^ 2 / 2`, attaining the Kantorovich value. -/
theorem isKantorovichOptimalTransportMap_of_ae_mem_subdifferential
    [OpensMeasurableSpace E] [IsFiniteMeasure μ] (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν)
    {T : E → E} (hT : HasLaw T ν μ)
    {u : E → EReal} (h : ∀ᵐ x ∂μ, T x ∈ subdifferential (innerₗ E) u x) :
    IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      μ ν T := by
  have hγ := isCoupling_graphPlan hT
  -- Measurability on `E × E` comes from the marginals, pulled back along the projections.
  have h₁ : AEStronglyMeasurable (fun z : E × E => z.1) (graphPlan T μ) :=
    hμ.aestronglyMeasurable.comp_measurePreserving hγ.measurePreserving_fst
  have h₂ : AEStronglyMeasurable (fun z : E × E => z.2) (graphPlan T μ) :=
    hν.aestronglyMeasurable.comp_measurePreserving hγ.measurePreserving_snd
  have hT₁ : AEStronglyMeasurable (fun z : E × E => T z.1) (graphPlan T μ) :=
    ((hT.map_eq ▸ hν.aestronglyMeasurable).comp_aemeasurable hT.aemeasurable).comp_measurePreserving
      hγ.measurePreserving_fst
  refine (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hT
    (continuous_ofReal_norm_sub_sq_div_two.comp_aestronglyMeasurable
      (h₁.prodMk h₂)).aemeasurable).2
    (hγ.isOptimalCoupling_of_ae_mem_subdifferential hμ hν (u := u) ?_)
  -- The graph plan is carried by the graph of `T`, a null-measurable set.
  have hgraph : ∀ᵐ z ∂graphPlan T μ, z.2 = T z.1 := by
    rw [ae_iff, graphPlan_def, Measure.map_apply₀ (aemeasurable_prodMk_self hT.aemeasurable)
      (graphPlan_def T μ ▸ (h₂.nullMeasurableSet_eq_fun hT₁).compl)]
    simp
  rw [← hγ.measurePreserving_fst.map_eq] at h
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable h, hgraph] with z hz hz'
  rwa [hz']

omit [OpensMeasurableSpace (E × E)] in
/-- **Gradients of convex functions are optimal transport maps for the quadratic cost.** Let `μ`
and `ν` be finite measures with finite second moments on a real Hilbert space with open sets
measurable, and let `u : E → EReal` be convex, never `⊥`, and finite with differentiable real
representative `u.toReal` at `μ`-almost every point. If the gradient `∇ u` pushes `μ` to `ν`, it is
an optimal transport map for the cost `‖x - y‖ ^ 2 / 2`, attaining the Kantorovich value. This is
the converse of Brenier's theorem `TauCeti.exists_isKantorovichOptimalTransportMap_gradient`. -/
theorem isKantorovichOptimalTransportMap_gradient [OpensMeasurableSpace E] [CompleteSpace E]
    [IsFiniteMeasure μ] (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) {u : E → EReal}
    (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hbot : ∀ x, u x ≠ ⊥)
    (hdiff : ∀ᵐ x ∂μ, u x ≠ ⊤ ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x)
    (hT : HasLaw (∇ fun x => (u x).toReal) ν μ) :
    IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      μ ν (∇ fun x => (u x).toReal) :=
  isKantorovichOptimalTransportMap_of_ae_mem_subdifferential hμ hν hT
    (hdiff.mono fun _ hx => gradient_toReal_mem_subdifferential hconv hbot hx.1 hx.2)

/-- **The Knott–Smith optimality criterion.** On a second-countable real inner product space (so
open sets in `E × E` are measurable), a coupling `π` of finite measures `μ` and `ν` with finite
second moments is an optimal plan for the cost `‖x - y‖ ^ 2 / 2` exactly when there is a proper
(never `⊥`, and finite somewhere) convex, lower semicontinuous `u : E → EReal` such that
`y ∈ ∂u(x)` for `π`-almost every `(x, y)`. -/
theorem IsCoupling.isOptimalCoupling_iff_exists_ae_mem_subdifferential
    [SecondCountableTopology E] [IsFiniteMeasure μ] (hπ : IsCoupling π μ ν) (hμ : MemLp id 2 μ)
    (hν : MemLp id 2 ν) :
    IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν ↔
      ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
        (∀ x, u x ≠ ⊥) ∧ (∃ x, u x ≠ ⊤) ∧ ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1 := by
  have : OpensMeasurableSpace E := OpensMeasurableSpace.of_prod_left (Y := E)
  refine ⟨fun h => ?_, fun ⟨_, _, _, _, _, hu⟩ =>
    hπ.isOptimalCoupling_of_ae_mem_subdifferential hμ hν hu⟩
  have hfin := h.toIsCoupling.transportCost_norm_sub_sq_div_two_ne_top hμ hν
  exact h.exists_ae_mem_subdifferential hfin

end InnerProduct

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {π : Measure (E × E)}

/-- **A plan on a subdifferential graph is the graph plan of the gradient** on a real Hilbert space
under an almost-everywhere differentiability hypothesis on `u` along `μ`. -/
theorem eq_graphPlan_gradient_of_ae_mem_subdifferential_of_ae_differentiableAt (hπ : π.fst = μ)
    {u : E → EReal}
    (hu_diff : (∀ x, u x ≠ ⊥) → ∀ᵐ x ∂μ, u x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x)
    (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      π = graphPlan (∇ fun x => (u x).toReal) μ := by
  -- The empty plan is trivial; otherwise a subgradient exists somewhere, so `u` is never `⊥`.
  rcases eq_zero_or_neZero π with rfl | hne
  · obtain rfl : μ = 0 := hπ.symm.trans Measure.fst_zero
    simp
  have := ae_neBot.2 hne.out
  obtain ⟨z, hz⟩ := hsub.exists
  have hbot : ∀ x, u x ≠ ⊥ := apply_ne_bot_of_mem_subdifferential (innerₗ E) hz
  -- Pull the a.e. differentiability implication back to `π`; subgradient membership puts `z.1`
  -- in the open set `interior {x | u x ≠ ⊤}`, which pushes forward to `μ`.
  have hμ_ev : ∀ᵐ x ∂μ, u x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x := hu_diff hbot
  have hπ_int : ∀ᵐ z ∂π, z.1 ∈ interior {x | u x ≠ ⊤} := by
    have hπ_ev := hπ ▸ hμ_ev
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hπ_ev, hsub] with z hz hzs
    exact mem_interior_iff_mem_nhds.2 (hz (ne_top_of_mem_subdifferential (innerₗ E) hzs)).1
  have hdom : ∀ᵐ x ∂μ, x ∈ interior {x | u x ≠ ⊤} := by
    rw [← hπ]
    exact (ae_map_iff measurable_fst.aemeasurable isOpen_interior.measurableSet).2 hπ_int
  have hdiff : ∀ᵐ x ∂μ,
      (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x := by
    filter_upwards [hμ_ev, hdom] with x hx hx' using hx (interior_subset hx')
  -- At almost every point of `π` the second coordinate is a subgradient at the first, which is
  -- then the gradient.
  have hgraph : ∀ᵐ z ∂π, z.2 = ∇ (fun x => (u x).toReal) z.1 := by
    rw [← hπ] at hdiff
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hdiff, hsub] with z ⟨hdom, hd⟩ hz
    exact (gradient_toReal_eq_of_mem_subdifferential hz hdom hd).symm
  refine ⟨hdiff, ?_⟩
  rw [eq_graphPlan_of_ae_snd_eq (measurable_gradient _).aemeasurable hgraph, hπ]

end Hilbert

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E} {π : Measure (E × E)}

/-- **A plan on a subdifferential graph is the graph plan of the gradient.** Let `π` be a plan
with first marginal `μ` on a finite-dimensional real inner product space, with `μ` `c - c`-regular,
and let `u : E → EReal` have convex real epigraph.
If `y ∈ ∂u(x)` for `π`-almost every `(x, y)`, then `u ≠ ⊤`
near `μ`-almost every point with differentiable real representative there, and `π` is the graph
plan of the gradient of that real representative. -/
theorem eq_graphPlan_gradient_of_ae_mem_subdifferential (hπ : π.fst = μ) (hμ : IsCCRegular μ)
    {u : E → EReal} (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      π = graphPlan (∇ fun x => (u x).toReal) μ :=
  eq_graphPlan_gradient_of_ae_mem_subdifferential_of_ae_differentiableAt hπ
    (fun _ => hμ.ae_eventually_ne_top_and_differentiableAt_toReal hconv) hsub

/-- **An optimal quadratic plan is induced by the gradient of a convex function.** Let `π` be an
optimal plan of finite cost for `‖x - y‖ ^ 2 / 2` between finite measures `μ` and `ν` on a
finite-dimensional real inner product space, with `μ` `c - c`-regular.
Then there is a convex, lower semicontinuous `u : E → EReal` that never
takes the value `⊥`, is finite near `μ`-almost every point and has differentiable real
representative there, such that `π` is the graph plan of the gradient of that real representative.
-/
theorem IsOptimalCoupling.exists_eq_graphPlan_gradient [IsFiniteMeasure μ] (hμ : IsCCRegular μ)
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      π = graphPlan (∇ fun x => (u x).toReal) μ := by
  obtain ⟨u, hconv, hlsc, hbot, -, hsub⟩ := h.exists_ae_mem_subdifferential hfin
  obtain ⟨hdiff, hgraph⟩ := eq_graphPlan_gradient_of_ae_mem_subdifferential h.fst_eq hμ hconv hsub
  exact ⟨u, hconv, hlsc, hbot, hdiff, hgraph⟩

/-- **The exchanged plan is the graph plan of the gradient of the conjugate.** Let `π` be a plan
with second marginal `ν` on a finite-dimensional real inner product space, with `ν` `c - c`-regular,
and let `u : E → EReal` be any function such
that `y ∈ ∂u(x)` for `π`-almost every `(x, y)`. Then the Legendre–Fenchel conjugate `u⋆` of `u`
for the inner product satisfies `u⋆ ≠ ⊤` near `ν`-almost every point with differentiable real
representative there, and the plan with exchanged coordinates is the graph plan over `ν` of the
gradient of that real representative. -/
theorem map_swap_eq_graphPlan_gradient_fenchelConjugate (hπ : π.snd = ν) (hν : IsCCRegular ν)
    {u : E → EReal} (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    (∀ᵐ y ∂ν, (∀ᶠ y' in 𝓝 y, fenchelConjugate (innerₗ E) u y' ≠ ⊤) ∧
        DifferentiableAt ℝ (fun y' => (fenchelConjugate (innerₗ E) u y').toReal) y) ∧
      π.map Prod.swap = graphPlan (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) ν := by
  exact eq_graphPlan_gradient_of_ae_mem_subdifferential (Measure.fst_map_swap.trans hπ) hν
    (convex_epigraph_fenchelConjugate (innerₗ E) u)
    (ae_mem_subdifferential_fenchelConjugate_map_swap hsub)

private theorem IsCoupling.gradient_fenchelConjugate_comp_ae_eq_id_and (hπ : IsCoupling π μ ν)
    (hμ : IsCCRegular μ) (hν : IsCCRegular ν) {u : E → EReal}
    (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    ((∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) ∘ (∇ fun x => (u x).toReal) =ᵐ[μ] id) ∧
      ((∇ fun x => (u x).toReal) ∘ (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) =ᵐ[ν]
        id) := by
  have h₁ :=
    (eq_graphPlan_gradient_of_ae_mem_subdifferential hπ.fst_eq hμ hconv hsub).2
  have h₂ := (map_swap_eq_graphPlan_gradient_fenchelConjugate hπ.snd_eq hν hsub).2
  rw [h₁] at h₂
  exact comp_ae_eq_id_of_map_swap_graphPlan_eq (measurable_gradient _).aemeasurable
    (measurable_gradient _).aemeasurable h₂

/-- **Conjugate potentials give inverse maps.** Let `π` couple `μ` and `ν`, both `c - c`-regular
on a finite-dimensional real inner product
space, and let `u : E → EReal` have convex real epigraph, with `y ∈ ∂u(x)`
for `π`-almost every `(x, y)`. Then the gradient of the conjugate `u⋆` is a left inverse of the
gradient of `u`, `μ`-almost everywhere. -/
theorem IsCoupling.gradient_fenchelConjugate_comp_gradient_ae_eq_id (hπ : IsCoupling π μ ν)
    (hμ : IsCCRegular μ) (hν : IsCCRegular ν) {u : E → EReal}
    (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) ∘ (∇ fun x => (u x).toReal) =ᵐ[μ] id :=
  (hπ.gradient_fenchelConjugate_comp_ae_eq_id_and hμ hν hconv hsub).1

/-- **Conjugate potentials give inverse maps.** Let `π` couple `μ` and `ν`, both `c - c`-regular
on a finite-dimensional real inner product
space, and let `u : E → EReal` have convex real epigraph, with `y ∈ ∂u(x)`
for `π`-almost every `(x, y)`. Then the gradient of `u` is a left inverse of the gradient of the
conjugate `u⋆`, `ν`-almost everywhere. -/
theorem IsCoupling.gradient_comp_gradient_fenchelConjugate_ae_eq_id (hπ : IsCoupling π μ ν)
    (hμ : IsCCRegular μ) (hν : IsCCRegular ν) {u : E → EReal}
    (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    (∇ fun x => (u x).toReal) ∘ (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) =ᵐ[ν] id :=
  (hπ.gradient_fenchelConjugate_comp_ae_eq_id_and hμ hν hconv hsub).2

/-- **Uniqueness of the optimal quadratic plan.** Between finite measures on a finite-dimensional
real inner product space, if the source `μ` is `c - c`-regular
and the optimal cost for `‖x - y‖ ^ 2 / 2` is finite, any two optimal plans are
equal. -/
theorem IsOptimalCoupling.unique [IsFiniteMeasure μ] (hμ : IsCCRegular μ) {π' : Measure (E × E)}
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (h' : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π' μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    π = π' :=
  h.eq_of_add_eq_graphPlan h' fun hsum => by
    obtain ⟨u, -, -, -, -, hgraph⟩ := hsum.exists_eq_graphPlan_gradient (hμ.add hμ)
      (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin, hfin⟩) (transportCost_add_le _ _ _ _ _))
    exact ⟨_, (measurable_gradient _).aemeasurable, hgraph⟩

/-- **Optimality of the gradient graph plan for a `c - c`-regular source.** Let `μ` and `ν` be
finite measures with finite second moments on a finite-dimensional real inner product space, with
`μ` `c - c`-regular. If `u : E → EReal` has convex real epigraph with `u ≠ ⊤` `μ`-almost everywhere
and `∇ u` pushes `μ` to `ν`, then the graph plan of `∇ u` is an optimal quadratic coupling from `μ`
to `ν`, without assuming `u ≠ ⊥` or `μ`-a.e. differentiability. -/
theorem IsCCRegular.isOptimalCoupling_graphPlan_gradient [IsFiniteMeasure μ] (hμ : IsCCRegular μ)
    (hμ2 : MemLp id 2 μ) (hν2 : MemLp id 2 ν) {u : E → EReal}
    (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hu_dom : ∀ᵐ x ∂μ, u x ≠ ⊤)
    (huν : HasLaw (∇ fun x => (u x).toReal) ν μ) :
    IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (graphPlan (∇ fun x => (u x).toReal) μ) μ ν := by
  have hc := (continuous_ofReal_norm_sub_sq_div_two (F := E)).measurable
  have hdiff := (hμ.ae_eventually_ne_top_and_differentiableAt_toReal hu).and hu_dom
    |>.mono fun _ ⟨h, h'⟩ => h h'
  by_cases hbot : ∀ x, u x ≠ ⊥
  · exact (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan huν hc.aemeasurable).1
      (isKantorovichOptimalTransportMap_gradient hμ2 hν2 hu hbot
        (hdiff.mono fun _ hx => ⟨hx.1.self_of_nhds, hx.2⟩) huν)
  · push Not at hbot; obtain ⟨z₀, hz₀⟩ := hbot
    have hgrad : (∇ fun x => (u x).toReal) =ᵐ[μ] ∇ fun _ : E => ((0 : EReal).toReal) := by
      filter_upwards [hdiff] with x hx
      have hev : (fun x' => (u x').toReal) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hx.1)] with x' hx'
        simp [eq_bot_of_mem_interior_of_eq_bot hu hx' hz₀]
      rw [((hasGradientAt_const x (0 : ℝ)).congr_of_eventuallyEq hev).gradient,
        (by simpa using hasGradientAt_const x (0 : ℝ) :
          HasGradientAt (fun _ : E => ((0 : EReal).toReal)) 0 x).gradient]
    have hu₀ : Convex ℝ {p : E × ℝ | (0 : EReal) ≤ p.2} := fun x hx y hy a b ha hb _ => by
      simp only [mem_ofPred_eq, EReal.coe_nonneg, Prod.snd_add, Prod.smul_snd,
        smul_eq_mul] at hx hy ⊢; positivity
    have hu₀ν := huν.congr hgrad.symm
    rw [graphPlan_congr hgrad]
    exact (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hu₀ν hc.aemeasurable).1
      (isKantorovichOptimalTransportMap_gradient hμ2 hν2 hu₀ (fun _ => EReal.zero_ne_bot)
        (.of_forall fun _ => ⟨EReal.zero_ne_top, differentiableAt_const _⟩) hu₀ν)

/-- **Uniqueness of the monotone rearrangement.** Let `μ` and `ν` be finite measures with finite
second moments on a finite-dimensional real inner product space, with `μ` `c - c`-regular.
If `u` and `v : E → EReal` have convex real epigraphs with `u ≠ ⊤` and `v ≠ ⊤` `μ`-a.e.,
and both gradients push
`μ` to `ν`, then `∇u = ∇v` `μ`-almost everywhere. -/
theorem gradient_ae_eq_gradient_of_hasLaw [IsFiniteMeasure μ] (hμ2 : MemLp id 2 μ)
    (hν2 : MemLp id 2 ν) (hμ : IsCCRegular μ) {u v : E → EReal}
    (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hu_dom : ∀ᵐ x ∂μ, u x ≠ ⊤)
    (huν : HasLaw (∇ fun x => (u x).toReal) ν μ)
    (hv : Convex ℝ {p : E × ℝ | v p.1 ≤ p.2}) (hv_dom : ∀ᵐ x ∂μ, v x ≠ ⊤)
    (hvν : HasLaw (∇ fun x => (v x).toReal) ν μ) :
    (∇ fun x => (u x).toReal) =ᵐ[μ] ∇ fun x => (v x).toReal := by
  have hu' := hμ.isOptimalCoupling_graphPlan_gradient hμ2 hν2 hu hu_dom huν
  have hv' := hμ.isOptimalCoupling_graphPlan_gradient hμ2 hν2 hv hv_dom hvν
  have hfin := hu'.toIsCoupling.transportCost_norm_sub_sq_div_two_ne_top hμ2 hν2
  exact (graphPlan_eq_graphPlan_iff huν.aemeasurable hvν.aemeasurable).1
    (hu'.unique hμ hv' hfin)

/-- **Brenier's theorem.** Let `μ` be a finite measure and `ν` a measure on a
finite-dimensional real inner product space `E`, with `μ` `c - c`-regular,
and suppose the optimal cost for `‖x - y‖ ^ 2 / 2` is finite, as it is for
finite measures of equal total mass with finite second moment
(`TauCeti.transportCost_norm_sub_sq_div_two_ne_top_of_memLp`); then `ν` is
finite with `ν univ = μ univ`. Then there is a convex, lower
semicontinuous `u : E → EReal` that never takes the value `⊥`, is finite near `μ`-almost every
point and has differentiable real representative there, such that the gradient
`T = ∇ (fun x => (u x).toReal)`:

* is an optimal transport map from `μ` to `ν`, attaining the Kantorovich value;
* induces the unique optimal plan: a plan is optimal exactly when it is the graph plan of `T`;
* is the unique optimal transport map up to `μ`-almost everywhere equality. -/
theorem exists_isKantorovichOptimalTransportMap_gradient [IsFiniteMeasure μ]
    (hμ : IsCCRegular μ)
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
    continuous_ofReal_norm_sub_sq_div_two
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling_of_transportCost_ne_top hc.lowerSemicontinuous hfin
  obtain ⟨u, hconv, hlsc, hbot, hdiff, hgraph⟩ := hπ.exists_eq_graphPlan_gradient hμ hfin
  have hT := measurable_gradient fun x => (u x).toReal
  have hopt_T : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (graphPlan (∇ fun x => (u x).toReal) μ) μ ν := hgraph ▸ hπ
  refine ⟨u, hconv, hlsc, hbot, hdiff,
    isKantorovichOptimalTransportMap_of_isOptimalCoupling_graphPlan hT.aemeasurable
      hc.measurable.aemeasurable hopt_T,
    fun σ => ⟨fun hσ => hσ.unique hμ hopt_T hfin, fun hσ => hσ ▸ hopt_T⟩,
    fun S hS => hS.ae_eq_of_isOptimalCoupling_eq_graphPlan hT.aemeasurable
      hc.measurable.aemeasurable fun hS_opt => hS_opt.unique hμ hopt_T hfin⟩

/-- **Brenier's theorem with the inverse map.** Let `μ` be a finite measure and `ν` a measure
on a finite-dimensional real inner product space `E`, both `c - c`-regular, and suppose the optimal
cost for `‖x - y‖ ^ 2 / 2` is finite (so `ν` is finite with `ν univ = μ univ`). Then there is a
convex, lower semicontinuous `u : E → EReal` that never
takes the value `⊥` such that `u` is finite near `μ`-almost every point and its Legendre–Fenchel
conjugate `u⋆` satisfies `u⋆ ≠ ⊤` near `ν`-almost every point, both with differentiable real
representatives there, and:

* the gradient `∇ u` is an optimal transport map from `μ` to `ν`;
* the gradient `∇ u⋆` is an optimal transport map from `ν` to `μ`;
* the two maps are inverse to each other, `∇ u⋆ ∘ ∇ u = id` `μ`-almost everywhere and
  `∇ u ∘ ∇ u⋆ = id` `ν`-almost everywhere.

The almost everywhere uniqueness of the optimal maps and plans in each direction is recorded
separately, in `TauCeti.exists_isKantorovichOptimalTransportMap_gradient` and
`TauCeti.IsOptimalCoupling.unique`. -/
theorem exists_isKantorovichOptimalTransportMap_gradient_and_gradient_fenchelConjugate
    [IsFiniteMeasure μ] (hμ : IsCCRegular μ) (hν : IsCCRegular ν)
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
    continuous_ofReal_norm_sub_sq_div_two
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling_of_transportCost_ne_top hc.lowerSemicontinuous hfin
  obtain ⟨u, hconv, hlsc, hbot, -, hsub⟩ := hπ.exists_ae_mem_subdifferential hfin
  obtain ⟨hdiff, hgraph⟩ :=
    eq_graphPlan_gradient_of_ae_mem_subdifferential hπ.fst_eq hμ hconv hsub
  obtain ⟨hdiff', hgraph'⟩ :=
    map_swap_eq_graphPlan_gradient_fenchelConjugate hπ.snd_eq hν hsub
  -- The quadratic cost is symmetric, so the exchanged plan is optimal from `ν` to `μ`.
  have hswap : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (π.map Prod.swap) ν μ := by
    have hcs : (fun z : E × E => ENNReal.ofReal (‖z.swap.1 - z.swap.2‖ ^ 2 / 2)) =
        fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) := by
      ext z
      rw [Prod.fst_swap, Prod.snd_swap, norm_sub_rev]
    exact hcs ▸ hπ.swap
  have hT := measurable_gradient fun x => (u x).toReal
  have hS := measurable_gradient fun y => (fenchelConjugate (innerₗ E) u y).toReal
  have hinv := comp_ae_eq_id_of_map_swap_graphPlan_eq hT.aemeasurable hS.aemeasurable
    (hgraph ▸ hgraph')
  refine ⟨u, hconv, hlsc, hbot, hdiff, hdiff',
    isKantorovichOptimalTransportMap_of_isOptimalCoupling_graphPlan hT.aemeasurable
      hc.measurable.aemeasurable (hgraph ▸ hπ),
    isKantorovichOptimalTransportMap_of_isOptimalCoupling_graphPlan hS.aemeasurable
      hc.measurable.aemeasurable (hgraph' ▸ hswap),
    hinv.1, hinv.2⟩

/-- **Strict convexity of the quadratic transport cost in the target for `c - c`-regular sources.**
Whenever `μ` is a finite `c - c`-regular measure and `ν₀ ≠ ν₁` have finite quadratic transport cost
from `μ`, any nontrivial convex combination `a • ν₀ + b • ν₁` (`a, b ≠ 0`, `a + b = 1`) has
strictly smaller transport cost than the convex combination of the two costs. -/
theorem IsCCRegular.transportCost_smul_add_smul_lt [IsFiniteMeasure μ] (hμ : IsCCRegular μ)
    {ν₀ ν₁ : Measure E} {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfin₀ : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₀ ≠ ∞)
    (hfin₁ : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₁ ≠ ∞)
    (hne : ν₀ ≠ ν₁) :
    transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ (a • ν₀ + b • ν₁) <
      a * transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₀ +
        b * transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₁ := by
  let c : E × E → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)
  have hc := (continuous_ofReal_norm_sub_sq_div_two (F := E)).lowerSemicontinuous
  obtain ⟨π₀, hπ₀⟩ := exists_isOptimalCoupling_of_transportCost_ne_top hc hfin₀
  obtain ⟨π₁, hπ₁⟩ := exists_isOptimalCoupling_of_transportCost_ne_top hc hfin₁
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_self_add)
  have hbtop : b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_add_self)
  have hfin_mix : transportCost c μ (a • ν₀ + b • ν₁) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hatop hfin₀, ENNReal.mul_ne_top hbtop hfin₁⟩) <| by
      simpa only [← add_smul, hab, one_smul, transportCost_smul hatop, transportCost_smul hbtop]
        using transportCost_add_le c (a • μ) (b • μ) (a • ν₀) (b • ν₁)
  exact TauCeti.transportCost_smul_add_smul_lt hab ha hb hπ₀ hπ₁ (fun π hπ =>
    let ⟨_, _, _, _, _, hgraph⟩ := hπ.exists_eq_graphPlan_gradient hμ hfin_mix
    ⟨_, (measurable_gradient _).aemeasurable, hgraph⟩) hne

section AbsolutelyContinuous

variable {ρ : Measure E} [ρ.IsAddHaarMeasure]

/-- **The Brenier potential is a weak solution of its transport equation.** Let `μ` be a
probability measure and `ν` a measure on a finite-dimensional real inner product space `E`, both
absolutely continuous with respect to an additive Haar measure, and suppose the optimal cost for
`‖x - y‖ ^ 2 / 2` is finite. Then there is a convex, lower semicontinuous `u : E → EReal` that
never takes the value `⊥`, with `D` the interior of its effective domain, such that:

* the gradient `∇ u` is an optimal transport map from `μ` to `ν`;
* the Monge–Ampère measure of `u` weighted by `ν` is `μ`, that is, `ν(∂u(s ∩ D)) = μ(s)` for
  every measurable `s`; for `μ = g₀ dx` and `ν = g₁ dy` this is `∫_{∂u(s ∩ D)} g₁ = ∫_s g₀`;
* `ν`-almost every point is a subgradient of `u` at a point of `D`. -/
theorem exists_isKantorovichOptimalTransportMap_gradient_and_mongeAmpereMeasure_eq
    [IsProbabilityMeasure μ] (hμ : μ ≪ ρ) (hν : ν ≪ ρ)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        μ ν (∇ fun x => (u x).toReal) ∧
      mongeAmpereMeasure ν u = μ ∧
      ∀ᵐ y ∂ν, y ∈ subgradientImage (innerₗ E) u (interior {x | u x ≠ ⊤}) := by
  have := isProbabilityMeasure_right_of_transportCost_ne_top hfin
  obtain ⟨u, hconv, hlsc, hbot, hdiff, hT, -⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient (isCCRegular_of_absolutelyContinuous hμ) hfin
  refine ⟨u, hconv, hlsc, hbot, hT,
    (hasLaw_gradient_and_ae_ne_top_iff_mongeAmpereMeasure_eq_and_ae_mem_subgradientImage
      hconv hbot hμ hν).1 ⟨hT.toHasLaw, ?_⟩⟩
  filter_upwards [hdiff] with x hx using hx.1.self_of_nhds

/-- **Brenier solutions with a convex target are Aleksandrov solutions.** Let `μ` be a probability
measure and `ν` a measure on a finite-dimensional real inner product space `E`, with `μ`
`c - c`-regular and `ν = g ρ` for an additive Haar measure `ρ`, and suppose the optimal cost for
`‖x - y‖ ^ 2 / 2` is finite. Let `K` be a closed convex set carrying `ν` on which `g` is
`ρ`-almost everywhere positive. Then there is a convex, lower semicontinuous `u : E → EReal` that
never takes the value `⊥` such that:

* the gradient `∇ u` is an optimal transport map from `μ` to `ν`;
* every subgradient of `u`, at every point, lies in `K`;
* `u` is an Aleksandrov solution of the Monge–Ampère equation: its Aleksandrov measure with respect
  to `ρ` is `MA_u = (g ∘ ∇u)⁻¹ μ` (reducing to `det D²u = g₀ / g(∇u)` when `μ = g₀ ρ`).

For a general transporting potential, `TauCeti.mongeAmpereMeasure_eq_withDensity_inv_iff`
identifies the obstruction: the zero-density remainder, the subgradient mass falling where `g`
vanishes, which the weighted transport equation `MA_{u, g ρ} = μ` does not see. -/
theorem exists_isKantorovichOptimalTransportMap_gradient_and_mongeAmpereMeasure_eq_withDensity
    [IsProbabilityMeasure μ] (hμ : IsCCRegular μ) {g : E → ℝ≥0∞}
    (hg : Measurable g) (hνg : ν = ρ.withDensity g) {K : Set E} (hKc : Convex ℝ K)
    (hKcl : IsClosed K) (hνK : ν Kᶜ = 0) (hgK : ∀ᵐ y ∂ρ, y ∈ K → g y ≠ 0)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        μ ν (∇ fun x => (u x).toReal) ∧
      (∀ x, subdifferential (innerₗ E) u x ⊆ K) ∧
      mongeAmpereMeasure ρ u = μ.withDensity fun x => (g ((∇ fun x => (u x).toReal) x))⁻¹ := by
  obtain ⟨u, hconv, -, hbot, hdiff, hT, -⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient hμ hfin
  set T := ∇ fun x => (u x).toReal
  -- Confine the slopes of `u` to `K`, keeping the slopes `T x ∈ ∂u(x) ∩ K`.
  obtain ⟨v, hvconv, hvlsc, hvu, hK, hkeep⟩ := exists_le_subdifferential_subset u hKc hKcl
  have hTK : ∀ᵐ x ∂μ, T x ∈ K := ae_of_ae_map hT.toHasLaw.aemeasurable
    (by rw [hT.toHasLaw.map_eq]; exact mem_ae_iff.2 hνK)
  have hsub : ∀ᵐ x ∂μ, T x ∈ subdifferential (innerₗ E) v x := by
    filter_upwards [hdiff, hTK] with x hx hxK
    exact hkeep x ⟨gradient_toReal_mem_subdifferential hconv hbot hx.1.self_of_nhds hx.2, hxK⟩
  have hD : ∀ᵐ x ∂μ, x ∈ interior {x | v x ≠ ⊤} := by
    filter_upwards [hdiff] with x hx
    exact mem_interior_iff_mem_nhds.2 (hx.1.mono fun x' hx' => ne_top_of_le_ne_top hx' (hvu x'))
  have hvbot : ∀ x, v x ≠ ⊥ := by
    have : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
    obtain ⟨x₀, hx₀⟩ := hsub.exists
    exact apply_ne_bot_of_mem_subdifferential (innerₗ E) hx₀
  -- By Zajíček's theorem `v` is differentiable at `μ`-almost every point of `D`, where its
  -- gradient is its slope `T x`.
  have hgrad : (∇ fun x => (v x).toReal) =ᵐ[μ] T := by
    filter_upwards [hμ.ae_eventually_ne_top_and_differentiableAt_toReal hvconv, hD, hsub] with
      x hx hxD hxs
    have hdom : ∀ᶠ x' in 𝓝 x, v x' ≠ ⊤ := mem_interior_iff_mem_nhds.1 hxD
    exact gradient_toReal_eq_of_mem_subdifferential hxs hdom (hx hdom.self_of_nhds).2
  have hsub' : ∀ᵐ x ∂μ, (∇ fun x => (v x).toReal) x ∈ subdifferential (innerₗ E) v x := by
    filter_upwards [hsub, hgrad] with x hx hx'
    rwa [hx']
  have := isProbabilityMeasure_right_of_transportCost_ne_top hfin
  have hgtop : ∀ᵐ y ∂ρ, g y ≠ ⊤ := by
    refine (ae_lt_top hg ?_).mono fun y hy => hy.ne
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hνg]
    exact measure_ne_top ν univ
  refine ⟨v, hvconv, hvlsc, hvbot, hT.congr hgrad, hK,
    mongeAmpereMeasure_eq_withDensity_inv_of_convex hvconv hvbot hg hgtop
      (hνg ▸ hT.toHasLaw.congr hgrad) hD hsub' hKc (fun y hy => ?_) hgK⟩
  obtain ⟨x, -, hxy⟩ := (mem_subgradientImage_iff _).1 hy
  exact subset_closure (hK x hxy)

end AbsolutelyContinuous

section AbsolutelyContinuous

variable {ρ : Measure E} [ρ.IsAddHaarMeasure]

/-- **The Brenier potential solves the Monge–Ampère equation almost everywhere.** Let `μ` be a
probability measure and `ν` a measure on a finite-dimensional real inner product space `E`, both
absolutely continuous with respect to an additive Haar measure `ρ`, with densities `g₀ = dμ/dρ` and
`g₁ = dν/dρ`, and suppose the optimal cost for `‖x - y‖ ^ 2 / 2` is finite. Then there is a
convex, lower semicontinuous `u : E → EReal` that never takes the value `⊥`, with `D` the interior
of its effective domain, such that:

* the gradient `∇ u` is an optimal transport map from `μ` to `ν`;
* at `ρ`-almost every point `x` of the effective domain, the subdifferential of `u` has a positive
  derivative `H x`, the Alexandrov Hessian of `u`: every subgradient `y'` at a point `x'` near `x`
  satisfies `y' = ∇ u x + H x (x' - x) + o(‖x' - x‖)`;
* the **Jacobian equation** `g₀ x = g₁ (∇ u x) det (H x)` holds for `ρ`-almost every `x ∈ D`,
  and `g₀ = 0` almost everywhere off `D`. -/
theorem exists_isKantorovichOptimalTransportMap_gradient_and_rnDeriv_ae_eq
    [IsProbabilityMeasure μ] (hμ : μ ≪ ρ) (hν : ν ≪ ρ)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        μ ν (∇ fun x => (u x).toReal) ∧
      ∃ H : E → E →L[ℝ] E, (∀ᵐ x ∂ρ, u x ≠ ⊤ → (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
          ∀ y' ∈ subdifferential (innerₗ E) u x',
            ‖y' - (∇ fun x => (u x).toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖) ∧
        μ.rnDeriv ρ =ᵐ[ρ] (interior {x | u x ≠ ⊤}).indicator fun x =>
          ENNReal.ofReal (H x).det * ν.rnDeriv ρ ((∇ fun x => (u x).toReal) x) := by
  have := isProbabilityMeasure_right_of_transportCost_ne_top hfin
  obtain ⟨u, hconv, hlsc, hbot, hT, hMA, -⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient_and_mongeAmpereMeasure_eq hμ hν hfin
  obtain ⟨H, hH, -⟩ := exists_mongeAmpereMeasure_eq_singularPart_add_withDensity ρ hconv hbot
  refine ⟨u, hconv, hlsc, hbot, hT, H, hH,
    rnDeriv_ae_eq_indicator_ofReal_det_mul_rnDeriv_of_mongeAmpereMeasure_eq ρ hconv hbot ?_ hν hMA⟩
  filter_upwards [hH] with x hx hxD
  exact ⟨_, (hx (interior_subset hxD)).2⟩

/-- **Displacement interpolants of an absolutely continuous law are absolutely continuous.** Let
`μ` be a probability measure and `ν` a measure on a finite-dimensional real inner product space
`E`, with `μ` absolutely continuous with respect to an additive Haar measure `ρ`, and suppose the
optimal cost for `‖x - y‖ ^ 2 / 2` is finite. Then there is a convex, lower semicontinuous
`u : E → EReal` that never takes the value `⊥`, with `D` the interior of its effective domain,
such that:

* the gradient `∇ u` is an optimal transport map from `μ` to `ν`;
* at `ρ`-almost every point `x` of the effective domain, the subdifferential of `u` has a positive
  derivative `H x`, the Alexandrov Hessian of `u`;
* for every `0 ≤ t < 1`, the displacement interpolant `μₜ`, the pushforward of `μ` by
  `Tₜ x = (1 - t) • x + t • ∇ u x`, is absolutely continuous with respect to `ρ`, and the
  densities satisfy the **Jacobian equation**
  `dμ/dρ (x) = det ((1 - t) • 1 + t • H x) * dμₜ/dρ (Tₜ x)` for `ρ`-almost every `x ∈ D`, with
  `dμ/dρ = 0` almost everywhere off `D`.

The target `ν = μ₁` need not be absolutely continuous. -/
theorem
    exists_isKantorovichOptimalTransportMap_gradient_and_rnDeriv_ae_eq_map_smul_add_smul_gradient
    [IsProbabilityMeasure μ] (hμ : μ ≪ ρ)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        μ ν (∇ fun x => (u x).toReal) ∧
      ∃ H : E → E →L[ℝ] E, (∀ᵐ x ∂ρ, u x ≠ ⊤ → (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
          ∀ y' ∈ subdifferential (innerₗ E) u x',
            ‖y' - (∇ fun x => (u x).toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖) ∧
        ∀ t : ℝ, 0 ≤ t → t < 1 →
          μ.map (fun x => (1 - t) • x + t • (∇ fun x' => (u x').toReal) x) ≪ ρ ∧
          μ.rnDeriv ρ =ᵐ[ρ] (interior {x | u x ≠ ⊤}).indicator fun x =>
            ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det *
              (μ.map fun x => (1 - t) • x + t • (∇ fun x' => (u x').toReal) x).rnDeriv ρ
                ((1 - t) • x + t • (∇ fun x' => (u x').toReal) x) := by
  have := isProbabilityMeasure_right_of_transportCost_ne_top hfin
  obtain ⟨u, hconv, hlsc, hbot, hdiff, hT, -⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient (isCCRegular_of_absolutelyContinuous hμ) hfin
  obtain ⟨H, hH, -⟩ := exists_mongeAmpereMeasure_eq_singularPart_add_withDensity ρ hconv hbot
  have hμD : ∀ᵐ x ∂μ, x ∈ interior {x | u x ≠ ⊤} := by
    filter_upwards [hdiff] with x hx using mem_interior_iff_mem_nhds.2 hx.1
  refine ⟨u, hconv, hlsc, hbot, hT, H, hH, fun t ht₀ ht₁ =>
    ⟨map_smul_add_smul_gradient_absolutelyContinuous ρ hconv hbot hμ hμD ht₀ ht₁,
      rnDeriv_ae_eq_indicator_ofReal_det_mul_rnDeriv_map_smul_add_smul_gradient ρ hconv hbot ?_ hμ
        hμD ht₀ ht₁⟩⟩
  filter_upwards [hH] with x hx hxD
  exact ⟨_, (hx (interior_subset hxD)).2⟩

end AbsolutelyContinuous

end FiniteDimensional

end TauCeti
