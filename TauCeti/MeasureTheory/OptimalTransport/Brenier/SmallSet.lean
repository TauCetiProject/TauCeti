/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SingularSet.FiniteDimensional
public import TauCeti.MeasureTheory.OptimalTransport.Brenier.Basic

/-!
# Brenier's theorem for sources vanishing on Lipschitz hypersurfaces and small sets

In `TauCeti.MeasureTheory.OptimalTransport.Brenier.Basic`, Brenier's theorem is proved for source
measures `μ` absolutely continuous with respect to an additive Haar measure on a finite-dimensional
real inner product space `E`: absolute continuity enters only to invoke Rademacher's theorem for the
convex Legendre–Fenchel potential `u : E → EReal` carrying the support of an optimal plan.

By `TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs`, any measure
`μ` that gives mass `0` to every globally Lipschitz graph
`range (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v)` over the orthogonal complement of a unit vector `v`
already sees every convex `u : E → EReal` (never `⊥`) finite on a neighbourhood and differentiable
at `μ`-almost every point of `{x | u x ≠ ⊤}`. Consequently, the entire forward Brenier theory—graph
representation of subdifferential plans, gradient representation and uniqueness of optimal quadratic
plans, existence and uniqueness of the gradient Kantorovich optimal transport map, and graph
representation of optimal `edist ^ 2` plans—holds under this weaker geometric hypothesis on `μ`.

Since globally Lipschitz graphs over `(ℝ ∙ v)ᗮ` (`‖v‖ = 1`) are closed and satisfy
`dimH + 1 ≤ finrank ℝ E`, the same conclusions hold whenever `μ` vanishes on all Borel sets `A`
satisfying `dimH A + 1 ≤ finrank ℝ E` (a condition valid in every dimension, including `0`, and
satisfied by every measure absolutely continuous with respect to an additive Haar measure), and in
particular whenever `μ` vanishes on all Borel sets of Hausdorff dimension at most
`finrank ℝ E - 1`—the "vanishing on small sets" hypothesis of Villani and of Agueh and Carlier.

## Main statements

* `TauCeti.eq_graphPlan_gradient_of_ae_mem_subdifferential_of_null_lipschitz_graphs` — a plan on the
  subdifferential graph of a convex, lower semicontinuous `u : E → EReal` whose first marginal `μ`
  vanishes on Lipschitz hypersurface graphs is the graph plan of `∇ u`;
* `TauCeti.IsOptimalCoupling.exists_eq_graphPlan_gradient_of_null_lipschitz_graphs` and
  `TauCeti.IsOptimalCoupling.unique_of_null_lipschitz_graphs` — gradient representation and
  uniqueness of optimal quadratic plans out of such a `μ`;
* `TauCeti.exists_isKantorovichOptimalTransportMap_gradient_of_null_lipschitz_graphs`,
  `TauCeti.exists_isKantorovichOptimalTransportMap_gradient_of_dimH_add_one_le`, and
  `TauCeti.exists_isKantorovichOptimalTransportMap_gradient_of_dimH_le` — **Brenier's theorem for
  sources vanishing on Lipschitz hypersurfaces or small sets**;
* `TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_null_lipschitz_graphs`,
  `TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_dimH_add_one_le`, and
  `TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_dimH_le` — optimal `edist ^ 2` plans out of
  such sources are graph plans of measurable maps.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  Theorem 2.12(ii) and §2.4.
* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43 (2011),
  904–924, Proposition 2.1 and Definition 2.2.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser, 2015, Theorem 1.22.
-/

public section

noncomputable section

open Filter MeasureTheory Module ProbabilityTheory Set
open scoped ENNReal NNReal Topology Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E} {π : Measure (E × E)}

section NullLipschitzGraphs

/-- **A plan on a subdifferential graph is the graph plan of the gradient.** Let `π` be a plan with
first marginal `μ` on a finite-dimensional real inner product space `E`, where `μ` gives mass `0`
to every globally Lipschitz graph over the orthogonal complement of a unit vector, and let
`u : E → EReal` be convex and lower semicontinuous. If `y ∈ ∂u(x)` for `π`-almost every `(x, y)`,
then `u` is finite near `μ`-almost every point with differentiable real representative there, and
`π` is the graph plan of `∇ (fun x => (u x).toReal)`. -/
theorem eq_graphPlan_gradient_of_ae_mem_subdifferential_of_null_lipschitz_graphs
    (hπ : π.fst = μ)
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0)
    {u : E → EReal} (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hlsc : LowerSemicontinuous u)
    (hsub : ∀ᵐ z ∂π, z.2 ∈ subdifferential (innerₗ E) u z.1) :
    (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      π = graphPlan (∇ fun x => (u x).toReal) μ :=
  eq_graphPlan_gradient_of_ae_mem_subdifferential_of_ae_differentiableAt hπ hlsc
    (fun hbot => ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs
      hconv hbot hμ) hsub

/-- **An optimal quadratic plan out of a source vanishing on Lipschitz hypersurfaces is induced by
the gradient of a convex function.** -/
theorem IsOptimalCoupling.exists_eq_graphPlan_gradient_of_null_lipschitz_graphs
    [IsFiniteMeasure μ]
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0)
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      π = graphPlan (∇ fun x => (u x).toReal) μ :=
  h.exists_eq_graphPlan_gradient_of_forall_convex_ae_differentiableAt
    (fun _ hu hbot =>
      ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs hu hbot hμ) hfin

/-- **Uniqueness of the optimal quadratic plan** when the finite source `μ` vanishes on globally
Lipschitz graphs over hyperplanes. -/
theorem IsOptimalCoupling.unique_of_null_lipschitz_graphs [IsFiniteMeasure μ]
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0)
    {π' : Measure (E × E)}
    (h : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν)
    (h' : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π' μ ν)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    π = π' :=
  h.unique_of_forall_convex_ae_differentiableAt
    (fun _ hu hbot =>
      ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs hu hbot hμ) h' hfin

/-- **Brenier's theorem for sources vanishing on Lipschitz hypersurfaces** (Villani, *Topics in
Optimal Transportation*, Theorem 2.12(ii) and §2.4). Let `μ` be a probability measure on a
finite-dimensional real inner product space `E` that gives mass `0` to every globally Lipschitz
graph over the orthogonal complement of a unit vector, and let `ν` be a measure on `E` at finite
transport cost from `μ` for `‖x - y‖ ^ 2 / 2`. Then there is a convex, lower semicontinuous
`u : E → EReal`, never `⊥`, finite on a neighbourhood and differentiable `μ`-almost everywhere,
whose gradient `T = ∇ (fun x => (u x).toReal)` is the `μ`-almost everywhere unique Kantorovich
optimal transport map from `μ` to `ν` and induces the unique optimal plan. -/
theorem exists_isKantorovichOptimalTransportMap_gradient_of_null_lipschitz_graphs
    [IsProbabilityMeasure μ]
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0)
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
          μ ν S → S =ᵐ[μ] ∇ fun x => (u x).toReal :=
  exists_isKantorovichOptimalTransportMap_gradient_of_forall_convex_ae_differentiableAt
    (fun _ hu hbot =>
      ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs hu hbot hμ) hfin

/-- **Brenier's theorem for the cost `edist ^ 2` out of a source vanishing on Lipschitz
hypersurfaces.** -/
theorem IsOptimalCoupling.exists_eq_graphPlan_of_null_lipschitz_graphs [IsFiniteMeasure μ]
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0)
    (h : IsOptimalCoupling (fun z : E × E => edist z.1 z.2 ^ (2 : ℝ)) π μ ν)
    (hfin : wassersteinEDist 2 μ ν ≠ ∞) :
    ∃ T : E → E, Measurable T ∧ π = graphPlan T μ :=
  h.exists_eq_graphPlan_of_forall_convex_ae_differentiableAt
    (fun _ hu hbot =>
      ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs hu hbot hμ) hfin

end NullLipschitzGraphs

section SmallSets

/-- **Brenier's theorem for sources vanishing on Borel sets with `dimH A + 1 ≤ finrank ℝ E`.**
This hypothesis holds in every finite dimension, including `0`, and is satisfied by every measure
absolutely continuous with respect to an additive Haar measure. -/
theorem exists_isKantorovichOptimalTransportMap_gradient_of_dimH_add_one_le
    [IsProbabilityMeasure μ]
    (hμ : ∀ A, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) → μ A = 0)
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
          μ ν S → S =ᵐ[μ] ∇ fun x => (u x).toReal :=
  exists_isKantorovichOptimalTransportMap_gradient_of_null_lipschitz_graphs
    (fun _ hv _ _ hg => measure_range_add_smul_eq_zero_of_dimH_add_one_le hμ hv hg) hfin

/-- **Brenier's theorem for sources vanishing on small sets (`dimH A ≤ finrank ℝ E - 1`).** -/
theorem exists_isKantorovichOptimalTransportMap_gradient_of_dimH_le
    [IsProbabilityMeasure μ]
    (hμ : ∀ A, MeasurableSet A → dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) → μ A = 0)
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
          μ ν S → S =ᵐ[μ] ∇ fun x => (u x).toReal :=
  exists_isKantorovichOptimalTransportMap_gradient_of_dimH_add_one_le
    (fun _ hA hdim => measure_eq_zero_of_dimH_add_one_le_of_forall_dimH_le hμ hA hdim) hfin

/-- **Brenier's theorem for `edist ^ 2` out of a source vanishing on Borel sets with
`dimH A + 1 ≤ finrank ℝ E`.** -/
theorem IsOptimalCoupling.exists_eq_graphPlan_of_dimH_add_one_le [IsFiniteMeasure μ]
    (hμ : ∀ A, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) → μ A = 0)
    (h : IsOptimalCoupling (fun z : E × E => edist z.1 z.2 ^ (2 : ℝ)) π μ ν)
    (hfin : wassersteinEDist 2 μ ν ≠ ∞) :
    ∃ T : E → E, Measurable T ∧ π = graphPlan T μ :=
  h.exists_eq_graphPlan_of_null_lipschitz_graphs
    (fun _ hv _ _ hg => measure_range_add_smul_eq_zero_of_dimH_add_one_le hμ hv hg) hfin

/-- **Brenier's theorem for `edist ^ 2` out of a source vanishing on small sets
(`dimH A ≤ finrank ℝ E - 1`).** -/
theorem IsOptimalCoupling.exists_eq_graphPlan_of_dimH_le [IsFiniteMeasure μ]
    (hμ : ∀ A, MeasurableSet A → dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) → μ A = 0)
    (h : IsOptimalCoupling (fun z : E × E => edist z.1 z.2 ^ (2 : ℝ)) π μ ν)
    (hfin : wassersteinEDist 2 μ ν ≠ ∞) :
    ∃ T : E → E, Measurable T ∧ π = graphPlan T μ :=
  h.exists_eq_graphPlan_of_dimH_add_one_le
    (fun _ hA hdim => measure_eq_zero_of_dimH_add_one_le_of_forall_dimH_le hμ hA hdim) hfin

end SmallSets

end TauCeti
