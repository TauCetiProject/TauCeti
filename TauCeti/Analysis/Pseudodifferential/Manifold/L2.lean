/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Topology.Algebra.Module.LinearPMap.CommonDomain
public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic.Basic
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
public import TauCeti.Geometry.Manifold.Sobolev.L2
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain
import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic.Estimate

/-!
# Pseudodifferential operators on a compact manifold as operators in `L²`

Let `M` be a compact manifold modelled on `ℝⁿ`, `μ` a finite measure on `M` with a smooth positive
density (`TauCeti.HasSmoothPositiveDensity`), and `ψᵢ` cutoffs in charts `cᵢ` whose readings on
`M` add up to `1`, with Sobolev spaces `H^s(M)` (`TauCeti.chartSobolevSpace`). For `s ≥ 0` these are
subspaces of `L²(M, μ)` (`TauCeti.chartSobolevToLp`), with `H⁰(M) = L²(M, μ)`
(`TauCeti.chartSobolevSpaceZeroEquivLp`).

A classical pseudodifferential operator `P` of order `m ≥ 0` extends to a bounded operator
`H^m(M) → H⁰(M)` (`TauCeti.chartSobolevExtension`). Read in `L²(M, μ)`, this is an unbounded
operator with domain `H^m(M)`, its **realization in `L²`**
(`TauCeti.chartSobolevRealization`): a function `f ∈ L²` lies in its domain when `f ∈ H^m(M)`,
and its value is then the extension of `P` applied to `f`. It is the partial operator
`ContinuousLinearMap.domainOperator` of the pair formed by the injection `H^m(M) → L²(M, μ)` and
the extension of `P`, so the graph, domain and evaluation lemmas of `domainOperator` apply to
it. On smooth functions it is `P`
(`TauCeti.chartSobolevRealization_toLp`), and its domain is dense
(`TauCeti.dense_domain_chartSobolevRealization`).

* **Formal adjoints.** If `Q` is a classical pseudodifferential operator of order `m` and a formal
  adjoint of `P` for `μ`, `∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ` for smooth `u` and `v`, then the
  realizations of `P` and `Q` are formal adjoints of each other in `L²`
  (`TauCeti.isFormalAdjoint_chartSobolevRealization`), so the realization of `Q` lies in the
  adjoint of that of `P` (`TauCeti.chartSobolevRealization_le_adjoint`). In particular the
  realization of a formally self-adjoint operator is **symmetric**.
* **Closedness.** If `P` is elliptic, its realization is a **closed** operator
  (`TauCeti.IsClassicalElliptic.isClosed_chartSobolevRealization`). This rests on the elliptic
  estimate `‖x‖_{H^m} ≤ C (‖P x‖_{H⁰} + ‖x‖_{H⁰})` on all of `H^m(M)`
  (`TauCeti.IsClassicalElliptic.exists_norm_le_mul_norm_chartSobolevExtension_add`), which bounds
  the norm of the Hilbert space `H^m(M)` by the graph norm
  (`ContinuousLinearMap.isClosed_domainOperator_of_norm_le`).

For a formally self-adjoint elliptic operator the realization is therefore a closed, densely
defined symmetric operator in `L²(M, μ)` with domain `H^m(M)`. Self-adjointness, the equality of
this domain with the domain of the adjoint, additionally needs elliptic regularity for weak
`L²` solutions.

## Main definitions

* `TauCeti.chartSobolevRealization`: the realization of `P` in `L²(M, μ)` with domain `H^m(M)`.

## Main results

* `TauCeti.chartSobolevRealization_toLp`: on smooth functions the realization is `P`.
* `TauCeti.dense_domain_chartSobolevRealization`: its domain is dense.
* `TauCeti.isFormalAdjoint_chartSobolevRealization`, `TauCeti.chartSobolevRealization_le_adjoint`:
  formal adjoints give formally adjoint realizations.
* `TauCeti.IsClassicalElliptic.isClosed_chartSobolevRealization`: the realization of an elliptic
  operator is closed.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, 2nd ed., Springer, 2001,
  Chapter I, §8 (operators on a compact manifold as closed operators in `L²`, their closedness
  from the elliptic estimate and their adjoints).
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds).
-/

public section

noncomputable section

open MeasureTheory Set OpenPartialHomeomorph
open scoped ENNReal NNReal ContDiff Manifold Distributions BesselPotentialSpace

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ) {ι : Type*} [Fintype ι]
  {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  (hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (ψ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ))
  (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
  (P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) {m : ℝ} (hm : 0 ≤ m)

/-! ### The realization in `L²` -/

/-- The **realization in `L²(M, μ)`** of an operator `P` on the smooth functions of a compact
manifold, with domain the Sobolev space `H^m(M)` of a chart partition, `m ≥ 0`: the partial
operator `ContinuousLinearMap.domainOperator` of the pair formed by the injection
`TauCeti.chartSobolevToLp : H^m(M) → L²(M, μ)` and `Pₑ = chartSobolevExtension P m 0`, the
extension `H^m(M) → H⁰(M)` of `P` (`TauCeti.chartSobolevExtension`) read in `L²` through
`H⁰(M) = L²(M, μ)`. Its domain is the image of `H^m(M)`, and it sends the image of `x` to that of
`Pₑ x`. The extension is meaningful when `P` satisfies the a priori estimate
`‖P u‖_{H⁰} ≤ C ‖u‖_{H^m}` on smooth functions, for instance when `P` is a classical
pseudodifferential operator of order `m`; it then agrees with `P` on smooth functions
(`TauCeti.chartSobolevRealization_toLp`). Otherwise the extension, and with it the realization, is
a junk value unrelated to `P`. -/
def chartSobolevRealization : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ :=
  ContinuousLinearMap.domainOperator (chartSobolevToLp hμ hc ψ hψ hm)
    ((chartSobolevSpaceZeroEquivLp hμ hc ψ hψ : chartSobolevSpace hc ψ 0 →L[ℂ] Lp ℂ 2 μ) ∘L
      chartSobolevExtension hc ψ hc ψ P m 0)
    (chartSobolevToLp_injective hμ hc ψ hψ hm)

/-- The realization is the partial operator `ContinuousLinearMap.domainOperator` of the injection
`H^m(M) → L²(M, μ)` and the extension of `P` read in `L²`; rewrite with this lemma to apply the
graph, domain and evaluation lemmas of `domainOperator`. -/
theorem chartSobolevRealization_def :
    chartSobolevRealization hμ hc ψ hψ P hm =
      ContinuousLinearMap.domainOperator (chartSobolevToLp hμ hc ψ hψ hm)
        ((chartSobolevSpaceZeroEquivLp hμ hc ψ hψ : chartSobolevSpace hc ψ 0 →L[ℂ] Lp ℂ 2 μ) ∘L
          chartSobolevExtension hc ψ hc ψ P m 0)
        (chartSobolevToLp_injective hμ hc ψ hψ hm) :=
  (rfl)

/-- Smooth functions lie in the domain of the realization. -/
theorem toLp_mem_domain_chartSobolevRealization
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ u ∈
      (chartSobolevRealization hμ hc ψ hψ P hm).domain := by
  rw [chartSobolevRealization_def, ← chartSobolevToLp_toChartSobolevSpace hμ hc ψ hψ hm u]
  exact ContinuousLinearMap.apply_mem_domain_domainOperator _ _ _ _

/-- **On smooth functions the realization is `P`.** For a classical pseudodifferential operator
`P` of order `m`, the realization of `P` sends the class of a smooth function `u` in `L²` to the
class of `P u`. -/
theorem chartSobolevRealization_toLp (hP : P ∈ classicalPseudodifferentialOperators m)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevRealization hμ hc ψ hψ P hm
        ⟨ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ u,
          toLp_mem_domain_chartSobolevRealization hμ hc ψ hψ P hm u⟩ =
      ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ (P u) := by
  -- The domain of the realization depends on it, so `chartSobolevRealization_def` cannot be
  -- rewritten here; `domainOperator_apply` applies through the definitional unfolding instead.
  refine (ContinuousLinearMap.domainOperator_apply _ _ _
    (y := ⟨_, toLp_mem_domain_chartSobolevRealization hμ hc ψ hψ P hm u⟩)
    (chartSobolevToLp_toChartSobolevSpace hμ hc ψ hψ hm u)).trans ?_
  rw [ContinuousLinearMap.comp_apply,
    chartSobolevExtension_toChartSobolevSpace_of_mem hP hψ (by linarith),
    ContinuousLinearEquiv.coe_coe, chartSobolevSpaceZeroEquivLp_toChartSobolevSpace]

/-- The domain `H^m(M)` of the realization is dense in `L²(M, μ)`: it contains the smooth
functions. -/
theorem dense_domain_chartSobolevRealization :
    Dense ((chartSobolevRealization hμ hc ψ hψ P hm).domain : Set (Lp ℂ 2 μ)) :=
  (ContMDiffMap.denseRange_toLp (I := 𝓘(ℝ, CoordinateSpace n)) (μ := μ)).mono <| by
    rintro _ ⟨u, rfl⟩
    exact toLp_mem_domain_chartSobolevRealization hμ hc ψ hψ P hm u

/-- **Formal adjoints have formally adjoint realizations.** If `P` and `Q` are classical
pseudodifferential operators of order `m ≥ 0` and `Q` is a formal adjoint of `P` for `μ`, then
`⟪P f, g⟫ = ⟪f, Q g⟫` in `L²(M, μ)` for `f` and `g` in their common domain `H^m(M)`. -/
theorem isFormalAdjoint_chartSobolevRealization (hP : P ∈ classicalPseudodifferentialOperators m)
    {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ) :
    (chartSobolevRealization hμ hc ψ hψ P hm).IsFormalAdjoint
      (chartSobolevRealization hμ hc ψ hψ Q hm) := by
  rw [chartSobolevRealization_def, chartSobolevRealization_def]
  intro f g
  obtain ⟨x, hx⟩ := (ContinuousLinearMap.mem_domain_domainOperator_iff _ _ _).1 f.property
  obtain ⟨y, hy⟩ := (ContinuousLinearMap.mem_domain_domainOperator_iff _ _ _).1 g.property
  rw [ContinuousLinearMap.domainOperator_apply _ _ _ hx,
    ContinuousLinearMap.domainOperator_apply _ _ _ hy, ← hx, ← hy]
  have h := inner_chartSobolevToLp_eq_of_forall_integral_inner_eq hμ hc ψ hψ hPQ hm le_rfl hm le_rfl
    (chartSobolevExtension_toChartSobolevSpace_of_mem hP hψ (by linarith))
    (chartSobolevExtension_toChartSobolevSpace_of_mem hQ hψ (by linarith)) x y
  simpa using h

/-- **The realization of a formal adjoint lies in the adjoint.** If `P` and `Q` are classical
pseudodifferential operators of order `m ≥ 0` and `Q` is a formal adjoint of `P` for `μ`, the
adjoint of the realization of `P` extends the realization of `Q`. For a formally self-adjoint `P`
this says that the realization of `P` is symmetric. -/
theorem chartSobolevRealization_le_adjoint (hP : P ∈ classicalPseudodifferentialOperators m)
    {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ) :
    chartSobolevRealization hμ hc ψ hψ Q hm ≤ (chartSobolevRealization hμ hc ψ hψ P hm).adjoint :=
  (isFormalAdjoint_chartSobolevRealization hμ hc ψ hψ P hm hP hQ hPQ).le_adjoint
    (dense_domain_chartSobolevRealization hμ hc ψ hψ P hm)

/-- **The realization of an elliptic operator is closed.** If `P` is an elliptic classical
pseudodifferential operator of order `m ≥ 0`, its realization in `L²(M, μ)` with domain `H^m(M)`
is a closed operator: by the elliptic estimate, the norm of the Hilbert space `H^m(M)` is bounded
by the graph norm. -/
theorem IsClassicalElliptic.isClosed_chartSobolevRealization
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P) :
    (chartSobolevRealization hμ hc ψ hψ P hm).IsClosed := by
  rw [chartSobolevRealization_def]
  set J₀ := chartSobolevSpaceZeroEquivLp hμ hc ψ hψ
  -- The norm on `H⁰(M)` is bounded by that on `L²`.
  set E₀ := (J₀.symm : Lp ℂ 2 μ →L[ℂ] chartSobolevSpace hc ψ 0)
  have hJ₀ (y : chartSobolevSpace hc ψ 0) : ‖y‖ ≤ ‖E₀‖ * ‖J₀ y‖ := by
    simpa [E₀] using E₀.le_opNorm (J₀ y)
  obtain ⟨C, hC⟩ := hPe.exists_norm_le_mul_norm_chartSobolevExtension_add hP hc ψ hψ
    (zero_add m) hm
  -- The elliptic estimate bounds the norm of `H^m(M)` by the graph norm.
  refine ContinuousLinearMap.isClosed_domainOperator_of_norm_le (C := |C| * ‖E₀‖) fun x ↦ ?_
  calc ‖x‖ ≤ C * (‖chartSobolevExtension hc ψ hc ψ P m 0 x‖ +
        ‖chartSobolevInclusion hc ψ hm x‖) := hC x
    _ ≤ |C| * (‖E₀‖ * ‖J₀ (chartSobolevExtension hc ψ hc ψ P m 0 x)‖ +
        ‖E₀‖ * ‖J₀ (chartSobolevInclusion hc ψ hm x)‖) :=
        mul_le_mul (le_abs_self C) (add_le_add (hJ₀ _) (hJ₀ _)) (by positivity) (abs_nonneg C)
    _ = |C| * ‖E₀‖ * (‖chartSobolevToLp hμ hc ψ hψ hm x‖ +
        ‖((J₀ : chartSobolevSpace hc ψ 0 →L[ℂ] Lp ℂ 2 μ) ∘L
          chartSobolevExtension hc ψ hc ψ P m 0) x‖) := by
        rw [chartSobolevToLp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
        ring

end TauCeti
