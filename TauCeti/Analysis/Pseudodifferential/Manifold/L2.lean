/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic.Basic
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
public import TauCeti.Geometry.Manifold.Sobolev.L2
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
and its value is then the extension of `P` applied to `f`. On smooth functions it is `P`
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
  (`TauCeti.IsClassicalElliptic.exists_norm_le_mul_norm_chartSobolevExtension_add`): the graph is
  the range of `x ↦ (x, P x)` on the Hilbert space `H^m(M)`, which this estimate bounds below.

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

/-- The map `x ↦ (x, P x)` from `H^m(M)` to `L²(M, μ) × L²(M, μ)`, whose range is the graph of
the realization of `P` (`TauCeti.graph_chartSobolevRealization`). -/
def chartSobolevGraphMap : chartSobolevSpace hc ψ m →L[ℂ] Lp ℂ 2 μ × Lp ℂ 2 μ :=
  (chartSobolevToLp hμ hc ψ hψ hm).prod
    ((chartSobolevSpaceZeroEquivLp hμ hc ψ hψ : chartSobolevSpace hc ψ 0 →L[ℂ] Lp ℂ 2 μ) ∘L
      chartSobolevExtension hc ψ hc ψ P m 0)

@[simp]
theorem chartSobolevGraphMap_apply (x : chartSobolevSpace hc ψ m) :
    chartSobolevGraphMap hμ hc ψ hψ P hm x = (chartSobolevToLp hμ hc ψ hψ hm x,
      chartSobolevSpaceZeroEquivLp hμ hc ψ hψ (chartSobolevExtension hc ψ hc ψ P m 0 x)) :=
  (rfl)

/-- The **realization in `L²(M, μ)`** of an operator `P` on the smooth functions of a compact
manifold, with domain the Sobolev space `H^m(M)` of a chart partition, `m ≥ 0`: the unbounded
operator whose graph is the set of pairs `(x, Pₑ x)` for `x ∈ H^m(M)`, read in `L²(M, μ)` through
`TauCeti.chartSobolevToLp` and `H⁰(M) = L²(M, μ)`, where `Pₑ = chartSobolevExtension P m 0` is the
extension `H^m(M) → H⁰(M)` of `P` (`TauCeti.chartSobolevExtension`). The extension is meaningful
when `P` satisfies the a priori estimate `‖P u‖_{H⁰} ≤ C ‖u‖_{H^m}` on smooth functions, for
instance when `P` is a classical pseudodifferential operator of order `m`; it then agrees with `P`
on smooth functions (`TauCeti.chartSobolevRealization_toLp`). Otherwise the extension, and with it
the realization, is a junk value unrelated to `P`. -/
def chartSobolevRealization : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ :=
  (LinearMap.range (chartSobolevGraphMap hμ hc ψ hψ P hm :
    chartSobolevSpace hc ψ m →ₗ[ℂ] Lp ℂ 2 μ × Lp ℂ 2 μ)).toLinearPMap

/-- The graph of the realization of `P` is the range of `x ↦ (x, P x)` on `H^m(M)`. -/
theorem graph_chartSobolevRealization :
    (chartSobolevRealization hμ hc ψ hψ P hm).graph =
      LinearMap.range (chartSobolevGraphMap hμ hc ψ hψ P hm :
        chartSobolevSpace hc ψ m →ₗ[ℂ] Lp ℂ 2 μ × Lp ℂ 2 μ) := by
  refine Submodule.toLinearPMap_graph_eq _ ?_
  rintro _ ⟨x, rfl⟩ hx
  obtain rfl : x = 0 := chartSobolevToLp_injective hμ hc ψ hψ hm (by simpa using hx)
  simp

/-- `(f, g)` lies on the graph of the realization of `P` exactly when `f` is the image of some
`x ∈ H^m(M)` and `g` that of the extension of `P` applied to `x`. -/
theorem mem_graph_chartSobolevRealization_iff {f g : Lp ℂ 2 μ} :
    (f, g) ∈ (chartSobolevRealization hμ hc ψ hψ P hm).graph ↔
      ∃ x : chartSobolevSpace hc ψ m, chartSobolevToLp hμ hc ψ hψ hm x = f ∧
        chartSobolevSpaceZeroEquivLp hμ hc ψ hψ (chartSobolevExtension hc ψ hc ψ P m 0 x) = g := by
  simp [graph_chartSobolevRealization, Prod.ext_iff]

/-- The domain of the realization of `P` is `H^m(M)`, read in `L²(M, μ)`. -/
theorem mem_domain_chartSobolevRealization_iff {f : Lp ℂ 2 μ} :
    f ∈ (chartSobolevRealization hμ hc ψ hψ P hm).domain ↔
      ∃ x : chartSobolevSpace hc ψ m, chartSobolevToLp hμ hc ψ hψ hm x = f := by
  simp [chartSobolevRealization, Submodule.toLinearPMap_domain]

/-- The image in `L²` of every `x ∈ H^m(M)` lies in the domain of the realization. -/
theorem chartSobolevToLp_mem_domain_chartSobolevRealization (x : chartSobolevSpace hc ψ m) :
    chartSobolevToLp hμ hc ψ hψ hm x ∈ (chartSobolevRealization hμ hc ψ hψ P hm).domain :=
  (mem_domain_chartSobolevRealization_iff hμ hc ψ hψ P hm).2 ⟨x, rfl⟩

/-- On the image `f` of `x ∈ H^m(M)` in `L²`, the realization of `P` is the extension of `P`
applied to `x`. -/
theorem chartSobolevRealization_apply (f : (chartSobolevRealization hμ hc ψ hψ P hm).domain)
    {x : chartSobolevSpace hc ψ m} (hx : chartSobolevToLp hμ hc ψ hψ hm x = f) :
    chartSobolevRealization hμ hc ψ hψ P hm f =
      chartSobolevSpaceZeroEquivLp hμ hc ψ hψ (chartSobolevExtension hc ψ hc ψ P m 0 x) := by
  obtain ⟨y, hy, hPy⟩ := (mem_graph_chartSobolevRealization_iff hμ hc ψ hψ P hm).1
    ((chartSobolevRealization hμ hc ψ hψ P hm).mem_graph f)
  obtain rfl := chartSobolevToLp_injective hμ hc ψ hψ hm (hy.trans hx.symm)
  exact hPy.symm

/-- Smooth functions lie in the domain of the realization. -/
theorem toLp_mem_domain_chartSobolevRealization
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ u ∈
      (chartSobolevRealization hμ hc ψ hψ P hm).domain :=
  (mem_domain_chartSobolevRealization_iff hμ hc ψ hψ P hm).2
    ⟨_, chartSobolevToLp_toChartSobolevSpace hμ hc ψ hψ hm u⟩

/-- **On smooth functions the realization is `P`.** For a classical pseudodifferential operator
`P` of order `m`, the realization of `P` sends the class of a smooth function `u` in `L²` to the
class of `P u`. -/
theorem chartSobolevRealization_toLp (hP : P ∈ classicalPseudodifferentialOperators m)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevRealization hμ hc ψ hψ P hm
        ⟨ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ u,
          toLp_mem_domain_chartSobolevRealization hμ hc ψ hψ P hm u⟩ =
      ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ (P u) := by
  rw [chartSobolevRealization_apply hμ hc ψ hψ P hm _
    (chartSobolevToLp_toChartSobolevSpace hμ hc ψ hψ hm u),
    chartSobolevExtension_toChartSobolevSpace_of_mem hP hψ (by linarith),
    chartSobolevSpaceZeroEquivLp_toChartSobolevSpace]

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
  intro f g
  obtain ⟨x, hx⟩ := (mem_domain_chartSobolevRealization_iff hμ hc ψ hψ P hm).1 f.property
  obtain ⟨y, hy⟩ := (mem_domain_chartSobolevRealization_iff hμ hc ψ hψ Q hm).1 g.property
  rw [chartSobolevRealization_apply hμ hc ψ hψ P hm f hx,
    chartSobolevRealization_apply hμ hc ψ hψ Q hm g hy, ← hx, ← hy]
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
is a closed operator. Its graph is the range of `x ↦ (x, P x)` on the Hilbert space `H^m(M)`,
which the elliptic estimate bounds below, so the range is complete. -/
theorem IsClassicalElliptic.isClosed_chartSobolevRealization
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P) :
    (chartSobolevRealization hμ hc ψ hψ P hm).IsClosed := by
  set J₀ := (chartSobolevSpaceZeroEquivLp hμ hc ψ hψ : chartSobolevSpace hc ψ 0 →L[ℂ] Lp ℂ 2 μ)
  set L := chartSobolevGraphMap hμ hc ψ hψ P hm
  -- The norm on `H⁰(M)` is bounded by that on `L²`.
  set E₀ := ((chartSobolevSpaceZeroEquivLp hμ hc ψ hψ).symm :
    Lp ℂ 2 μ →L[ℂ] chartSobolevSpace hc ψ 0)
  set D := ‖E₀‖
  have hD : 0 ≤ D := norm_nonneg E₀
  have hJ₀ (y : chartSobolevSpace hc ψ 0) : ‖y‖ ≤ D * ‖J₀ y‖ := by
    simpa [J₀, E₀] using E₀.le_opNorm (J₀ y)
  obtain ⟨C, hC⟩ := hPe.exists_norm_le_mul_norm_chartSobolevExtension_add hP hc ψ hψ
    (zero_add m) hm
  -- The elliptic estimate bounds `x ↦ (x, P x)` below.
  have hL (x : chartSobolevSpace hc ψ m) : ‖x‖ ≤ (2 * |C| * D).toNNReal * ‖L x‖ := by
    have h₁ : ‖chartSobolevExtension hc ψ hc ψ P m 0 x‖ ≤ D * ‖L x‖ :=
      (hJ₀ _).trans (mul_le_mul_of_nonneg_left (norm_snd_le (L x)) hD)
    have h₂ : ‖chartSobolevInclusion hc ψ hm x‖ ≤ D * ‖L x‖ :=
      (hJ₀ _).trans (mul_le_mul_of_nonneg_left (by
        simpa only [L, J₀, chartSobolevGraphMap_apply, chartSobolevToLp_apply,
          ContinuousLinearEquiv.coe_coe] using norm_fst_le (L x)) hD)
    rw [Real.coe_toNNReal _ (by positivity)]
    calc ‖x‖ ≤ C * (‖chartSobolevExtension hc ψ hc ψ P m 0 x‖ +
          ‖chartSobolevInclusion hc ψ hm x‖) := hC x
      _ ≤ |C| * (D * ‖L x‖ + D * ‖L x‖) :=
          mul_le_mul (le_abs_self C) (add_le_add h₁ h₂) (by positivity) (abs_nonneg C)
      _ = 2 * |C| * D * ‖L x‖ := by ring
  rw [LinearPMap.IsClosed, graph_chartSobolevRealization, LinearMap.coe_range]
  exact (L.antilipschitz_of_bound hL).isClosed_range L.uniformContinuous

end TauCeti
