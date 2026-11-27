/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.CommonDomain
public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic.Basic
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
public import TauCeti.Geometry.Manifold.Sobolev.L2
import TauCeti.Analysis.InnerProductSpace.LinearPMap.CommonDomain
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain
import TauCeti.Geometry.Manifold.ContMDiffMap.L2
import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic.Estimate
import TauCeti.Analysis.Pseudodifferential.Manifold.Adjoint
import TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix

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
(`TauCeti.chartSobolevRealization`): a function `f ∈ L²` lies in its domain exactly when
`f ∈ H^m(M)` (`TauCeti.mem_domain_chartSobolevRealization_iff`), and its value is then the
extension of `P` applied to `f`. It is the partial operator `LinearMap.domainOperator` of the
pair formed by the injection `H^m(M) → L²(M, μ)` and the extension of `P`; rewrite with
`TauCeti.chartSobolevRealization_def` to use the graph and domain lemmas of `domainOperator`, and
evaluate with `TauCeti.chartSobolevRealization_apply`. On smooth functions it is `P`
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
* **Weak solutions.** If `n ≠ 0` and `P` is elliptic, every weak solution `f ∈ L²(M, μ)` of
  `P f = g ∈ L²(M, μ)`, in the sense that `⟪f, P u⟫ = ⟪g, u⟫` for all smooth `u`, lies in `H^m(M)`
  (`TauCeti.IsClassicalElliptic.exists_chartSobolevToLp_eq_of_forall_inner_eq`). Indeed, for a
  parametrix `S` with `P ∘ S - 1` of order `-∞`, testing against `S u` gives `f = S* g - R* f`,
  where the formal adjoints `S*` and `R*` of `S` and `R = P ∘ S - 1` have order `-m` and so map
  `L²(M, μ)` into `H^m(M)`.
* **Adjoints.** Consequently the adjoint of the realization of an elliptic `P` is the realization
  of its formal adjoint, with the same domain `H^m(M)`
  (`TauCeti.IsClassicalElliptic.adjoint_chartSobolevRealization`): the weak solutions are exactly
  the elements of the domain of the adjoint. In particular the realization of a formally
  self-adjoint elliptic operator is **self-adjoint**
  (`TauCeti.IsClassicalElliptic.isSelfAdjoint_chartSobolevRealization`).

## Main definitions

* `TauCeti.chartSobolevRealization`: the realization of `P` in `L²(M, μ)` with domain `H^m(M)`.

## Main results

* `TauCeti.chartSobolevRealization_toLp`: on smooth functions the realization is `P`.
* `TauCeti.dense_domain_chartSobolevRealization`: its domain is dense.
* `TauCeti.isFormalAdjoint_chartSobolevRealization`, `TauCeti.chartSobolevRealization_le_adjoint`:
  formal adjoints give formally adjoint realizations.
* `TauCeti.IsClassicalElliptic.isClosed_chartSobolevRealization`: the realization of an elliptic
  operator is closed.
* `TauCeti.IsClassicalElliptic.exists_chartSobolevToLp_eq_of_forall_inner_eq`: weak `L²`
  solutions of an elliptic equation lie in `H^m(M)`.
* `TauCeti.IsClassicalElliptic.adjoint_chartSobolevRealization`: the adjoint of the realization of
  an elliptic operator is the realization of its formal adjoint.
* `TauCeti.IsClassicalElliptic.isSelfAdjoint_chartSobolevRealization`: a formally self-adjoint
  elliptic operator has a self-adjoint realization.

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
operator `LinearMap.domainOperator` of the pair formed by the injection
`TauCeti.chartSobolevToLp : H^m(M) → L²(M, μ)` and `Pₑ = chartSobolevExtension P m 0`, the
extension `H^m(M) → H⁰(M)` of `P` (`TauCeti.chartSobolevExtension`) read in `L²` through
`H⁰(M) = L²(M, μ)`. Its domain is the image of `H^m(M)`, and it sends the image of `x` to that of
`Pₑ x`. The extension is meaningful when `P` satisfies the a priori estimate
`‖P u‖_{H⁰} ≤ C ‖u‖_{H^m}` on smooth functions, for instance when `P` is a classical
pseudodifferential operator of order `m`; it then agrees with `P` on smooth functions
(`TauCeti.chartSobolevRealization_toLp`). Otherwise the extension, and with it the realization, is
a junk value unrelated to `P`. -/
def chartSobolevRealization : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ :=
  LinearMap.domainOperator (chartSobolevToLp μ hc ψ hμ hψ hm).toLinearMap
    ((chartSobolevSpaceZeroEquivLp μ hc ψ hμ hψ : chartSobolevSpace hc ψ 0 →L[ℂ] Lp ℂ 2 μ) ∘L
      chartSobolevExtension hc ψ hc ψ P m 0).toLinearMap
    (chartSobolevToLp_injective hc ψ hμ hψ hm)

/-- The realization is the partial operator `LinearMap.domainOperator` of the injection
`H^m(M) → L²(M, μ)` and the extension of `P` read in `L²`; rewrite with this lemma to apply the
graph and domain lemmas of `domainOperator`, and evaluate with
`TauCeti.chartSobolevRealization_apply`. -/
theorem chartSobolevRealization_def :
    chartSobolevRealization hμ hc ψ hψ P hm =
      LinearMap.domainOperator (chartSobolevToLp μ hc ψ hμ hψ hm).toLinearMap
        ((chartSobolevSpaceZeroEquivLp μ hc ψ hμ hψ : chartSobolevSpace hc ψ 0 →L[ℂ] Lp ℂ 2 μ) ∘L
          chartSobolevExtension hc ψ hc ψ P m 0).toLinearMap
        (chartSobolevToLp_injective hc ψ hμ hψ hm) :=
  (rfl)

/-- **Evaluation of the realization.** The realization sends the image in `L²(M, μ)` of
`x ∈ H^m(M)` to the image of `chartSobolevExtension P m 0 x`. -/
theorem chartSobolevRealization_apply {y : (chartSobolevRealization hμ hc ψ hψ P hm).domain}
    {x : chartSobolevSpace hc ψ m} (hx : chartSobolevToLp μ hc ψ hμ hψ hm x = y) :
    chartSobolevRealization hμ hc ψ hψ P hm y =
      chartSobolevSpaceZeroEquivLp μ hc ψ hμ hψ (chartSobolevExtension hc ψ hc ψ P m 0 x) :=
  -- The domain of the realization depends on it, so `chartSobolevRealization_def` cannot be
  -- rewritten here; `domainOperator_apply` applies through the definitional unfolding instead.
  LinearMap.domainOperator_apply _ _ _ hx

/-- **The domain of the realization is `H^m(M)`.** An element of `L²(M, μ)` lies in the domain of
the realization exactly when it is the image of an element of `H^m(M)`. -/
theorem mem_domain_chartSobolevRealization_iff {f : Lp ℂ 2 μ} :
    f ∈ (chartSobolevRealization hμ hc ψ hψ P hm).domain ↔
      ∃ x, chartSobolevToLp μ hc ψ hμ hψ hm x = f := by
  rw [chartSobolevRealization_def]
  exact LinearMap.mem_domain_domainOperator_iff _ _ _

/-- The image in `L²(M, μ)` of an element of `H^m(M)` lies in the domain of the realization. -/
theorem chartSobolevToLp_mem_domain_chartSobolevRealization (x : chartSobolevSpace hc ψ m) :
    chartSobolevToLp μ hc ψ hμ hψ hm x ∈ (chartSobolevRealization hμ hc ψ hψ P hm).domain :=
  (mem_domain_chartSobolevRealization_iff hμ hc ψ hψ P hm).2 ⟨x, rfl⟩

/-- Smooth functions lie in the domain of the realization. -/
theorem toLp_mem_domain_chartSobolevRealization
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ)) ∈
      (chartSobolevRealization hμ hc ψ hψ P hm).domain := by
  rw [← chartSobolevToLp_toChartSobolevSpace hc ψ hμ hψ hm u]
  exact chartSobolevToLp_mem_domain_chartSobolevRealization hμ hc ψ hψ P hm _

/-- **On smooth functions the realization is `P`.** For a classical pseudodifferential operator
`P` of order `m`, the realization of `P` sends the class of a smooth function `u` in `L²` to the
class of `P u`. -/
theorem chartSobolevRealization_toLp (hP : P ∈ classicalPseudodifferentialOperators m)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevRealization hμ hc ψ hψ P hm
        ⟨ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ)),
          toLp_mem_domain_chartSobolevRealization hμ hc ψ hψ P hm u⟩ =
      ContinuousMap.toLp 2 μ ℂ (P u : C(M, ℂ)) := by
  rw [chartSobolevRealization_apply hμ hc ψ hψ P hm
      (chartSobolevToLp_toChartSobolevSpace hc ψ hμ hψ hm u),
    chartSobolevExtension_toChartSobolevSpace_of_mem hP hψ (by linarith),
    chartSobolevSpaceZeroEquivLp_toChartSobolevSpace]

/-- The domain `H^m(M)` of the realization is dense in `L²(M, μ)`: it contains the smooth
functions. -/
theorem dense_domain_chartSobolevRealization :
    Dense ((chartSobolevRealization hμ hc ψ hψ P hm).domain : Set (Lp ℂ 2 μ)) :=
  (ContMDiffMap.denseRange_toL2 (I := 𝓘(ℝ, CoordinateSpace n)) μ).mono <| by
    rintro _ ⟨u, rfl⟩
    rw [SetLike.mem_coe, ContMDiffMap.toL2_apply]
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
  refine LinearMap.isFormalAdjoint_domainOperator_iff.2 fun x y ↦ ?_
  have h := inner_chartSobolevToLp_eq_of_forall_integral_inner_eq hc ψ hμ hψ hPQ hm le_rfl hm
    le_rfl
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
  set J₀ := chartSobolevSpaceZeroEquivLp μ hc ψ hμ hψ
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
    _ = |C| * ‖E₀‖ * (‖chartSobolevToLp μ hc ψ hμ hψ hm x‖ +
        ‖((J₀ : chartSobolevSpace hc ψ 0 →L[ℂ] Lp ℂ 2 μ) ∘L
          chartSobolevExtension hc ψ hc ψ P m 0) x‖) := by
        rw [chartSobolevToLp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
        ring

/-! ### Self-adjointness -/

section SelfAdjoint

/-- Let `T` be a classical pseudodifferential operator of order `-m ≤ 0` with a formal adjoint `T'`
of order `-m`. Then the extension of `T'` to `H⁰(M) → H^m(M)`, read in `L²(M, μ)`, is adjoint to
`T` against smooth functions: `⟪T' g, u⟫ = ⟪g, T u⟫` for `g ∈ L²(M, μ)` and smooth `u`. -/
private theorem inner_chartSobolevToLp_chartSobolevExtension_eq
    {T T' : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hT : T ∈ classicalPseudodifferentialOperators (-m))
    (hT' : T' ∈ classicalPseudodifferentialOperators (-m))
    (hTT' : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, inner ℂ (T u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (T' v x) ∂μ)
    (g : Lp ℂ 2 μ) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    inner ℂ (chartSobolevToLp μ hc ψ hμ hψ hm
        (chartSobolevExtension hc ψ hc ψ T' 0 m
          ((chartSobolevSpaceZeroEquivLp μ hc ψ hμ hψ).symm g)))
        (ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ))) =
      inner ℂ g (ContinuousMap.toLp 2 μ ℂ (T u : C(M, ℂ))) := by
  have hm' : m ≤ 0 - -m := by linarith
  have h := inner_chartSobolevToLp_eq_of_forall_integral_inner_eq hc ψ hμ hψ hTT' le_rfl hm le_rfl
    hm (chartSobolevExtension_toChartSobolevSpace_of_mem hT hψ hm')
    (chartSobolevExtension_toChartSobolevSpace_of_mem hT' hψ hm') (toChartSobolevSpace hc ψ 0 u)
    ((chartSobolevSpaceZeroEquivLp μ hc ψ hμ hψ).symm g)
  simp only [chartSobolevExtension_toChartSobolevSpace_of_mem hT hψ hm',
    chartSobolevToLp_toChartSobolevSpace, chartSobolevToLp_zero, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, chartSobolevSpaceZeroEquivLp_toChartSobolevSpace] at h
  rw [← inner_conj_symm, ← h, inner_conj_symm]

variable [NeZero n] {P}

/-- **Elliptic regularity for weak `L²` solutions.** Let `M` be a compact manifold modelled on `ℝⁿ`
with `n ≠ 0`, `μ` a finite measure with a smooth positive density, and `P` an elliptic classical
pseudodifferential operator of order `m ≥ 0`. If `f, g ∈ L²(M, μ)` satisfy `P f = g` weakly, in the
sense that `⟪f, P u⟫ = ⟪g, u⟫` for every smooth `u`, then `f` lies in the Sobolev space `H^m(M)`.
-/
theorem IsClassicalElliptic.exists_chartSobolevToLp_eq_of_forall_inner_eq
    (hPe : IsClassicalElliptic m P) {f g : Lp ℂ 2 μ}
    (hfg : ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      inner ℂ f (ContinuousMap.toLp 2 μ ℂ (P u : C(M, ℂ))) =
        inner ℂ g (ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ)))) :
    ∃ x : chartSobolevSpace hc ψ m, chartSobolevToLp μ hc ψ hμ hψ hm x = f := by
  -- A right parametrix `S` of order `-m`, with `R = P ∘ S - 1` of order `-∞`, and the formal
  -- adjoints `S'` and `R'` of `S` and `R`, of order `-m`.
  obtain ⟨S, hS, hR, -⟩ := hPe.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators
    (isProperlySupported_of_compactSpace P)
  set R := P ∘ₗ S - LinearMap.id with hR_def
  obtain ⟨S', hS', hSS', -⟩ :=
    exists_mem_classicalPseudodifferentialOperators_forall_integral_inner_eq hμ hS
  obtain ⟨R', hR', hRR', -⟩ :=
    exists_mem_classicalPseudodifferentialOperators_forall_integral_inner_eq hμ
      (smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators (-m) hR)
  set J₀ := chartSobolevSpaceZeroEquivLp μ hc ψ hμ hψ
  refine ⟨chartSobolevExtension hc ψ hc ψ S' 0 m (J₀.symm g) -
    chartSobolevExtension hc ψ hc ψ R' 0 m (J₀.symm f), ext_inner_right ℂ fun w ↦ ?_⟩
  -- Both sides have the same inner products with the classes of smooth functions, which are dense.
  refine (ContMDiffMap.denseRange_toLp (I := 𝓘(ℝ, CoordinateSpace n)) μ ℂ).induction_on w
    (isClosed_eq (by fun_prop) (by fun_prop)) fun u ↦ ?_
  -- Testing against `u`: `⟪f, u⟫ = ⟪f, P (S u)⟫ - ⟪f, R u⟫ = ⟪g, S u⟫ - ⟪f, R u⟫`.
  have hRu : ContinuousMap.toLp 2 μ ℂ (R u : C(M, ℂ)) =
      ContinuousMap.toLp 2 μ ℂ (P (S u) : C(M, ℂ)) - ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ)) := by
    simp only [← ContMDiffMap.toL2_apply, hR_def, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, map_sub]
  rw [map_sub, inner_sub_left,
    inner_chartSobolevToLp_chartSobolevExtension_eq hμ hc ψ hψ hm hS hS' hSS',
    inner_chartSobolevToLp_chartSobolevExtension_eq hμ hc ψ hψ hm
      (smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators (-m) hR) hR'
      hRR',
    hRu, inner_sub_right, hfg, sub_sub_cancel]

/-- **The adjoint of the realization is the realization of the formal adjoint.** Let `M` be a
compact manifold modelled on `ℝⁿ` with `n ≠ 0`, `μ` a finite measure with a smooth positive
density, and `P` an elliptic classical pseudodifferential operator of order `m ≥ 0` with a formal
adjoint `Q`: `∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ` for all smooth `u` and `v`. Then the adjoint of the
realization of `P` in `L²(M, μ)` with domain `H^m(M)` is the realization of `Q`, with the same
domain `H^m(M)`. -/
theorem IsClassicalElliptic.adjoint_chartSobolevRealization (hPe : IsClassicalElliptic m P)
    {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ) :
    (chartSobolevRealization hμ hc ψ hψ P hm).adjoint =
      chartSobolevRealization hμ hc ψ hψ Q hm := by
  have hP := hPe.mem_of_isProperlySupported (isProperlySupported_of_compactSpace P)
  have hQ := mem_classicalPseudodifferentialOperators_of_forall_integral_inner_eq hμ hP
    (isProperlySupported_of_compactSpace Q) fun u v _ _ ↦ hPQ u v
  have hle := chartSobolevRealization_le_adjoint hμ hc ψ hψ P hm hP hQ hPQ
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun f hf ↦ ?_)).symm
  -- An element `f` of the domain of the adjoint solves `P f = g` weakly, for `g` its image.
  obtain ⟨x, rfl⟩ := hPe.exists_chartSobolevToLp_eq_of_forall_inner_eq hμ hc ψ hψ hm
    (g := (chartSobolevRealization hμ hc ψ hψ P hm).adjoint ⟨f, hf⟩) fun u ↦ by
      have h := LinearPMap.adjoint_isFormalAdjoint (dense_domain_chartSobolevRealization hμ hc ψ hψ
        P hm) ⟨f, hf⟩ ⟨_, toLp_mem_domain_chartSobolevRealization hμ hc ψ hψ P hm u⟩
      rw [chartSobolevRealization_toLp hμ hc ψ hψ P hm hP u] at h
      exact h.symm
  exact chartSobolevToLp_mem_domain_chartSobolevRealization hμ hc ψ hψ Q hm x

/-- **Formally self-adjoint elliptic operators have self-adjoint realizations.** On a compact
manifold modelled on `ℝⁿ` with `n ≠ 0`, with a finite measure `μ` that has a smooth positive
density, the realization in `L²(M, μ)` with domain `H^m(M)` of a formally self-adjoint elliptic
classical pseudodifferential operator of order `m ≥ 0` is self-adjoint. -/
theorem IsClassicalElliptic.isSelfAdjoint_chartSobolevRealization (hPe : IsClassicalElliptic m P)
    (hPP : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (P v x) ∂μ) :
    IsSelfAdjoint (chartSobolevRealization hμ hc ψ hψ P hm) :=
  LinearPMap.isSelfAdjoint_def.mpr (hPe.adjoint_chartSobolevRealization hμ hc ψ hψ hm hPP)

end SelfAdjoint

end TauCeti
