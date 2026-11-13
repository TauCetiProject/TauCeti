/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import TauCeti.Topology.ContinuousMap.Ascoli
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Uniform narrow convergence over totally bounded and equicontinuous families

Narrow convergence of finite measures `μs n → μ` tests against one bounded continuous function at a
time. When a family `g : ι → α →ᵇ 𝕜` of `RCLike`-valued bounded continuous functions has totally
bounded range in the supremum metric, a finite `ε`-net reduces the whole family to finitely many
test functions, so the integrals `∫ g i d(μs n)` converge to `∫ g i dμ` uniformly in `i`.

On a compact space `α`, Arzelà–Ascoli (`EquicontinuousOn.exists_finite_approx_of_isCompact`) makes
every equicontinuous, pointwise totally bounded family `g : ι → α → 𝕜` totally bounded in `α →ᵇ 𝕜`.
Narrow convergence therefore upgrades automatically to uniform convergence of integrals over such
families, for both `FiniteMeasure α` and `ProbabilityMeasure α`.

## Main statements

* `MeasureTheory.FiniteMeasure.tendstoUniformly_integral_of_totallyBounded`: narrow convergence of
  finite measures implies uniform convergence of integrals over any family in `α →ᵇ 𝕜` with totally
  bounded range.
* `MeasureTheory.FiniteMeasure.tendstoUniformly_integral_of_equicontinuous`: on a compact space,
  narrow convergence of finite measures implies uniform convergence of integrals over any
  equicontinuous, pointwise totally bounded family `g : ι → α → 𝕜`.
* `MeasureTheory.ProbabilityMeasure.tendstoUniformly_integral_of_totallyBounded` and
  `MeasureTheory.ProbabilityMeasure.tendstoUniformly_integral_of_equicontinuous`: the
  probability-measure specializations.

## References

* R. Ranga Rao, *Relations between weak and uniform convergence of measures with applications*,
  Ann. Math. Statist. 33 (1962), 659–680, Theorem 3.1.
-/

public section

noncomputable section

open Filter Set Topology
open scoped BoundedContinuousFunction

namespace MeasureTheory

variable {α 𝕜 ι γ : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [RCLike 𝕜]

/-- Integration against a finite measure is Lipschitz in the supremum distance on `α →ᵇ 𝕜`, with
constant the total mass of the measure. -/
private theorem dist_integral_boundedContinuousFunction_le (ν : FiniteMeasure α) (f₁ f₂ : α →ᵇ 𝕜) :
    dist (∫ x, f₁ x ∂(ν : Measure α)) (∫ x, f₂ x ∂(ν : Measure α)) ≤
      dist f₁ f₂ * (ν.mass : ℝ) := by
  rw [dist_eq_norm, ← integral_sub (f₁.integrable _) (f₂.integrable _)]
  refine (norm_integral_le_of_norm_le_const (C := dist f₁ f₂) (ae_of_all _ fun x ↦ ?_)).trans_eq ?_
  · rw [← dist_eq_norm]
    exact f₁.dist_coe_le_dist x
  · rw [measureReal_def, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]

omit [MeasurableSpace α] [OpensMeasurableSpace α] in
/-- On a compact space, an equicontinuous and pointwise totally bounded family of functions has
totally bounded range when bundled into `α →ᵇ 𝕜`. -/
private theorem totallyBounded_range_mkOfCompact_of_equicontinuous [CompactSpace α] {g : ι → α → 𝕜}
    (hequi : Equicontinuous g) (hg : ∀ x, TotallyBounded (range fun i ↦ g i x)) :
    TotallyBounded
      (range fun i ↦ BoundedContinuousFunction.mkOfCompact ⟨g i, hequi.continuous i⟩) := by
  refine Metric.totallyBounded_iff.2 fun r hr ↦ ?_
  obtain ⟨t, htf, hcov⟩ := (hequi.equicontinuousOn univ).exists_finite_approx_of_isCompact
    isCompact_univ (fun x _ ↦ hg x) (Metric.dist_mem_uniformity (half_pos hr))
  refine ⟨(fun j ↦ BoundedContinuousFunction.mkOfCompact ⟨g j, hequi.continuous j⟩) '' t,
    htf.image _, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hjt, hij⟩ := hcov i
  refine mem_iUnion₂.2 ⟨_, mem_image_of_mem _ hjt, Metric.mem_ball.2 ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hr).le).2 fun x ↦ ?_)
    (half_lt_self hr)
  exact (hij x (mem_univ x)).le

/-- **Uniform narrow convergence over a totally bounded family.** If finite measures `μs n`
converge narrowly to `μ`, then for every family `g : ι → α →ᵇ 𝕜` with totally bounded range in
`α →ᵇ 𝕜`, the integrals `∫ g i d(μs n)` converge to `∫ g i dμ` uniformly in `i`. -/
theorem FiniteMeasure.tendstoUniformly_integral_of_totallyBounded {l : Filter γ}
    {μs : γ → FiniteMeasure α} {μ : FiniteMeasure α} (hμ : Tendsto μs l (𝓝 μ)) {g : ι → α →ᵇ 𝕜}
    (hg : TotallyBounded (range g)) :
    TendstoUniformly (fun n i ↦ ∫ x, g i x ∂(μs n : Measure α))
      (fun i ↦ ∫ x, g i x ∂(μ : Measure α)) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  set M : ℝ := (μ.mass : ℝ) + 1
  have hM : 0 < M := by positivity
  have hμM : (μ.mass : ℝ) < M := lt_add_one (μ.mass : ℝ)
  obtain ⟨t, htf, hcov⟩ := Metric.totallyBounded_iff.1 hg (ε / (3 * M)) (by positivity)
  have hmass : Tendsto (fun n ↦ ((μs n).mass : ℝ)) l (𝓝 (μ.mass : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp ((FiniteMeasure.continuous_mass.tendsto μ).comp hμ)
  have hnet : ∀ᶠ n in l, ∀ f ∈ t,
      dist (∫ x, f x ∂(μ : Measure α)) (∫ x, f x ∂(μs n : Measure α)) < ε / 3 :=
    (htf.eventually_all).2 fun f _ ↦ by
      have hlim := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜).1 hμ f
      exact (Metric.tendsto_nhds.1 hlim (ε / 3) (by positivity)).mono fun n hn ↦ by
        rwa [dist_comm]
  filter_upwards [hnet, hmass.eventually (eventually_lt_nhds hμM)] with n hn hmn i
  obtain ⟨f, hft, hgf⟩ := mem_iUnion₂.1 (hcov (mem_range_self i))
  rw [Metric.mem_ball] at hgf
  have h1 : dist (∫ x, g i x ∂(μ : Measure α)) (∫ x, f x ∂(μ : Measure α)) < ε / 3 := by
    refine (dist_integral_boundedContinuousFunction_le μ (g i) f).trans_lt ?_
    calc dist (g i) f * (μ.mass : ℝ) < ε / (3 * M) * M :=
          mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hgf.le hμM μ.mass.coe_nonneg (by positivity)
      _ = ε / 3 := by field_simp
  have h3 : dist (∫ x, f x ∂(μs n : Measure α)) (∫ x, g i x ∂(μs n : Measure α)) < ε / 3 := by
    refine (dist_integral_boundedContinuousFunction_le (μs n) f (g i)).trans_lt ?_
    rw [dist_comm]
    calc dist (g i) f * ((μs n).mass : ℝ) < ε / (3 * M) * M :=
          mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hgf.le hmn (μs n).mass.coe_nonneg (by positivity)
      _ = ε / 3 := by field_simp
  calc dist (∫ x, g i x ∂(μ : Measure α)) (∫ x, g i x ∂(μs n : Measure α))
      ≤ dist (∫ x, g i x ∂(μ : Measure α)) (∫ x, f x ∂(μ : Measure α)) +
          dist (∫ x, f x ∂(μ : Measure α)) (∫ x, f x ∂(μs n : Measure α)) +
          dist (∫ x, f x ∂(μs n : Measure α)) (∫ x, g i x ∂(μs n : Measure α)) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add h1 (hn f hft)) h3
    _ = ε := by ring

/-- **Ranga Rao's uniform narrow convergence theorem on a compact space.** If finite measures
`μs n` on a compact space converge narrowly to `μ`, then for every equicontinuous and pointwise
totally bounded family `g : ι → α → 𝕜`, the integrals `∫ g i d(μs n)` converge to `∫ g i dμ`
uniformly in `i`. -/
theorem FiniteMeasure.tendstoUniformly_integral_of_equicontinuous [CompactSpace α] {l : Filter γ}
    {μs : γ → FiniteMeasure α} {μ : FiniteMeasure α} (hμ : Tendsto μs l (𝓝 μ)) {g : ι → α → 𝕜}
    (hequi : Equicontinuous g) (hg : ∀ x, TotallyBounded (range fun i ↦ g i x)) :
    TendstoUniformly (fun n i ↦ ∫ x, g i x ∂(μs n : Measure α))
      (fun i ↦ ∫ x, g i x ∂(μ : Measure α)) l :=
  FiniteMeasure.tendstoUniformly_integral_of_totallyBounded hμ
    (totallyBounded_range_mkOfCompact_of_equicontinuous hequi hg)

/-- **Uniform weak convergence over a totally bounded family.** If probability measures `μs n`
converge weakly to `μ`, then for every family `g : ι → α →ᵇ 𝕜` with totally bounded range in
`α →ᵇ 𝕜`, the integrals `∫ g i d(μs n)` converge to `∫ g i dμ` uniformly in `i`. -/
theorem ProbabilityMeasure.tendstoUniformly_integral_of_totallyBounded {l : Filter γ}
    {μs : γ → ProbabilityMeasure α} {μ : ProbabilityMeasure α} (hμ : Tendsto μs l (𝓝 μ))
    {g : ι → α →ᵇ 𝕜} (hg : TotallyBounded (range g)) :
    TendstoUniformly (fun n i ↦ ∫ x, g i x ∂(μs n : Measure α))
      (fun i ↦ ∫ x, g i x ∂(μ : Measure α)) l :=
  FiniteMeasure.tendstoUniformly_integral_of_totallyBounded
    ((ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds l).1 hμ) hg

/-- **Ranga Rao's uniform weak convergence theorem on a compact space.** If probability measures
`μs n` on a compact space converge weakly to `μ`, then for every equicontinuous and pointwise
totally bounded family `g : ι → α → 𝕜`, the integrals `∫ g i d(μs n)` converge to `∫ g i dμ`
uniformly in `i`. -/
theorem ProbabilityMeasure.tendstoUniformly_integral_of_equicontinuous [CompactSpace α]
    {l : Filter γ} {μs : γ → ProbabilityMeasure α} {μ : ProbabilityMeasure α}
    (hμ : Tendsto μs l (𝓝 μ)) {g : ι → α → 𝕜} (hequi : Equicontinuous g)
    (hg : ∀ x, TotallyBounded (range fun i ↦ g i x)) :
    TendstoUniformly (fun n i ↦ ∫ x, g i x ∂(μs n : Measure α))
      (fun i ↦ ∫ x, g i x ∂(μ : Measure α)) l :=
  FiniteMeasure.tendstoUniformly_integral_of_equicontinuous
    ((ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds l).1 hμ) hequi hg

end MeasureTheory
