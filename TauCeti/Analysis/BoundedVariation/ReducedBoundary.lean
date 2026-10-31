/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.BoundedVariation.PolarDecomposition
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.MeasureTheory.Covering.Besicovitch

/-!
# The reduced boundary and the measure-theoretic outer normal

Let `Ω` be an open set of a finite-dimensional real inner product space `E` and `s` a set of
locally finite perimeter in `Ω`. The derivative of its indicator is the vector measure
`Dχ_s = σ |Dχ_s|`, where `|Dχ_s|` is the perimeter measure (`TauCeti.variationMeasure`) and `σ` is
the polar density (`TauCeti.polarDensity`). A point `x ∈ Ω` belongs to the **reduced boundary**
`∂*s` (`TauCeti.reducedBoundary`) when the averages

`⨍_{closedBall x r} σ d|Dχ_s| = Dχ_s (closedBall x r) / |Dχ_s| (closedBall x r)`

converge, as `r → 0⁺`, to a unit vector. The **measure-theoretic outer normal**
`ν_s x` (`TauCeti.outerNormal`) is minus that limit, so that `Dχ_s = -ν_s |Dχ_s|`.

These are the objects of De Giorgi's structure theorem for sets of finite perimeter. This file
proves their basic properties.

* The perimeter measure is concentrated on the reduced boundary, and the outer normal is `-σ`
  at `|Dχ_s|`-almost every point (`TauCeti.ae_mem_reducedBoundary`,
  `TauCeti.ae_outerNormal_eq`). This is Lebesgue's differentiation theorem for `σ` against the
  Radon measure `|Dχ_s|` on `Ω`, which is available because `Ω` inherits the Besicovitch
  covering property (`Besicovitch.ae_tendsto_average_closedBall`). Consequently
  `∫_s div φ = ∫ ⟪φ, ν_s⟫ d|Dχ_s|` for every test vector field `φ` on `Ω`
  (`TauCeti.integral_divergenceCLM_mul_indicator_eq_integral_inner_outerNormal`).
* A point of the reduced boundary forces `s` to have locally finite perimeter in `Ω`
  (`TauCeti.locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary`), so otherwise
  `∂*s` is empty (`TauCeti.reducedBoundary_eq_empty_of_not`).
* Every point of the reduced boundary lies in the support of `|Dχ_s|`
  (`TauCeti.variationMeasure_preimage_closedBall_ne_zero`), and hence, when `μ` is an additive
  Haar measure, in the topological frontier of `s` (`TauCeti.reducedBoundary_subset_frontier`).
* The reduced boundary and the outer normal only depend on `s` almost everywhere on `Ω`
  (`TauCeti.reducedBoundary_congr_ae`, `TauCeti.outerNormal_congr_ae`). When `μ` is an additive
  Haar measure, the complement has the same reduced boundary with the opposite normal
  (`TauCeti.reducedBoundary_compl`, `TauCeti.outerNormal_compl`).

The definition uses closed balls, matching `TauCeti.HasDensityAt`; it does not require `x` to lie
in the support of `|Dχ_s|`, since a unit limit forces this. When `s` does not have locally finite
perimeter in `Ω`, the perimeter measure is zero by convention and the reduced boundary is empty.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §15.1 (Definition 15.1
  and Proposition 15.5).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric TestFunction
open scoped ENNReal Topology RealInnerProductSpace Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s t : Set E} {x : E}

/-- The **reduced boundary** `∂*s` of `s` in the open set `Ω`: the points `x ∈ Ω` at which the
averages of the polar density `σ` of `Dχ_s` over `closedBall x r`, against the perimeter measure
`|Dχ_s|`, converge to a unit vector as `r → 0⁺`. When `|Dχ_s| (closedBall x r)` is positive and
finite, these averages are the ratios `Dχ_s (closedBall x r) / |Dχ_s| (closedBall x r)`. -/
def reducedBoundary (μ : Measure E) (Ω : Opens E) (s : Set E) : Set E :=
  {x | x ∈ Ω ∧ ∃ ν : E, ‖ν‖ = 1 ∧
    Tendsto (fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
      polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1)) (𝓝[>] 0) (𝓝 ν)}

/-- The **measure-theoretic outer normal** `ν_s x` of `s` in `Ω`: minus the limit, as `r → 0⁺`,
of the averages of the polar density of `Dχ_s` over `closedBall x r` against `|Dχ_s|`. At points
of the reduced boundary it is a unit vector (`TauCeti.norm_outerNormal`), and
`Dχ_s = -ν_s |Dχ_s|`
(`TauCeti.integral_divergenceCLM_mul_indicator_eq_integral_inner_outerNormal`). Elsewhere its
value carries no meaning. -/
def outerNormal (μ : Measure E) (Ω : Opens E) (s : Set E) (x : E) : E :=
  -limUnder (𝓝[>] (0 : ℝ)) fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
    polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1)

/-- Membership in the reduced boundary, unfolded. -/
theorem mem_reducedBoundary : x ∈ reducedBoundary μ Ω s ↔ x ∈ Ω ∧ ∃ ν : E, ‖ν‖ = 1 ∧
    Tendsto (fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
      polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1)) (𝓝[>] 0) (𝓝 ν) :=
  Iff.rfl

/-- The reduced boundary of `s` in `Ω` lies in `Ω`. -/
theorem reducedBoundary_subset : reducedBoundary μ Ω s ⊆ Ω := fun _ hx => hx.1

/-- At a point of the reduced boundary, the averages of the polar density of `Dχ_s` over shrinking
closed balls tend to `-ν_s x`. -/
theorem tendsto_setAverage_polarDensity (hx : x ∈ reducedBoundary μ Ω s) :
    Tendsto (fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
      polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1)) (𝓝[>] 0)
      (𝓝 (-outerNormal μ Ω s x)) := by
  obtain ⟨-, ν, -, hν⟩ := hx
  rw [outerNormal, neg_neg]
  exact tendsto_nhds_limUnder ⟨ν, hν⟩

/-- If the averages of the polar density of `Dχ_s` over shrinking closed balls around `x` tend to
`ν`, then the outer normal at `x` is `-ν`. -/
theorem outerNormal_eq_of_tendsto {ν : E}
    (h : Tendsto (fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
      polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1)) (𝓝[>] 0) (𝓝 ν)) :
    outerNormal μ Ω s x = -ν := by
  rw [outerNormal, h.limUnder_eq]

/-- The outer normal is a unit vector at every point of the reduced boundary. -/
@[simp]
theorem norm_outerNormal (hx : x ∈ reducedBoundary μ Ω s) : ‖outerNormal μ Ω s x‖ = 1 := by
  obtain ⟨-, ν, hν1, hν⟩ := hx
  rw [outerNormal_eq_of_tendsto hν, norm_neg, hν1]

/-- **The reduced boundary lies in the support of the perimeter measure.** Every closed ball of
positive radius around a point of `∂*s` has positive `|Dχ_s|` measure. -/
theorem variationMeasure_preimage_closedBall_ne_zero (hx : x ∈ reducedBoundary μ Ω s) {r : ℝ}
    (hr : 0 < r) :
    variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) ≠ 0 := by
  intro h0
  obtain ⟨-, ν, hν1, hν⟩ := hx
  -- The averages over the smaller balls are averages against the zero measure.
  have h : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x ρ,
      polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1) = 0 := by
    filter_upwards [Ioc_mem_nhdsGT hr] with ρ hρ
    rw [Measure.restrict_eq_zero.2 (measure_mono_null
      (preimage_mono (closedBall_subset_closedBall hρ.2)) h0), average_zero_measure]
  have hν0 := tendsto_nhds_unique hν (tendsto_const_nhds.congr' (h.mono fun _ h => h.symm))
  simp [hν0] at hν1

/-- A point of the reduced boundary forces `s` to have locally finite perimeter in `Ω`: its
indicator is locally integrable on `Ω` and has finite total variation near every compact subset
of `Ω`. -/
theorem locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary
    (hx : x ∈ reducedBoundary μ Ω s) :
    LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ ∧ ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞ := by
  by_contra h
  exact variationMeasure_preimage_closedBall_ne_zero hx one_pos
    (by simp [variationMeasure_eq_zero_of_not h])

/-- The reduced boundary is empty unless `s` has locally finite perimeter in `Ω`. -/
theorem reducedBoundary_eq_empty_of_not (h : ¬(LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ ∧
    ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)) :
    reducedBoundary μ Ω s = ∅ :=
  eq_empty_of_forall_notMem fun _ hx =>
    h (locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx)

/-- **The reduced boundary lies in the topological frontier.** Near a point outside the frontier
of `s`, the indicator of `s` is constant, so the perimeter measure vanishes there. -/
theorem reducedBoundary_subset_frontier [μ.IsAddHaarMeasure] :
    reducedBoundary μ Ω s ⊆ frontier s := by
  intro x hx
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  by_contra hxf
  -- A ball around `x` inside `Ω` lies in `s` or in its complement.
  obtain ⟨V, hV, hVs⟩ : ∃ V ∈ 𝓝 x, V ⊆ s ∨ V ⊆ sᶜ := by
    rw [frontier, Set.mem_sdiff, not_and_or, not_not] at hxf
    rcases hxf with h | h
    · exact ⟨_, isClosed_closure.isOpen_compl.mem_nhds h,
        Or.inr (compl_subset_compl.2 subset_closure)⟩
    · exact ⟨_, isOpen_interior.mem_nhds h, Or.inl interior_subset⟩
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 (inter_mem hV (Ω.isOpen.mem_nhds hx.1))
  have hP : perimeter μ ⟨ball x r, isOpen_ball⟩ s = 0 := by
    rcases hVs with h | h
    · rw [perimeter_congr_ae (t := univ), perimeter_univ]
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      simp [h (hrV hy).1]
    · rw [perimeter_congr_ae (t := ∅), perimeter_empty]
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      simpa using h (hrV hy).1
  have hU := variationMeasure_preimage_coe hu hfin (U := ⟨ball x r, isOpen_ball⟩)
    fun y hy => (hrV hy).2
  rw [Opens.coe_mk, ← perimeter_def, hP] at hU
  exact variationMeasure_preimage_closedBall_ne_zero hx (half_pos hr)
    (measure_mono_null (preimage_mono (closedBall_subset_ball (half_lt_self hr))) hU)

/-- At `|Dχ_s|`-almost every point the polar density has norm one and is the limit of its averages
over shrinking closed balls. -/
private theorem ae_tendsto_setAverage_polarDensity :
    ∀ᵐ y : Ω ∂variationMeasure μ Ω (s.indicator 1), ‖polarDensity μ Ω (s.indicator 1) y‖ = 1 ∧
      Tendsto (fun r => ⨍ z in ((↑) : Ω → E) ⁻¹' closedBall (y : E) r,
        polarDensity μ Ω (s.indicator 1) z ∂variationMeasure μ Ω (s.indicator 1)) (𝓝[>] 0)
        (𝓝 (polarDensity μ Ω (s.indicator 1) y)) := by
  by_cases h : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ ∧ ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞
  · have := Ω.isOpen.locallyCompactSpace
    filter_upwards [ae_norm_polarDensity_eq_one h.1 h.2,
      Besicovitch.ae_tendsto_average_closedBall _ (locallyIntegrable_polarDensity h.1 h.2)]
      with y h1 hy
    simpa only [Subtype.preimage_closedBall] using ⟨h1, hy⟩
  · simp [variationMeasure_eq_zero_of_not h]

/-- **The perimeter measure is concentrated on the reduced boundary**: `|Dχ_s|`-almost every point
of `Ω` lies in `∂*s`. -/
theorem ae_mem_reducedBoundary :
    ∀ᵐ y : Ω ∂variationMeasure μ Ω (s.indicator 1), ↑y ∈ reducedBoundary μ Ω s := by
  filter_upwards [ae_tendsto_setAverage_polarDensity] with y ⟨h1, hy⟩
  exact ⟨y.2, _, h1, hy⟩

/-- The outer normal is minus the polar density of `Dχ_s` at `|Dχ_s|`-almost every point. -/
theorem ae_outerNormal_eq :
    ∀ᵐ y : Ω ∂variationMeasure μ Ω (s.indicator 1),
      outerNormal μ Ω s y = -polarDensity μ Ω (s.indicator 1) y := by
  filter_upwards [ae_tendsto_setAverage_polarDensity] with y hy
  exact outerNormal_eq_of_tendsto hy.2

/-- **`Dχ_s = -ν_s |Dχ_s|`.** For a set of locally finite perimeter in `Ω`, the outer normal
represents the distributional derivative of the indicator against the perimeter measure:
`∫_s div φ dμ = ∫ ⟪φ, ν_s⟫ d|Dχ_s|` for every test vector field `φ` on `Ω`. -/
theorem integral_divergenceCLM_mul_indicator_eq_integral_inner_outerNormal
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (φ : 𝓓(Ω, E)) :
    ∫ x, divergenceCLM φ x * s.indicator 1 x ∂μ =
      ∫ y, ⟪φ y, outerNormal μ Ω s y⟫ ∂variationMeasure μ Ω (s.indicator 1) := by
  rw [integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hu hfin, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [ae_outerNormal_eq] with y hy
  rw [hy, inner_neg_right]

/-! ### Invariance under null modification and complements -/

/-- The averages defining the reduced boundary only depend on `s` almost everywhere on `Ω`. -/
private theorem setAverage_polarDensity_congr_ae (h : s =ᵐ[μ.restrict Ω] t) (x : E) (r : ℝ) :
    ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1) =
      ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity μ Ω (t.indicator 1) y ∂variationMeasure μ Ω (t.indicator 1) := by
  have hst : s.indicator (1 : E → ℝ) =ᵐ[μ.restrict Ω] t.indicator 1 :=
    indicator_ae_eq_of_ae_eq_set h
  rw [← variationMeasure_congr_ae hst]
  exact average_congr (ae_restrict_of_ae (polarDensity_congr_ae hst))

/-- **Locality of the reduced boundary.** If `s = t` almost everywhere on `Ω`, they have the same
reduced boundary in `Ω`. -/
theorem reducedBoundary_congr_ae (h : s =ᵐ[μ.restrict Ω] t) :
    reducedBoundary μ Ω s = reducedBoundary μ Ω t := by
  ext x
  simp only [mem_reducedBoundary, setAverage_polarDensity_congr_ae h]

/-- **Locality of the outer normal.** If `s = t` almost everywhere on `Ω`, they have the same
outer normal. -/
theorem outerNormal_congr_ae (h : s =ᵐ[μ.restrict Ω] t) :
    outerNormal μ Ω s = outerNormal μ Ω t := by
  ext x
  simp only [outerNormal, setAverage_polarDensity_congr_ae h]

/-- Against an additive Haar measure, the averages defining the reduced boundary of `sᶜ` are
opposite to those of `s`. -/
private theorem setAverage_polarDensity_compl [μ.IsAddHaarMeasure] (x : E) (r : ℝ) :
    ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity μ Ω (sᶜ.indicator 1) y ∂variationMeasure μ Ω (sᶜ.indicator 1) =
      -⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1) := by
  have hc : sᶜ.indicator (1 : E → ℝ) = fun y => 1 - s.indicator 1 y := by
    ext y
    by_cases hy : y ∈ s <;> simp [hy]
  rw [hc, variationMeasure_const_sub, ← average_neg]
  exact average_congr (ae_restrict_of_ae (polarDensity_const_sub 1))

/-- **The complement has the same reduced boundary**, against an additive Haar measure. -/
@[simp]
theorem reducedBoundary_compl [μ.IsAddHaarMeasure] :
    reducedBoundary μ Ω sᶜ = reducedBoundary μ Ω s := by
  ext x
  simp only [mem_reducedBoundary, setAverage_polarDensity_compl]
  refine and_congr_right fun _ => ⟨fun ⟨ν, h1, hν⟩ => ⟨-ν, by rwa [norm_neg], ?_⟩,
    fun ⟨ν, h1, hν⟩ => ⟨-ν, by rwa [norm_neg], hν.neg⟩⟩
  simpa using hν.neg

/-- **The complement has the opposite outer normal** at every point of the reduced boundary,
against an additive Haar measure. -/
theorem outerNormal_compl [μ.IsAddHaarMeasure] (hx : x ∈ reducedBoundary μ Ω s) :
    outerNormal μ Ω sᶜ x = -outerNormal μ Ω s x := by
  rw [outerNormal]
  simp only [setAverage_polarDensity_compl]
  rw [(tendsto_setAverage_polarDensity hx).neg.limUnder_eq, neg_neg]

end TauCeti
