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
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.InnerProductSpace.CompleteSquare
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
  covering property (`Besicovitch.ae_tendsto_average_closedBall`). Consequently the
  **Gauss–Green formula** `∫_s div φ = ∫ ⟪φ, ν_s⟫ d|Dχ_s|` holds for every `C¹` vector field `φ`
  with compact support in `Ω`, where `div φ = tr (Dφ)`
  (`TauCeti.integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal`). It is the case
  `u = χ_s` of integration by parts against `C¹` vector fields,
  `∫ u div φ dμ = -∫ ⟪φ, σ_u⟫ d|Du|`
  (`TauCeti.integral_trace_fderiv_mul_eq_neg_integral_inner_polarDensity`).
* A point of the reduced boundary forces `s` to have locally finite perimeter in `Ω`
  (`TauCeti.locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary`), and in
  particular to be null-measurable on `Ω`
  (`TauCeti.nullMeasurableSet_restrict_of_mem_reducedBoundary`), so otherwise `∂*s` is empty
  (`TauCeti.reducedBoundary_eq_empty_of_not`).
* Every point of the reduced boundary lies in the support of `|Dχ_s|`
  (`TauCeti.variationMeasure_preimage_closedBall_ne_zero`). Hence `s` has nonzero perimeter and
  positive measure in every small ball around it (`TauCeti.perimeter_ball_ne_zero`,
  `TauCeti.measure_inter_ball_pos`), and, when `μ` is an additive Haar measure, the point lies in
  the topological frontier of `s` (`TauCeti.reducedBoundary_subset_frontier`).
* The outer normal concentrates at `ν_s x` in mean at every point `x` of the reduced boundary:
  `⨍_{closedBall x r} ‖ν_s - ν_s x‖ d|Dχ_s| → 0`
  (`TauCeti.tendsto_setLIntegral_enorm_outerNormal_sub_div`). The averages of the unit vectors
  `ν_s` tend to the unit vector `ν_s x`, and for unit vectors `‖a - ν‖² = 2 (1 - ⟪a, ν⟫)`.
* The reduced boundary and the outer normal only depend on `s` almost everywhere on `Ω`
  (`TauCeti.reducedBoundary_congr_ae`, `TauCeti.outerNormal_congr_ae`); in particular
  `∂*(s ∩ Ω) = ∂*s` (`TauCeti.reducedBoundary_inter_opens`). When `μ` is an additive
  Haar measure, the complement has the same reduced boundary with the opposite normal
  (`TauCeti.reducedBoundary_compl`, `TauCeti.outerNormal_compl`).

The definition uses closed balls, matching `TauCeti.HasDensityAt`; it does not require `x` to lie
in the support of `|Dχ_s|`, since a unit limit forces this. When `s` does not have locally finite
perimeter in `Ω`, the perimeter measure is zero by convention and the reduced boundary is empty.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §15.1 (Definition 15.1
  and Proposition 15.5) and Chapter 15 (blow-ups at points of the reduced boundary).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1 (the
  Gauss–Green measure of a set of locally finite perimeter).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace

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
(`TauCeti.integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal`). Elsewhere its
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

/-- A point of the reduced boundary forces `s` to be null-measurable on `Ω`. -/
theorem nullMeasurableSet_restrict_of_mem_reducedBoundary (hx : x ∈ reducedBoundary μ Ω s) :
    NullMeasurableSet s (μ.restrict Ω) :=
  (aemeasurable_indicator_const_iff (1 : ℝ)).1
    (locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary
      hx).1.aestronglyMeasurable.aemeasurable

/-- A point of the reduced boundary of `s` in `Ω` forces `s ∩ Ω` to be null-measurable. -/
theorem nullMeasurableSet_inter_of_mem_reducedBoundary (hx : x ∈ reducedBoundary μ Ω s) :
    NullMeasurableSet (s ∩ Ω) μ :=
  (nullMeasurableSet_restrict Ω.isOpen.measurableSet.nullMeasurableSet).1
    (nullMeasurableSet_restrict_of_mem_reducedBoundary hx)

/-- At a point of the reduced boundary, the perimeter of `s` in every ball around the point that
lies in `Ω` is nonzero. -/
theorem perimeter_ball_ne_zero (hx : x ∈ reducedBoundary μ Ω s) {r : ℝ} (hr : 0 < r)
    (hrΩ : ball x r ⊆ Ω) : perimeter μ ⟨ball x r, isOpen_ball⟩ s ≠ 0 := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  intro hP
  have hU := variationMeasure_preimage_coe hu hfin (U := ⟨ball x r, isOpen_ball⟩) hrΩ
  rw [Opens.coe_mk, ← perimeter_def, hP] at hU
  exact variationMeasure_preimage_closedBall_ne_zero hx (half_pos hr)
    (measure_mono_null (preimage_mono (closedBall_subset_ball (half_lt_self hr))) hU)

/-- At a point of the reduced boundary, `s` charges every ball around the point. -/
theorem measure_inter_ball_pos (hx : x ∈ reducedBoundary μ Ω s) {r : ℝ} (hr : 0 < r) :
    0 < μ (s ∩ ball x r) := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  set ρ := min r ε
  refine (measure_mono (inter_subset_inter_right s (ball_subset_ball (min_le_left r ε)))).trans_lt'
    (pos_iff_ne_zero.2 fun h0 => perimeter_ball_ne_zero hx (lt_min hr hε)
      ((ball_subset_ball (min_le_right r ε)).trans hεΩ) ?_)
  -- Otherwise `s` is null in `ball x ρ`, so its perimeter there vanishes.
  rw [perimeter_congr_ae (t := ∅), perimeter_empty]
  rw [Opens.coe_mk, ae_eq_empty, Measure.restrict_apply' measurableSet_ball, h0]

/-- **The reduced boundary lies in the topological frontier.** Near a point outside the frontier
of `s`, the indicator of `s` is constant, so the perimeter measure vanishes there. -/
theorem reducedBoundary_subset_frontier [μ.IsAddHaarMeasure] :
    reducedBoundary μ Ω s ⊆ frontier s := by
  intro x hx
  by_contra hxf
  -- A ball around `x` inside `Ω` lies in `s` or in its complement.
  obtain ⟨V, hV, hVs⟩ : ∃ V ∈ 𝓝 x, V ⊆ s ∨ V ⊆ sᶜ := by
    rw [frontier, Set.mem_sdiff, not_and_or, not_not] at hxf
    rcases hxf with h | h
    · exact ⟨_, isClosed_closure.isOpen_compl.mem_nhds h,
        Or.inr (compl_subset_compl.2 subset_closure)⟩
    · exact ⟨_, isOpen_interior.mem_nhds h, Or.inl interior_subset⟩
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 (inter_mem hV (Ω.isOpen.mem_nhds hx.1))
  refine perimeter_ball_ne_zero hx hr (fun y hy => (hrV hy).2) ?_
  rcases hVs with h | h
  · rw [perimeter_congr_ae (t := univ), perimeter_univ]
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    simp [h (hrV hy).1]
  · rw [perimeter_congr_ae (t := ∅), perimeter_empty]
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    simpa using h (hrV hy).1

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

/-- **The Gauss–Green formula, `Dχ_s = -ν_s |Dχ_s|`.** For a set `s` of locally finite perimeter
in `Ω`, the outer normal `ν_s` represents the distributional derivative of the indicator against
the perimeter measure: `∫_s div φ dμ = ∫ ⟪φ, ν_s⟫ d|Dχ_s|` for every `C¹` vector field `φ` with
compact support in `Ω`, where `div φ = tr (Dφ)`. -/
theorem integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x ∂μ =
      ∫ y, ⟪φ y, outerNormal μ Ω s y⟫ ∂variationMeasure μ Ω (s.indicator 1) := by
  rw [integral_trace_fderiv_mul_eq_neg_integral_inner_polarDensity hu hfin hφ hc hs,
    ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [ae_outerNormal_eq] with y hy
  rw [hy, inner_neg_right]

/-! ### Concentration of the outer normal -/

/-- The outer normal is integrable against the perimeter measure on sets of finite measure. -/
theorem integrableOn_outerNormal {S : Set Ω} (hS : variationMeasure μ Ω (s.indicator 1) S ≠ ∞) :
    IntegrableOn (fun y : Ω => outerNormal μ Ω s y) S (variationMeasure μ Ω (s.indicator 1)) := by
  refine Measure.integrableOn_of_bounded hS ?_ (M := 1) ?_
  · exact (measurable_polarDensity (μ := μ) (Ω := Ω) (u := s.indicator 1)).neg
      |>.aestronglyMeasurable.congr (ae_outerNormal_eq.mono fun _ h => h.symm)
  · filter_upwards [ae_restrict_of_ae ae_mem_reducedBoundary] with y hy
    exact (norm_outerNormal hy).le

/-- At a point `x` of the reduced boundary, for every `η > 0` and every small `r`, the perimeter
measure of `closedBall x r` is finite and
`∫_{closedBall x r} ‖ν_s - ν_s x‖ d|Dχ_s| ≤ 2 η |Dχ_s| (closedBall x r)`. -/
theorem eventually_setIntegral_norm_outerNormal_sub_le
    (hx : x ∈ reducedBoundary μ Ω s) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] 0,
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) ≠ ∞ ∧
      ∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
          ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖ ∂variationMeasure μ Ω (s.indicator 1) ≤
        2 * η * (variationMeasure μ Ω (s.indicator 1)).real
          (((↑) : Ω → E) ⁻¹' closedBall x r) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  set lam := variationMeasure μ Ω (s.indicator 1)
  set ν := outerNormal μ Ω s x
  set n : Ω → E := fun y => outerNormal μ Ω s y
  have hν : ‖ν‖ = 1 := norm_outerNormal hx
  have hn1 : ∀ᵐ y ∂lam, ‖n y‖ = 1 := by
    filter_upwards [ae_outerNormal_eq, ae_norm_polarDensity_eq_one hu hfin] with y h1 h2
    simp only [n, h1, norm_neg, h2]
  -- The averages of `ν_s` over small balls tend to `ν`.
  have havg : Tendsto (fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r, n y ∂lam) (𝓝[>] 0)
      (𝓝 ν) := by
    have h := (tendsto_setAverage_polarDensity hx).neg
    rw [neg_neg] at h
    refine h.congr fun r => ?_
    rw [← average_neg]
    exact average_congr (ae_restrict_of_ae (ae_outerNormal_eq.mono fun _ h => h.symm))
  have hinner : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      1 - η ^ 2 / 2 < ⟪ν, ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r, n y ∂lam⟫ := by
    refine (tendsto_const_nhds.inner havg).eventually_const_lt ?_
    rw [real_inner_self_eq_norm_sq, hν]
    linarith [pow_pos hη 2]
  obtain ⟨ε, hε, hεΩ⟩ :=
    nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [hinner, Ioc_mem_nhdsGT hε] with r hr hrε
  set S := ((↑) : Ω → E) ⁻¹' closedBall x r
  have hS : IsCompact S := Topology.IsInducing.subtypeVal.isCompact_preimage'
    (isCompact_closedBall x r) (by
      rw [Subtype.range_coe]
      exact (closedBall_subset_closedBall hrε.2).trans hεΩ)
  have hSfin : lam S ≠ ∞ := hS.measure_lt_top.ne
  refine ⟨hSfin, ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hn : IntegrableOn n S lam := integrableOn_outerNormal hSfin
  have hc (c : ℝ) : IntegrableOn (fun _ => c) S lam := integrableOn_const hSfin
  have hν' : IntegrableOn (fun _ => ν) S lam := integrableOn_const hSfin
  have hin : IntegrableOn (fun y => ⟪ν, n y⟫) S lam := Integrable.const_inner ν hn
  calc ∫ y in S, ‖n y - ν‖ ∂lam
      ≤ ∫ y in S, ((η / 2 + 1 / η) - 1 / η * ⟪ν, n y⟫) ∂lam := by
        refine setIntegral_mono_on_ae (hn.sub hν').norm ((hc _).sub (hin.const_mul _)) hSm ?_
        filter_upwards [hn1] with y hy _
        exact norm_sub_le_add_div_sub_inner hy hν hη
    _ = lam.real S * ((η / 2 + 1 / η) - 1 / η * ⟪ν, ⨍ y in S, n y ∂lam⟫) := by
        rw [integral_sub (hc _) (hin.const_mul _), integral_const_mul, integral_inner hn,
          setIntegral_const, ← measure_smul_setAverage _ hSfin, inner_smul_right, smul_eq_mul]
        ring
    _ ≤ 2 * η * lam.real S := by
        have hle : (η / 2 + 1 / η) - 1 / η * ⟪ν, ⨍ y in S, n y ∂lam⟫ ≤ 2 * η := by
          have h2 : 1 / η * (1 - η ^ 2 / 2) = 1 / η - η / 2 := by field_simp
          nlinarith [mul_lt_mul_of_pos_left hr (one_div_pos.2 hη)]
        nlinarith [measureReal_nonneg (μ := lam) (s := S)]

/-- **Concentration of the outer normal at the reduced boundary.** At a point `x` of the reduced
boundary of `s` in `Ω`, the mean deviation of the outer normal from `ν_s x` over small closed
balls tends to zero:

`(∫_{closedBall x r} ‖ν_s - ν_s x‖ d|Dχ_s|) / |Dχ_s| (closedBall x r) → 0`  as `r → 0⁺`. -/
theorem tendsto_setLIntegral_enorm_outerNormal_sub_div (hx : x ∈ reducedBoundary μ Ω s) :
    Tendsto (fun r => (∫⁻ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖ₑ ∂variationMeasure μ Ω (s.indicator 1)) /
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
  set lam := variationMeasure μ Ω (s.indicator 1)
  refine ENNReal.tendsto_nhds_zero.2 fun δ hδ => ?_
  obtain rfl | hδt := eq_or_ne δ ∞
  · exact .of_forall fun _ => le_top
  have hδr : 0 < δ.toReal / 2 := half_pos (ENNReal.toReal_pos hδ.ne' hδt)
  filter_upwards [eventually_setIntegral_norm_outerNormal_sub_le hx hδr] with r ⟨hSfin, hr⟩
  set S := ((↑) : Ω → E) ⁻¹' closedBall x r
  refine ENNReal.div_le_of_le_mul ?_
  have hi : IntegrableOn (fun y : Ω => outerNormal μ Ω s y - outerNormal μ Ω s x) S lam :=
    (integrableOn_outerNormal hSfin).sub (integrableOn_const hSfin)
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
  calc ENNReal.ofReal (∫ y in S, ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖ ∂lam)
      ≤ ENNReal.ofReal (2 * (δ.toReal / 2) * lam.real S) := ENNReal.ofReal_le_ofReal hr
    _ = δ * lam S := by
        rw [mul_div_cancel₀ _ two_ne_zero, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hδt, ofReal_measureReal hSfin]


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

/-- Intersecting `s` with `Ω` does not change its reduced boundary in `Ω`. -/
@[simp]
theorem reducedBoundary_inter_opens : reducedBoundary μ Ω (s ∩ Ω) = reducedBoundary μ Ω s := by
  refine reducedBoundary_congr_ae ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
  exact propext ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩

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
