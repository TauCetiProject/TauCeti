/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import TauCeti.MeasureTheory.Integral.Lebesgue.Semicontinuity

/-!
# Measures below a fiber measure

Let `π : X → B` be a map, `μ` a measure on `X`, and `ν` a measure on `B`. For a submersion of
manifolds with smooth positive measures, the fiber measures `dμ / dν` on the fibers of `π` are
determined by disintegration against `ν` and continuity of fiber integrals of compactly supported
continuous functions. This file does not construct fiber measures; instead it defines the relation
`TauCeti.IsLeFiberMeasure μ ν π b l` asserting that `l` is at most the fiber measure `dμ / dν` over
`b`, and proves that this relation is preserved under coordinate parametrizations, monotonicity,
a.e. congruence, finite scaling, base homeomorphisms, two-step fibrations, and fiber-preserving
maps.

## Main definitions and results

* `TauCeti.IsLeFiberMeasure`: a measure `l` is at most the fiber measure `dμ / dν` of `π` over `b`,
  with unfolding lemma `TauCeti.isLeFiberMeasure_iff`, `TauCeti.IsLeFiberMeasure.lintegral_le`, and
  `MeasureTheory.Measure.isLeFiberMeasure_zero`.
* `Measurable.isLeFiberMeasure_of_coordinates` and
  `MeasureTheory.MeasurePreserving.isLeFiberMeasure`: local coordinates or a measure-preserving
  product parametrization yield a measure below the fiber measure.
* `TauCeti.IsLeFiberMeasure.mono`, `TauCeti.IsLeFiberMeasure.congr`,
  `TauCeti.IsLeFiberMeasure.smul`, `TauCeti.IsLeFiberMeasure.comp_homeomorph`: basic closure
  properties.
* `TauCeti.IsLeFiberMeasure.trans`: two-step fibration rule for `(π, π₂)`.
* `TauCeti.IsLeFiberMeasure.map_prod` and `TauCeti.IsLeFiberMeasure.map`: pushforward along
  fiber-preserving families with almost everywhere continuous sections.

## References

* A. Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113
  (1965), 1–87, no. 6 (fiber measures).
* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  `New.LeFibreMeasure` in `src/Lib/General/Measure/FibreMeasure.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

open MeasureTheory Measure Filter Topology Set ENNReal

namespace TauCeti

variable {X X' B B' P : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace X']
  [MeasurableSpace X'] [TopologicalSpace B] [MeasurableSpace B] [TopologicalSpace B']
  [MeasurableSpace B'] [MeasurableSpace P]

/-- The measure `l` is at most the fiber measure `dμ / dν` of the map `π : X → B` over the point
`b`: for every lower semicontinuous `K : X → ℝ≥0∞`, a bound `∫⁻ x in π ⁻¹' S, K x ∂μ ≤ C * ν S`
for all open sets `S` contained in some fixed neighborhood of `b` gives `∫⁻ x, K x ∂l ≤ C`. -/
def IsLeFiberMeasure (μ : Measure X) (ν : Measure B) (π : X → B) (b : B) (l : Measure X) : Prop :=
  ∀ K : X → ℝ≥0∞, LowerSemicontinuous K → ∀ C : ℝ≥0∞,
    (∀ᶠ S : Set B in (𝓝 b).smallSets, IsOpen S → ∫⁻ x : X in π ⁻¹' S, K x ∂μ ≤ C * ν S) →
    ∫⁻ x : X, K x ∂l ≤ C

/-- Unfolding lemma for `IsLeFiberMeasure`. -/
theorem isLeFiberMeasure_iff {μ l : Measure X} {ν : Measure B} {π : X → B} {b : B} :
    IsLeFiberMeasure μ ν π b l ↔
      ∀ K : X → ℝ≥0∞, LowerSemicontinuous K → ∀ C : ℝ≥0∞,
        (∀ᶠ S : Set B in (𝓝 b).smallSets, IsOpen S → ∫⁻ x : X in π ⁻¹' S, K x ∂μ ≤ C * ν S) →
        ∫⁻ x : X, K x ∂l ≤ C :=
  Iff.rfl

namespace IsLeFiberMeasure

variable {μ μ' l l' : Measure X} {ν ν' : Measure B} {π π' : X → B} {b : B}

/-- Applying `IsLeFiberMeasure` to a lower semicontinuous integrand `K : X → ℝ≥0∞`. -/
theorem lintegral_le (hl : IsLeFiberMeasure μ ν π b l) {K : X → ℝ≥0∞}
    (hK : LowerSemicontinuous K) {C : ℝ≥0∞}
    (hC : ∀ᶠ S : Set B in (𝓝 b).smallSets, IsOpen S → ∫⁻ x : X in π ⁻¹' S, K x ∂μ ≤ C * ν S) :
    ∫⁻ x : X, K x ∂l ≤ C :=
  hl K hK C hC

/-- The zero measure is below every fiber measure. -/
@[simp]
theorem _root_.MeasureTheory.Measure.isLeFiberMeasure_zero
    (μ : Measure X) (ν : Measure B) (π : X → B) (b : B) :
    IsLeFiberMeasure μ ν π b 0 := fun _ _ _ _ ↦ by simp

/-- Let `(t, p) ↦ ψ t p`, for `t` in a neighborhood `V` of `b`, parametrize a part of `X` so that
`π (ψ t p) = t` for almost every `p` with `w t p ≠ 0` and `μ` dominates `w t p dν(t) dρ(p)` there.
Suppose `ν` is finite on some neighborhood of `b`. If `ψ` is continuous and `w` is lower
semicontinuous in `t` at `b` for almost every `p`, then `(ρ.withDensity (w b)).map (ψ b)` is at
most the fiber measure `dμ / dν` of `π` over `b`. -/
theorem _root_.Measurable.isLeFiberMeasure_of_coordinates
    [OpensMeasurableSpace X] [OpensMeasurableSpace B]
    [IsCountablyGenerated (𝓝 b)] [ν.IsOpenPosMeasure] {ρ : Measure P}
    {ψ : B → P → X} {w : B → P → ℝ≥0∞} {V : Set B} (hπ : Measurable π)
    (hν : ν.FiniteAtFilter (𝓝 b))
    (hψ : ∀ t, Measurable (ψ t)) (hw : ∀ t, Measurable (w t)) (hV : V ∈ 𝓝 b)
    (h_fiber : ∀ t ∈ V, ∀ᵐ p : P ∂ρ, w t p ≠ 0 → π (ψ t p) = t)
    (h_reg : ∀ᵐ p : P ∂ρ, ContinuousAt (ψ · p) b ∧ LowerSemicontinuousAt (w · p) b)
    (h_le : ∀ K : X → ℝ≥0∞, Measurable K →
      ∫⁻ t : B in V, ∫⁻ p : P, w t p * K (ψ t p) ∂ρ ∂ν ≤ ∫⁻ x : X, K x ∂μ) :
    IsLeFiberMeasure μ ν π b ((ρ.withDensity (w b)).map (ψ b)) := by
  intro K hK C hC
  let A (t : B) : ℝ≥0∞ := ∫⁻ p, w t p * K (ψ t p) ∂ρ
  have hK_meas : Measurable K := hK.measurable
  have hA : LowerSemicontinuousAt A b := by
    refine lowerSemicontinuousAt_lintegral (fun t ↦ ((hw t).mul (hK_meas.comp (hψ t))).aemeasurable)
      (h_reg.mono fun p ⟨hψ_cont, hw_lsc⟩ ↦ ?_)
    rw [lowerSemicontinuousAt_iff_le_liminf]
    calc
      w b p * K (ψ b p) ≤ liminf (w · p) (𝓝 b) * liminf (fun t ↦ K (ψ t p)) (𝓝 b) :=
        mul_le_mul' (lowerSemicontinuousAt_iff_le_liminf.1 hw_lsc)
          (lowerSemicontinuousAt_iff_le_liminf.1 ((hK _).comp hψ_cont))
      _ ≤ liminf (fun t ↦ w t p * K (ψ t p)) (𝓝 b) := ENNReal.le_liminf_mul
  rw [lintegral_map hK_meas (hψ b),
    lintegral_withDensity_eq_lintegral_mul _ (hw b) (by fun_prop)]
  refine hA.le_of_setLIntegral_le hν ?_
  filter_upwards [hC, eventually_smallSets_subset.2 hV] with S hS hS_sub hS_open
  have hπS : MeasurableSet (π ⁻¹' S) := hπ hS_open.measurableSet
  calc
    ∫⁻ t in S, A t ∂ν = ∫⁻ t in S, ∫⁻ p, w t p * (π ⁻¹' S).indicator K (ψ t p) ∂ρ ∂ν := by
      refine setLIntegral_congr_fun hS_open.measurableSet fun t ht ↦ lintegral_congr_ae ?_
      filter_upwards [h_fiber t (hS_sub ht)] with p hp
      by_cases h_zero : w t p = 0
      · simp [h_zero]
      · simp [hp h_zero, ht]
    _ ≤ ∫⁻ t in V, ∫⁻ p, w t p * (π ⁻¹' S).indicator K (ψ t p) ∂ρ ∂ν := lintegral_mono_set hS_sub
    _ ≤ ∫⁻ x, (π ⁻¹' S).indicator K x ∂μ := h_le _ (hK_meas.indicator hπS)
    _ ≤ C * ν S := (lintegral_indicator hπS K).trans_le (hS hS_open)

/-- If `μ` is the image of `ν.prod ρ` under a map `φ` with `π (φ (t, p)) = t` for almost every `p`
at each `t`, and `φ (·, p)` is continuous at `b` for almost every `p`, then
`ρ.map (fun p ↦ φ (b, p))` is at most the fiber measure `dμ / dν` of `π` over `b`, provided `ν` is
finite on some neighborhood of `b`. -/
theorem _root_.MeasureTheory.MeasurePreserving.isLeFiberMeasure
    [OpensMeasurableSpace X] [OpensMeasurableSpace B]
    [IsCountablyGenerated (𝓝 b)] [ν.IsOpenPosMeasure] {ρ : Measure P}
    [SFinite ρ] {φ : B × P → X} (hφ : MeasurePreserving φ (ν.prod ρ) μ) (hπ : Measurable π)
    (hν : ν.FiniteAtFilter (𝓝 b))
    (h_fiber : ∀ t : B, ∀ᵐ p : P ∂ρ, π (φ (t, p)) = t)
    (h_cont : ∀ᵐ p : P ∂ρ, ContinuousAt (fun t : B ↦ φ (t, p)) b) :
    IsLeFiberMeasure μ ν π b (ρ.map fun p : P ↦ φ (b, p)) := by
  rw [← withDensity_one (μ := ρ)]
  exact hπ.isLeFiberMeasure_of_coordinates (ψ := fun t p ↦ φ (t, p)) (w := 1)
    hν (fun _ ↦ hφ.measurable.comp (measurable_const.prodMk measurable_id))
    (fun _ ↦ measurable_const) univ_mem (fun t _ ↦ (h_fiber t).mono fun _ hp _ ↦ hp)
    (h_cont.mono fun _ hp ↦ ⟨hp, continuousAt_const.lowerSemicontinuousAt⟩) fun K hK ↦ by
      simpa [← hφ.lintegral_comp hK] using
        (lintegral_prod _ (hK.comp hφ.measurable).aemeasurable).ge

/-- Monotonicity of `IsLeFiberMeasure`: if `l` is at most the fiber measure `dμ / dν`, then every
smaller measure `l' ≤ l` is at most `dμ' / dν'` for `μ ≤ μ'` and `ν' ≤ ν`. -/
theorem mono (hl : IsLeFiberMeasure μ ν π b l) (hμ_le : μ ≤ μ') (hν_le : ν' ≤ ν) (hl_le : l' ≤ l) :
    IsLeFiberMeasure μ' ν' π b l' := fun K hK C hC ↦
  (lintegral_mono' hl_le le_rfl).trans <| hl K hK C <| hC.mono fun S hS hS_open ↦
    (lintegral_mono' (restrict_mono subset_rfl hμ_le) le_rfl).trans <|
      (hS hS_open).trans (mul_le_mul_right (hν_le S) C)

/-- `IsLeFiberMeasure` is invariant under changing `π` on a `μ`-null set. -/
theorem congr (hl : IsLeFiberMeasure μ ν π b l) (hπ : π =ᵐ[μ] π') :
    IsLeFiberMeasure μ ν π' b l :=
  fun K hK C hC ↦ hl K hK C <| hC.mono fun S hS hS_open ↦
    (setLIntegral_congr (hπ.preimage S)).trans_le (hS hS_open)

/-- If `l` is at most `dμ / dν` and `c ≠ ∞`, then `c • l` is at most `d(c • μ) / dν`. -/
theorem smul (hl : IsLeFiberMeasure μ ν π b l) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    IsLeFiberMeasure (c • μ) ν π b (c • l) := by
  intro K hK C hC
  have h_scale (σ : Measure X) : ∫⁻ x, K x ∂c • σ = ∫⁻ x, c * K x ∂σ := by
    simp [lintegral_smul_measure, lintegral_const_mul' _ _ hc]
  simp only [restrict_smul, h_scale] at hC ⊢
  exact hl _ ((ENNReal.continuous_const_mul hc).comp_lowerSemicontinuous hK mul_right_mono) C hC

/-- If `l` is at most the fiber measure `dμ / dν` of `π` over `b` and the homeomorphism `e` of the
base carries `ν` to `ν''`, then `l` is at most the fiber measure `dμ / dν''` of `e ∘ π` over
`e b`. -/
theorem comp_homeomorph [OpensMeasurableSpace B'] {ν'' : Measure B'}
    (hl : IsLeFiberMeasure μ ν π b l) (e : B ≃ₜ B') (he : MeasurePreserving e ν ν'') :
    IsLeFiberMeasure μ ν'' (e ∘ π) (e b) l := by
  intro K hK C hC
  refine hl K hK C (((e.continuous.tendsto b).image_smallSets.eventually hC).mono
    fun S hS hS_open ↦ ?_)
  have h_open : IsOpen (e '' S) := e.isOpenMap S hS_open
  have h_bound : ∫⁻ x in e ∘ π ⁻¹' (e '' S), K x ∂μ ≤ C * ν'' (e '' S) := hS h_open
  rwa [← he.measure_preimage h_open.measurableSet.nullMeasurableSet, preimage_comp,
    preimage_image_eq S e.injective] at h_bound

/-- Two-step fibration rule: if `l` is at most `dμ / dν` of `π` over `b`, and `l'` is at most
`dl / dν''` of a continuous map `π₂` over `b'`, then `l'` is at most `dμ / d(ν.prod ν'')` of
`fun x ↦ (π x, π₂ x)` over `(b, b')`. -/
theorem trans {ν'' : Measure B'} {π₂ : X → B'} {b' : B'} [SFinite ν''] [OpensMeasurableSpace X]
    (hl : IsLeFiberMeasure μ ν π b l) (hl' : IsLeFiberMeasure l ν'' π₂ b' l')
    (hπ₂ : Continuous π₂) :
    IsLeFiberMeasure μ (ν.prod ν'') (fun x : X ↦ (π x, π₂ x)) (b, b') l' := by
  intro K hK C hC
  obtain ⟨V, hV, h_sub⟩ := eventually_smallSets.1 hC
  obtain ⟨W, hW, W', hW', h_prod⟩ := mem_nhds_prod_iff.1 hV
  refine hl' K hK C ((eventually_smallSets_subset.2 hW').mono fun S' hS' hS'_open ↦ ?_)
  have h_open : IsOpen (π₂ ⁻¹' S') := hS'_open.preimage hπ₂
  have h_lsc : LowerSemicontinuous ((π₂ ⁻¹' S').indicator K) := fun x c hc ↦ by
    have hx : x ∈ π₂ ⁻¹' S' := mem_of_indicator_ne_zero hc.ne_zero
    filter_upwards [hK x c (by simpa [hx] using hc), h_open.mem_nhds hx] with y hy hy_mem
    simpa [hy_mem] using hy
  rw [← lintegral_indicator h_open.measurableSet]
  refine hl _ h_lsc _ ((eventually_smallSets_subset.2 hW).mono fun S hS hS_open ↦ ?_)
  calc
    ∫⁻ x in π ⁻¹' S, (π₂ ⁻¹' S').indicator K x ∂μ
      = ∫⁻ x in (fun x ↦ (π x, π₂ x)) ⁻¹' S ×ˢ S', K x ∂μ := by
        rw [lintegral_indicator h_open.measurableSet, restrict_restrict h_open.measurableSet,
          mk_preimage_prod, inter_comm]
    _ ≤ C * ν.prod ν'' (S ×ˢ S') :=
        h_sub _ (by grw [hS, hS', h_prod]) (hS_open.prod hS'_open)
    _ = C * ν'' S' * ν S := by rw [prod_prod, mul_comm (ν S), mul_assoc]

/-- Let `φ` be measurable with `π₀ (φ (p, x)) = π x` and `x ↦ φ (p, x)` continuous for almost
every `p`. If `l` is at most the fiber measure `dμ / dν` of `π` over `b`, then
`(ρ.prod l).map φ` is at most the fiber measure of `π₀` for `(ρ.prod μ).map φ` over `b`. -/
theorem map_prod [OpensMeasurableSpace X'] [OpensMeasurableSpace B] [FirstCountableTopology X]
    [SFinite μ] [SFinite l] {ρ : Measure P} [SFinite ρ] {φ : P × X → X'} {π₀ : X' → B}
    (hl : IsLeFiberMeasure μ ν π b l) (hφ : Measurable φ)
    (h_cont : ∀ᵐ p : P ∂ρ, Continuous fun x : X ↦ φ (p, x)) (hπ₀ : Measurable π₀)
    (h_comm : ∀ (p : P) (x : X), π₀ (φ (p, x)) = π x) :
    IsLeFiberMeasure ((ρ.prod μ).map φ) ν π₀ b ((ρ.prod l).map φ) := by
  intro K hK C hC
  have hK_meas : Measurable K := hK.measurable
  have h_lsc : LowerSemicontinuous fun x ↦ ∫⁻ p, K (φ (p, x)) ∂ρ := fun x ↦
    lowerSemicontinuousAt_lintegral (fun _ ↦ by fun_prop)
      (h_cont.mono fun _ hp ↦ hK.comp hp x)
  rw [lintegral_map hK_meas hφ, lintegral_prod_symm' _ (by fun_prop)]
  refine hl _ h_lsc C (hC.mono fun S hS hS_open ↦ ?_)
  have h_pre : φ ⁻¹' (π₀ ⁻¹' S) = univ ×ˢ (π ⁻¹' S) := Set.ext fun ⟨p, x⟩ ↦ by simp [h_comm]
  calc
    ∫⁻ x in π ⁻¹' S, ∫⁻ p, K (φ (p, x)) ∂ρ ∂μ
      = ∫⁻ x in π₀ ⁻¹' S, K x ∂(ρ.prod μ).map φ := by
        rw [setLIntegral_map (hπ₀ hS_open.measurableSet) hK_meas hφ, h_pre, ← prod_restrict,
          restrict_univ, lintegral_prod_symm' _ (by fun_prop)]
    _ ≤ C * ν S := hS hS_open

/-- If `l` is at most the fiber measure `dμ / dν` of `π₀ ∘ φ` over `b`, with `φ` continuous and
measurable, then `l.map φ` is at most the fiber measure of `π₀` for `μ.map φ` over `b`. -/
theorem map [OpensMeasurableSpace X'] [OpensMeasurableSpace B] {φ : X → X'} {π₀ : X' → B}
    (hl : IsLeFiberMeasure μ ν (π₀ ∘ φ) b l) (hφ : Measurable φ) (h_cont : Continuous φ)
    (hπ₀ : Measurable π₀) : IsLeFiberMeasure (μ.map φ) ν π₀ b (l.map φ) := by
  intro K hK C hC
  rw [lintegral_map hK.measurable hφ]
  exact hl _ (hK.comp h_cont) C <| hC.mono fun S hS hS_open ↦
    (setLIntegral_map (hπ₀ hS_open.measurableSet) hK.measurable hφ).ge.trans (hS hS_open)

end IsLeFiberMeasure

end TauCeti
