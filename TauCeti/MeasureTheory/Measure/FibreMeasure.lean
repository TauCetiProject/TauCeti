/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Measures below a fibre measure

Let `π : X → B` be a map, `μ` a measure on `X` and `ν` a measure on `B`. For a submersion of
manifolds with smooth positive measures, the fibre measures `dμ / dν` on the fibres of `π` are
determined by two properties: integrating over the fibres and then against `ν` is integrating
against `μ`, and the fibre integrals of a continuous function of compact support are continuous on
`B`. This file does not construct them. It defines the relation of being at most the fibre measure
over a point, tested against lower semicontinuous functions, and proves that it is kept by the
usual operations on measures and maps.

## Main definitions and results

* `TauCeti.LeFibreMeasure`: a measure `l` is at most the fibre measure `dμ / dν` of `π` over a
  point `b`.
* `TauCeti.LeFibreMeasure.of_coordinates`: a parametrisation `ψ t p` of a part of `X` with
  `π (ψ t p) = t` and a weight `w t p`, both continuous at `t = b` and dominated by `μ`, gives such
  a measure; `TauCeti.LeFibreMeasure.of_measurePreserving` is the case of a product decomposition.
* `TauCeti.LeFibreMeasure.trans`: the relation for a pair of maps follows from the relations for
  the two steps, the second map being continuous.
* `TauCeti.LeFibreMeasure.map_prod`, `TauCeti.LeFibreMeasure.map`,
  `TauCeti.LeFibreMeasure.comp_homeomorph`, `TauCeti.LeFibreMeasure.congr`: the relation is kept
  by maps that respect `π`, by homeomorphisms of the base and by changing `π` on a null set.
* `TauCeti.lowerSemicontinuousAt_lintegral`: Fatou's lemma with a parameter, and
  `TauCeti.le_of_setLIntegral_le`: a lower semicontinuous function whose means over small open
  sets are at most `C` is at most `C` at the point.

## Provenance

The file is adapted from `src/Lib/General/Measure/FibreMeasure.lean` of the Lean proof of the
Riemann hypothesis by Levent Alpöge with Claude, as published under Apache 2.0 at
https://github.com/leanprover-community/riemann-hypothesis (commit `5aa76fdf49d4`), declarations
`New.lowerSemicontinuousAt_lintegral`, `New.le_of_setLIntegral_le`, `New.LeFibreMeasure` and
`New.LeFibreMeasure.of_coordinates`, `.of_measurePreserving`, `.congr`, `.comp_homeomorph`,
`.trans`, `.map_prod`, `.map`.

## References

* A. Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113
  (1965), 1–87, no. 6: fibre measures of a submersion.
-/

@[expose] public section

namespace TauCeti

open MeasureTheory Measure Filter Topology Set ENNReal

/-- **Fatou's lemma with a parameter.** If `F x` is almost everywhere measurable for every `x`
and `F · p` is lower semicontinuous at `x₀` for almost every `p`, then `x ↦ ∫⁻ F x dρ` is lower
semicontinuous at `x₀`. -/
theorem lowerSemicontinuousAt_lintegral {X P : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [MeasurableSpace P] {ρ : Measure P} {F : X → P → ℝ≥0∞} {x₀ : X}
    (h_meas : ∀ x : X, AEMeasurable (F x) ρ)
    (h_lsc : ∀ᵐ p : P ∂ρ, LowerSemicontinuousAt (F · p) x₀) :
    LowerSemicontinuousAt (fun x : X ↦ ∫⁻ p : P, F x p ∂ρ) x₀ := by
  rw [lowerSemicontinuousAt_iff_le_liminf]
  calc ∫⁻ p, F x₀ p ∂ρ ≤ ∫⁻ p, liminf (F · p) (𝓝 x₀) ∂ρ :=
        lintegral_mono_ae (h_lsc.mono fun _ ↦ lowerSemicontinuousAt_iff_le_liminf.1)
    _ ≤ liminf (fun x ↦ ∫⁻ p, F x p ∂ρ) (𝓝 x₀) := lintegral_liminf_le' h_meas

/-- Let `ν` be locally finite and positive on nonempty open sets. A function that is lower
semicontinuous at `b`, and whose integral for `ν` over every open set `S` contained in some fixed
neighbourhood of `b` is at most `C * ν S`, is at most `C` at `b`. -/
theorem le_of_setLIntegral_le {B : Type*} [TopologicalSpace B] [MeasurableSpace B]
    [OpensMeasurableSpace B] {ν : Measure B} [ν.IsOpenPosMeasure] [IsLocallyFiniteMeasure ν]
    {A : B → ℝ≥0∞} {b : B} {C : ℝ≥0∞} (hA : LowerSemicontinuousAt A b)
    (h_mean : ∀ᶠ S : Set B in (𝓝 b).smallSets, IsOpen S → ∫⁻ t : B in S, A t ∂ν ≤ C * ν S) :
    A b ≤ C := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  obtain ⟨S, ⟨hb, hS_open⟩, hS_mean, hS_lt, hS_fin⟩ : ∃ S : Set B, (b ∈ S ∧ IsOpen S) ∧
      (IsOpen S → ∫⁻ t in S, A t ∂ν ≤ C * ν S) ∧ S ⊆ {t | c < A t} ∧ ν S < ∞ :=
    (h_mean.and ((eventually_smallSets_subset.2 (hA c hc)).and
      (ν.finiteAt_nhds b).eventually)).exists_mem_basis_of_smallSets (nhds_basis_opens b)
  refine (ENNReal.mul_le_mul_iff_left (hS_open.measure_ne_zero ν ⟨b, hb⟩) hS_fin.ne).1 ?_
  calc c * ν S = ∫⁻ _ in S, c ∂ν := (setLIntegral_const S c).symm
    _ ≤ ∫⁻ t in S, A t ∂ν := setLIntegral_mono' hS_open.measurableSet fun t ht ↦ (hS_lt ht).le
    _ ≤ C * ν S := hS_mean hS_open

variable {X X' B B' P : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace B]
  [MeasurableSpace B]

/-- The measure `l` is at most the fibre measure `dμ / dν` of the map `π : X → B` over the point
`b`: for a lower semicontinuous `K ≥ 0`, a bound `∫_{π ∈ S} K dμ ≤ C ν(S)` for all open sets `S`
contained in some fixed neighbourhood of `b` gives `∫ K dl ≤ C`. -/
def LeFibreMeasure (μ : Measure X) (ν : Measure B) (π : X → B) (b : B) (l : Measure X) : Prop :=
  ∀ K : X → ℝ≥0∞, LowerSemicontinuous K → ∀ C : ℝ≥0∞,
    (∀ᶠ S : Set B in (𝓝 b).smallSets, IsOpen S → ∫⁻ x : X in π ⁻¹' S, K x ∂μ ≤ C * ν S) →
    ∫⁻ x : X, K x ∂l ≤ C

namespace LeFibreMeasure

variable {μ l : Measure X} {ν : Measure B} {π π' : X → B} {b : B}

/-- Let `(t, p) ↦ ψ t p`, for `t` in a neighbourhood `V` of `b`, parametrise a part of `X` so that
`π (ψ t p) = t` for almost every `p` with `w t p ≠ 0` and `μ` is at least `w t p dν(t) dρ(p)` there.
If `ψ` and `w` are continuous in `t` at `b` for almost every `p`, then the image of `w b p dρ(p)`
under `ψ b` is at most the fibre measure `dμ / dν` of `π` over `b`. -/
theorem of_coordinates [MeasurableSpace P] [OpensMeasurableSpace X] [OpensMeasurableSpace B]
    [FirstCountableTopology B] [ν.IsOpenPosMeasure] [IsLocallyFiniteMeasure ν] {ρ : Measure P}
    {ψ : B → P → X} {w : B → P → ℝ≥0∞} {V : Set B} (hπ : Measurable π)
    (hψ : Measurable ψ.uncurry) (hw : Measurable w.uncurry) (hV : V ∈ 𝓝 b)
    (h_fibre : ∀ t ∈ V, ∀ᵐ p : P ∂ρ, w t p ≠ 0 → π (ψ t p) = t)
    (h_cont : ∀ᵐ p : P ∂ρ, ContinuousAt (ψ · p) b ∧ ContinuousAt (w · p) b)
    (h_le : ∀ K : X → ℝ≥0∞, Measurable K →
      ∫⁻ t : B in V, ∫⁻ p : P, w t p * K (ψ t p) ∂ρ ∂ν ≤ ∫⁻ x : X, K x ∂μ) :
    LeFibreMeasure μ ν π b ((ρ.withDensity (w b)).map (ψ b)) := by
  -- The fibre integral `A t` of `K` is lower semicontinuous at `b`, and its integral over a small
  -- open set `S` is at most the integral of `K` over `π ⁻¹' S`.
  intro K hK C hC
  let A (t : B) : ℝ≥0∞ := ∫⁻ p, w t p * K (ψ t p) ∂ρ
  have hK_meas : Measurable K := hK.measurable
  have hA : LowerSemicontinuousAt A b := by
    refine lowerSemicontinuousAt_lintegral (fun _ ↦ by fun_prop)
      (h_cont.mono fun p ⟨hψ_cont, hw_cont⟩ ↦ ?_)
    rw [lowerSemicontinuousAt_iff_le_liminf]
    calc w b p * K (ψ b p) ≤ liminf (w · p) (𝓝 b) * liminf (fun t ↦ K (ψ t p)) (𝓝 b) :=
          mul_le_mul' hw_cont.tendsto.liminf_eq.ge
            (lowerSemicontinuousAt_iff_le_liminf.1 ((hK _).comp hψ_cont))
      _ ≤ liminf (fun t ↦ w t p * K (ψ t p)) (𝓝 b) := ENNReal.le_liminf_mul
  rw [lintegral_map hK_meas hψ.of_uncurry_left,
    lintegral_withDensity_eq_lintegral_mul _ hw.of_uncurry_left (by fun_prop)]
  change A b ≤ C
  refine le_of_setLIntegral_le (ν := ν) hA ?_
  filter_upwards [hC, eventually_smallSets_subset.2 hV] with S hS hS_sub hS_open
  have hπS : MeasurableSet (π ⁻¹' S) := hπ hS_open.measurableSet
  calc ∫⁻ t in S, A t ∂ν = ∫⁻ t in S, ∫⁻ p, w t p * (π ⁻¹' S).indicator K (ψ t p) ∂ρ ∂ν := by
        refine setLIntegral_congr_fun hS_open.measurableSet fun t ht ↦ lintegral_congr_ae ?_
        filter_upwards [h_fibre t (hS_sub ht)] with p hp
        by_cases h_zero : w t p = 0
        · simp [h_zero]
        · simp [hp h_zero, ht]
    _ ≤ ∫⁻ t in V, ∫⁻ p, w t p * (π ⁻¹' S).indicator K (ψ t p) ∂ρ ∂ν := lintegral_mono_set hS_sub
    _ ≤ ∫⁻ x, (π ⁻¹' S).indicator K x ∂μ := h_le _ (hK_meas.indicator hπS)
    _ ≤ C * ν S := (lintegral_indicator hπS K).trans_le (hS hS_open)

/-- If `μ` is the image of `ν × ρ` under a map `φ`, continuous in the first variable at `b`, with
`π (φ (t, p)) = t`, then the image of `ρ` under `φ (b, ·)` is at most the fibre measure
`dμ / dν` of `π` over `b`. -/
theorem of_measurePreserving [MeasurableSpace P] [OpensMeasurableSpace X]
    [OpensMeasurableSpace B] [FirstCountableTopology B] [ν.IsOpenPosMeasure]
    [IsLocallyFiniteMeasure ν] {ρ : Measure P} [SFinite ρ] {φ : B × P → X}
    (hφ : MeasurePreserving φ (ν.prod ρ) μ) (hπ : Measurable π)
    (h_fibre : ∀ (t : B) (p : P), π (φ (t, p)) = t)
    (h_cont : ∀ p : P, ContinuousAt (fun t : B ↦ φ (t, p)) b) :
    LeFibreMeasure μ ν π b (ρ.map fun p : P ↦ φ (b, p)) := by
  -- Take `ψ t p = φ (t, p)` and the weight `1`.
  rw [← withDensity_one (μ := ρ)]
  exact of_coordinates (ψ := fun t p ↦ φ (t, p)) (w := 1) hπ hφ.measurable measurable_const
    univ_mem (fun t _ ↦ .of_forall fun p _ ↦ h_fibre t p)
    (.of_forall fun p ↦ ⟨h_cont p, continuousAt_const⟩) fun K hK ↦ by
      simpa [← hφ.lintegral_comp hK] using
        (lintegral_prod _ (hK.comp hφ.measurable).aemeasurable).ge

/-- Being at most the fibre measure is kept when `π` is changed on a `μ`-null set. -/
theorem congr (hl : LeFibreMeasure μ ν π b l) (hπ : π =ᵐ[μ] π') : LeFibreMeasure μ ν π' b l :=
  fun K hK C hC ↦ hl K hK C <| hC.mono fun S hS hS_open ↦
    (setLIntegral_congr (hπ.preimage S)).trans_le (hS hS_open)

/-- If `l` is at most the fibre measure `dμ / dν` of `π` over `b` and the homeomorphism `e` of
the base carries `ν` to `ν'`, then `l` is at most the fibre measure `dμ / dν'` of `e ∘ π` over
`e b`. -/
theorem comp_homeomorph [TopologicalSpace B'] [MeasurableSpace B'] [BorelSpace B]
    [BorelSpace B'] {ν' : Measure B'} (hl : LeFibreMeasure μ ν π b l) (e : B ≃ₜ B')
    (he : MeasurePreserving e ν ν') : LeFibreMeasure μ ν' (e ∘ π) (e b) l := by
  intro K hK C hC
  refine hl K hK C (((e.continuous.tendsto b).image_smallSets.eventually hC).mono
    fun S hS hS_open ↦ ?_)
  have h_bound : ∫⁻ x in e ∘ π ⁻¹' (e '' S), K x ∂μ ≤ C * ν' (e '' S) := hS (e.isOpenMap S hS_open)
  rwa [← he.measure_preimage_emb e.measurableEmbedding, preimage_comp,
    preimage_image_eq S e.injective] at h_bound

/-- **Fibre measures in two steps.** If `l` is at most the fibre measure `dμ / dν` of `π` over
`b`, and `l'` is at most the fibre measure `dl / dν'` of a continuous map `π₂` over `b'`, then `l'`
is at most the fibre measure `dμ / d(ν × ν')` of `(π, π₂)` over `(b, b')`. -/
theorem trans [TopologicalSpace B'] [MeasurableSpace B'] [OpensMeasurableSpace X] {ν' : Measure B'}
    [SFinite ν'] {l' : Measure X} {π₂ : X → B'} {b' : B'} (hl : LeFibreMeasure μ ν π b l)
    (hl' : LeFibreMeasure l ν' π₂ b' l') (hπ₂ : Continuous π₂) :
    LeFibreMeasure μ (ν.prod ν') (fun x : X ↦ (π x, π₂ x)) (b, b') l' := by
  -- For small open `S` and `S'` the hypothesis at `S ×ˢ S'` bounds the integral of `K` cut off by
  -- `π₂ ⁻¹' S'`, a lower semicontinuous function, over `π ⁻¹' S`.
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
  calc ∫⁻ x in π ⁻¹' S, (π₂ ⁻¹' S').indicator K x ∂μ
      = ∫⁻ x in (fun x ↦ (π x, π₂ x)) ⁻¹' S ×ˢ S', K x ∂μ := by
        rw [lintegral_indicator h_open.measurableSet, restrict_restrict h_open.measurableSet,
          mk_preimage_prod, inter_comm]
    _ ≤ C * ν.prod ν' (S ×ˢ S') := h_sub _ (by grw [hS, hS', h_prod]) (hS_open.prod hS'_open)
    _ = C * ν' S' * ν S := by rw [prod_prod, mul_comm (ν S), mul_assoc]

/-- Let `x ↦ φ (p, x)` be a measurable family of continuous maps `X → X'` with
`π₀ (φ (p, x)) = π x`. If `l` is at most the fibre measure of `π` for `μ` over `b`, then the image
of `ρ × l` under `φ` is at most the fibre measure of `π₀` for the image of `ρ × μ` over `b`. -/
theorem map_prod [MeasurableSpace P] [TopologicalSpace X'] [MeasurableSpace X']
    [OpensMeasurableSpace X'] [OpensMeasurableSpace B] [FirstCountableTopology X] [SFinite μ]
    [SFinite l] {ρ : Measure P} [SFinite ρ] {φ : P × X → X'} {π₀ : X' → B}
    (hl : LeFibreMeasure μ ν π b l) (hφ : Measurable φ)
    (h_cont : ∀ p : P, Continuous fun x : X ↦ φ (p, x)) (hπ₀ : Measurable π₀)
    (h_comm : ∀ (p : P) (x : X), π₀ (φ (p, x)) = π x) :
    LeFibreMeasure ((ρ.prod μ).map φ) ν π₀ b ((ρ.prod l).map φ) := by
  -- Apply the hypothesis to the integral of `K` over the family.
  intro K hK C hC
  have hK_meas : Measurable K := hK.measurable
  have h_lsc : LowerSemicontinuous fun x ↦ ∫⁻ p, K (φ (p, x)) ∂ρ := fun x ↦
    lowerSemicontinuousAt_lintegral (fun _ ↦ by fun_prop)
      (.of_forall fun p ↦ hK.comp (h_cont p) x)
  rw [lintegral_map hK_meas hφ, lintegral_prod_symm' _ (by fun_prop)]
  refine hl _ h_lsc C (hC.mono fun S hS hS_open ↦ ?_)
  have h_pre : φ ⁻¹' (π₀ ⁻¹' S) = univ ×ˢ (π ⁻¹' S) := Set.ext fun ⟨p, x⟩ ↦ by simp [h_comm]
  calc ∫⁻ x in π ⁻¹' S, ∫⁻ p, K (φ (p, x)) ∂ρ ∂μ
      = ∫⁻ x in π₀ ⁻¹' S, K x ∂(ρ.prod μ).map φ := by
        rw [setLIntegral_map (hπ₀ hS_open.measurableSet) hK_meas hφ, h_pre, ← prod_restrict,
          restrict_univ, lintegral_prod_symm' _ (by fun_prop)]
    _ ≤ C * ν S := hS hS_open

/-- If `l` is at most the fibre measure of `π₀ ∘ φ` for `μ` over `b`, with `φ` continuous, then the
image of `l` under `φ` is at most the fibre measure of `π₀` for the image of `μ` over `b`. -/
theorem map [TopologicalSpace X'] [MeasurableSpace X'] [OpensMeasurableSpace X']
    [OpensMeasurableSpace B] {φ : X → X'} {π₀ : X' → B} (hl : LeFibreMeasure μ ν (π₀ ∘ φ) b l)
    (hφ : Measurable φ) (h_cont : Continuous φ) (hπ₀ : Measurable π₀) :
    LeFibreMeasure (μ.map φ) ν π₀ b (l.map φ) := by
  intro K hK C hC
  rw [lintegral_map hK.measurable hφ]
  exact hl _ (hK.comp h_cont) C <| hC.mono fun S hS hS_open ↦
    (setLIntegral_map (hπ₀ hS_open.measurableSet) hK.measurable hφ).ge.trans (hS hS_open)

end LeFibreMeasure

end TauCeti
