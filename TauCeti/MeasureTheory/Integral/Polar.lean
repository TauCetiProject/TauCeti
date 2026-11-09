/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.MeasureTheory.Constructions.HaarToSphere

/-!
# Radial null sets and almost-everywhere polar transport

A measurable set meeting each positive ray at most once and avoiding the origin has
zero additive Haar measure. Arbitrary Haar almost-everywhere predicates transport to
almost every unit direction and almost every positive radius. The proof reuses polar
integration and its measure-preserving homeomorphism. These are the measure-theoretic
steps for terminal radial sets and weak distance comparison in reduced geometry.

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open MeasureTheory Measure Metric Set Module Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A set meets each positive unit ray in at most one point. This imposes no condition at the
origin, which must be excluded separately in the nullity lemma. -/
def IsRadialGraph (A : Set E) : Prop :=
  ∀ u ∈ sphere (0 : E) 1, ∀ r₁ r₂ : ℝ, 0 < r₁ → 0 < r₂ →
    r₁ • u ∈ A → r₂ • u ∈ A → r₁ = r₂

/-- A measurable radial graph avoiding the origin has zero additive Haar measure. In dimension zero
the origin-exclusion hypothesis makes the set empty. -/
theorem addHaar_eq_zero_of_isRadialGraph (μ : Measure E) [μ.IsAddHaarMeasure]
    {A : Set E} (hAmeas : MeasurableSet A) (hA0 : (0 : E) ∉ A) (hray : IsRadialGraph A) :
    μ A = 0 := by
  classical
  by_cases hE : Subsingleton E
  · have hA : A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hA0 (hE.elim x 0 ▸ hx)
    simp only [hA, measure_empty]
  have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
  rw [← lintegral_indicator_one hAmeas]
  change (∫⁻ a : E, A.indicator (fun _ : E ↦ (1 : ℝ≥0∞)) a ∂μ) = 0
  rw [lintegral_eq_lintegral_toSphere_lintegral_Ioi (μ := μ)
    (f := A.indicator (fun _ : E ↦ (1 : ℝ≥0∞)))
    (measurable_const.indicator hAmeas)]
  refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun ω ↦ ?_)
  have hslice : {t : ℝ | 0 < t ∧ t • (ω : E) ∈ A}.Subsingleton := by
    intro s hs t ht
    exact hray ω ω.2 s t hs.1 ht.1 hs.2 ht.2
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_of_ae (hslice.countable.ae_notMem volume),
    ae_restrict_mem measurableSet_Ioi] with t ht htpos
  have hnot : t • (ω : E) ∉ A := fun h ↦ ht ⟨htpos, h⟩
  simp only [indicator_of_notMem hnot, mul_zero, Pi.zero_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem polarScale_homeomorphUnitSphereProd (x : ({0}ᶜ : Set E)) :
    ((homeomorphUnitSphereProd E x).2 : ℝ) •
      ((homeomorphUnitSphereProd E x).1 : E) = (x : E) := by
  simpa only [homeomorphUnitSphereProd_symm_apply_coe] using
    congrArg (fun y : ({0}ᶜ : Set E) ↦ (y : E))
      ((homeomorphUnitSphereProd E).symm_apply_apply x)

private theorem ae_volumeIoiPow_iff (k : ℕ) (P : ℝ → Prop) :
    (∀ᵐ t : Ioi (0 : ℝ) ∂Measure.volumeIoiPow k, P t) ↔
      ∀ᵐ t : ℝ, 0 < t → P t := by
  rw [Measure.volumeIoiPow, ae_withDensity_iff (by fun_prop)]
  have hpos (t : Ioi (0 : ℝ)) : ENNReal.ofReal ((t : ℝ) ^ k) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos t.property _)).ne'
  have hsub :
      (∀ᵐ t : Ioi (0 : ℝ) ∂Measure.comap Subtype.val volume, P t) ↔
        ∀ᵐ t : ℝ, 0 < t → P t :=
    (ae_restrict_iff_subtype measurableSet_Ioi).symm.trans
      (ae_restrict_iff' measurableSet_Ioi)
  constructor
  · intro h
    apply hsub.mp
    filter_upwards [h] with t ht
    exact ht (hpos t)
  · intro h
    have hp := hsub.mpr h
    filter_upwards [hp] with t ht
    intro _
    exact ht

/-- An arbitrary Haar almost-everywhere predicate transports to the polar product measure; no
measurability of its truth set is required. -/
theorem ae_polar_comp (μ : Measure E) [μ.IsAddHaarMeasure]
    {P : E → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ)
      ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)),
      P ((p.2 : ℝ) • (p.1 : E)) := by
  rw [← μ.measurePreserving_homeomorphUnitSphereProd.map_eq,
    (Homeomorph.measurableEmbedding _).ae_map_iff]
  simpa only [polarScale_homeomorphUnitSphereProd] using
    (ae_restrict_iff_subtype (measurableSet_singleton (0 : E)).compl).mp
      (ae_restrict_of_ae hP)

/-- Almost every unit direction and almost every positive radius inherit an arbitrary Haar
almost-everywhere predicate. -/
theorem ae_ae_polar (μ : Measure E) [μ.IsAddHaarMeasure]
    {P : E → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ θ : Metric.sphere (0 : E) 1 ∂μ.toSphere,
      ∀ᵐ t : ℝ, 0 < t → P (t • (θ : E)) := by
  have hp := Measure.ae_ae_of_ae_prod (ae_polar_comp μ hP)
  filter_upwards [hp] with θ hθ
  exact (ae_volumeIoiPow_iff _ (fun t ↦ P (t • (θ : E)))).mp hθ

end TauCeti
