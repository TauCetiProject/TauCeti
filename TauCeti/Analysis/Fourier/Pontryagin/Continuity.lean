/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Pontryagin.Measure
public import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuity of the Fourier–Stieltjes transform on a Pontryagin dual

The Fourier–Stieltjes transform of a tight finite positive measure on the Pontryagin dual is
continuous on the original additive monoid when its topology is weakly locally compact.
For locally compact abelian groups, together with its positive-definiteness, this supplies
the measure-to-function direction of Bochner representation for regular measures.
A compact set carries almost all of the measure; character evaluation is uniformly continuous
there near each fixed monoid element, while the complement contributes at most its small mass.

This is the standard compact truncation argument for Fourier–Stieltjes transforms; see
G. B. Folland, *A Course in Abstract Harmonic Analysis*, Chapter 4.
-/

public section

open MeasureTheory
open scoped Topology

namespace TauCeti

variable {G : Type*} [AddMonoid G] [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [OpensMeasurableSpace (PontryaginDual (Multiplicative G))]

/-- The transform of a tight finite measure on the Pontryagin dual is continuous. Tightness is
automatic for finite Radon measures and is the regularity needed when the dual is not metrizable. -/
theorem _root_.MeasureTheory.FiniteMeasure.continuous_pontryaginMeasureTransform
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G)))
    (hμ : IsTightMeasureSet {μ.toMeasure}) :
    Continuous μ.pontryaginMeasureTransform := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt]
  refine Metric.nhds_basis_ball.tendsto_right_iff.mpr ?_
  intro ε hε
  let C := μ.toMeasure.real Set.univ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨K, hK, hKmass⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hμ
      (ENNReal.ofReal (ε / 8)) (ENNReal.ofReal_pos.mpr (by positivity))
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have htail : μ.toMeasure.real Kᶜ ≤ ε / 8 := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ ε / 8)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hKmass μ.toMeasure (Set.mem_singleton _))
  let δ := ε / (4 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  -- Joint evaluation and compactness give a common bound for all characters in K.
  have heval : Continuous (fun p : G × PontryaginDual (Multiplicative G) =>
      (p.2 (Multiplicative.ofAdd p.1) : ℂ)) :=
    continuous_subtype_val.comp
      ((continuous_eval (F := Multiplicative G →ₜ* Circle)).comp
        (continuous_snd.prodMk (continuous_ofAdd.comp continuous_fst)))
  have hnear : ∀ᶠ x in 𝓝 g, ∀ χ ∈ K,
      ‖(χ (Multiplicative.ofAdd x) : ℂ) - (χ (Multiplicative.ofAdd g) : ℂ)‖ ≤ δ := by
    apply hK.eventually_forall_of_forall_eventually
    intro χ _
    have hcont := (heval.sub
      ((PontryaginDual.continuous_coe_eval_const (Multiplicative.ofAdd g)).comp
        continuous_snd)).norm
    exact (hcont.continuousAt.eventually_lt continuousAt_const
      (by simpa using hδ)).mono fun _ h => h.le
  filter_upwards [hnear] with x hx
  -- The ball basis expresses continuity through the distance between transform values.
  change dist (μ.pontryaginMeasureTransform x) (μ.pontryaginMeasureTransform g) < ε
  rw [dist_eq_norm]
  have hint (y : G) : Integrable
      (fun χ : PontryaginDual (Multiplicative G) =>
        (χ (Multiplicative.ofAdd y) : ℂ)) μ.toMeasure :=
    PontryaginDual.integrable_coe_eval (Multiplicative.ofAdd y)
  have hmass : μ.toMeasure.real K ≤ C := by
    exact (measureReal_mono (μ := μ.toMeasure) (Set.subset_univ K)).trans
      (by dsimp [C]; linarith)
  have hcenter' : δ * μ.toMeasure.real K ≤ ε / 4 := by
    calc
      δ * μ.toMeasure.real K ≤ δ * C := mul_le_mul_of_nonneg_left hmass hδ.le
      _ = ε / 4 := by dsimp [δ]; field_simp
  -- Split the integral of the difference into the small compact part and the bounded tail.
  rw [FiniteMeasure.pontryaginMeasureTransform_apply,
    FiniteMeasure.pontryaginMeasureTransform_apply, ← integral_sub (hint x) (hint g),
    ← integral_add_compl (f := fun χ => (χ (Multiplicative.ofAdd x) : ℂ) -
      (χ (Multiplicative.ofAdd g) : ℂ)) hKmeas ((hint x).sub (hint g))]
  refine (norm_add_le _ _).trans_lt ?_
  have hcenter := norm_setIntegral_le_of_norm_le_const
    (measure_lt_top μ.toMeasure K) hx
  have htail' : ‖∫ χ in Kᶜ, (χ (Multiplicative.ofAdd x) : ℂ) -
      (χ (Multiplicative.ofAdd g) : ℂ) ∂μ.toMeasure‖ ≤ 2 * μ.toMeasure.real Kᶜ :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top μ.toMeasure Kᶜ) fun χ _ => by
      simpa only [Circle.norm_coe, one_add_one_eq_two] using
        norm_sub_le (χ (Multiplicative.ofAdd x) : ℂ)
          (χ (Multiplicative.ofAdd g) : ℂ)
  linarith

end TauCeti

end
