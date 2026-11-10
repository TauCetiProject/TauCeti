/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.TranslateBounds
public import TauCeti.MeasureTheory.Measure.Prokhorov

/-!
# Subsequential limits of translated renewal measures

The translates of a nondegenerate renewal measure have subsequences converging against every
continuous compactly supported function on the real line. The limiting measure is locally finite
and has a uniform bound on its unit intervals. These are the compactness inputs to the
identification of renewal limits by their convolution equations.

Translations may be chosen arbitrarily: neither divergence of the translation parameters,
nonlattice support, nor a finite mean is needed for subsequence extraction. The limiting measure
can have atoms and need not have finite total mass. Convergence here is vague convergence,
expressed directly through its test functions.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition, Wiley, 1971, Chapter XI.
-/

public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal CompactlySupported

namespace MeasureTheory.Measure

/-- Every sequence of translated renewal measures has a vaguely convergent subsequence.
The limiting measure is locally finite and uniformly bounded on all unit intervals. No moment
or lattice assumption is needed, and the translation parameters need not tend to infinity. -/
theorem exists_subseq_tendsto_integral_translatedRenewalMeasure
    (F : Measure ℝ≥0) [IsProbabilityMeasure F] (hF : F {0} < 1) (t : ℕ → ℝ) :
    ∃ (η : Measure ℝ) (φ : ℕ → ℕ), IsLocallyFiniteMeasure η ∧ StrictMono φ ∧
      (∀ a : ℝ, η (Icc a (a + 1)) ≤ F.renewalMeasure (Iic 3)) ∧
      ∀ f : C_c(ℝ, ℝ), Tendsto
        (fun k => ∫ x, f x ∂F.translatedRenewalMeasure (t (φ k))) atTop
        (𝓝 (∫ x, f x ∂η)) := by
  obtain ⟨C, hmass, htight⟩ :=
    F.exists_bound_isTightMeasureSet_withDensity_translatedRenewalMeasure hF t
  let w : ℝ → ℝ≥0 := fun x => (Real.exp (-|x|)).toNNReal
  have hw : Continuous w := continuous_real_toNNReal.comp (by fun_prop)
  have hpos : ∀ x, 0 < w x := fun x => Real.toNNReal_pos.mpr (Real.exp_pos _)
  have hcast (x : ℝ) : (w x : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-|x|)) := by
    exact ENNReal.ofNNReal_toNNReal _
  obtain ⟨η, φ, hη, hφ, hlim⟩ :=
    TauCeti.exists_subseq_tendsto_integral_of_withDensity
      (fun n => F.translatedRenewalMeasure (t n)) w hw hpos C
      (by simpa only [hcast] using hmass) (by simpa only [hcast] using htight)
  have : IsLocallyFiniteMeasure η := hη
  refine ⟨η, φ, hη, hφ, fun a => ?_, hlim⟩
  apply isCompact_Icc.measure_le_of_tendsto_integral
    (V := Ioo (a - 1) (a + 2)) isOpen_Ioo
    (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) _ hlim
  have hend : a - 1 + (3 : ℝ) = a + 2 := by ring
  exact Eventually.of_forall fun k => (measure_mono Ioo_subset_Icc_self).trans
    (by simpa only [NNReal.coe_ofNat, hend] using
      F.translatedRenewalMeasure_Icc_add_le (t (φ k)) (a - 1) 3)

end MeasureTheory.Measure
