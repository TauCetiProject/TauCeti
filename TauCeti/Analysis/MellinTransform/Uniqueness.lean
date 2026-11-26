/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform.Basic
import Mathlib.Analysis.MellinInversion
import TauCeti.Analysis.Fourier.IntegrableUniqueness
import TauCeti.MeasureTheory.Measure.Haar.MultHaar

/-!
# Uniqueness on a vertical Mellin line

An absolutely convergent Mellin transform on a single vertical line determines its input almost
everywhere on the positive ray, whether or not the transform is integrable along the line.
For continuous upper-tail kernels, this identifies both functions on the closed ray, including the
cutoff. In a smoothed explicit formula one can thus identify a continuous prime sum with a
continuous sum of zero contributions by comparing their Mellin transforms.

The reduction uses Mathlib's `mellin_eq_fourier` and the multiplicative Haar measure `dt / t`,
which has the same null sets as Lebesgue measure on the positive ray.
-/

public section

open Complex MeasureTheory Set
open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Two functions with absolutely convergent Mellin transforms on a common vertical line agree
almost everywhere on `(0, ∞)` if their transforms agree on that line. -/
theorem MellinConvergent.ae_eq_of_mellin_eq_on_verticalLine {f g : ℝ → E} {c : ℝ}
    (hf : MellinConvergent f c) (hg : MellinConvergent g c)
    (h : EqOn (mellin f) (mellin g) {s : ℂ | s.re = c}) :
    f =ᵐ[volume.restrict (Ioi 0)] g := by
  let damp (k : ℝ → E) (u : ℝ) := Real.exp (-c * u) • k (Real.exp (-u))
  have hweight (u : ℝ) : exp (-(c : ℂ) * u) = (Real.exp (-c * u) : ℂ) := by
    push_cast
    rfl
  have hi {k : ℝ → E} (hk : MellinConvergent k c) : Integrable (damp k) := by
    simpa only [damp, hweight, Complex.coe_smul] using
      (TauCeti.mellinConvergent_iff_integrable_exp_smul k c).mp hk
  have hF : 𝓕 (damp f) = 𝓕 (damp g) := by
    ext t
    have hs := h (x := (c : ℂ) + (↑(2 * Real.pi * t) : ℂ) * I) (by simp)
    have hp : 2 * Real.pi ≠ 0 := by positivity
    simpa only [mellin_eq_fourier, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero,
      add_im, mul_I_im, zero_add, mul_div_cancel_left₀ _ hp, damp] using hs
  have hneg : (fun u : ℝ ↦ f (Real.exp (-u))) =ᵐ[volume] fun u ↦ g (Real.exp (-u)) := by
    filter_upwards [(hi hf).ae_eq_of_fourier_eq (hi hg) hF] with u hu
    exact smul_right_injective E (Real.exp_ne_zero _) hu
  have he : MeasurableEmbedding Real.exp :=
    Real.continuous_exp.measurableEmbedding Real.exp_injective
  have hae : ∀ᵐ u : ℝ ∂volume, f (Real.exp u) = g (Real.exp u) := by
    have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hneg
    simpa only [neg_neg] using hn
  rw [← TauCeti.ae_multHaar_eq_ae_volume_Ioi, ← TauCeti.map_volume_exp]
  exact he.ae_map_iff.mpr hae

namespace TauCeti

/-- A continuous kernel on `[a, ∞)` is determined there by its upper-tail Mellin integral
`∫ x in Ioi a, x ^ (-s - 1) • f x` on any vertical line of absolute convergence. -/
theorem eqOn_Ici_of_mellin_integral_Ioi_eq_on_verticalLine {f g : ℝ → E} {a c : ℝ}
    (ha : 0 ≤ a) (hf : ContinuousOn f (Ici a)) (hg : ContinuousOn g (Ici a))
    (hfi : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (-(c : ℂ) - 1) • f x) (Ioi a))
    (hgi : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (-(c : ℂ) - 1) • g x) (Ioi a))
    (h : ∀ s : ℂ, s.re = c →
      (∫ x in Ioi a, (x : ℂ) ^ (-s - 1) • f x) = ∫ x in Ioi a, (x : ℂ) ^ (-s - 1) • g x) :
    EqOn f g (Ici a) := by
  have hfi' : MellinConvergent ((Ioi a).indicator f) ((-c : ℝ) : ℂ) :=
    (mellinConvergent_indicator_Ioi_iff ha).mpr (by simpa only [ofReal_neg] using hfi)
  have hgi' : MellinConvergent ((Ioi a).indicator g) ((-c : ℝ) : ℂ) :=
    (mellinConvergent_indicator_Ioi_iff ha).mpr (by simpa only [ofReal_neg] using hgi)
  have hae := hfi'.ae_eq_of_mellin_eq_on_verticalLine hgi' (fun s hs ↦ by
    rw [mellin_indicator_Ioi _ ha, mellin_indicator_Ioi _ ha]
    simpa only [neg_neg] using h (-s) (by simpa using congrArg Neg.neg hs))
  have htail : f =ᵐ[volume.restrict (Ioi a)] g := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi ha) hae,
      ae_restrict_mem measurableSet_Ioi] with x hx hxa
    simpa only [indicator_of_mem hxa] using hx
  rw [restrict_Ioi_eq_restrict_Ici] at htail
  exact Measure.eqOn_of_ae_eq htail hf hg (by simp)

end TauCeti
