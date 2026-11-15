/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
public import TauCeti.Analysis.Complex.ImDilation

/-!
# The weak chain rule for dilations of the imaginary part

For `c ≠ 0`, the dilation `TauCeti.imDilation c : x + iy ↦ x + i c y` of the plane is a linear
isomorphism that multiplies Lebesgue measure by `|c|`. If `g` has weak derivative `Dg` on an open
set `V`, then `g ∘ imDilation c` has weak derivative `z ↦ Dg (imDilation c z) ∘L imDilation c` on
every open set that `imDilation c` maps into `V`.

The proof rescales Lebesgue measure by `|c⁻¹|`, which preserves weak derivatives and makes the
dilation measure-preserving, and then applies `TauCeti.HasWeakFDerivOn.comp_measurePreserving`.

## Main declarations

* `TauCeti.HasWeakFDerivOn.comp_imDilation`: the weak chain rule for `imDilation c`.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The weak chain rule for a dilation of the imaginary part: if `g` has weak derivative `Dg` on
`V`, then `g ∘ σ` has weak derivative `z ↦ Dg (σ z) ∘ σ` on every open set that `σ` maps into `V`,
for `σ = imDilation c`, `c ≠ 0`. -/
theorem HasWeakFDerivOn.comp_imDilation {c : ℝ} (hc : c ≠ 0) {U V : Opens ℂ}
    {g : ℂ → F} {Dg : ℂ → ℂ →L[ℝ] F} (hg : HasWeakFDerivOn volume V g Dg)
    (hUV : MapsTo (imDilation c) U V) :
    HasWeakFDerivOn volume U (fun z => g (imDilation c z))
      fun z => (Dg (imDilation c z)).comp (imDilation c) := by
  have := hg.completeSpace
  set a : ℝ≥0∞ := ENNReal.ofReal |c⁻¹|
  have ha0 : a ≠ 0 := by simp [a, hc]
  have hatop : a ≠ ∞ := ENNReal.ofReal_ne_top
  have : (a • (volume : Measure ℂ)).IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul _ ha0 hatop
  -- Scaling the measure by a finite constant preserves weak derivatives.
  have hga : HasWeakFDerivOn (a • volume) V g Dg := by
    refine hasWeakFDerivOn_iff.2 fun v => ?_
    obtain ⟨hcs, hgi, hDi, hint⟩ :=
      hasWeakLineDerivOn_iff_testFunction.1 (hasWeakFDerivOn_iff.1 hg v)
    have hsmul {h : ℂ → F} (hh : LocallyIntegrableOn h V volume) :
        LocallyIntegrableOn h V (a • volume) := fun x hx => by
      obtain ⟨t, ht, hti⟩ := hh x hx
      exact ⟨t, ht, by simpa [IntegrableOn] using hti.smul_measure hatop⟩
    refine hasWeakLineDerivOn_iff_testFunction.2 ⟨hcs, hsmul hgi, hsmul hDi, fun φ => ?_⟩
    rw [integral_smul_measure, integral_smul_measure, hint φ, smul_neg]
  have hΦ : MeasurePreserving (imDilation c) volume (a • volume) :=
    ⟨(imDilation c).continuous.measurable, map_imDilation_volume hc⟩
  have h := hga.comp_measurePreserving hΦ
    (imDilation c).lipschitzWith.locallyLipschitz.locallyLipschitzOn hUV
  simpa [Function.comp_def, ContinuousLinearMap.fderiv] using h

end TauCeti
