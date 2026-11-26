/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.LeftSymbol
public import TauCeti.Analysis.Pseudodifferential.Amplitude.ProperSupport

/-!
# Mapping properties of properly supported amplitudes on Schwartz functions

Combining smoothness for input-proper amplitudes
(`TauCeti.Amplitude.HasProperInputSupport.contDiff_quantizeAmplitudeValue`) with compact support
preservation for output-proper amplitudes
(`TauCeti.Amplitude.HasProperOutputSupport.hasCompactSupport_quantizeAmplitudeValue`), properly
supported amplitudes preserve compactly supported Schwartz functions unconditionally on the target
normed spaces.

## Main declarations

* `TauCeti.Amplitude.HasProperSupport.exists_schwartzMap_quantizeAmplitudeValue`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, pp. 68–72.
* M. E. Taylor, *Pseudodifferential Operators*, Princeton University Press, 1981, Chapter II,
  §§1–2.
-/

public section

noncomputable section

open scoped SchwartzMap

namespace TauCeti

namespace Amplitude

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- **Properly supported amplitudes preserve `C_c^∞` inside Schwartz space.** Unconditional on
completeness of `V` and `W`: if `a` is properly supported and `u : 𝓢(ℝⁿ, V)` has compact support,
then `Op(a) u` is the underlying function of a compactly supported Schwartz map `v : 𝓢(ℝⁿ, W)`, so
properly supported amplitude operators can be composed directly without spatial cutoffs. -/
theorem HasProperSupport.exists_schwartzMap_quantizeAmplitudeValue
    {a : Amplitude n V W m} (ha : a.HasProperSupport) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport (u : CoordinateSpace n → V)) :
    ∃ v : 𝓢(CoordinateSpace n, W),
      (v : CoordinateSpace n → W) = quantizeAmplitudeValue a.coefficient u ∧
      HasCompactSupport (v : CoordinateSpace n → W) := by
  have hsupp := ha.hasProperOutputSupport.hasCompactSupport_quantizeAmplitudeValue hu
  have hsmooth := ha.hasProperInputSupport.contDiff_quantizeAmplitudeValue u
  have hv : ((hsupp.toSchwartzMap hsmooth : 𝓢(CoordinateSpace n, W)) : CoordinateSpace n → W) =
      quantizeAmplitudeValue a.coefficient u :=
    funext (HasCompactSupport.toSchwartzMap_toFun hsupp hsmooth)
  exact ⟨hsupp.toSchwartzMap hsmooth, hv, hv.symm ▸ hsupp⟩

end Amplitude

end TauCeti
