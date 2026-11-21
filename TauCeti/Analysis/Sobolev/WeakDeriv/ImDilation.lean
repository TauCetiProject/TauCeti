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

The proof applies `TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv` to the continuous linear
equivalence `TauCeti.imDilationEquiv`.

## Main declarations

* `TauCeti.HasWeakFDerivOn.comp_imDilation`: the weak chain rule for `imDilation c`.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set

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
  have he : ((imDilationEquiv hc : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) = imDilation c :=
    ContinuousLinearMap.ext fun z => congrFun (coe_imDilationEquiv hc) z
  simpa only [Function.comp_def, coe_imDilationEquiv, he] using
    hg.comp_continuousLinearEquiv (μ := volume) (imDilationEquiv hc)
      (by simpa only [coe_imDilationEquiv] using hUV)

end TauCeti
