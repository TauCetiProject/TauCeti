/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
public import TauCeti.Analysis.Pseudodifferential.Sobolev

/-!
# Output support of pseudodifferential operators on Bessel-potential spaces

If a symbol `b` with compact spatial support vanishes at the positions outside a closed set `K`,
then `Op(b) v` is supported in `K` for every `v` in the Bessel-potential space `H^s`, as a
distribution on the whole space (`TemperedDistribution.toDistribution`). On Schwartz functions
this is immediate from the quantization formula, and it extends to `H^s` by density, since the
value of `Op(b) v` on a fixed test function is continuous in `v`.

This is the Sobolev-level counterpart of the output-support results for the Schwartz-level
quantization in `TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic`.

## Main results

* `TauCeti.Symbol.dsupport_toDistribution_quantizeSobolev_subset`: `Op(b) v` is supported in any
  closed set outside which `b` vanishes.
-/

public section

noncomputable section

open Complex MeasureTheory Set TopologicalSpace TestFunction TemperedDistribution Distribution
open scoped Distributions SchwartzMap BesselPotentialSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-- **Output support.** If the symbol `b` vanishes at the positions outside a closed set `K`, the
distribution `Op(b) v` is supported in `K`, for every `v ∈ H^s`. -/
theorem dsupport_toDistribution_quantizeSobolev_subset {V W : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport)
    {K : Set (CoordinateSpace n)} (hK : IsClosed K)
    (hbK : ∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) (s : ℝ) (v : H^{s}(CoordinateSpace n, V)) :
    dsupport (toDistribution ⊤ (b.quantizeSobolev hb s v).toDistr) ⊆ K := by
  have hvan : IsVanishingOn (toDistribution ⊤ (b.quantizeSobolev hb s v).toDistr) Kᶜ := by
    intro φ hφ
    rw [toDistribution_apply]
    set g := toSchwartzMapCLM ℝ (postcompCLM (𝕜 := ℝ) ofRealCLM φ)
    -- The value on `g` is continuous in `v` and vanishes on Schwartz functions.
    have hzero : (fun u ↦ (b.quantizeSobolev hb s u).toDistr g) = fun _ ↦ 0 := by
      refine (SchwartzMap.denseRange_toBesselPotentialSpaceCLM s (by norm_num)).equalizer
        (((continuous_eval_const g).comp BesselPotentialSpace.continuous_toDistr).comp
          (b.quantizeSobolev hb s).continuous) continuous_const (funext fun u ↦ ?_)
      simp only [Function.comp_apply, toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]
      refine integral_eq_zero_of_ae (ae_of_all _ fun x ↦ ?_)
      by_cases hx : x ∈ K
      · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hφ h hx
        simp [g, this]
      · simp [quantizeSchwartzValue_def, hbK x hx]
    exact congrFun hzero v
  exact fun x hx ↦ (mem_dsupport_iff x).1 hx K hvan hK

end Symbol

end TauCeti
