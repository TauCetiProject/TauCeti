/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Translation
public import TauCeti.Analysis.Sobolev.W1p.Mollification
public import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Smooth approximate identities in arbitrary-order Sobolev spaces

On the whole space, average translations of a function in `W^{k,p}` against a normalized smooth
bump. Translation preserves every weak derivative and the full iterated graph norm, so this gives
a contraction on `W^{k,p}` when `p < ∞`. The same strong continuity of translation implies that
these averages converge in the Sobolev norm when the bump radii tend to zero.

The value and every highest weak derivative of the Sobolev average are the corresponding `Lᵖ`
averages. These identities make the construction usable together with the pointwise convolution
and smoothness theory for mollifiers.

The argument is the standard mollification proof from L. C. Evans, *Partial Differential
Equations*, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open ContinuousLinearMap Filter MeasureTheory Metric Set TopologicalSpace
open scoped Convolution ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

local instance : (mu.restrict ((⊤ : Opens E) : Set E)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

private theorem continuous_translateLIE (hp : p ≠ ∞) (k : ℕ) (u : Wkp mu ⊤ p k) :
    Continuous fun h => translateLIE h k u := by
  simpa only [translateLIE_apply] using continuous_translate hp k u

/-- Mollification by a normalized smooth bump on the whole-space Sobolev space `W^{k,p}`, as a
continuous linear operator. It averages the Sobolev translations in the Bochner sense. The
restriction `p < ∞` supplies the strong continuity that makes this integrand Bochner integrable. -/
def normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (k : ℕ) :
    Wkp mu ⊤ p k →L[ℝ] Wkp mu ⊤ p k :=
  TauCeti.normedBumpAverageL phi (mu.restrict ((⊤ : Opens E) : Set E))
    (fun h => translateLIE h k) (continuous_translateLIE hp k)

/-- The defining Bochner-integral formula for Sobolev mollification. -/
theorem normedBumpL_apply (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p k) :
    normedBumpL hp phi k u =
      ∫ t, phi.normed (mu.restrict ((⊤ : Opens E) : Set E)) t • translate (-t) k u
        ∂(mu.restrict ((⊤ : Opens E) : Set E)) := by
  rw [normedBumpL, TauCeti.normedBumpAverageL_apply]
  simp only [translateLIE_apply]

/-- Mollification by a normalized nonnegative bump does not increase the `W^{k,p}` norm. -/
theorem norm_normedBumpL_le_one (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (k : ℕ) :
    ‖normedBumpL (mu := mu) hp phi k‖ ≤ 1 := by
  exact TauCeti.norm_normedBumpAverageL_le_one (F := Wkp mu ⊤ p k) phi
    (mu.restrict ((⊤ : Opens E) : Set E)) (fun h => translateLIE h k)
    (continuous_translateLIE hp k)

/-- The value of a Sobolev mollification is the `Lᵖ` mollification of its value. -/
@[simp]
theorem value_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p k) :
    value k (normedBumpL hp phi k u) =
      TauCeti.normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) (value k u) := by
  rw [normedBumpL, TauCeti.normedBumpLp_eq_normedBumpAverageL, ← valueL_apply,
    ← valueL_apply k u]
  refine TauCeti.normedBumpAverageL_comm _ _ _ _ _ _ _ (fun h u => ?_) u
  simp only [valueL_apply, translateLIE_apply, value_translate]

/-- At order zero, Sobolev mollification is the existing `Lᵖ` approximate identity. -/
@[simp]
theorem normedBumpL_zero (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    normedBumpL (mu := mu) hp phi 0 =
      TauCeti.normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext 0
  rw [value_normedBumpL, value_zero, value_zero]

/-- At order one, Sobolev mollification agrees with the existing `W^{1,p}` mollifier. -/
@[simp]
theorem normedBumpL_one (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    normedBumpL (mu := mu) hp phi 1 = W1p.normedBumpL hp phi := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext 1
  rw [value_normedBumpL, value_one, value_one, W1p.value_normedBumpL]

/-- Mollification commutes with forgetting the highest weak derivative. -/
theorem lowerOrder_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) :
    lowerOrder k (normedBumpL hp phi (k + 1) u) =
      normedBumpL hp phi k (lowerOrder k u) := by
  rw [normedBumpL, normedBumpL, ← lowerOrderL_apply, ← lowerOrderL_apply k u]
  refine TauCeti.normedBumpAverageL_comm _ _ _ _ _ _ _ (fun h u => ?_) u
  rw [lowerOrderL_apply, lowerOrderL_apply, translateLIE_apply, translateLIE_apply,
    lowerOrder_translate]

/-- The highest weak derivative of a Sobolev mollification is the `Lᵖ` mollification of the
highest weak derivative. -/
theorem iteratedGradient_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) :
    iteratedGradient k (normedBumpL hp phi (k + 1) u) =
      TauCeti.normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E))
        (iteratedGradient k u) := by
  rw [normedBumpL, TauCeti.normedBumpLp_eq_normedBumpAverageL, ← iteratedGradientL_apply,
    ← iteratedGradientL_apply k u]
  refine TauCeti.normedBumpAverageL_comm _ _ _ _ _ _ _ (fun h u => ?_) u
  rw [iteratedGradientL_apply, iteratedGradientL_apply, translateLIE_apply,
    iteratedGradient_translate]

/-- **Smooth approximate identity in `W^{k,p}(ℝⁿ)`.** Normalized smooth bumps whose
outer radii tend to zero converge strongly to the identity on every finite-exponent whole-space
Sobolev space. -/
theorem tendsto_normedBumpL (hp : p ≠ ∞) {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (nhds 0))
    (k : ℕ) (u : Wkp mu ⊤ p k) :
    Tendsto (fun i => normedBumpL hp (phi i) k u) l (nhds u) := by
  simpa only [normedBumpL, translateLIE_apply, translate_zero] using
    TauCeti.tendsto_normedBumpAverageL (F := Wkp mu ⊤ p k) hphi
      (mu.restrict ((⊤ : Opens E) : Set E)) (fun h => translateLIE h k)
      (continuous_translateLIE hp k) u

end TauCeti.Wkp
