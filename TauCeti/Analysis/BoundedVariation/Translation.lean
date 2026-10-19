/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.Distribution.TestFunction.Translation
import Mathlib.MeasureTheory.Group.Integral

/-!
# Translation of distributional total variation and perimeter

Distributional total variation is unchanged when the function and its open domain are translated
by the same vector. More generally, translating a function from an open set `Ω` back to an open
set `V` does not increase its variation whenever `V + h ⊆ Ω`. The equality follows when the two
open sets are exact translates. The corresponding statements for perimeter transport sets by the
same translation.

The proof translates each admissible compactly supported test vector field in the opposite
direction. Translation preserves both its pointwise norm and its divergence, and a
right-invariant measure, such as an additive Haar measure, makes the resulting distributional
pairings equal.

These results give the translation part of affine-isometric transport for BV functions and sets of
finite perimeter. No integrability, measurability, boundedness, or finiteness assumption is needed.

## Main declarations

* `TauCeti.totalVariationOn_comp_add_right_le`: translation into a larger open set does not
  increase total variation.
* `TauCeti.totalVariationOn_comp_add_right`: total variation is invariant under exact translation
  of its open domain.
* `TauCeti.perimeter_preimage_add_right_le` and `TauCeti.perimeter_preimage_add_right`: the
  corresponding transport results for perimeter.
* `TauCeti.totalVariationOn_comap_add_right` and `TauCeti.perimeter_comap_add_right`: convenient
  exact-translation forms using the canonical preimage open set.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TestFunction TopologicalSpace
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω V : Opens E} {h : E}

section Variation

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddRightInvariant]
  {u : E → ℝ} {s : Set E}

/-- Translating a function from `Ω` back to `V` does not increase its total variation when
`V + h ⊆ Ω`. -/
theorem totalVariationOn_comp_add_right_le (hVO : MapsTo (· + h) V Ω) :
    totalVariationOn μ V (fun x => u (x + h)) ≤ totalVariationOn μ Ω u := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  let ψ : 𝓓(Ω, E) := translateTestFunction hVO φ
  have hpair :
      (∫ x, divergenceCLM φ x * u (x + h) ∂μ) =
        ∫ y, divergenceCLM ψ y * u y ∂μ := by
    simpa only [ψ, divergenceCLM_translateTestFunction, translateTestFunction_apply,
      add_sub_cancel_right] using
      integral_add_right_eq_self (fun y => divergenceCLM ψ y * u y) h
  rw [hpair]
  exact ofReal_integral_le_totalVariationOn ψ fun y => by
    simpa only [ψ, translateTestFunction_apply] using hφ (y - h)

/-- **Translation invariance of total variation.** If translation by `h` maps `V` into `Ω` and
translation by `-h` maps `Ω` back into `V`, then translating the function and its domain together
does not change its total variation. -/
theorem totalVariationOn_comp_add_right (hVO : MapsTo (· + h) V Ω)
    (hOV : MapsTo (· - h) Ω V) :
    totalVariationOn μ V (fun x => u (x + h)) = totalVariationOn μ Ω u := by
  apply le_antisymm (totalVariationOn_comp_add_right_le hVO)
  have hle := totalVariationOn_comp_add_right_le (μ := μ)
    (u := fun x => u (x + h)) (h := -h) (V := Ω) (Ω := V) (by simpa [sub_eq_add_neg] using hOV)
  simpa using hle

/-- Total variation is invariant when the translated domain is written canonically as the
preimage open set. -/
theorem totalVariationOn_comap_add_right :
    totalVariationOn μ
        (Opens.comap (ContinuousMap.addRight h) Ω)
        (fun x => u (x + h)) =
      totalVariationOn μ Ω u := by
  apply totalVariationOn_comp_add_right
  · intro x hx
    exact Opens.mem_comap.mp hx
  · intro y hy
    simpa [Opens.mem_comap] using hy

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The indicator of a translated set is the translated indicator. -/
private theorem indicator_one_preimage_add_right :
    ((· + h) ⁻¹' s).indicator (1 : E → ℝ) = fun x => s.indicator 1 (x + h) := by
  funext x
  simpa only [Function.comp_def, Pi.one_def] using
    (Set.indicator_comp_right (s := s) (g := fun _ => (1 : ℝ)) (fun y : E => y + h) (x := x))

/-- Translating a set and an open domain together cannot increase perimeter when the translated
domain lies in the original domain. -/
theorem perimeter_preimage_add_right_le (hVO : MapsTo (· + h) V Ω) :
    perimeter μ V ((· + h) ⁻¹' s) ≤ perimeter μ Ω s := by
  rw [perimeter_def, perimeter_def, indicator_one_preimage_add_right]
  exact totalVariationOn_comp_add_right_le hVO

/-- **Translation invariance of perimeter.** If translation by `h` identifies `V` with `Ω`, then
the perimeter in `V` of the translate by `-h` of `s` equals the perimeter of `s` in `Ω`. -/
theorem perimeter_preimage_add_right (hVO : MapsTo (· + h) V Ω)
    (hOV : MapsTo (· - h) Ω V) :
    perimeter μ V ((· + h) ⁻¹' s) = perimeter μ Ω s := by
  rw [perimeter_def, perimeter_def, indicator_one_preimage_add_right]
  exact totalVariationOn_comp_add_right hVO hOV

/-- Perimeter is invariant when a set and its ambient open set are both pulled back by the same
translation. -/
theorem perimeter_comap_add_right :
    perimeter μ (Opens.comap (ContinuousMap.addRight h) Ω)
        ((· + h) ⁻¹' s) =
      perimeter μ Ω s := by
  rw [perimeter_def, perimeter_def, indicator_one_preimage_add_right]
  exact totalVariationOn_comap_add_right

end Variation

end TauCeti
