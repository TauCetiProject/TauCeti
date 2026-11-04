/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Set integral bounds from closed subsets

On a pseudometrizable space, a bound `‖∫ x in F, f x ∂μ‖ₑ ≤ ∫⁻ x in F, k x ∂μ` on every closed
subset `F` of a measurable set `B` on which `f` is integrable extends to `B` itself. The proof
approximates `B` from inside by a closed set, for the finite and hence weakly regular measure with
density `‖f‖ₑ` on `B`. When `B` lies in a compact set, its closed subsets are compact, so bounds on
compact sets extend to measurable subsets of compact sets.

## Main statements

* `TauCeti.enorm_setIntegral_le_of_forall_isClosed_subset`: the bound on closed subsets of `B`
  gives the bound on `B`.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-- **Inner regularity of set integral bounds.** On a pseudometrizable space, if
`‖∫ x in F, f x ∂μ‖ₑ ≤ ∫⁻ x in F, k x ∂μ` for every closed subset `F` of a measurable set `B`
on which `f` is integrable, then the same bound holds on `B`. -/
theorem enorm_setIntegral_le_of_forall_isClosed_subset {X G : Type*} [TopologicalSpace X]
    [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {μ : Measure X} {f : X → G} {k : X → ℝ≥0∞} {B : Set X}
    (hf : IntegrableOn f B μ) (hB : MeasurableSet B)
    (hF : ∀ F ⊆ B, IsClosed F → ‖∫ x in F, f x ∂μ‖ₑ ≤ ∫⁻ x in F, k x ∂μ) :
    ‖∫ x in B, f x ∂μ‖ₑ ≤ ∫⁻ x in B, k x ∂μ := by
  -- A finite measure carrying the mass of `‖f‖` on `B`; it is weakly regular.
  set ζ := (μ.restrict B).withDensity fun x => ‖f x‖ₑ
  have : IsFiniteMeasure ζ := isFiniteMeasure_withDensity hf.2.ne
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨F, hFB, hFc, hζ⟩ :=
    hB.exists_isClosed_sdiff_lt (measure_ne_top ζ B) (ENNReal.coe_ne_zero.2 hε.ne')
  rw [withDensity_apply _ (hB.diff hFc.measurableSet),
    Measure.restrict_restrict (hB.diff hFc.measurableSet), inter_eq_left.2 sdiff_subset] at hζ
  calc ‖∫ x in B, f x ∂μ‖ₑ = ‖∫ x in F, f x ∂μ + ∫ x in B \ F, f x ∂μ‖ₑ := by
        rw [setIntegral_sdiff hFc.measurableSet hf hFB, add_sub_cancel]
    _ ≤ ‖∫ x in F, f x ∂μ‖ₑ + ‖∫ x in B \ F, f x ∂μ‖ₑ := enorm_add_le _ _
    _ ≤ ∫⁻ x in B, k x ∂μ + ε :=
        add_le_add ((hF F hFB hFc).trans (lintegral_mono_set hFB))
          ((enorm_integral_le_lintegral_enorm _).trans hζ.le)

end TauCeti
