/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-!
# Averaging an invariant integral over a finite measure of group elements

Let a group `G` act jointly measurably on `X`, preserving an s-finite measure `μ`. For an
integrable `F : X → ℝ` and a finite measure `ν` on `G`, the translates `(x, g) ↦ F (g • x)` are
integrable for `μ.prod ν` (`MeasureTheory.integrable_smul_prod`), and integrating the invariance
`∫ F (g • x) dμ = ∫ F dμ` against `ν` with Fubini gives
`∫ (∫ F (g • x) dν(g)) dμ(x) = ν(G) ∫ F dμ` (`MeasureTheory.integral_integral_smul_eq`). These
are the Fubini steps of averaging arguments over time windows for flows. The additive versions are
`MeasureTheory.integrable_vadd_prod` and `MeasureTheory.integral_integral_vadd_eq`.
-/

public section

namespace MeasureTheory

variable {G X : Type*} [MeasurableSpace G] [MeasurableSpace X] [Group G] [MulAction G X]
  [MeasurableSMul₂ G X] {μ : Measure X} [SFinite μ] [SMulInvariantMeasure G X μ]
  {ν : Measure G} [IsFiniteMeasure ν]

/-- The translates of an integrable function, over a finite measure `ν` of group elements, are
jointly integrable. -/
@[to_additive integrable_vadd_prod
/-- The translates of an integrable function, over a finite measure `ν` of group
elements, are jointly integrable. -/]
theorem integrable_smul_prod {F : X → ℝ} (hF : Measurable F) (hFi : Integrable F μ) :
    Integrable (fun p : X × G => F (p.2 • p.1)) (μ.prod ν) := by
  refine (integrable_prod_iff'
    (hF.comp (measurable_snd.smul measurable_fst)).aestronglyMeasurable).2
    ⟨ae_of_all _ fun s => (measurePreserving_smul s μ).integrable_comp_of_integrable hFi, ?_⟩
  exact (integrable_const (∫ x, ‖F x‖ ∂μ)).congr
    (ae_of_all _ fun s => (integral_smul_eq_self (μ := μ) (fun x => ‖F x‖)).symm)

/-- Integrating the invariance `∫ F dμ = ∫ F (g • ·) dμ` against a finite measure `ν` of group
elements and applying Fubini. -/
@[to_additive /-- Integrating the invariance `∫ F dμ = ∫ F (g +ᵥ ·) dμ` against a finite measure
`ν` of group elements and applying Fubini. -/]
theorem integral_integral_smul_eq {F : X → ℝ} (hF : Measurable F) (hFi : Integrable F μ) :
    ∫ x, (∫ g, F (g • x) ∂ν) ∂μ = ν.real Set.univ * ∫ x, F x ∂μ := by
  rw [integral_integral_swap (integrable_smul_prod hF hFi)]
  simp [integral_smul_eq_self]

end MeasureTheory
