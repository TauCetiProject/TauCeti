/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Integrability of the applied derivative of a compactly supported function

The derivative of a `C¹` function with compact support is continuous and compactly supported,
hence bounded. So along a strongly measurable family of points `G`, the derivative applied to an
integrable family of vectors `Z` is integrable: it is dominated by a constant times `‖Z‖`. No
finiteness of the measure is needed.

On a Euclidean product `ℝ × V`, the derivative of such a function in a fixed direction is also
integrable on the product of a half-line with `V`.

## Main results

* `TauCeti.integrable_fderiv_apply`: for `f` of class `C¹` with compact support, an a.e. strongly
  measurable `G` and an integrable `Z`, the map `x ↦ fderiv 𝕜 f (G x) (Z x)` is integrable.
* `TauCeti.integrable_fderiv_apply_prod`: the directional derivative of a compactly supported
  `C¹` function on `ℝ × V` is integrable on the product of `Ioi a` with `V`.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The derivative of a `C¹` compactly supported function, evaluated along an a.e. strongly
measurable family of points `G` and applied to an integrable family of vectors `Z`, is integrable:
it is bounded by a constant times `‖Z‖`. -/
theorem integrable_fderiv_apply {f : E → F} (hf : ContDiff 𝕜 1 f) (hfc : HasCompactSupport f)
    {G : α → E} (hG : AEStronglyMeasurable G μ) {Z : α → E} (hZ : Integrable Z μ) :
    Integrable (fun x ↦ fderiv 𝕜 f (G x) (Z x)) μ := by
  have hDf := hf.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hDf.bounded_above_of_compact_support (hfc.fderiv 𝕜)
  exact (hZ.norm.const_mul C).mono'
    (Continuous.comp_aestronglyMeasurable₂ (g := fun (L : E →L[𝕜] F) w ↦ L w)
      (by fun_prop) (hDf.comp_aestronglyMeasurable hG) hZ.1)
    (.of_forall fun x ↦ (fderiv 𝕜 f _).le_of_opNorm_le (hC _) _)

section Prod

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The directional derivative of a compactly supported `C¹` function is integrable on the
product of `Ioi a` with `V`. -/
theorem integrable_fderiv_apply_prod {g : WithLp 2 (ℝ × V) → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (a : ℝ) (d : WithLp 2 (ℝ × V)) :
    Integrable (fun z : ℝ × V ↦ fderiv ℝ g (WithLp.toLp 2 z) d)
      ((volume.restrict (Ioi a)).prod volume) := by
  have hdc : Continuous fun x ↦ fderiv ℝ g x d :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h : Integrable (fun x ↦ fderiv ℝ g x d) volume :=
    hdc.integrable_of_hasCompactSupport (hgc.fderiv_apply (𝕜 := ℝ) d)
  have hprod :=
    (WithLp.volume_preserving_toLp ℝ V).integrable_comp h.aestronglyMeasurable |>.mpr h
  rw [Measure.restrict_prod_eq_prod_univ]
  exact hprod.integrableOn

end Prod

end TauCeti
