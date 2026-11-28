/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.TestFunction.Convolution.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Convolution on fixed-support spaces of Lie test functions

`MeasureTheory.Measure.convolutionFixedSupport` restricts convolution to the support bound
`C * D` using Mathlib's bilinear restriction maps.
For a left-invariant measure, `MeasureTheory.Measure.fixedSupportSeminorm_convolution_le` bounds
each output seminorm by the corresponding left-derivative seminorm of the first factor times
the supremum norm of the second and the measure of the first support. The proof combines
`MeasureTheory.Measure.leftDerivWord_convolution` with
Mathlib's `norm_setIntegral_le_of_norm_le_const`.

`MeasureTheory.Measure.continuous_convolutionFixedSupport` gives joint continuity on the
fixed-support spaces when the first support bound has finite measure. See Bernstein–Krötz,
*Smooth Fréchet globalizations of Harish-Chandra modules*, §2.5.
-/

public section

noncomputable section

open MeasureTheory Set Topology
open scoped ContDiff Manifold Pointwise

namespace TauCeti.LieTestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- For a left-invariant measure, the seminorm of a convolution for `w` is bounded by the
product of the seminorm of the first factor for `w`, the supremum norm of the second factor,
and the measure of the first factor's support closure. -/
theorem _root_.MeasureTheory.Measure.fixedSupportSeminorm_convolution_le [μ.IsMulLeftInvariant]
    (a b : LieTestFunction I G) (w : List (GroupLieAlgebra I G)) :
    fixedSupportSeminorm w (convolution μ a b) ≤
      μ.real (tsupport a) * (fixedSupportSeminorm w a * fixedSupportSeminorm [] b) := by
  refine (fixedSupportSeminorm_le_iff w _ (by positivity)).2 fun g ↦ ?_
  rw [μ.leftDerivWord_convolution, convolution_apply,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport a)]
  · rw [mul_comm (μ.real (tsupport a))]
    refine norm_setIntegral_le_of_norm_le_const a.hasCompactSupport.isCompact.measure_lt_top
      fun x _ ↦ ?_
    rw [norm_mul]
    have hb := norm_leftDerivWord_le [] b (x⁻¹ * g)
    simp only [leftDerivWord_nil, LinearMap.id_apply] at hb
    gcongr
    exact norm_leftDerivWord_le w a x
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport
      (fun hx' ↦ hx (tsupport_leftDerivWord_subset w a hx')), zero_mul]

namespace FixedSupport

variable {C D : Set G}

/-- Convolution restricted to functions supported in `C` and `D`, with codomain the
fixed-support space for `C * D`. -/
def _root_.MeasureTheory.Measure.convolutionFixedSupport (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] :
    FixedSupport I G C →ₗ[ℂ] FixedSupport I G D →ₗ[ℂ] FixedSupport I G (C * D) :=
  ((LieTestFunction.convolution μ).compl₁₂ (inclusion I G C) (inclusion I G D)).codRestrict₂
    (inclusion I G (C * D)) inclusion_injective fun a b ↦ by
      rw [LinearMap.compl₁₂_apply, LinearMap.mem_range]
      exact ⟨mk _ ((tsupport_convolution_subset μ _ _).trans
        (mul_subset_mul (tsupport_inclusion_subset a) (tsupport_inclusion_subset b))),
        inclusion_mk ..⟩

/-- The inclusion of a fixed-support convolution into the space of test functions is the
convolution of the two inclusions. -/
@[simp]
theorem _root_.MeasureTheory.Measure.convolutionFixedSupport_inclusion
    (a : FixedSupport I G C) (b : FixedSupport I G D) :
    inclusion I G (C * D) (μ.convolutionFixedSupport a b) =
      LieTestFunction.convolution μ (inclusion I G C a) (inclusion I G D b) := by
  rw [Measure.convolutionFixedSupport, LinearMap.codRestrict₂_apply, LinearMap.compl₁₂_apply]

/-- On fixed-support spaces the convolution seminorm bound uses the measure of `C`. -/
theorem _root_.MeasureTheory.Measure.seminormFamily_convolutionFixedSupport_le
    [μ.IsMulLeftInvariant] (hC : μ C ≠ ⊤) (a : FixedSupport I G C) (b : FixedSupport I G D)
    (w : List (GroupLieAlgebra I G)) :
    seminormFamily I G (C * D) w (μ.convolutionFixedSupport a b) ≤
      μ.real C * (seminormFamily I G C w a * seminormFamily I G D [] b) := by
  simp only [seminormFamily_apply, Measure.convolutionFixedSupport_inclusion]
  refine (μ.fixedSupportSeminorm_convolution_le _ _ w).trans ?_
  gcongr
  exact tsupport_inclusion_subset a

/-- Convolution against a left-invariant measure is jointly continuous on fixed-support spaces
when the first support bound has finite measure. -/
theorem _root_.MeasureTheory.Measure.continuous_convolutionFixedSupport [μ.IsMulLeftInvariant]
    (hC : μ C ≠ ⊤) :
    Continuous (fun p : FixedSupport I G C × FixedSupport I G D ↦
      μ.convolutionFixedSupport p.1 p.2) := by
  have hbound := μ.seminormFamily_convolutionFixedSupport_le (I := I) (D := D) hC
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  apply ((withSeminorms I G (C * D)).tendsto_nhds _ _).2
  intro w ε hε
  let q := seminormFamily I G C w
  let r := seminormFamily I G D []
  have hq : Continuous q := (withSeminorms I G C).continuous_seminorm w
  have hr : Continuous r := (withSeminorms I G D).continuous_seminorm []
  have hcont : Continuous (fun z : FixedSupport I G C × FixedSupport I G D ↦
      μ.real C * (q (z.1 - p.1) * r z.2) + μ.real C * (q p.1 * r (z.2 - p.2))) := by fun_prop
  have hsmall := hcont.continuousAt.eventually_lt continuousAt_const
    (x₀ := p) (g := fun _ ↦ ε) (by simpa only [sub_self, map_zero, zero_mul, mul_zero, add_zero]
      using hε)
  filter_upwards [hsmall] with z hz
  have hsub : μ.convolutionFixedSupport z.1 z.2 - μ.convolutionFixedSupport p.1 p.2 =
      μ.convolutionFixedSupport (z.1 - p.1) z.2 + μ.convolutionFixedSupport p.1 (z.2 - p.2) := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  rw [hsub]
  exact ((map_add_le_add (seminormFamily I G (C * D) w) _ _).trans
    (add_le_add (hbound _ _ w) (hbound _ _ w))).trans_lt hz

end FixedSupport

end TauCeti.LieTestFunction
