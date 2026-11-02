/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import TauCeti.Topology.Instances.AddCircle.Lift

import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# Pushforwards of Haar measure along circle diffeomorphisms

Let `φ : AddCircle T → AddCircle T` be the map of the circle with lift `F : ℝ → ℝ`, so that
`F (x + T) = F x + T` and `φ x = F x` for every real `x`
(`TauCeti/Topology/Instances/AddCircle/Lift.lean`). When `F` is differentiable with
`c ≤ F' ≤ M` for constants `0 < c ≤ M`, the map `φ` distorts measure only by bounded factors:
`φ` pushes Haar measure forward to at most `c⁻¹` times Haar measure, and the inverse of `φ`
pushes Haar measure forward to at most `M` times Haar measure. These are the bounds which make
precomposition with an orientation-preserving diffeomorphism of the circle a bounded isomorphism
of `L²` of the circle (`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`).

The proof reads the measure of the circle on the fundamental interval `(0, T]`, which `F` maps
onto the fundamental interval `(F 0, F 0 + T]`, and applies the change of variables formula
`map_withDensity_abs_det_fderiv_eq_addHaar` there.

## Main declarations

* `AddCircle.map_volume_le_of_lift` and `AddCircle.map_haarAddCircle_le_of_lift`: if `c ≤ F'`
  with `c > 0`, then `φ` pushes the measure of the circle forward to at most `c⁻¹` times itself.
* `AddCircle.volume_le_smul_map_volume_of_lift`: if `0 < F' ≤ M`, then the measure of the
  circle is at most `M` times its pushforward along `φ`.
* `AddCircle.map_volume_le_of_lift_of_leftInverse` and
  `AddCircle.map_haarAddCircle_le_of_lift_of_leftInverse`: if `0 < F' ≤ M`, then a measurable
  left inverse of `φ` pushes the measure of the circle forward to at most `M` times itself.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)] {φ : AddCircle T → AddCircle T} {F F' : ℝ → ℝ}

/-- Haar measure on the circle is the measure of the circle divided by its length `T`. -/
theorem haarAddCircle_eq_smul_volume :
    (haarAddCircle : Measure (AddCircle T)) = (ENNReal.ofReal T)⁻¹ • volume := by
  rw [volume_eq_smul_haarAddCircle, smul_smul, ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.2 hT.out).ne' ENNReal.ofReal_ne_top, one_smul]

section Pushforward

variable (hF : ∀ x, HasDerivAt F (F' x) x) (hper : ∀ x, F (x + T) = F x + T)
  (hφ : ∀ x : ℝ, φ x = F x)
include hF hper hφ

omit hper in
/-- Pushing the measure of the circle forward along `φ` is pushing Lebesgue measure on `(0, T]`
forward along the lift `F`, and then to the circle. -/
private theorem map_volume_eq_of_lift :
    (volume : Measure (AddCircle T)).map φ =
      ((volume.restrict (Ioc 0 T)).map F).map ((↑) : ℝ → AddCircle T) := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  rw [← (AddCircle.measurePreserving_mk T 0).map_eq, zero_add,
    Measure.map_map (continuous_of_lift hFc hφ).measurable AddCircle.measurable_mk',
    Measure.map_map AddCircle.measurable_mk' hFc.measurable]
  congr 1
  funext x
  simp [hφ]

/-- **Pushforward bound for a circle map with derivative bounded below.** If the lift `F` of `φ`
satisfies `c ≤ F'` with `c > 0`, then `φ` pushes the measure of the circle forward to at most `c⁻¹`
times itself. -/
theorem map_volume_le_of_lift {c : ℝ} (hc : 0 < c) (hcF : ∀ x, c ≤ F' x) :
    (volume : Measure (AddCircle T)).map φ ≤ (ENNReal.ofReal c)⁻¹ • volume := by
  have hmono : StrictMono F := strictMono_of_hasDerivAt_pos hF fun x ↦ hc.trans_le (hcF x)
  rw [map_volume_eq_of_lift hF hφ, ← (AddCircle.measurePreserving_mk T (F 0)).map_eq,
    ← Measure.map_smul _ AddCircle.measurable_mk'.aemeasurable]
  refine Measure.map_mono ?_ AddCircle.measurable_mk'
  refine (map_restrict_le_smul_restrict_image volume measurableSet_Ioc.nullMeasurableSet
    (fun x _ ↦ (hF x).hasFDerivAt.hasFDerivWithinAt) hmono.injective.injOn hc
    (fun x _ ↦ by simpa using (hcF x).trans (le_abs_self _))).trans ?_
  gcongr
  exact image_Ioc_subset_of_lift hmono hper

/-- **Reverse pushforward bound for a circle map with derivative bounded above.** If the lift `F`
of `φ` satisfies `0 < F' ≤ M`, then the measure of the circle is at most `M` times its pushforward
along `φ`. -/
theorem volume_le_smul_map_volume_of_lift (hpos : ∀ x, 0 < F' x) {M : ℝ} (hMF : ∀ x, F' x ≤ M) :
    (volume : Measure (AddCircle T)) ≤
      ENNReal.ofReal M • (volume : Measure (AddCircle T)).map φ := by
  have hmono : StrictMono F := strictMono_of_hasDerivAt_pos hF hpos
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  rw [map_volume_eq_of_lift hF hφ, ← Measure.map_smul _ AddCircle.measurable_mk'.aemeasurable,
    ← (AddCircle.measurePreserving_mk T (F 0)).map_eq, ← image_Ioc_of_lift hmono hFc hper,
    ← map_withDensity_abs_det_fderiv_eq_addHaar volume measurableSet_Ioc.nullMeasurableSet
      (fun x _ ↦ (hF x).hasFDerivAt.hasFDerivWithinAt) hmono.injective.injOn,
    ← Measure.map_smul _ hFc.measurable.aemeasurable, ← withDensity_const]
  refine Measure.map_mono (Measure.map_mono (withDensity_mono (Filter.Eventually.of_forall
    fun x ↦ ?_)) hFc.measurable) AddCircle.measurable_mk'
  simpa [abs_of_pos (hpos x)] using ENNReal.ofReal_le_ofReal (hMF x)

/-- If the lift `F` of `φ` satisfies `0 < F' ≤ M` and `ψ` is a measurable left inverse of `φ`,
then `ψ` pushes the measure of the circle forward to at most `M` times itself. -/
theorem map_volume_le_of_lift_of_leftInverse (hpos : ∀ x, 0 < F' x) {M : ℝ}
    (hMF : ∀ x, F' x ≤ M) {ψ : AddCircle T → AddCircle T} (hψ : Measurable ψ)
    (hψφ : Function.LeftInverse ψ φ) :
    (volume : Measure (AddCircle T)).map ψ ≤ ENNReal.ofReal M • volume := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  calc (volume : Measure (AddCircle T)).map ψ
      ≤ (ENNReal.ofReal M • (volume : Measure (AddCircle T)).map φ).map ψ :=
        Measure.map_mono (volume_le_smul_map_volume_of_lift hF hper hφ hpos hMF) hψ
    _ = ENNReal.ofReal M • volume := by
        rw [Measure.map_smul _ hψ.aemeasurable,
          Measure.map_map hψ (continuous_of_lift hFc hφ).measurable, hψφ.comp_eq_id,
          Measure.map_id]

/-- The `haarAddCircle` form of `AddCircle.map_volume_le_of_lift`. -/
theorem map_haarAddCircle_le_of_lift {c : ℝ} (hc : 0 < c) (hcF : ∀ x, c ≤ F' x) :
    (haarAddCircle : Measure (AddCircle T)).map φ ≤ (ENNReal.ofReal c)⁻¹ • haarAddCircle := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  rw [haarAddCircle_eq_smul_volume, Measure.map_smul _
    (continuous_of_lift hFc hφ).measurable.aemeasurable, smul_comm]
  gcongr
  exact map_volume_le_of_lift hF hper hφ hc hcF

/-- The `haarAddCircle` form of `AddCircle.map_volume_le_of_lift_of_leftInverse`. -/
theorem map_haarAddCircle_le_of_lift_of_leftInverse (hpos : ∀ x, 0 < F' x) {M : ℝ}
    (hMF : ∀ x, F' x ≤ M) {ψ : AddCircle T → AddCircle T} (hψ : Measurable ψ)
    (hψφ : Function.LeftInverse ψ φ) :
    (haarAddCircle : Measure (AddCircle T)).map ψ ≤ ENNReal.ofReal M • haarAddCircle := by
  rw [haarAddCircle_eq_smul_volume, Measure.map_smul _ hψ.aemeasurable, smul_comm]
  gcongr
  exact map_volume_le_of_lift_of_leftInverse hF hper hφ hpos hMF hψ hψφ

end Pushforward

end AddCircle
