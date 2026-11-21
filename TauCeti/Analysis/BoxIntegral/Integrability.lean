/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.BoxIntegral.Integrability

/-!
# Equality of box integrals and closed-box Bochner set integrals

For a function `f : (ι → ℝ) → E` taking values in a Banach space `E` and continuous on the closed
rectangular box `Set.Icc I.lower I.upper`, Mathlib's `MeasureTheory.ContinuousOn.hasBoxIntegral`
identifies the box integral of `f` (for any `BoxIntegral.IntegrationParams`, including Riemann,
Henstock–Kurzweil, McShane and `⊥`) with the Bochner integral over the half-open box `(I : Set _)`,
and `BoxIntegral.Box.coe_ae_eq_Icc` identifies that half-open box almost everywhere with the closed
box `Set.Icc I.lower I.upper`. Combining the two gives direct `BoxIntegral.integral` rewrite lemmas
against closed-box Bochner set integrals, on a box and on its coordinate hyperfaces `I.face i`.
-/

public section

open BoxIntegral MeasureTheory Set

section Box

universe u v

variable {ι : Type u} [Fintype ι] {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- If `f` is continuous on `Box.Icc I`, its `BoxIntegral.integral` with respect to any locally
finite measure `μ` and any `IntegrationParams` equals the Bochner set integral over `I`. -/
theorem ContinuousOn.boxIntegral_eq_setIntegral {f : (ι → ℝ) → E} (μ : Measure (ι → ℝ))
    [IsLocallyFiniteMeasure μ] {I : Box ι} (hc : ContinuousOn f (Box.Icc I))
    (l : IntegrationParams) :
    BoxIntegral.integral.{u, v, v} I l f μ.toBoxAdditive.toSMul = ∫ x in I, f x ∂μ :=
  (hc.hasBoxIntegral μ l).integral_eq

/-- If `f` is continuous on the closed box `Set.Icc I.lower I.upper`, its volume `BoxIntegral` for
any `IntegrationParams` equals its Bochner set integral over `Set.Icc I.lower I.upper`. -/
theorem ContinuousOn.boxIntegral_volume_eq_setIntegral_Icc {f : (ι → ℝ) → E}
    {I : Box ι} (hc : ContinuousOn f (Icc I.lower I.upper)) (l : IntegrationParams) :
    BoxIntegral.integral.{u, v, v} I l f BoxAdditiveMap.volume =
      ∫ x in Icc I.lower I.upper, f x := by
  rw [← Box.Icc_def] at hc
  rw [BoxAdditiveMap.volume, hc.boxIntegral_eq_setIntegral volume l,
    setIntegral_congr_set I.coe_ae_eq_Icc, Box.Icc_def]

end Box

namespace BoxIntegral.Box

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The volume `BoxIntegral` over the coordinate face `I.face i` of a function `f : (Fin n → ℝ) → E`
continuous on `Set.Icc (I.lower ∘ i.succAbove) (I.upper ∘ i.succAbove)` equals its Bochner set
integral over that closed face. -/
theorem integral_face_eq_setIntegral_Icc (I : Box (Fin (n + 1))) {f : (Fin n → ℝ) → E}
    {i : Fin (n + 1)}
    (hc : ContinuousOn f (Icc (I.lower ∘ i.succAbove) (I.upper ∘ i.succAbove)))
    (l : IntegrationParams) :
    BoxIntegral.integral (I.face i) l f BoxAdditiveMap.volume =
      ∫ x in Icc (I.lower ∘ i.succAbove) (I.upper ∘ i.succAbove), f x := by
  have hl : (I.face i).lower = I.lower ∘ i.succAbove := funext (face_lower I i)
  have hu : (I.face i).upper = I.upper ∘ i.succAbove := funext (face_upper I i)
  rw [← hl, ← hu] at hc
  simpa only [hl, hu] using hc.boxIntegral_volume_eq_setIntegral_Icc l

end BoxIntegral.Box
