/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.BoxIntegral.Integrability
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# One-dimensional box integrals and interval integrals

`TauCeti.BoxIntegral.intervalBox` realizes a nondegenerate real interval as a box on `Fin 1`.
For a Bochner integrable function, the box integral agrees with its interval integral for
any non-Riemann integration parameters, in particular Henstock–Kurzweil parameters.
-/

public section

open MeasureTheory Set

open BoxIntegral

namespace TauCeti.BoxIntegral

/-- The one-dimensional box corresponding to the half-open interval `(a, b]`. -/
def intervalBox (a b : ℝ) (hab : a < b) : Box (Fin 1) :=
  ⟨fun _ ↦ a, fun _ ↦ b, fun _ ↦ hab⟩

@[simp]
theorem intervalBox_lower (a b : ℝ) (hab : a < b) (i : Fin 1) :
    (intervalBox a b hab).lower i = a := (rfl)

@[simp]
theorem intervalBox_upper (a b : ℝ) (hab : a < b) (i : Fin 1) :
    (intervalBox a b hab).upper i = b := (rfl)

@[simp]
theorem mem_intervalBox {a b : ℝ} {hab : a < b} {x : Fin 1 → ℝ} :
    x ∈ intervalBox a b hab ↔ x 0 ∈ Ioc a b := by
  simp [Box.mem_def, intervalBox]

@[simp]
theorem mem_Icc_intervalBox {a b : ℝ} {hab : a < b} {x : Fin 1 → ℝ} :
    x ∈ Box.Icc (intervalBox a b hab) ↔ x 0 ∈ Icc a b := by
  simp [Box.Icc_def, intervalBox, Pi.le_def]

/-- Evaluation at the sole coordinate identifies the interval box with a real interval. -/
theorem coe_intervalBox (a b : ℝ) (hab : a < b) :
    (intervalBox a b hab : Set (Fin 1 → ℝ)) =
      (MeasurableEquiv.piUnique fun _ : Fin 1 ↦ ℝ) ⁻¹' Ioc a b := by
  ext x
  simp [MeasurableEquiv.piUnique]

/-- Almost-everywhere equality on a real interval pulls back to its one-dimensional box. -/
theorem ae_eq_intervalBox {E : Type*} {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (h : f =ᵐ[volume.restrict (Ioc a b)] g) :
    (fun x : Fin 1 → ℝ ↦ f (x 0)) =ᵐ[volume.restrict (intervalBox a b hab)]
      (fun x ↦ g (x 0)) := by
  rw [coe_intervalBox]
  exact ((volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ)).restrict_preimage
    measurableSet_Ioc).quasiMeasurePreserving.ae_eq_comp h

/-- Interval-box inclusion is exactly the pair of endpoint inequalities. -/
@[simp]
theorem intervalBox_le_intervalBox_iff {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    intervalBox c d hcd ≤ intervalBox a b hab ↔ a ≤ c ∧ d ≤ b := by
  simp [Box.le_iff_bounds, intervalBox, Pi.le_def]

/-- Splitting at an interior point gives the lower interval box. -/
theorem splitLower_intervalBox (hac : a < c) (hcb : c < b) :
    (intervalBox a b (hac.trans hcb)).splitLower 0 c =
      (intervalBox a c hac : WithBot (Box (Fin 1))) := by
  rw [← Box.withBotCoe_inj]
  ext x
  simp only [Box.coe_splitLower, Box.coe_coe, mem_inter_iff, mem_ofPred_eq, Box.mem_coe,
    mem_intervalBox, mem_Ioc]
  grind

/-- Splitting at an interior point gives the upper interval box. -/
theorem splitUpper_intervalBox (hac : a < c) (hcb : c < b) :
    (intervalBox a b (hac.trans hcb)).splitUpper 0 c =
      (intervalBox c b hcb : WithBot (Box (Fin 1))) := by
  rw [← Box.withBotCoe_inj]
  ext x
  simp only [Box.coe_splitUpper, Box.coe_coe, mem_inter_iff, mem_ofPred_eq, Box.mem_coe,
    mem_intervalBox, mem_Ioc]
  grind

variable {E : Type*} [TopologicalSpace E] [ENormedAddMonoid E]

/-- Integrability on an interval is equivalent to integrability on its interval box. -/
theorem integrableOn_intervalBox_iff {a b : ℝ} (hab : a < b) {f : ℝ → E} :
    IntegrableOn (fun x : Fin 1 → ℝ ↦ f (x 0)) (intervalBox a b hab) ↔
      IntervalIntegrable f volume a b := by
  simp only [coe_intervalBox, IntervalIntegrable, Ioc_eq_empty_of_le hab.le,
    integrableOn_empty, and_true]
  exact (volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ)).integrableOn_comp_preimage
    (MeasurableEquiv.piUnique _).measurableEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Bochner integral on an interval box is the usual oriented interval integral. -/
theorem setIntegral_intervalBox {a b : ℝ} (hab : a < b) (f : ℝ → E) :
    (∫ x in (intervalBox a b hab : Set (Fin 1 → ℝ)), f (x 0)) = ∫ x in a..b, f x := by
  rw [coe_intervalBox, intervalIntegral.integral_of_le hab.le]
  exact (volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ)).setIntegral_preimage_emb
    (MeasurableEquiv.piUnique _).measurableEmbedding f _

end TauCeti.BoxIntegral

open TauCeti.BoxIntegral in
/-- Every Bochner integrable function has the same non-Riemann box integral on `Fin 1`. -/
theorem IntervalIntegrable.hasBoxIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hab : a < b) (l : BoxIntegral.IntegrationParams) (hl : l.bRiemann = false) :
    BoxIntegral.HasIntegral (TauCeti.BoxIntegral.intervalBox a b hab) l (fun x ↦ f (x 0))
      BoxIntegral.BoxAdditiveMap.volume (∫ x in a..b, f x) := by
  rw [← TauCeti.BoxIntegral.setIntegral_intervalBox hab]
  exact ((TauCeti.BoxIntegral.integrableOn_intervalBox_iff hab).2 hf).hasBoxIntegral l hl
