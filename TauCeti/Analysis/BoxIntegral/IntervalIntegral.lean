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

`BoxIntegral.intervalBox` realizes a nondegenerate real interval as a box on `Fin 1`.
For a Bochner integrable function, the box integral agrees with its interval integral for
any non-Riemann integration parameters, in particular Henstock–Kurzweil parameters.
-/

public section

open MeasureTheory Set

namespace BoxIntegral

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

variable {E : Type*} [NormedAddCommGroup E]

/-- Integrability on an interval is equivalent to Bochner integrability on its interval box. -/
theorem integrableOn_intervalBox_iff {a b : ℝ} (hab : a < b) {f : ℝ → E} :
    IntegrableOn (fun x : Fin 1 → ℝ ↦ f (x 0)) (intervalBox a b hab) ↔
      IntervalIntegrable f volume a b := by
  rw [coe_intervalBox, intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
  exact (volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ)).integrableOn_comp_preimage
    (MeasurableEquiv.piUnique _).measurableEmbedding

variable [NormedSpace ℝ E]

/-- The Bochner integral on an interval box is the usual oriented interval integral. -/
theorem setIntegral_intervalBox {a b : ℝ} (hab : a < b) (f : ℝ → E) :
    (∫ x in (intervalBox a b hab : Set (Fin 1 → ℝ)), f (x 0)) = ∫ x in a..b, f x := by
  rw [coe_intervalBox, intervalIntegral.integral_of_le hab.le]
  exact (volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ)).setIntegral_preimage_emb
    (MeasurableEquiv.piUnique _).measurableEmbedding f _

end BoxIntegral

/-- Every Bochner integrable function has the same non-Riemann box integral on `Fin 1`. -/
theorem IntervalIntegrable.hasBoxIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hab : a < b) (l : BoxIntegral.IntegrationParams) (hl : l.bRiemann = false) :
    BoxIntegral.HasIntegral (BoxIntegral.intervalBox a b hab) l (fun x ↦ f (x 0))
      BoxIntegral.BoxAdditiveMap.volume (∫ x in a..b, f x) := by
  rw [← BoxIntegral.setIntegral_intervalBox hab]
  exact ((BoxIntegral.integrableOn_intervalBox_iff hab).2 hf).hasBoxIntegral l hl

namespace BoxIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The box integral agrees with the interval integral under Bochner integrability. -/
theorem integral_intervalBox {a b : ℝ} {f : ℝ → E} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (l : IntegrationParams) (hl : l.bRiemann = false) :
    integral (intervalBox a b hab) l (fun x ↦ f (x 0)) BoxAdditiveMap.volume =
      ∫ x in a..b, f x :=
  (hf.hasBoxIntegral hab l hl).integral_eq

/-- A box-integral value is the interval-integral value whenever Bochner integrability holds. -/
theorem HasIntegral.eq_intervalIntegral {a b : ℝ} {hab : a < b} {f : ℝ → E}
    {l : IntegrationParams} {y : E}
    (h : HasIntegral (intervalBox a b hab) l (fun x ↦ f (x 0)) BoxAdditiveMap.volume y)
    (hf : IntervalIntegrable f volume a b) (hl : l.bRiemann = false) :
    y = ∫ x in a..b, f x :=
  h.unique (hf.hasBoxIntegral hab l hl)

end BoxIntegral
