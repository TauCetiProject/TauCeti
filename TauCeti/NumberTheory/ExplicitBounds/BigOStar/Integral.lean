/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.NumberTheory.ExplicitBounds.BigOStar.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrating explicit errors

An integrable pointwise error bound integrates to an explicit error between the integrals.
The measure need not be finite: integrability of the displayed error is the relevant condition.
The almost-everywhere form also permits estimates with exceptional null sets.
-/

public section

open MeasureTheory

namespace TauCeti

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {f g : α → E} {h : α → ℝ}

/-- Integrating almost-everywhere explicit errors adds their errors by integration. -/
theorem bigOStar_integral (H : ∀ᵐ x ∂μ, BigOStar (f x) (g x) (h x))
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    BigOStar (∫ x, f x ∂μ) (∫ x, g x ∂μ) (∫ x, h x ∂μ) := by
  rw [bigOStar_iff, ← integral_sub hf hg]
  exact norm_integral_le_of_norm_le hh (H.mono fun _ hx ↦ bigOStar_iff.mp hx)

/-- Integrating an explicit error on a measurable set gives an error between set integrals. -/
theorem BigOStarOn.integral {s : Set α} (H : BigOStarOn f g h s) (hs : MeasurableSet s)
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) (hh : IntegrableOn h s μ) :
    BigOStar (∫ x in s, f x ∂μ) (∫ x in s, g x ∂μ) (∫ x in s, h x ∂μ) :=
  bigOStar_integral (ae_restrict_of_forall_mem hs (bigOStarOn_iff.mp H)) hf hg hh

end TauCeti
