/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# `Lᵖ` bounds from a pointwise bound by two functions

If `‖f‖ ≤ A ‖g‖ + B ‖h‖` almost everywhere, then for `1 ≤ p` the Minkowski inequality gives
`‖f‖_{Lᵖ} ≤ A ‖g‖_{Lᵖ} + B ‖h‖_{Lᵖ}` (`TauCeti.eLpNorm_le_mul_add_mul_of_ae_norm_le`). This is the
`Lᵖ` step of a product rule estimate such as `‖ψ Du + Dψ ⊗ u‖_{Lᵖ}`, where only the pointwise
bound depends on the product.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {α E F G : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup G] {p : ℝ≥0∞}

/-- If `‖f‖ ≤ A ‖g‖ + B ‖h‖` almost everywhere, then for `1 ≤ p`,
`‖f‖_{Lᵖ} ≤ A ‖g‖_{Lᵖ} + B ‖h‖_{Lᵖ}`. -/
theorem eLpNorm_le_mul_add_mul_of_ae_norm_le (hp : 1 ≤ p) {f : α → E} {g : α → F} {h : α → G}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) {A B : ℝ≥0}
    (hfgh : ∀ᵐ x ∂μ, ‖f x‖ ≤ A * ‖g x‖ + B * ‖h x‖) :
    eLpNorm f p μ ≤ A * eLpNorm g p μ + B * eLpNorm h p μ := by
  calc eLpNorm f p μ ≤ eLpNorm ((A : ℝ) • (fun x ↦ ‖g x‖) + (B : ℝ) • fun x ↦ ‖h x‖) p μ :=
        eLpNorm_mono_ae_real hf hfgh
    _ ≤ eLpNorm ((A : ℝ) • fun x ↦ ‖g x‖) p μ + eLpNorm ((B : ℝ) • fun x ↦ ‖h x‖) p μ :=
        eLpNorm_add_le hp
    _ = A * eLpNorm g p μ + B * eLpNorm h p μ := by
        rw [eLpNorm_const_smul, eLpNorm_const_smul, eLpNorm_norm _ hg, eLpNorm_norm _ hh]
        simp

end TauCeti
