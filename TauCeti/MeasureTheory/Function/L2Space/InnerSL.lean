/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Covector fields of square-integrable functions

An element `h` of `L²(μ, E)`, for an inner product space `E`, gives the covector field
`z ↦ ⟪h z, ·⟫`. Since `innerSL` is an isometry, a field `η` almost everywhere equal to it is
square integrable, with `∫ ‖η‖² = ‖h‖²`
(`MeasureTheory.Lp.integral_norm_sq_eq_and_integrable_of_innerSL_ae_eq`). This is how an element
of `L²` orthogonal to the range of an operator is compared with a regular covector field
representing it.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A covector field almost everywhere equal to `⟪h, ·⟫` for `h ∈ L²(μ, E)` is square integrable,
and the integral of its squared norm is the squared norm of `h`. -/
theorem integral_norm_sq_eq_and_integrable_of_innerSL_ae_eq {h : Lp E 2 μ}
    {η : α → E →L[𝕜] 𝕜} (hae : (fun z ↦ innerSL 𝕜 (h z)) =ᵐ[μ] η) :
    ∫ z, ‖η z‖ ^ 2 ∂μ = ‖h‖ ^ 2 ∧ Integrable (fun z ↦ ‖η z‖ ^ 2) μ := by
  have hn : (fun z ↦ ‖η z‖ ^ 2) =ᵐ[μ] fun z ↦ ‖h z‖ ^ 2 :=
    hae.mono fun z hz ↦ by
      simp only at hz ⊢
      rw [← hz, innerSL_apply_norm]
  have hm : MemLp (⇑h) ((2 : ℕ) : ℝ≥0∞) μ := by simpa using Lp.memLp h
  exact ⟨by rw [integral_congr_ae hn, Lp.integral_norm_sq_eq_norm_sq],
    (hm.integrable_norm_pow two_ne_zero).congr hn.symm⟩

end MeasureTheory.Lp
