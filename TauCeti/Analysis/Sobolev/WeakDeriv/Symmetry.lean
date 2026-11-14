/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Weak derivatives commute

Let `u` have weak derivatives `u₁` in the direction `v` and `u₂` in the direction `w` on an open
set `Ω`. If `u₁` has a weak derivative `u₁₂` in the direction `w`, then `u₂` has the same weak
derivative `u₁₂` in the direction `v`: the mixed weak derivatives `∂_w ∂_v u` and `∂_v ∂_w u`
agree as soon as one of them exists. No regularity beyond the existence of the three weak
derivatives is assumed.

The proof moves both derivatives onto the test function and uses that directional derivatives of
test functions commute (`TestFunction.lineDerivOp_comm`).

## Main declarations

* `TauCeti.HasWeakLineDerivOn.comm`: weak derivatives in two directions commute.
* `TauCeti.HasWeakLineDerivOn.integral_inner_fderiv_comm` and
  `TauCeti.HasWeakFDerivOn.integral_inner_fderiv_comm`: distributional symmetry of first weak
  derivatives paired against directional derivatives of vector-valued test functions,
  `∫ ⟪∂_v φ, ∂_w u⟫ = ∫ ⟪∂_w φ, ∂_v u⟫`.
-/

public section

namespace TauCeti

open LineDeriv MeasureTheory TopologicalSpace
open scoped Distributions InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] {μ : Measure E} {Ω : Opens E}
  {u u₁ u₂ u₁₂ : E → F} {v w : E}

/-- **Weak derivatives commute.** If `u` has weak derivatives `u₁ = ∂_v u` and `u₂ = ∂_w u` on
`Ω`, and `u₁` has a weak derivative `u₁₂ = ∂_w ∂_v u`, then `u₁₂` is also a weak derivative of
`u₂` in the direction `v`, that is, `∂_v ∂_w u = ∂_w ∂_v u`. -/
theorem HasWeakLineDerivOn.comm (h₁ : HasWeakLineDerivOn μ Ω u u₁ v)
    (h₁₂ : HasWeakLineDerivOn μ Ω u₁ u₁₂ w) (h₂ : HasWeakLineDerivOn μ Ω u u₂ w) :
    HasWeakLineDerivOn μ Ω u₂ u₁₂ v := by
  refine hasWeakLineDerivOn_iff_testFunction.2
    ⟨h₁.completeSpace, h₂.locallyIntegrableOn_deriv, h₁₂.locallyIntegrableOn_deriv, fun φ => ?_⟩
  calc ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u₂ x ∂μ
      = ∫ x, (∂_{v} φ : 𝓓(Ω, ℝ)) x • u₂ x ∂μ := by simp only [TestFunction.lineDerivOp_apply]
    _ = -∫ x, lineDeriv ℝ (∂_{v} φ : 𝓓(Ω, ℝ)) x w • u x ∂μ := by
        rw [h₂.integral_lineDeriv_smul_eq_neg_integral_smul, neg_neg]
    _ = -∫ x, lineDeriv ℝ (∂_{w} φ : 𝓓(Ω, ℝ)) x v • u x ∂μ := by
        simp only [TestFunction.lineDeriv_lineDerivOp_comm φ v w]
    _ = ∫ x, (∂_{w} φ : 𝓓(Ω, ℝ)) x • u₁ x ∂μ := by
        rw [h₁.integral_lineDeriv_smul_eq_neg_integral_smul, neg_neg]
    _ = ∫ x, lineDeriv ℝ (φ : E → ℝ) x w • u₁ x ∂μ := by
        simp only [TestFunction.lineDerivOp_apply]
    _ = -∫ x, (φ : E → ℝ) x • u₁₂ x ∂μ := h₁₂.integral_lineDeriv_smul_eq_neg_integral_smul φ

/-- **Distributional symmetry of weak directional derivatives.** Without assuming second weak
derivatives of `u`, weak directional derivatives `u₁ = ∂_v u` and `u₂ = ∂_w u` on `Ω` satisfy
`∫ ⟪∂_v φ, u₂⟫ = ∫ ⟪∂_w φ, u₁⟫` for every `φ ∈ 𝓓(Ω, V)`: both sides equal `-∫ ⟪∂_v ∂_w φ, u⟫`. -/
theorem HasWeakLineDerivOn.integral_inner_fderiv_comm [OpensMeasurableSpace E]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {u u₁ u₂ : E → V} {v w : E} (hv : HasWeakLineDerivOn μ Ω u u₁ v)
    (hw : HasWeakLineDerivOn μ Ω u u₂ w) (φ : 𝓓(Ω, V)) :
    ∫ x, ⟪fderiv ℝ (φ : E → V) x v, u₂ x⟫_ℝ ∂μ =
      ∫ x, ⟪fderiv ℝ (φ : E → V) x w, u₁ x⟫_ℝ ∂μ := by
  have hw' := hw.integral_inner_lineDeriv_eq_neg (∂_{v} φ)
  have hv' := hv.integral_inner_lineDeriv_eq_neg (∂_{w} φ)
  simp_rw [TestFunction.lineDeriv_lineDerivOp_comm φ v w,
    TestFunction.lineDerivOp_apply_eq_fderiv] at hw'
  simp_rw [TestFunction.lineDerivOp_apply_eq_fderiv] at hv'
  linarith

/-- **Distributional symmetry of first weak derivatives.** Without assuming second weak derivatives
of `u`, a weak Fréchet derivative `U` of `u` on `Ω` satisfies
`∫ ⟪∂_v φ, U · w⟫ = ∫ ⟪∂_w φ, U · v⟫` for every `φ ∈ 𝓓(Ω, V)` and directions `v, w : E`: both sides
equal `-∫ ⟪∂_v ∂_w φ, u⟫`. -/
theorem HasWeakFDerivOn.integral_inner_fderiv_comm [OpensMeasurableSpace E]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {u : E → V} {U : E → E →L[ℝ] V}
    (h : HasWeakFDerivOn μ Ω u U) (v w : E) (φ : 𝓓(Ω, V)) :
    ∫ x, ⟪fderiv ℝ (φ : E → V) x v, U x w⟫_ℝ ∂μ =
      ∫ x, ⟪fderiv ℝ (φ : E → V) x w, U x v⟫_ℝ ∂μ :=
  (h.hasWeakLineDerivOn v).integral_inner_fderiv_comm (h.hasWeakLineDerivOn w) φ

end TauCeti
