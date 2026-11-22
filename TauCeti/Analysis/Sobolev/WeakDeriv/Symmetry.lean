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
test functions commute (`TestFunction.lineDerivOp_comm`). The same argument shows, with no second
weak derivative assumed, that the first weak derivatives of `u` pair symmetrically with the
derivatives of a vector-valued test function.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.comm`: weak derivatives in two directions commute.
* `TauCeti.HasWeakFDerivOn.integral_inner_fderiv_apply_comm`: for a weak derivative `Du` and a
  test function `φ`, `∫ ⟪∂_v φ, Du w⟫ = ∫ ⟪∂_w φ, Du v⟫`.
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

/-- **Mixed weak derivatives commute against test functions.** If `u` has a weak derivative `Du`
on `Ω`, then for every test function `φ` and all directions `v` and `w`,
`∫ ⟪∂_v φ, Du w⟫ = ∫ ⟪∂_w φ, Du v⟫`: both sides are `-∫ ⟪∂_w ∂_v φ, u⟫`. No second weak
derivative of `u` is assumed to exist. -/
theorem HasWeakFDerivOn.integral_inner_fderiv_apply_comm [OpensMeasurableSpace E]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {u : E → V} {Du : E → E →L[ℝ] V} (hu : HasWeakFDerivOn μ Ω u Du) (φ : 𝓓(Ω, V)) (v w : E) :
    ∫ x, ⟪fderiv ℝ (φ : E → V) x v, Du x w⟫_ℝ ∂μ =
      ∫ x, ⟪fderiv ℝ (φ : E → V) x w, Du x v⟫_ℝ ∂μ := by
  have h1 := (hu.hasWeakLineDerivOn w).integral_inner_lineDeriv_eq_neg (∂_{v} φ)
  have h2 := (hu.hasWeakLineDerivOn v).integral_inner_lineDeriv_eq_neg (∂_{w} φ)
  have h3 : (fun x => ⟪lineDeriv ℝ ((∂_{v} φ : 𝓓(Ω, V)) : E → V) x w, u x⟫_ℝ) =
      fun x => ⟪lineDeriv ℝ ((∂_{w} φ : 𝓓(Ω, V)) : E → V) x v, u x⟫_ℝ :=
    funext fun x => by rw [TestFunction.lineDeriv_lineDerivOp_comm]
  rw [h3, h2] at h1
  simpa only [TestFunction.lineDerivOp_apply_eq_fderiv, neg_inj] using h1.symm

end TauCeti
