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

For vector-valued test functions paired through an inner product, the same computation shows that
the first weak derivatives of a single function already satisfy the symmetry of mixed partials in
the sense of distributions: `∫ ⟪∂_w φ, ∂_v u⟫ = ∫ ⟪∂_v φ, ∂_w u⟫`, with no second weak derivative
assumed.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.comm`: weak derivatives in two directions commute.
* `TauCeti.HasWeakLineDerivOn.integral_inner_lineDeriv_comm`,
  `TauCeti.HasWeakFDerivOn.integral_inner_fderiv_comm`: the distributional symmetry of
  mixed partials, tested against vector-valued test functions.
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

section Inner

open scoped InnerProductSpace

variable [OpensMeasurableSpace E] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {f f₁ f₂ : E → V}

/-- **Mixed partials of a weakly differentiable function are symmetric as distributions.** If `f`
has weak derivatives `f₁ = ∂_v f` and `f₂ = ∂_w f` on `Ω`, then
`∫ ⟪∂_w φ, f₁⟫ = ∫ ⟪∂_v φ, f₂⟫` for every `φ ∈ 𝓓(Ω, V)`: both sides are `-∫ ⟪∂_v ∂_w φ, f⟫`.
No second weak derivative of `f` is assumed. -/
theorem HasWeakLineDerivOn.integral_inner_lineDeriv_comm (h₁ : HasWeakLineDerivOn μ Ω f f₁ v)
    (h₂ : HasWeakLineDerivOn μ Ω f f₂ w) (φ : 𝓓(Ω, V)) :
    ∫ x, ⟪lineDeriv ℝ (φ : E → V) x w, f₁ x⟫_ℝ ∂μ =
      ∫ x, ⟪lineDeriv ℝ (φ : E → V) x v, f₂ x⟫_ℝ ∂μ := by
  have e₁ := h₁.integral_inner_lineDeriv_eq_neg (∂_{w} φ)
  have e₂ := h₂.integral_inner_lineDeriv_eq_neg (∂_{v} φ)
  simp only [TestFunction.lineDeriv_lineDerivOp_comm φ w v] at e₁
  simpa only [TestFunction.lineDerivOp_apply, neg_inj] using e₁.symm.trans e₂

/-- **Symmetry of second derivatives against a weak Fréchet derivative.** If `f` has weak Fréchet
derivative `D` on `Ω`, then for any directions `v, w : E` and test function `Ψ ∈ 𝓓(Ω, V)`,
`∫ ⟪DΨ(x) v, D(x) w⟫ = ∫ ⟪DΨ(x) w, D(x) v⟫`. Both sides equal `-∫ ⟪∂_v ∂_w Ψ(x), f x⟫` by
commutativity of test-function directional derivatives. -/
theorem HasWeakFDerivOn.integral_inner_fderiv_comm
    {f : E → V} {D : E → E →L[ℝ] V} (hD : HasWeakFDerivOn μ Ω f D) (v w : E) (Ψ : 𝓓(Ω, V)) :
    ∫ x, ⟪fderiv ℝ (Ψ : E → V) x v, D x w⟫_ℝ ∂μ =
      ∫ x, ⟪fderiv ℝ (Ψ : E → V) x w, D x v⟫_ℝ ∂μ := by
  simpa only [TestFunction.lineDeriv_eq_fderiv] using
    (hD.hasWeakLineDerivOn w).integral_inner_lineDeriv_comm (hD.hasWeakLineDerivOn v) Ψ

end Inner

end TauCeti
