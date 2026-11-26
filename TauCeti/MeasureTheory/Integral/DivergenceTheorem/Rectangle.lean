/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# The divergence theorem on a rectangle of the Euclidean plane

Mathlib's divergence theorem on a rectangle,
`MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le` and its variants, is stated on
`ℝ × ℝ`, whose norm is the sup norm. Functions on the Euclidean plane, the inner product space
`WithLp 2 (ℝ × ℝ)`, have gradients and Sobolev derivatives, and are the setting of the Laplacian
on planar domains. This file transports the rectangle theorem to them along the
measure-preserving map `WithLp.toLp 2 : ℝ × ℝ → WithLp 2 (ℝ × ℝ)`.

## Main declarations

* `TauCeti.setIntegral_divergence_withLp_prod_Ioo`: for `C¹` fields `Φ₁`, `Φ₂` on the Euclidean
  plane and a rectangle `R = (a₁, b₁) × (a₂, b₂)`, the integral over `R` of the divergence
  `∂₁Φ₁ + ∂₂Φ₂` is the sum of the four boundary integrals of the flux.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The divergence theorem on a rectangle of the Euclidean plane.** Let `Φ₁` and `Φ₂` be
continuously differentiable on `WithLp 2 (ℝ × ℝ)`, let `a ≤ b` in `ℝ × ℝ`, and let `e₁ = (1, 0)`
and `e₂ = (0, 1)`. Then over the open rectangle `R = (a₁, b₁) × (a₂, b₂)`,

`∫_R (∂₁Φ₁ + ∂₂Φ₂) = ∫_{a₁}^{b₁} (Φ₂(t, b₂) - Φ₂(t, a₂)) dt`
  `+ ∫_{a₂}^{b₂} (Φ₁(b₁, s) - Φ₁(a₁, s)) ds`.

This is `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le` on `ℝ × ℝ`, transported
along the measure-preserving map `WithLp.toLp 2`. -/
theorem setIntegral_divergence_withLp_prod_Ioo {Φ₁ Φ₂ : WithLp 2 (ℝ × ℝ) → E}
    (h₁ : ContDiff ℝ 1 Φ₁) (h₂ : ContDiff ℝ 1 Φ₂) {a b : ℝ × ℝ} (hab : a ≤ b) :
    ∫ x in {x : WithLp 2 (ℝ × ℝ) | x.fst ∈ Ioo a.1 b.1 ∧ x.snd ∈ Ioo a.2 b.2},
        (fderiv ℝ Φ₁ x (WithLp.toLp 2 (1, 0)) + fderiv ℝ Φ₂ x (WithLp.toLp 2 (0, 1))) =
      (((∫ t in a.1..b.1, Φ₂ (WithLp.toLp 2 (t, b.2))) -
          ∫ t in a.1..b.1, Φ₂ (WithLp.toLp 2 (t, a.2))) +
        ∫ s in a.2..b.2, Φ₁ (WithLp.toLp 2 (b.1, s))) -
          ∫ s in a.2..b.2, Φ₁ (WithLp.toLp 2 (a.1, s)) := by
  set L : ℝ × ℝ →L[ℝ] WithLp 2 (ℝ × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap
  have hL (y : ℝ × ℝ) : L y = WithLp.toLp 2 y := by
    simp [L, WithLp.prodContinuousLinearEquiv_symm_apply]
  have hd (Φ : WithLp 2 (ℝ × ℝ) → E) (hΦ : ContDiff ℝ 1 Φ) (y : ℝ × ℝ) :
      HasFDerivAt (fun y => Φ (L y)) ((fderiv ℝ Φ (L y)).comp L) y :=
    ((hΦ.differentiable one_ne_zero) (L y)).hasFDerivAt.comp y L.hasFDerivAt
  have hc (Φ : WithLp 2 (ℝ × ℝ) → E) (hΦ : ContDiff ℝ 1 Φ) :
      Continuous fun y => Φ (L y) := hΦ.continuous.comp L.continuous
  have hi : IntegrableOn (fun y : ℝ × ℝ => (fderiv ℝ Φ₁ (L y)).comp L (1, 0) +
      (fderiv ℝ Φ₂ (L y)).comp L (0, 1)) (Icc a b) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
    have c₁ := (h₁.continuous_fderiv one_ne_zero).comp L.continuous
    have c₂ := (h₂.continuous_fderiv one_ne_zero).comp L.continuous
    exact (c₁.clm_apply continuous_const).add (c₂.clm_apply continuous_const)
  have key := integral_divergence_prod_Icc_of_hasFDerivAt_of_le (fun y => Φ₁ (L y))
    (fun y => Φ₂ (L y)) (fun y => (fderiv ℝ Φ₁ (L y)).comp L)
    (fun y => (fderiv ℝ Φ₂ (L y)).comp L) a b hab
    (hc Φ₁ h₁).continuousOn (hc Φ₂ h₂).continuousOn (fun y _ => hd Φ₁ h₁ y)
    (fun y _ => hd Φ₂ h₂ y) hi
  simp only [hL, ContinuousLinearMap.comp_apply] at key
  rw [← key]
  -- Transport the integral over the open rectangle to the closed rectangle `[a, b]` of `ℝ × ℝ`.
  have hpre : WithLp.toLp 2 ⁻¹' {x : WithLp 2 (ℝ × ℝ) | x.fst ∈ Ioo a.1 b.1 ∧ x.snd ∈ Ioo a.2 b.2} =
      Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 := by
    ext y
    simp [Set.mem_prod]
  rw [← (WithLp.volume_preserving_toLp ℝ ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding, hpre]
  rw [Icc_prod_eq, Measure.volume_eq_prod,
    Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)]

end TauCeti
