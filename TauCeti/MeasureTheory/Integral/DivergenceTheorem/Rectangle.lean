/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
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

* `TauCeti.setIntegral_divergence_withLp_prod_Ioo`: for fields `Φ₁`, `Φ₂` on the Euclidean plane,
  continuous on the closed rectangle and differentiable on the open rectangle
  `R = (a₁, b₁) × (a₂, b₂)` with integrable divergence, the integral over `R` of the divergence
  `∂₁Φ₁ + ∂₂Φ₂` is the sum of the four boundary integrals of the flux.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The divergence theorem on a rectangle of the Euclidean plane.** Let `a ≤ b` in `ℝ × ℝ`, let
`e₁ = (1, 0)` and `e₂ = (0, 1)`, and let `Φ₁`, `Φ₂` be continuous on the closed rectangle
`[a₁, b₁] × [a₂, b₂]`, with derivatives `Φ₁'`, `Φ₂'` on the open rectangle
`R = (a₁, b₁) × (a₂, b₂)` such that the divergence `Φ₁' x e₁ + Φ₂' x e₂` is integrable on `R`.
Then

`∫_R (∂₁Φ₁ + ∂₂Φ₂) = ∫_{a₁}^{b₁} (Φ₂(t, b₂) - Φ₂(t, a₂)) dt`
  `+ ∫_{a₂}^{b₂} (Φ₁(b₁, s) - Φ₁(a₁, s)) ds`.

This is `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le` on `ℝ × ℝ`, transported
along the measure-preserving map `WithLp.toLp 2`. -/
theorem setIntegral_divergence_withLp_prod_Ioo {Φ₁ Φ₂ : WithLp 2 (ℝ × ℝ) → E}
    {Φ₁' Φ₂' : WithLp 2 (ℝ × ℝ) → WithLp 2 (ℝ × ℝ) →L[ℝ] E} {a b : ℝ × ℝ} (hab : a ≤ b)
    (hc₁ : ContinuousOn Φ₁ {x | x.fst ∈ Icc a.1 b.1 ∧ x.snd ∈ Icc a.2 b.2})
    (hc₂ : ContinuousOn Φ₂ {x | x.fst ∈ Icc a.1 b.1 ∧ x.snd ∈ Icc a.2 b.2})
    (hd₁ : ∀ x ∈ {x : WithLp 2 (ℝ × ℝ) | x.fst ∈ Ioo a.1 b.1 ∧ x.snd ∈ Ioo a.2 b.2},
      HasFDerivAt Φ₁ (Φ₁' x) x)
    (hd₂ : ∀ x ∈ {x : WithLp 2 (ℝ × ℝ) | x.fst ∈ Ioo a.1 b.1 ∧ x.snd ∈ Ioo a.2 b.2},
      HasFDerivAt Φ₂ (Φ₂' x) x)
    (hi : IntegrableOn (fun x => Φ₁' x (WithLp.toLp 2 (1, 0)) + Φ₂' x (WithLp.toLp 2 (0, 1)))
      {x : WithLp 2 (ℝ × ℝ) | x.fst ∈ Ioo a.1 b.1 ∧ x.snd ∈ Ioo a.2 b.2}) :
    ∫ x in {x : WithLp 2 (ℝ × ℝ) | x.fst ∈ Ioo a.1 b.1 ∧ x.snd ∈ Ioo a.2 b.2},
        (Φ₁' x (WithLp.toLp 2 (1, 0)) + Φ₂' x (WithLp.toLp 2 (0, 1))) =
      (((∫ t in a.1..b.1, Φ₂ (WithLp.toLp 2 (t, b.2))) -
          ∫ t in a.1..b.1, Φ₂ (WithLp.toLp 2 (t, a.2))) +
        ∫ s in a.2..b.2, Φ₁ (WithLp.toLp 2 (b.1, s))) -
          ∫ s in a.2..b.2, Φ₁ (WithLp.toLp 2 (a.1, s)) := by
  set L : ℝ × ℝ →L[ℝ] WithLp 2 (ℝ × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap
  have hL (y : ℝ × ℝ) : L y = WithLp.toLp 2 y := by
    simp [L, WithLp.prodContinuousLinearEquiv_symm_apply]
  have hT := WithLp.volume_preserving_toLp ℝ ℝ
  have hE := (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding
  -- The open rectangle of the Euclidean plane pulls back to the open rectangle of `ℝ × ℝ`, which
  -- is almost everywhere equal to the closed rectangle `[a, b]`.
  have hpre : WithLp.toLp 2 ⁻¹' {x : WithLp 2 (ℝ × ℝ) | x.fst ∈ Ioo a.1 b.1 ∧ x.snd ∈ Ioo a.2 b.2} =
      Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 := by
    ext y
    simp [Set.mem_prod]
  have hae : Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 =ᵐ[volume] Icc a b := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have hc (Φ : WithLp 2 (ℝ × ℝ) → E)
      (hΦ : ContinuousOn Φ {x | x.fst ∈ Icc a.1 b.1 ∧ x.snd ∈ Icc a.2 b.2}) :
      ContinuousOn (fun y => Φ (L y)) (Icc a b) := by
    refine hΦ.comp L.continuous.continuousOn fun y hy => ?_
    simp only [mem_Icc, Prod.le_def] at hy
    simp [hL, hy]
  have hd {Φ : WithLp 2 (ℝ × ℝ) → E} {Φ' : WithLp 2 (ℝ × ℝ) → WithLp 2 (ℝ × ℝ) →L[ℝ] E}
      (hΦ : ∀ x ∈ {x : WithLp 2 (ℝ × ℝ) | x.fst ∈ Ioo a.1 b.1 ∧ x.snd ∈ Ioo a.2 b.2},
        HasFDerivAt Φ (Φ' x) x) (y : ℝ × ℝ) (hy : y ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2) :
      HasFDerivAt (fun y => Φ (L y)) ((Φ' (L y)).comp L) y := by
    refine (hΦ (L y) ?_).comp y L.hasFDerivAt
    rw [← hpre] at hy
    simpa [hL] using hy
  have hi' : IntegrableOn (fun y : ℝ × ℝ => (Φ₁' (L y)).comp L (1, 0) +
      (Φ₂' (L y)).comp L (0, 1)) (Icc a b) := by
    have h := (hT.integrableOn_comp_preimage hE).2 hi
    rw [hpre, integrableOn_congr_set_ae hae] at h
    simpa [Function.comp_def, hL] using h
  have key := integral_divergence_prod_Icc_of_hasFDerivAt_of_le (fun y => Φ₁ (L y))
    (fun y => Φ₂ (L y)) (fun y => (Φ₁' (L y)).comp L) (fun y => (Φ₂' (L y)).comp L) a b hab
    (hc Φ₁ hc₁) (hc Φ₂ hc₂) (hd hd₁) (hd hd₂) hi'
  simp only [hL, ContinuousLinearMap.comp_apply] at key
  rw [← key, ← hT.setIntegral_preimage_emb hE, hpre, Measure.restrict_congr_set hae]

end TauCeti
