/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform
public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Analysis.Contour.ConnectorLimit
import TauCeti.Analysis.Contour.Residue.VerticalLineShift
import TauCeti.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Shifting the line of Mellin inversion (DLMF 2.5.6)

Let `G` be continuous on the closed strip `d ≤ Re z ≤ c` except at finitely many poles in the open
strip, complex differentiable on the open strip off the poles, integrable on both boundary lines,
and with `G(σ + iT) → 0` as `|T| → ∞` uniformly for `σ ∈ [d, c]`. Then, for `x > 0`,

`(2πi)⁻¹ ∫_{(c)} x^{-z} G(z) dz = ∑ Res(x^{-z} G(z)) + (2πi)⁻¹ ∫_{(d)} x^{-z} G(z) dz`,

in Mathlib's notation `mellinInv c G x = ∑_p Res(x^{-·} G, p) + mellinInv d G x`. By the
Riemann–Lebesgue estimate `TauCeti.mellinInv_isLittleO_nhdsGT_zero` of
`TauCeti.Analysis.MellinInversion` (DLMF 2.5.7), the remaining integral is `o(x^{-d})` as `x → 0+`.

## Main results

* `TauCeti.mellinInv_eq_sum_residue_add`: the shift of the line of Mellin inversion.

The statement follows the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/AsymptoticApproximations/Mellin/Transforms.lean`. The line shift is proved here through Tau
Ceti's rectangle residue theorem instead of lean-DLMF's own contour machinery.
-/

public section

open Complex Set Filter MeasureTheory
open scoped Topology Real Interval

namespace TauCeti

/-- **DLMF 2.5.6: shifting the line of Mellin inversion.** Let `G` be continuous on the closed
strip `d ≤ Re z ≤ c` except at a finite set `P` of points of the open strip, complex differentiable
on the open strip `d < Re z < c` off `P`, meromorphic at each point of `P`, integrable on both
lines, and with `G(σ + iT) → 0` as `|T| → ∞` uniformly for `σ ∈ [d, c]`. Then for `x > 0`,
`mellinInv c G x = ∑_{p ∈ P} Res(x^{-·} G, p) + mellinInv d G x`. -/
theorem mellinInv_eq_sum_residue_add {G : ℂ → ℂ} {c d x : ℝ} (hdc : d ≤ c) (hx : 0 < x)
    (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hGc : ContinuousOn G ({z : ℂ | d ≤ z.re ∧ z.re ≤ c} \ (P : Set ℂ)))
    (hGd : DifferentiableOn ℂ G ({z : ℂ | d < z.re ∧ z.re < c} \ (P : Set ℂ)))
    (hm : ∀ p ∈ P, MeromorphicAt G p)
    (hc : Integrable fun y : ℝ => G (c + y * I)) (hd : Integrable fun y : ℝ => G (d + y * I))
    (hdecay : Tendsto (fun q : ℝ × ℝ => G (q.2 + q.1 * I)) (cocompact ℝ ×ˢ 𝓟 (Icc d c))
      (𝓝 0)) :
    mellinInv c G x =
      ∑ p ∈ P, Contour.residue (fun z => (x : ℂ) ^ (-z) * G z) p + mellinInv d G x := by
  set F : ℂ → ℂ := fun z => (x : ℂ) ^ (-z) * G z with hFdef
  have hpow (z : ℂ) : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ (-z)) z :=
    analyticAt_const.cpow analyticAt_id.neg (ofReal_mem_slitPlane.mpr hx)
  have hnorm (σ y : ℝ) : ‖(x : ℂ) ^ (-((σ : ℂ) + y * I))‖ = x ^ (-σ) := by
    rw [norm_cpow_eq_rpow_re_of_pos hx]; simp
  have hFc : ContinuousOn F ({z : ℂ | d ≤ z.re ∧ z.re ≤ c} \ (P : Set ℂ)) := fun z hz =>
    (hpow z).continuousAt.continuousWithinAt.mul (hGc z hz)
  have hFd : DifferentiableOn ℂ F ({z : ℂ | d < z.re ∧ z.re < c} \ (P : Set ℂ)) := fun z hz =>
    (hpow z).differentiableAt.differentiableWithinAt.mul (hGd z hz)
  have hmF : ∀ p ∈ P, MeromorphicAt F p := fun p hp => (hpow p).meromorphicAt.mul (hm p hp)
  have hline {σ : ℝ} (hσ : Integrable fun y : ℝ => G (σ + y * I)) :
      Integrable fun y : ℝ => F (σ + y * I) := by
    simpa [F, smul_eq_mul] using Complex.VerticalIntegrable.integrable_cpow_smul hσ hx
  -- `x^{-σ}` is bounded on `[d, c]`, so `x^{-z} G(z)` decays uniformly on the strip.
  have hX (σ : ℝ) (hσ : σ ∈ Icc d c) : x ^ (-σ) ≤ max (x ^ (-d)) (x ^ (-c)) := by
    rcases le_total 1 x with h1 | h1
    · exact (Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hσ.1])).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hx h1 (by linarith [hσ.2])).trans
        (le_max_right _ _)
  have hdecayF : Tendsto (fun q : ℝ × ℝ => F (q.2 + q.1 * I)) (cocompact ℝ ×ˢ 𝓟 (Icc d c))
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using (hdecay.norm.const_mul (max (x ^ (-d))
      (x ^ (-c)))))
    refine mem_prod_principal.mpr (univ_mem' fun T σ hσ => ?_)
    simp only [hFdef, norm_mul, hnorm]
    exact mul_le_mul_of_nonneg_right (hX σ hσ) (norm_nonneg _)
  have hhor := Contour.tendsto_intervalIntegral_horizontal (by rwa [uIcc_of_le hdc])
  have hshift := Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue F hdc P hP hFc hFd
    hmF (hline hc) (hline hd) (hhor.mono_left atTop_le_cocompact)
    (hhor.mono_left atBot_le_cocompact)
  simp only [hFdef] at hshift
  have e : ((1 / (2 * π) : ℝ) : ℂ) * (2 * π) = 1 := by
    push_cast
    field_simp
  simp only [mellinInv, Complex.real_smul, smul_eq_mul]
  linear_combination ((1 / (2 * π) : ℝ) : ℂ) * hshift +
    (∑ p ∈ P, Contour.residue (fun z => (x : ℂ) ^ (-z) * G z) p) * e

end TauCeti
