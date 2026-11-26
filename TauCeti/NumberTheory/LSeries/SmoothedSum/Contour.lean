/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Rectangle
public import TauCeti.NumberTheory.LSeries.SmoothedSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.NumberTheory.LSeries.Continuity

/-!
# Smoothed coefficient sums across a simple pole

Let `χ_ε = smoothCutoff ν ε` be the smoothed cutoff of a `C¹` bump `ν`, and let the L-series of `a`
be summable at `σ₀ > 1` and agree on the line `Re s = σ₀` with `G(s) + r/(s - 1)`, where `G` is
continuous on the rectangle `[σ₁, σ₀] ×ℂ [-T, T]` (`0 < σ₁ < 1`, `T > 0`) and complex
differentiable on its interior. For `x > 0` the smoothed sum `∑ₙ a(n) χ_ε(n / x)` is the integral
of `f(s) = (G(s) + r/(s - 1)) · mellin χ_ε s · xˢ` over the line `Re s = σ₀`, divided by `2π`.
Moving this line onto the left and horizontal edges of the rectangle passes the simple pole at
`1`, whose residue is `r · mellin χ_ε 1 · x`:

`∑ₙ a(n) χ_ε(n / x) = r · 𝓜χ_ε(1) · x + (2π)⁻¹ (∫_{|t| > T} f(σ₀ + it) dt + ∫_{-T}^{T} f(σ₁ + it) dt
  + (∫_{σ₁}^{σ₀} f(σ + iT) dσ - ∫_{σ₁}^{σ₀} f(σ - iT) dσ) / i)`.

When `G` is the holomorphic part of `L(a, s)` on a zero-free region and `σ₁` lies inside that
region, estimating the three remaining terms bounds the difference between the smoothed sum and
its main term `r · 𝓜χ_ε(1) · x`.

## Main results

* `TauCeti.LSeries.integrable_LSeries_mul_mellin_smoothCutoff`: on a vertical line `Re s = σ > 0`
  the product `L(a, s) · mellin χ_ε s` is integrable.
* `TauCeti.LSeries.tsum_mul_smoothCutoff_eq_residue_add_contour`: the smoothed sum as the residue
  at `1` plus the vertical tails, the left edge and the horizontal edges.

## References

* A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd* blueprint, §4.6 (the contour shift of
  the smoothed Chebyshev function, with `G = -ζ'/ζ - 1/(s - 1)` and `r = 1`),
  <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>; the Lean development in
  `PrimeNumberTheoremAnd/MediumPNT.lean` at revision `df0ccba` of
  <https://github.com/TauCetiProject/PrimeNumberTheoremAnd>.
-/

public section

open Set Complex MeasureTheory Filter
open scoped Real Interval

namespace TauCeti.LSeries

variable {ν : ℝ → ℝ} {ε : ℝ}

/-- For `ν` of class `C¹` on `(0, ∞)` and vanishing there off `[1/2, 2]`, `ε > 0` and `σ > 0`, the
function `t ↦ L(a, σ + it) · mellin χ_ε (σ + it)` is integrable on `ℝ`. Where the L-series is not
summable on the line it is `0` there. -/
theorem integrable_LSeries_mul_mellin_smoothCutoff (a : ℕ → ℂ) (hν : ContDiffOn ℝ 1 ν (Ioi 0))
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) (hε : 0 < ε) {σ : ℝ} (hσ : 0 < σ) :
    Integrable fun t : ℝ ↦
      LSeries a (σ + t * I) * mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) (σ + t * I) := by
  refine (verticalIntegrable_mellin_smoothCutoff hν hνs hε hσ).bdd_mul
    (continuous_vertical a σ).aestronglyMeasurable (c := ∑' n, ‖LSeries.term a σ n‖)
    (Eventually.of_forall fun t ↦ ?_)
  by_cases hs : LSeriesSummable a σ
  · exact tsum_of_norm_bounded hs.norm.hasSum
      fun n ↦ LSeries.norm_term_le_of_re_le_re a (by simp) n
  · rw [LSeries.eq_zero_of_not_LSeriesSummable _ _
      fun h ↦ hs ((LSeriesSummable_iff_of_re_eq_re (by simp)).mp h), norm_zero]
    exact tsum_nonneg fun _ ↦ norm_nonneg _

/-- The integrand `(G(s) + r/(s - 1)) · mellin χ_ε s · xˢ` is continuous on the closed rectangle
off `1` and complex differentiable on the open rectangle off `1`. -/
private lemma contour_hypotheses {G : ℂ → ℂ} {r : ℂ} {x σ₀ σ₁ T : ℝ}
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2)
    (hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0)) (hε : 0 < ε) (hσ₁ : 0 < σ₁)
    (hGc : ContinuousOn G (Icc σ₁ σ₀ ×ℂ Icc (-T) T))
    (hGd : DifferentiableOn ℂ G (Ioo σ₁ σ₀ ×ℂ Ioo (-T) T)) :
    let f : ℂ → ℂ := fun s ↦
      (G s + r / (s - 1)) * mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) s * (x : ℂ) ^ s
    ContinuousOn f (Icc σ₁ σ₀ ×ℂ Icc (-T) T \ {1}) ∧
      DifferentiableOn ℂ f (Ioo σ₁ σ₀ ×ℂ Ioo (-T) T \ {1}) := by
  intro f
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hM (s : ℂ) (hs : σ₁ ≤ s.re) :
      AnalyticAt ℂ (mellin fun y ↦ (smoothCutoff ν ε y : ℂ)) s :=
    (differentiableOn_mellin_smoothCutoff hνs hνi hε).analyticAt
      (hopen.mem_nhds (hσ₁.trans_le hs))
  have hpow (s : ℂ) (hs : σ₁ ≤ s.re) : DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow
      (Or.inr fun h ↦ by rw [id_eq] at h; rw [h, zero_re] at hs; linarith)
  have hpole (s : ℂ) (hs : s ≠ 1) : AnalyticAt ℂ (fun s : ℂ ↦ r / (s - 1)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)
  refine ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · exact ((((hGc s hs.1).add (hpole s hs.2).continuousAt.continuousWithinAt).mul
      (hM s hs.1.1.1).continuousAt.continuousWithinAt).mul
      (hpow s hs.1.1.1).continuousAt.continuousWithinAt).mono sdiff_subset
  · have hU : IsOpen (Ioo σ₁ σ₀ ×ℂ Ioo (-T) T) := isOpen_Ioo.reProdIm isOpen_Ioo
    exact ((((hGd.differentiableAt (hU.mem_nhds hs.1)).add
      (hpole s hs.2).differentiableAt).mul (hM s hs.1.1.1.le).differentiableAt).mul
      (hpow s hs.1.1.1.le)).differentiableWithinAt

/-- The integrand `(G(s) + r/(s - 1)) · mellin χ_ε s · xˢ` is meromorphic at `1`, with residue
`r · mellin χ_ε 1 · x`, when `G` is complex differentiable on an open rectangle containing `1`. -/
private lemma residue_one {G : ℂ → ℂ} {r : ℂ} {x σ₀ σ₁ T : ℝ}
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2)
    (hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0)) (hε : 0 < ε)
    (hGd : DifferentiableOn ℂ G (Ioo σ₁ σ₀ ×ℂ Ioo (-T) T)) (h1 : 1 ∈ Ioo σ₁ σ₀ ×ℂ Ioo (-T) T) :
    MeromorphicAt (fun s ↦ (G s + r / (s - 1)) *
      mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) s * (x : ℂ) ^ s) 1 ∧
    Contour.residue (fun s ↦ (G s + r / (s - 1)) *
      mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) s * (x : ℂ) ^ s) 1 =
      r * mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) 1 * x := by
  have hG := hGd.analyticAt ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds h1)
  have hH := (isOpen_lt continuous_const continuous_re).mem_nhds (by simp : (0 : ℝ) < (1 : ℂ).re)
  have hM := (differentiableOn_mellin_smoothCutoff hνs hνi hε).analyticAt hH
  have hpd : DifferentiableOn ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) {s : ℂ | 0 < s.re} := fun s hs ↦
    (differentiableAt_id.const_cpow (Or.inr fun h ↦ by simp_all)).differentiableWithinAt
  have hpow := hpd.analyticAt hH
  have hp : MeromorphicAt (fun s : ℂ ↦ r / (s - 1)) 1 := by fun_prop
  refine ⟨((hG.meromorphicAt.add hp).mul hM.meromorphicAt).mul hpow.meromorphicAt, ?_⟩
  have h := Contour.residue_add_div_sub_mul_of_analyticAt (r := r) hG (hM.mul hpow)
  simpa only [Pi.mul_apply, mul_assoc, cpow_one] using h

/-- **A smoothed coefficient sum across a simple pole.** Let `ν` be of class `C¹` on `(0, ∞)` and
vanish there off `[1/2, 2]`, `ε > 0`, `x ≥ 0`, `0 < σ₁ < 1 < σ₀` and `T > 0`. Let `G` be continuous
on `[σ₁, σ₀] ×ℂ [-T, T]` and complex differentiable on its interior, and let the L-series of `a` be
summable at `σ₀` with `L(a, s) = G(s) + r/(s - 1)` on the line `Re s = σ₀`. With
`f(s) = (G(s) + r/(s - 1)) · mellin χ_ε s · xˢ`, the smoothed sum `∑ₙ a(n) χ_ε(n / x)` equals the
residue `r · mellin χ_ε 1 · x` of `f` at `1` plus `(2π)⁻¹` times the sum of the tails
`∫_{|t| > T} f(σ₀ + it) dt`, the left edge `∫_{-T}^{T} f(σ₁ + it) dt` and the horizontal term
`(∫_{σ₁}^{σ₀} f(σ + iT) dσ - ∫_{σ₁}^{σ₀} f(σ - iT) dσ) / i`. -/
theorem tsum_mul_smoothCutoff_eq_residue_add_contour {a : ℕ → ℂ} {G f : ℂ → ℂ} {r : ℂ}
    {x σ₀ σ₁ T : ℝ} (hν : ContDiffOn ℝ 1 ν (Ioi 0))
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) (hε : 0 < ε) (hx : 0 ≤ x)
    (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ < 1) (hσ₀ : 1 < σ₀) (hT : 0 < T)
    (hs : LSeriesSummable a σ₀) (hGc : ContinuousOn G (Icc σ₁ σ₀ ×ℂ Icc (-T) T))
    (hGd : DifferentiableOn ℂ G (Ioo σ₁ σ₀ ×ℂ Ioo (-T) T))
    (hL : ∀ t : ℝ, LSeries a (σ₀ + t * I) = G (σ₀ + t * I) + r / (σ₀ + t * I - 1))
    (hf : ∀ s, f s =
      (G s + r / (s - 1)) * mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) s * (x : ℂ) ^ s) :
    ∑' n, a n * smoothCutoff ν ε (n / x) =
      r * mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) 1 * x +
        (1 / (2 * π)) * ((∫ t in {t : ℝ | T < |t|}, f (σ₀ + t * I)) +
          (∫ t in (-T)..T, f (σ₁ + t * I)) +
          ((∫ σ in σ₁..σ₀, f (σ + T * I)) - ∫ σ in σ₁..σ₀, f (σ - T * I)) / I) := by
  rcases hx.eq_or_lt with rfl | hx
  · -- for `x = 0` both sides vanish, since `0 ^ s = 0` for `s ≠ 0`
    have hR (σ t : ℝ) (h : σ ≠ 0 ∨ t ≠ 0) : f (σ + t * I) = 0 := by
      rw [hf, ofReal_zero, zero_cpow fun h' ↦ by simp [Complex.ext_iff] at h'; tauto, mul_zero]
    have hR' (σ : ℝ) : f (σ - T * I) = 0 := by
      rw [sub_eq_add_neg, ← neg_mul, ← ofReal_neg]
      exact hR _ _ (Or.inr (neg_ne_zero.mpr hT.ne'))
    simp [smoothCutoff_of_nonpos, fun t ↦ hR σ₀ t (Or.inl (by linarith)),
      fun t ↦ hR σ₁ t (Or.inl hσ₁.ne'), fun σ ↦ hR σ T (Or.inr hT.ne'), hR']
  have hνi := integrableOn_div_of_continuousOn_of_support_subset
    (hν.continuousOn.mono Icc_one_half_two_subset_Ioi) hνs
  obtain rfl : f = _ := funext hf
  have h1 : (1 : ℂ) ∈ Ioo σ₁ σ₀ ×ℂ Ioo (-T) T := by
    rw [mem_reProdIm]
    simp [hσ₁1, hσ₀, hT]
  obtain ⟨hc, hd⟩ := contour_hypotheses (r := r) (x := x) hνs hνi hε hσ₁ hGc hGd
  -- on the line `Re s = σ₀` the integrand is `L(a, s) · mellin χ_ε s · xˢ`
  have hline (t : ℝ) : (LSeries a (σ₀ + t * I) *
      mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) (σ₀ + t * I)) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) =
      (G (σ₀ + t * I) + r / (σ₀ + t * I - 1)) *
        mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) (σ₀ + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) := by
    rw [hL]
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hint := ((integrable_LSeries_mul_mellin_smoothCutoff a hν hνs hε (by linarith)).mul_bdd
    (Continuous.aestronglyMeasurable (by fun_prop)) (c := x ^ σ₀)
    (Eventually.of_forall fun t ↦ by simp [norm_cpow_eq_rpow_re_of_pos hx])).congr
    (Eventually.of_forall hline)
  obtain ⟨hmer, hres⟩ := residue_one (r := r) (x := x) hνs hνi hε hGd h1
  have hshift := Contour.integral_vertical_eq_uShaped_symm_add_two_pi_mul_sum_residue
    (P := {1}) (hσ₁1.trans hσ₀).le hT.le (by simpa using h1)
    (by rw [Finset.coe_singleton]; exact hc) (by rw [Finset.coe_singleton]; exact hd)
    (by simpa using hmer) hint
  rw [Finset.sum_singleton, hres] at hshift
  -- the smoothed sum is `(2π)⁻¹` times the integral over the line `Re s = σ₀`
  have hcpow (t : ℝ) : ((x⁻¹ : ℝ) : ℂ) ^ (-((σ₀ : ℂ) + t * I)) = (x : ℂ) ^ ((σ₀ : ℂ) + t * I) := by
    rw [ofReal_inv, inv_cpow _ _ (by simp [arg_ofReal_of_nonneg hx.le, Real.pi_ne_zero.symm]),
      cpow_neg, inv_inv]
  rw [(hasSum_mul_smoothCutoff hν hνs hε (by linarith) hs hx).tsum_eq, mellinInv, real_smul]
  simp only [smul_eq_mul, hcpow]
  rw [integral_congr_ae (Eventually.of_forall fun t ↦ (mul_comm _ _).trans (hline t)),
    hshift, mul_add, add_comm]
  push_cast
  congr 1
  field_simp

end TauCeti.LSeries
