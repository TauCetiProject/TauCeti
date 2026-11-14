/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Curve.Rectangle
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.MellinInversion
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Winding.Number.Rectangle

/-!
# The residue theorem on a rectangle and vertical contour shifts

For a closed rectangle `R = Complex.Rectangle z w` with lower left corner `z` and a function `f`
complex differentiable on `R \ S` and meromorphic at the points of `S` in `R`, where the finite set
`S` avoids the frontier of `R`, the contour integral of `f` along the counterclockwise boundary
`Complex.rectBoundary z w` equals `2πi` times the sum of the residues of `f` at the points of `S`
inside `R`.

Splitting the boundary integral into the four horizontal and vertical edge integrals via
`Complex.integral_rectBoundary` and letting the top and bottom heights `±T` tend to `∞` yields the
vertical-line contour shift formula on a closed strip `Icc a b ×ℂ univ`: when the horizontal
integrals at height `±T` vanish as `T → ∞` and `f` is integrable on the vertical lines `Re s = a`
and `Re s = b`, the difference `(∫ y, f (b + y * I)) - (∫ y, f (a + y * I))` equals `2π` times the
sum of the residues at the poles in the open strip `a < Re s < b`. Specializing `f` to
`(x : ℂ) ^ (-s) * F s` gives the shifted Mellin inversion identity
`mellinInv b F x - mellinInv a F x = ∑ Res_s (x⁻ˢ F)`.

## Main results

* `TauCeti.Contour.classicalResidueTheorem_rectBoundary`: the residue theorem on a rectangle.
* `TauCeti.Contour.integral_edges_rectangle_eq_two_pi_I_mul_sum_residue`: the four-edge form of the
  rectangle residue theorem.
* `TauCeti.Contour.verticalIntegral_sub_verticalIntegral_eq_two_pi_mul_sum_residue`: shifting a
  vertical line integral across finitely many poles in an open strip.
* `TauCeti.Contour.mellinInv_sub_mellinInv_eq_sum_residue`: shifting `mellinInv` between two
  abscissae under uniform decay on horizontal segments.

## References

* E. C. Titchmarsh, *The Theory of Functions*, §3.1 and §9.5.
* H. Davenport, *Multiplicative Number Theory*, the chapter on Siegel's theorem.
-/

public section

open Set Complex MeasureTheory Filter
open scoped Real Topology Interval

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {S : Finset ℂ} {z w : ℂ}

open scoped Classical in
/-- **The residue theorem on a rectangle.** Let `z` be the lower left corner of a closed rectangle
`Rectangle z w`, and let `f` be differentiable on `Rectangle z w \ S` and meromorphic at each point
of `S` in `Rectangle z w`, where the finite set `S` avoids the frontier of the rectangle. Then the
contour integral of `f` along the counterclockwise boundary is `2πi` times the sum of `residue f s`
over the points `s ∈ S` lying in the rectangle. -/
theorem classicalResidueTheorem_rectBoundary (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : DifferentiableOn ℂ f (Rectangle z w \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, s ∈ Rectangle z w → MeromorphicAt f s)
    (hS : ∀ s ∈ S, s ∉ frontier (Rectangle z w)) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • f (rectBoundary z w t) =
      2 * π * I * ∑ s ∈ S with s ∈ Rectangle z w, residue f s := by
  set T : Finset ℂ := S.filter (· ∈ Rectangle z w)
  have hfT : DifferentiableOn ℂ f (Rectangle z w \ (↑T : Set ℂ)) := hf.mono fun p hp ↦
    ⟨hp.1, fun hpS ↦ hp.2 (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hpS, hp.1⟩))⟩
  have hmeroT : ∀ s ∈ T, MeromorphicAt f s :=
    fun s hs ↦ hmero s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2
  set decomp := PolarPartDecomposition.ofMeromorphic hfT hmeroT
  have hrem_zero : ∫ t in (0 : ℝ)..4,
      deriv (rectBoundary z w) t • decomp.analyticRemainder (rectBoundary z w t) = 0 := by
    rw [integral_rectBoundary (decomp.analyticRemainder_differentiableOn.continuousOn.mono
      (isClosed_rectangle z w).frontier_subset)]
    exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ z w
      decomp.analyticRemainder_differentiableOn
  rw [decomp.intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum
    (isPiecewiseC1On_rectBoundary z w) (fun t _ ↦ rectBoundary_mem_rectangle t) (by simp)
    (fun _ _ hT ↦ hS _ (Finset.mem_filter.mp hT).1 (rectBoundary_mem_frontier _)),
    hrem_zero, zero_add]
  refine congrArg _ (Finset.sum_congr rfl fun s hs ↦ ?_)
  rw [windingNumber_rectBoundary_eq_one (mem_Ioo_reProdIm_of_mem_rectangle hre him
    (Finset.mem_filter.mp hs).2 (hS s (Finset.mem_filter.mp hs).1)), one_mul]

open scoped Classical in
/-- **The four-edge residue theorem on a rectangle.** Under the hypotheses of
`classicalResidueTheorem_rectBoundary`, the signed sum of the four horizontal and vertical edge
integrals equals `2πi` times the sum of the residues of `f` inside the rectangle. -/
theorem integral_edges_rectangle_eq_two_pi_I_mul_sum_residue (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im)
    (hf : DifferentiableOn ℂ f (Rectangle z w \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, s ∈ Rectangle z w → MeromorphicAt f s)
    (hS : ∀ s ∈ S, s ∉ frontier (Rectangle z w)) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
      I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) =
      2 * π * I * ∑ s ∈ S with s ∈ Rectangle z w, residue f s := by
  have hcont : ContinuousOn f (frontier (Rectangle z w)) :=
    hf.continuousOn.mono fun p hp ↦
      ⟨(isClosed_rectangle z w).frontier_subset hp, fun hpS ↦ hS p hpS hp⟩
  have h := (integral_rectBoundary hcont).symm.trans
    (classicalResidueTheorem_rectBoundary hre him hf hmero hS)
  simpa only [smul_eq_mul] using h

/-- **Shifting a vertical line integral across poles in a strip.** Suppose `a ≤ b`, `f` is
differentiable on `(Icc a b ×ℂ univ) \ S` and meromorphic at each `s ∈ S`, every `s ∈ S` has real
part strictly between `a` and `b`, `f` is integrable on the vertical lines `Re s = a` and
`Re s = b`, and the horizontal segment integrals at heights `±T` tend to `0` as `T → ∞`. Then
`(∫ y, f (b + y * I)) - (∫ y, f (a + y * I)) = 2π ∑_{s ∈ S} Res_s f`. -/
theorem verticalIntegral_sub_verticalIntegral_eq_two_pi_mul_sum_residue {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f ((Icc a b ×ℂ univ) \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hS : ∀ s ∈ S, s.re ∈ Ioo a b)
    (ha : Integrable (fun y : ℝ ↦ f (a + y * I)))
    (hb : Integrable (fun y : ℝ ↦ f (b + y * I)))
    (htop : Tendsto (fun T : ℝ ↦ ∫ x : ℝ in a..b, f (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ ↦ ∫ x : ℝ in a..b, f (x - T * I)) atTop (𝓝 0)) :
    (∫ y : ℝ, f (b + y * I)) - (∫ y : ℝ, f (a + y * I)) = 2 * π * ∑ s ∈ S, residue f s := by
  classical
  have hrect : ∀ᶠ T : ℝ in atTop,
      (∫ x : ℝ in a..b, f (x - T * I)) - (∫ x : ℝ in a..b, f (x + T * I)) +
        I * (∫ y : ℝ in (-T)..T, f (b + y * I)) -
        I * (∫ y : ℝ in (-T)..T, f (a + y * I)) =
      2 * π * I * ∑ s ∈ S, residue f s := by
    filter_upwards [eventually_ge_atTop ((∑ s ∈ S, |s.im|) + 1)] with T hT
    set z : ℂ := a - T * I
    set w : ℂ := b + T * I
    have hzre : z.re = a := by simp [z]
    have hzim : z.im = -T := by simp [z]
    have hwre : w.re = b := by simp [w]
    have hwim : w.im = T := by simp [w]
    have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
    have hre' : z.re ≤ w.re := by simpa [hzre, hwre] using hab
    have him' : z.im ≤ w.im := by simp [hzim, hwim]; linarith
    have hfR : DifferentiableOn ℂ f (Rectangle z w \ (↑S : Set ℂ)) :=
      hf.mono fun p hp ↦
        ⟨⟨by simpa [hzre, hwre] using ((mem_rectangle_iff hre' him').mp hp.1).1, trivial⟩, hp.2⟩
    have hmem_int : ∀ s ∈ S, s ∈ interior (Rectangle z w) := fun s hs ↦ by
      rw [interior_rectangle hre' him', hzre, hwre, hzim, hwim]
      have hle : |s.im| ≤ ∑ p ∈ S, |p.im| :=
        Finset.single_le_sum (f := fun p : ℂ ↦ |p.im|) (fun p _ ↦ abs_nonneg p.im) hs
      exact ⟨hS s hs, abs_lt.mp (by linarith)⟩
    have edges := integral_edges_rectangle_eq_two_pi_I_mul_sum_residue hre' him' hfR
      (fun s hs _ ↦ hmero s hs) (fun s hs hfr ↦ hfr.2 (hmem_int s hs))
    rw [Finset.filter_eq_self.mpr (fun s hs ↦ interior_subset (hmem_int s hs))] at edges
    simpa [hzre, hwre, hzim, hwim, sub_eq_add_neg] using edges
  have hlim := ((hbot.sub htop).add
    ((intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id).const_mul I)).sub
    ((intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id).const_mul I)
  have heq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hrect.mono fun _ h ↦ h.symm))
  simp only [sub_self, zero_add] at heq
  exact mul_left_cancel₀ I_ne_zero (by linear_combination heq)

/-- **Shifting `mellinInv` across poles in a strip.** Suppose `a ≤ b`, `0 < x`, `f` is
differentiable on `(Icc a b ×ℂ univ) \ S` and meromorphic at each `s ∈ S`, every `s ∈ S` has real
part strictly between `a` and `b`, `f` is vertically integrable on `Re s = a` and `Re s = b`, and
`‖f (σ ± T * I)‖ ≤ B T → 0` uniformly for `σ ∈ [a, b]`. Then
`mellinInv b f x - mellinInv a f x = ∑_{s ∈ S} Res_s (z ↦ x⁻ᶻ f(z))`. -/
theorem mellinInv_sub_mellinInv_eq_sum_residue {a b x : ℝ} (hab : a ≤ b) (hx : 0 < x)
    (hf : DifferentiableOn ℂ f ((Icc a b ×ℂ univ) \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hS : ∀ s ∈ S, s.re ∈ Ioo a b)
    (ha : VerticalIntegrable f a) (hb : VerticalIntegrable f b)
    (hdecay : ∃ B : ℝ → ℝ, Tendsto B atTop (𝓝 0) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc a b, ‖f (σ + T * I)‖ ≤ B T ∧ ‖f (σ - T * I)‖ ≤ B T) :
    mellinInv b f x - mellinInv a f x =
      ∑ s ∈ S, residue (fun z ↦ (x : ℂ) ^ (-z) * f z) s := by
  set g : ℂ → ℂ := fun z ↦ (x : ℂ) ^ (-z) * f z
  have hx_an (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ (-w)) z :=
    analyticAt_const.cpow analyticAt_id.neg (ofReal_mem_slitPlane.mpr hx)
  have hg_diff : DifferentiableOn ℂ g ((Icc a b ×ℂ univ) \ (↑S : Set ℂ)) :=
    DifferentiableOn.mul (fun z _ ↦ (hx_an z).differentiableAt.differentiableWithinAt) hf
  have hg_mero : ∀ s ∈ S, MeromorphicAt g s := fun s hs ↦ (hx_an s).meromorphicAt.mul (hmero s hs)
  obtain ⟨B, hB0, hB⟩ := hdecay
  set M : ℝ := max (x ^ (-a)) (x ^ (-b))
  have hpow {σ : ℝ} (hσ : σ ∈ Icc a b) (y : ℝ) : ‖(x : ℂ) ^ (-((σ : ℂ) + y * I))‖ ≤ M := by
    rw [norm_cpow_eq_rpow_re_of_pos hx, show (-((σ : ℂ) + y * I)).re = -σ by simp]
    rcases le_total 1 x with hx1 | hx1
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg hσ.1)).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (neg_le_neg hσ.2)).trans (le_max_right _ _)
  have hhoriz (sgn : ℝ)
      (hB_sgn : ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc a b, ‖f (σ + (sgn * T) * I)‖ ≤ B T) :
      Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in a..b, g (σ + (sgn * T) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun T ↦ M * B T * |b - a|) (hB_sgn.mono fun T hT ↦ ?_)
      (by simpa using (hB0.const_mul M).mul_const |b - a|)
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ ↦ ?_
    have hσ' : σ ∈ Icc a b := Ioc_subset_Icc_self (by rwa [uIoc_of_le hab] at hσ)
    simpa [g, norm_mul, ofReal_mul] using
      mul_le_mul (hpow hσ' (sgn * T)) (hT σ hσ') (norm_nonneg _)
        (le_trans (by positivity) (le_max_left (x ^ (-a)) (x ^ (-b))))
  have htop : Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in a..b, g (σ + T * I)) atTop (𝓝 0) := by
    simpa [one_mul] using hhoriz 1 (hB.mono fun T hT σ hσ ↦ by simpa using (hT σ hσ).1)
  have hbot : Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in a..b, g (σ - T * I)) atTop (𝓝 0) := by
    simpa [sub_eq_add_neg, neg_mul] using hhoriz (-1)
      (hB.mono fun T hT σ hσ ↦ by simpa [sub_eq_add_neg, neg_mul] using (hT σ hσ).2)
  have hshift := verticalIntegral_sub_verticalIntegral_eq_two_pi_mul_sum_residue hab hg_diff hg_mero
    hS (by simpa [g] using ha.integrable_cpow_smul hx)
    (by simpa [g] using hb.integrable_cpow_smul hx) htop hbot
  simp only [mellinInv, real_smul, smul_eq_mul, ← mul_sub]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((∫ y : ℝ, g (b + y * I)) - ∫ y : ℝ, g (a + y * I)) = _
  rw [hshift]
  push_cast
  field_simp [Real.pi_ne_zero]

end TauCeti.Contour
