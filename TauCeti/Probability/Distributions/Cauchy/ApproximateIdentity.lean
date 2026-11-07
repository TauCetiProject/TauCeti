/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import TauCeti.Analysis.Normed.Module.ModulusOfContinuity
import TauCeti.Probability.Distributions.Cauchy.Basic
import TauCeti.Probability.Distributions.Cauchy.Continuity

/-!
# Cauchy densities as an approximate identity

The Cauchy density of scale `γ`, `P_γ(s) = γ / (π (s ^ 2 + γ ^ 2))`
(`ProbabilityTheory.cauchyPDFReal 0 γ`), is the Poisson kernel of the upper half-plane at
height `γ`. As `γ → 0⁺` it concentrates at the origin. This file records the two forms of this
concentration in the form used for boundary values of holomorphic functions on `ℂ ∖ ℝ`: for a
bounded uniformly continuous `g`, the Poisson integrals `∫ P_γ(s) g(t - s) ds` converge to `g`
uniformly in `t`. The kernel may be multiplied by a bounded continuous weight equal to one at the
origin, such as a bump function, which makes the truncated kernel compactly supported without
changing the limit.

The concentration of the kernel itself is the weak convergence of Cauchy laws to the Dirac law,
`TauCeti.Probability.tendsto_cauchyMeasure_nhds_zero_dirac`. Away from the origin `g` changes by
at most its modulus of continuity, and the rest is controlled by integrating a bounded continuous
weight vanishing at the origin against `P_γ`; the pointwise split is
`TauCeti.norm_smul_sub_le_add_mul_min_dist_div`.

## Main declarations

* `TauCeti.Probability.tendstoUniformly_integral_mul_cauchyPDFReal_smul`: uniform convergence of
  the weighted Poisson integrals of a bounded uniformly continuous function.

## References

* E. M. Stein, G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter I,
  §1 (approximate identities and the Poisson kernel).
-/

public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrating a bounded continuous function against the Cauchy density of scale `γ` tends to
its value at the origin as `γ → 0⁺`: the weak convergence of Cauchy laws to `δ₀`, read through
their densities. -/
private theorem tendsto_integral_cauchyPDFReal_mul (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun γ : ℝ≥0 ↦ ∫ s, cauchyPDFReal 0 γ s * f s) (𝓝[≠] 0) (𝓝 (f 0)) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (tendsto_cauchyMeasure_nhds_zero_dirac 0) f
  simp only [Measure.coe_toProbabilityMeasure, integral_dirac] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  simp only [integral_cauchyMeasure_eq 0 hγ, smul_eq_mul]

/-- If `‖h(s) g(t - s) - g(t)‖ ≤ c + v(s)` for a bounded continuous `v`, then the weighted
Poisson integral of `g` at `t` differs from `g t` by at most `c + ∫ P_γ v`. -/
private theorem norm_integral_mul_cauchyPDFReal_smul_sub_le [CompleteSpace E] {g : ℝ → E}
    {h : ℝ → ℝ} {γ : ℝ≥0} (hγ : γ ≠ 0) {t : ℝ} (hcont : Continuous fun s ↦ h s • g (t - s))
    {v : ℝ → ℝ} (hv : Continuous v) {c C : ℝ} (hvC : ∀ s, ‖v s‖ ≤ C)
    (hpt : ∀ s, ‖h s • g (t - s) - g t‖ ≤ c + v s) :
    ‖(∫ s, (h s * cauchyPDFReal 0 γ s) • g (t - s)) - g t‖ ≤
      c + ∫ s, cauchyPDFReal 0 γ s * v s := by
  have hP := integrable_cauchyPDFReal (0 : ℝ) (γ := γ)
  have hbd (s : ℝ) : c + v s ≤ |c| + C := add_le_add (le_abs_self c) ((le_abs_self _).trans (hvC s))
  have hI : Integrable (fun s ↦ cauchyPDFReal 0 γ s • (h s • g (t - s) - g t)) :=
    hP.smul_bdd (|c| + C) (hcont.sub continuous_const).aestronglyMeasurable
      (ae_of_all _ fun s ↦ (hpt s).trans (hbd s))
  have hlow (s : ℝ) : -(|c| + C) ≤ c + v s := by
    have := hvC s
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le c, neg_abs_le (v s)]
  have hIb : Integrable (fun s ↦ cauchyPDFReal 0 γ s * (c + v s)) :=
    hP.smul_bdd (|c| + C) (continuous_const.add hv).aestronglyMeasurable
      (ae_of_all _ fun s ↦ abs_le.2 ⟨hlow s, hbd s⟩)
  -- The weighted Poisson integral minus `g t` is the integral of `P_γ(s) (h(s) g(t - s) - g(t))`.
  have hrepr : (∫ s, (h s * cauchyPDFReal 0 γ s) • g (t - s)) - g t =
      ∫ s, cauchyPDFReal 0 γ s • (h s • g (t - s) - g t) := by
    have hgt : g t = ∫ s, cauchyPDFReal 0 γ s • g t := by
      rw [integral_smul_const, integral_cauchyPDFReal_eq_one 0 hγ, one_smul]
    have hI₁ : Integrable fun s ↦ (h s * cauchyPDFReal 0 γ s) • g (t - s) := by
      refine (hI.add (hP.smul_const (g t))).congr (ae_of_all _ fun s ↦ ?_)
      simp only [Pi.add_apply, smul_sub, mul_comm (h s), mul_smul, sub_add_cancel]
    conv_lhs => rw [hgt]
    rw [← integral_sub hI₁ (hP.smul_const (g t))]
    congr 1
    ext s
    rw [smul_sub, mul_comm (h s), mul_smul]
  rw [hrepr]
  calc ‖∫ s, cauchyPDFReal 0 γ s • (h s • g (t - s) - g t)‖
      ≤ ∫ s, cauchyPDFReal 0 γ s * (c + v s) :=
        norm_integral_le_of_norm_le hIb (ae_of_all _ fun s ↦ by
          rw [norm_smul, Real.norm_of_nonneg (cauchyPDF_pos 0 hγ s).le]
          exact mul_le_mul_of_nonneg_left (hpt s) (cauchyPDF_pos 0 hγ s).le)
    _ = c + ∫ s, cauchyPDFReal 0 γ s * v s := by
        simp_rw [mul_add]
        have hIv : Integrable (fun s ↦ cauchyPDFReal 0 γ s * v s) :=
          hP.smul_bdd _ hv.aestronglyMeasurable (ae_of_all _ hvC)
        rw [integral_add (hP.mul_const _) hIv, integral_mul_const,
          integral_cauchyPDFReal_eq_one 0 hγ, one_mul]

/-- **The Poisson kernel of the half-plane is an approximate identity.** Let `g` be bounded and
uniformly continuous, and let `h` be a bounded continuous weight with `h 0 = 1`. Then the weighted
Poisson integrals `t ↦ ∫ h(s) P_γ(s) g(t - s) ds` converge to `g` uniformly as `γ → 0⁺`, where
`P_γ = cauchyPDFReal 0 γ`. The weight `h = 1` gives the Poisson integrals themselves. -/
theorem tendstoUniformly_integral_mul_cauchyPDFReal_smul [CompleteSpace E] {g : ℝ → E}
    (hg : UniformContinuous g) {M : ℝ} (hgM : ∀ t, ‖g t‖ ≤ M) {h : ℝ → ℝ} (hh : Continuous h)
    {H : ℝ} (hhH : ∀ s, |h s| ≤ H) (h0 : h 0 = 1) :
    TendstoUniformly (fun (γ : ℝ≥0) (t : ℝ) ↦ ∫ s, (h s * cauchyPDFReal 0 γ s) • g (t - s)) g
      (𝓝[≠] 0) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hH : 1 ≤ H := by simpa [h0] using hhH 0
  have hM : 0 ≤ M := (norm_nonneg _).trans (hgM 0)
  -- The modulus of continuity `η` of `g` is chosen so that `H η < ε / 2`.
  have hη : 0 < ε / (2 * (H + 1)) := by positivity
  have hHη : H * (ε / (2 * (H + 1))) < ε / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuous_iff.1 hg _ hη
  -- The rest of the error is a bounded continuous weight `v` with `v 0 = 0`, so `∫ P_γ v → 0`.
  let v : ℝ → ℝ := fun s ↦ 2 * H * M * min 1 (|s| / δ) + M * |h s - 1|
  have hv : Continuous v := (continuous_const.mul (continuous_const.min
    (continuous_abs.div_const δ))).add (continuous_const.mul ((hh.sub continuous_const).abs))
  have hvb (s : ℝ) : ‖v s‖ ≤ 2 * H * M + M * (H + 1) := by
    have hw0 : 0 ≤ min 1 (|s| / δ) := le_min zero_le_one (by positivity)
    have hw1 : min 1 (|s| / δ) ≤ 1 := min_le_left _ _
    have h1 : |h s - 1| ≤ H + 1 := (abs_sub _ _).trans (by simpa using hhH s)
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hM, mul_nonneg (mul_nonneg zero_le_two
      (zero_le_one.trans hH)) hM]
  have hlim := tendsto_integral_cauchyPDFReal_mul (.ofNormedAddCommGroup v hv _ hvb)
  simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup] at hlim
  have hv0 : v 0 = 0 := by simp [v, h0]
  rw [hv0] at hlim
  filter_upwards [hlim (Iio_mem_nhds (half_pos hε)), self_mem_nhdsWithin] with γ hγε hγ t
  rw [dist_eq_norm']
  refine (norm_integral_mul_cauchyPDFReal_smul_sub_le hγ
    (hh.smul (hg.continuous.comp (continuous_const.sub continuous_id))) hv hvb
    fun s ↦ by simpa [Real.dist_eq] using
      norm_smul_sub_le_add_mul_min_dist_div hgM hδ hgδ (hhH s) (t - s) t).trans_lt ?_
  linarith [Set.mem_Iio.1 hγε]

end TauCeti.Probability
