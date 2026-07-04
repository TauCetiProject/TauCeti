/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# The local argument principle

For `f : ℂ → ℂ` meromorphic on a closed disc `C(c, R)` in which the centre `c` is the only point
that may be a zero or pole, of order `n = meromorphicOrderAt f c`, the contour integral of the
logarithmic derivative recovers the order:
`∮_{C(c,R)} f'/f = 2πi · n`.

This is the per-orbit input to the valence formula: the residue of `f'/f` at `c` is `ord_c f`, so
integrating `logDeriv f = f'/f` around the circle counts (with multiplicity) the zero or pole at the
centre, and vanishes when `c` too is regular (`n = 0`). Mathlib has `logDeriv` and
`meromorphicOrderAt` but not this identity.

The proof is Cauchy's theorem plus the Cauchy kernel: off `c` the hypothesis forces `f` to be
analytic and non-vanishing, so `logDeriv f` is analytic there; near `c`, the local factorisation
`f = (· − c) ^ n • g` (with `g` analytic, `g c ≠ 0`) gives `logDeriv f = n · (· − c)⁻¹ + logDeriv g`
with `logDeriv g` analytic. Hence `logDeriv f − n · (· − c)⁻¹` extends holomorphically across the
whole disc, contributing `0` to the circle integral (Cauchy–Goursat), while
`∮ n · (· − c)⁻¹ = n · 2πi` (`circleIntegral.integral_sub_center_inv`).

## Main results

* `TauCeti.Contour.argumentPrinciple_local` — `∮_{C(c,R)} logDeriv f = 2πi · n` when `c` is the only
  zero or pole of `f` in the closed disc, of order `n`.

This is a Layer 2 target of the contour-integration roadmap, feeding the argument principle and,
ultimately, the valence formula.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (the argument-principle specialisation of
`ForMathlib/GeneralizedResidueTheory/Residue.lean` and
`.../Residue/GeneralizedTheoremBase.lean`, where the residue theorem is applied to `logDeriv f`),
specialised to a circle and to the raw-function design of the contour-integration roadmap.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

open Filter Topology Metric Complex
open scoped Real

namespace TauCeti.Contour

/-- At a point where a function is analytic and non-vanishing, its logarithmic derivative
`logDeriv f = deriv f / f` is analytic. -/
private lemma analyticAt_logDeriv_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hz : f z ≠ 0) : AnalyticAt ℂ (logDeriv f) z := by
  rw [logDeriv]
  exact hf.deriv.div hf hz

/-- The logarithmic derivative depends only on the germ. -/
private lemma logDeriv_eq_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    logDeriv f z = logDeriv g z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

/-- **Core Cauchy–Goursat computation for the argument principle.** If `F` is meromorphic at the
centre `c` with `meromorphicOrderAt F c = n`, and is analytic and non-vanishing everywhere else on
the closed disc, then `∮_{C(c,R)} logDeriv F = 2πi · n`. -/
private lemma circleIntegral_logDeriv_of_order_of_analyticAt_off
    {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℤ} (hR : 0 < R) (hmero : MeromorphicAt F c)
    (hord : meromorphicOrderAt F c = (n : WithTop ℤ))
    (hoff : ∀ z ∈ closedBall c R, z ≠ c → AnalyticAt ℂ F z ∧ F z ≠ 0) :
    circleIntegral (logDeriv F) c R = 2 * (π : ℂ) * I * (n : ℂ) := by
  -- Local factorisation at the centre: `F = (· - c) ^ n • g` on a punctured neighbourhood.
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hmero).1 hord
  have hlg : AnalyticAt ℂ (logDeriv g) c := analyticAt_logDeriv_of_analyticAt hg_an hg_ne
  set φ : ℂ → ℂ := fun z => logDeriv F z - (n : ℂ) * (z - c)⁻¹ with hφ_def
  set ψ : ℂ → ℂ := Function.update φ c (logDeriv g c) with hψ_def
  -- (A) The remainder agrees with `logDeriv g` near `c`.
  have hAφ : φ =ᶠ[𝓝[≠] c] logDeriv g := by
    -- Lift the punctured factorisation to germ-agreement at each nearby point.
    have hFH : ∀ᶠ z in 𝓝[≠] c, F =ᶠ[𝓝 z] fun w => (w - c) ^ n • g w := by
      obtain ⟨U, hU_open, hcU, hU_sub⟩ := mem_nhdsWithin.1 hg_eq
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hU_open.mem_nhds hcU), self_mem_nhdsWithin]
        with z hzU hz_ne
      filter_upwards [(hU_open.inter isOpen_compl_singleton).mem_nhds ⟨hzU, hz_ne⟩] with w hw
        using hU_sub hw
    filter_upwards [hFH, hg_an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (hg_an.continuousAt.eventually_ne hg_ne).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz_FH hz_gan hz_gne hz_ne
    have hz_ne' : z ≠ c := hz_ne
    have hz_sub : z - c ≠ 0 := sub_ne_zero.2 hz_ne'
    have hzpow : (z - c) ^ n ≠ 0 := zpow_ne_zero n hz_sub
    have hdz : DifferentiableAt ℂ (fun w => (w - c) ^ n) z :=
      (differentiableAt_id.sub_const c).zpow (Or.inl hz_sub)
    have hderiv : deriv (fun w => w - c) z = 1 := by simp
    have hld_sub : logDeriv (fun w => w - c) z = (z - c)⁻¹ := by
      rw [logDeriv_apply, hderiv, one_div]
    have hmul : (fun w => (w - c) ^ n • g w) = fun w => (w - c) ^ n * g w := by
      funext w; rw [smul_eq_mul]
    have hLF : logDeriv F z = (n : ℂ) * (z - c)⁻¹ + logDeriv g z := by
      rw [logDeriv_eq_of_eventuallyEq hz_FH, hmul,
        logDeriv_mul z hzpow hz_gne hdz hz_gan.differentiableAt,
        logDeriv_fun_zpow (f := fun w => w - c) (differentiableAt_id.sub_const c) n, hld_sub]
    simp only [hφ_def]; rw [hLF]; ring
  -- (A') Hence `ψ` agrees with `logDeriv g` on a full neighbourhood of `c`.
  have hAψ : ψ =ᶠ[𝓝 c] logDeriv g := by
    refine eventuallyEq_nhds_of_eventuallyEq_nhdsNE ?_ ?_
    · refine (?_ : ψ =ᶠ[𝓝[≠] c] φ).trans hAφ
      rw [hψ_def]; exact Function.update_eventuallyEq_nhdsNE φ c c (logDeriv g c)
    · rw [hψ_def, Function.update_self]
  -- (B) `ψ` is differentiable throughout the closed disc.
  have hψ_diff : ∀ z ∈ closedBall c R, DifferentiableAt ℂ ψ z := by
    intro z hz
    by_cases hzc : z = c
    · subst hzc
      exact hlg.differentiableAt.congr_of_eventuallyEq hAψ
    · have hφz : DifferentiableAt ℂ φ z := by
        have h1 : AnalyticAt ℂ (logDeriv F) z :=
          analyticAt_logDeriv_of_analyticAt (hoff z hz hzc).1 (hoff z hz hzc).2
        have h2 : DifferentiableAt ℂ (fun w => (n : ℂ) * (w - c)⁻¹) z :=
          (differentiableAt_const _).mul ((differentiableAt_id.sub_const _).inv
            (sub_ne_zero.2 hzc))
        exact h1.differentiableAt.sub h2
      have hne : ψ =ᶠ[𝓝 z] φ := by
        filter_upwards [compl_singleton_mem_nhds hzc] with w hw
        rw [hψ_def, Function.update_of_ne hw]
      exact hφz.congr_of_eventuallyEq hne
  -- On the circle every point is off the centre (`R > 0`), so `ψ` and `φ` agree there.
  have hsphere_ne : ∀ z ∈ sphere c R, z ≠ c := by
    intro z hz h
    rw [mem_sphere_iff_norm, h, sub_self, norm_zero] at hz
    exact hR.ne' hz.symm
  have hφψ_sphere : Set.EqOn φ ψ (sphere c R) := fun z hz => by
    rw [hψ_def, Function.update_of_ne (hsphere_ne z hz)]
  have hsub : sphere c R ⊆ closedBall c R := sphere_subset_closedBall
  have hψ_cont : ContinuousOn ψ (sphere c R) := fun z hz =>
    (hψ_diff z (hsub hz)).continuousAt.continuousWithinAt
  have hφ_cont : ContinuousOn φ (sphere c R) := hψ_cont.congr hφψ_sphere
  -- `∮ φ = ∮ ψ = 0` by Cauchy–Goursat, since `ψ` is differentiable on the whole disc.
  have hφ0 : circleIntegral φ c R = 0 := by
    rw [circleIntegral.integral_congr hR.le hφψ_sphere]
    exact circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
      (fun z hz => (hψ_diff z hz).continuousAt.continuousWithinAt)
      (fun z hz => hψ_diff z (ball_subset_closedBall hz.1))
  -- Integrability of the two summands on the circle.
  have hφ_int : CircleIntegrable φ c R := hφ_cont.circleIntegrable hR.le
  have hinv_cont : ContinuousOn (fun z => (n : ℂ) * (z - c)⁻¹) (sphere c R) :=
    continuousOn_const.mul <| (continuousOn_id.sub continuousOn_const).inv₀
      fun z hz => sub_ne_zero.2 (hsphere_ne z hz)
  have hinv_int : CircleIntegrable (fun z => (n : ℂ) * (z - c)⁻¹) c R :=
    hinv_cont.circleIntegrable hR.le
  -- Split `logDeriv F = φ + n·(· - c)⁻¹` and evaluate.
  have hsplit : circleIntegral (logDeriv F) c R
      = circleIntegral φ c R + circleIntegral (fun z => (n : ℂ) * (z - c)⁻¹) c R := by
    rw [← circleIntegral.integral_add hφ_int hinv_int]
    congr 1 with z
    simp only [hφ_def]; ring
  rw [hsplit, hφ0, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_center_inv c hR.ne']
  ring

/-- **Local argument principle.** If `f` is meromorphic on the closed disc `C(c, R)` (`R > 0`) and
every point of the disc except possibly the centre `c` is regular (analytic and non-vanishing), then
the contour integral of the logarithmic derivative recovers the order `n = meromorphicOrderAt f c`
at the centre:
`∮_{C(c,R)} f'/f = 2πi · n`. Thus the integral counts the zero (`n > 0`) or pole (`n < 0`) at the
centre with multiplicity, and vanishes when `c` too is regular (`n = 0`). -/
theorem argumentPrinciple_local {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℤ} (hR : 0 < R)
    (hf : MeromorphicOn f (Metric.closedBall c R))
    (honly : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z ≠ 0 → z = c)
    (hn : meromorphicOrderAt f c = (n : WithTop ℤ)) :
    circleIntegral (logDeriv f) c R = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
  -- Pass to the meromorphic normal form `F`, which is genuinely analytic off the centre (`f` may
  -- have isolated removable "wrong values" where `logDeriv f` is junk); the circle integral only
  -- sees `f` up to a discrete set, so it is unchanged.
  set F := toMeromorphicNFOn f (closedBall c R) with hF_def
  have hcc : c ∈ closedBall c R := mem_closedBall_self hR.le
  have hF_nf : MeromorphicNFOn F (closedBall c R) :=
    meromorphicNFOn_toMeromorphicNFOn f (closedBall c R)
  have hord : ∀ z ∈ closedBall c R, meromorphicOrderAt F z = meromorphicOrderAt f z :=
    fun z hz => meromorphicOrderAt_toMeromorphicNFOn hf hz
  -- Transport the hypotheses to `F`.
  have hnF : meromorphicOrderAt F c = (n : WithTop ℤ) := (hord c hcc).trans hn
  have honlyF : ∀ z ∈ closedBall c R, meromorphicOrderAt F z ≠ 0 → z = c :=
    fun z hz h => honly z hz (hord z hz ▸ h)
  have hoffF : ∀ z ∈ closedBall c R, z ≠ c → AnalyticAt ℂ F z ∧ F z ≠ 0 := by
    intro z hz hzc
    have h0 : meromorphicOrderAt F z = 0 := by
      by_contra h; exact hzc (honlyF z hz h)
    exact ⟨(hF_nf hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 h0.symm.le,
      (hF_nf hz).meromorphicOrderAt_eq_zero_iff.1 h0⟩
  have hFc_mero : MeromorphicAt F c := hF_nf.meromorphicOn c hcc
  -- The core computation applies to `F`.
  have hcore : circleIntegral (logDeriv F) c R = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) :=
    circleIntegral_logDeriv_of_order_of_analyticAt_off hR hFc_mero hnF hoffF
  -- Transfer back: `logDeriv f = logDeriv F` off a discrete subset of the circle.
  rw [← hcore]
  refine circleIntegral.circleIntegral_congr_codiscreteWithin ?_ hR.ne'
  have hspU : sphere c |R| ⊆ closedBall c R := by
    rw [abs_of_pos hR]; exact sphere_subset_closedBall
  filter_upwards [(toMeromorphicNFOn_eqOn_codiscrete hf).filter_mono
      (Filter.codiscreteWithin_mono hspU), self_mem_codiscreteWithin (sphere c |R|)]
    with z hz_eq hz_mem
  have hne : f =ᶠ[𝓝[≠] z] F := (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (hspU hz_mem)).symm
  exact logDeriv_eq_of_eventuallyEq (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hne hz_eq)

end TauCeti.Contour
