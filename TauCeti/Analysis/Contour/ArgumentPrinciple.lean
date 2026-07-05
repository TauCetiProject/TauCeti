/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The argument principle

For `f : ℂ → ℂ` meromorphic on a closed disc `C(c, R)` in which the centre `c` is the only point
that may have nonzero meromorphic order `n = meromorphicOrderAt f c` (every other point being at
worst a removable singularity), the contour integral of the logarithmic derivative recovers that
order:
`∮_{C(c,R)} f'/f = 2πi · n`.

More generally, when the nonzero-order points form a finite set `S` in the open disc, with orders
`ord`, the same integral counts them with multiplicity: `∮_{C(c,R)} f'/f = 2πi · ∑_{z ∈ S} ord z`.

This is the per-orbit input to the valence formula: the residue of `f'/f` at `c` is `ord_c f`, so
integrating `logDeriv f = f'/f` around the circle counts (with multiplicity) the zero or pole at the
centre, and vanishes when `c` too has order `0`. Mathlib has `logDeriv` and `meromorphicOrderAt`
but not this identity.

The proof passes to the meromorphic normal form `F` of `f` on the disc. Unlike raw `f` — which may
carry isolated removable "wrong values" off `c` where `logDeriv f` is meaningless — `F` is genuinely
analytic and non-vanishing at every non-central point, so `logDeriv F` is analytic there; near `c`,
the local factorisation `F = (· − c) ^ n • g` (with `g` analytic, `g c ≠ 0`) gives
`logDeriv F = n · (· − c)⁻¹ + logDeriv g` with `logDeriv g` analytic, so `(· − c) · logDeriv F`
extends continuously across `c` with value `n`. Mathlib's removable-singularity Cauchy kernel
formula then yields `∮ logDeriv F = 2πi · n`, and circle congruence (`F = f` off a discrete set)
transfers the value back to `logDeriv f`.

The finite-set version follows the same route: the normal form `F` supplies the local factorisation
at each `s ∈ S`, so `logDeriv F` minus its simple-pole principal parts is pole-free and integrates
to `0` (Cauchy–Goursat), while those principal parts `∑_{s ∈ S} ord(s) · (· − s)⁻¹` contribute
`2πi · ∑ ord`.

## Main results

* `TauCeti.Contour.argumentPrinciple_local` — `∮_{C(c,R)} logDeriv f = 2πi · n` when the centre `c`,
  of order `n`, is the only point of the closed disc that may have nonzero meromorphic order.
* `TauCeti.Contour.argumentPrinciple` — `∮_{C(c,R)} logDeriv f = 2πi · ∑_{z ∈ S} ord z` when the
  nonzero-order points form a finite set `S` inside the open disc, with orders `ord`.

These are Layer 2 targets of the contour-integration roadmap, feeding the argument principle and,
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

/-- Logarithmic derivative of a local factorisation `(· - c) ^ n · g`, away from the base point `c`.
Since `logDeriv` turns products into sums and `logDeriv ((· - c) ^ n) = n · (· - c)⁻¹`, we get
`logDeriv ((· - c) ^ n · g) = n · (· - c)⁻¹ + logDeriv g`. -/
private lemma logDeriv_zpow_sub_mul {g : ℂ → ℂ} {c z : ℂ} {n : ℤ} (hz : z ≠ c) (hg_ne : g z ≠ 0)
    (hg_diff : DifferentiableAt ℂ g z) :
    logDeriv (fun w => (w - c) ^ n * g w) z = (n : ℂ) * (z - c)⁻¹ + logDeriv g z := by
  have hz_sub : z - c ≠ 0 := sub_ne_zero.2 hz
  have hzpow : (z - c) ^ n ≠ 0 := zpow_ne_zero n hz_sub
  have hdz : DifferentiableAt ℂ (fun w => (w - c) ^ n) z :=
    (differentiableAt_id.sub_const c).zpow (Or.inl hz_sub)
  have hld_sub : logDeriv (fun w => w - c) z = (z - c)⁻¹ := by
    have hderiv : deriv (fun w => w - c) z = 1 := by simp
    rw [logDeriv_apply, hderiv, one_div]
  rw [logDeriv_mul z hzpow hg_ne hdz hg_diff,
    logDeriv_fun_zpow (f := fun w => w - c) (differentiableAt_id.sub_const c) n, hld_sub]

/-- **Simple-pole splitting of the logarithmic derivative.** Near a point `s` where `F` is
meromorphic of order `n`, the logarithmic derivative equals its simple-pole principal part
`n · (· - s)⁻¹` plus an analytic term: there is `g` analytic and non-vanishing at `s` (the local
factor of `F = (· - s) ^ n • g`) with `logDeriv F = n · (· - s)⁻¹ + logDeriv g` on a punctured
neighbourhood of `s`. -/
private lemma logDeriv_eventuallyEq_principalPart {F : ℂ → ℂ} {s : ℂ} {n : ℤ}
    (hF : MeromorphicAt F s) (hn : meromorphicOrderAt F s = (n : WithTop ℤ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ g s ≠ 0 ∧
      logDeriv F =ᶠ[𝓝[≠] s] fun z => (n : ℂ) * (z - s)⁻¹ + logDeriv g z := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hF).1 hn
  refine ⟨g, hg_an, hg_ne, ?_⟩
  -- Lift the punctured factorisation to germ-agreement at each nearby point.
  have hFH : ∀ᶠ z in 𝓝[≠] s, F =ᶠ[𝓝 z] fun w => (w - s) ^ n • g w := by
    obtain ⟨U, hU_open, hcU, hU_sub⟩ := mem_nhdsWithin.1 hg_eq
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU_open.mem_nhds hcU), self_mem_nhdsWithin]
      with z hzU hz_ne
    filter_upwards [(hU_open.inter isOpen_compl_singleton).mem_nhds ⟨hzU, hz_ne⟩] with w hw
      using hU_sub hw
  filter_upwards [hFH, hg_an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg_an.continuousAt.eventually_ne hg_ne).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz_FH hz_gan hz_gne hz_ne
  have hmul : (fun w => (w - s) ^ n • g w) = fun w => (w - s) ^ n * g w := by
    funext w; rw [smul_eq_mul]
  rw [logDeriv_eq_of_eventuallyEq hz_FH, hmul]
  exact logDeriv_zpow_sub_mul hz_ne hz_gne hz_gan.differentiableAt

/-- **Core computation for the argument principle.** If `F` is meromorphic at the centre `c` with
`meromorphicOrderAt F c = n`, and is analytic and non-vanishing everywhere else on the closed disc,
then `∮_{C(c,R)} logDeriv F = 2πi · n`. The local factorisation `F = (· - c) ^ n • g` makes
`(· - c)·logDeriv F` extend continuously to `c` with value `n`, and Mathlib's removable-singularity
Cauchy kernel formula evaluates the resulting integral. -/
private lemma circleIntegral_logDeriv_of_order_of_analyticAt_off
    {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℤ} (hR : 0 < R) (hmero : MeromorphicAt F c)
    (hord : meromorphicOrderAt F c = (n : WithTop ℤ))
    (hoff : ∀ z ∈ closedBall c R, z ≠ c → AnalyticAt ℂ F z ∧ F z ≠ 0) :
    circleIntegral (logDeriv F) c R = 2 * (π : ℂ) * I * (n : ℂ) := by
  -- Local factorisation at the centre: `F = (· - c) ^ n • g` on a punctured neighbourhood.
  obtain ⟨g, hg_an, hg_ne, hg_germ⟩ := logDeriv_eventuallyEq_principalPart hmero hord
  have hlg : AnalyticAt ℂ (logDeriv g) c := analyticAt_logDeriv_of_analyticAt hg_an hg_ne
  -- Near the centre, `logDeriv F = n·(· - c)⁻¹ + logDeriv g`, hence `(· - c)·logDeriv F → n`.
  have hEq : (fun z => (z - c) * logDeriv F z) =ᶠ[𝓝[≠] c]
      fun z => (n : ℂ) + (z - c) * logDeriv g z := by
    filter_upwards [hg_germ, self_mem_nhdsWithin] with z hz_germ hz_ne
    have hz_sub : z - c ≠ 0 := sub_ne_zero.2 hz_ne
    rw [hz_germ]; linear_combination (n : ℂ) * mul_inv_cancel₀ hz_sub
  -- The bracketed function extends continuously to the centre with value `n`.
  have hlim : Tendsto (fun z => (z - c) * logDeriv F z) (𝓝[≠] c) (𝓝 (n : ℂ)) := by
    refine Tendsto.congr' hEq.symm ?_
    have hz_sub : Tendsto (fun z : ℂ => z - c) (𝓝[≠] c) (𝓝 0) := by
      have h : Tendsto (fun z : ℂ => z - c) (𝓝 c) (𝓝 (c - c)) :=
        (continuous_id.sub continuous_const).tendsto c
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hprod := hz_sub.mul (hlg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    simpa using hprod.const_add (n : ℂ)
  -- `(· - c)·logDeriv F` is analytic off the centre.
  have hG_off : ∀ z ∈ closedBall c R, z ≠ c →
      AnalyticAt ℂ (fun w => (w - c) * logDeriv F w) z := fun z hz hzc =>
    (analyticAt_id.sub analyticAt_const).mul
      (analyticAt_logDeriv_of_analyticAt (hoff z hz hzc).1 (hoff z hz hzc).2)
  -- Mathlib's packaged removable-singularity Cauchy kernel formula evaluates the integral.
  have key := circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
    (f := fun z => (z - c) * logDeriv F z) hR Set.countable_empty
    (fun z hz => (hG_off z hz.1 hz.2).continuousAt.continuousWithinAt)
    (fun z hz => (hG_off z (ball_subset_closedBall hz.1.1) hz.1.2).differentiableAt) hlim
  calc circleIntegral (logDeriv F) c R
      = ∮ z in C(c, R), (z - c)⁻¹ • ((z - c) * logDeriv F z) := by
        refine circleIntegral.integral_congr hR.le fun z hz => ?_
        have hzc : z ≠ c := by
          intro h
          rw [mem_sphere_iff_norm, h, sub_self, norm_zero] at hz
          exact hR.ne' hz.symm
        rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.2 hzc), one_mul]
    _ = (2 * (π : ℂ) * I) • (n : ℂ) := key
    _ = 2 * (π : ℂ) * I * (n : ℂ) := by rw [smul_eq_mul]

/-- **Local argument principle.** If `f` is meromorphic on the closed disc `C(c, R)` (`R > 0`) and
the centre `c` is the only point of the disc that may have nonzero meromorphic order — every other
point is at worst a removable singularity — then the contour integral of the logarithmic derivative
recovers the order `n = meromorphicOrderAt f c` at the centre:
`∮_{C(c,R)} f'/f = 2πi · n`. Thus the integral counts the zero (`n > 0`) or pole (`n < 0`) at the
centre with multiplicity, and vanishes when `c` too has order `0`. The proof passes to the
meromorphic normal form of `f`, which — unlike raw `f` — is genuinely analytic and non-vanishing at
every non-central point of the disc; `f` itself may take isolated "wrong values" off `c`. -/
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

/-- **Cauchy–Goursat for a pole-free meromorphic function.** If `A` is meromorphic on the closed
disc `C(c, R)` (`R > 0`) and has non-negative meromorphic order at every point — so its normal form
is analytic throughout the disc — then `∮_{C(c,R)} A = 0`. -/
private lemma circleIntegral_eq_zero_of_nonneg_meromorphicOrderAt {A : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hA : MeromorphicOn A (closedBall c R))
    (hord : ∀ z ∈ closedBall c R, 0 ≤ meromorphicOrderAt A z) :
    circleIntegral A c R = 0 := by
  have hB_nf : MeromorphicNFOn (toMeromorphicNFOn A (closedBall c R)) (closedBall c R) :=
    meromorphicNFOn_toMeromorphicNFOn A (closedBall c R)
  -- The normal form of `A` is analytic on the whole disc.
  have hB_an : AnalyticOnNhd ℂ (toMeromorphicNFOn A (closedBall c R)) (closedBall c R) := by
    intro z hz
    refine (hB_nf hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
    rw [meromorphicOrderAt_toMeromorphicNFOn hA hz]
    exact hord z hz
  have hB0 : circleIntegral (toMeromorphicNFOn A (closedBall c R)) c R = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
      (fun z hz => (hB_an z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hB_an z (ball_subset_closedBall hz.1)).differentiableAt)
  -- The circle integral only sees `A` up to a discrete set, so it agrees with its normal form.
  rw [← hB0]
  refine circleIntegral.circleIntegral_congr_codiscreteWithin ?_ hR.ne'
  have hspU : sphere c |R| ⊆ closedBall c R := by rw [abs_of_pos hR]; exact sphere_subset_closedBall
  exact (toMeromorphicNFOn_eqOn_codiscrete hA).filter_mono (Filter.codiscreteWithin_mono hspU)

/-- **The argument principle.** If `f` is meromorphic on the closed disc `C(c, R)` (`R > 0`) with
all its nonzero-order points contained in a finite set `S` inside the open disc, with orders `ord`,
then the contour integral of the logarithmic derivative counts the zeros minus the poles with
multiplicity:
`∮_{C(c,R)} f'/f = 2πi · ∑_{z ∈ S} ord z`.
The proof passes to the meromorphic normal form `F` of `f` (genuinely analytic and non-vanishing off
`S`, whereas raw `f` may take isolated "wrong values"), subtracts the simple-pole principal parts
`∑_{s ∈ S} ord(s) · (· - s)⁻¹` — whose circle integral is `2πi · ∑ ord` — and observes that the
remainder is pole-free, so its circle integral vanishes by Cauchy–Goursat. -/
theorem argumentPrinciple {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (S : Finset ℂ) (ord : ℂ → ℤ)
    (hf : MeromorphicOn f (Metric.closedBall c R))
    (hS : (S : Set ℂ) ⊆ Metric.ball c R)
    (hsupp : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z ≠ 0 → z ∈ S)
    (hord : ∀ z ∈ S, meromorphicOrderAt f z = (ord z : WithTop ℤ)) :
    circleIntegral (logDeriv f) c R = 2 * (Real.pi : ℂ) * Complex.I * (∑ z ∈ S, (ord z : ℂ)) := by
  -- Pass to the meromorphic normal form `F` of `f`.
  set F := toMeromorphicNFOn f (closedBall c R) with hF_def
  have hF_nf : MeromorphicNFOn F (closedBall c R) := meromorphicNFOn_toMeromorphicNFOn f _
  have hF_mero : MeromorphicOn F (closedBall c R) := hF_nf.meromorphicOn
  have hordF : ∀ z ∈ closedBall c R, meromorphicOrderAt F z = meromorphicOrderAt f z :=
    fun z hz => meromorphicOrderAt_toMeromorphicNFOn hf hz
  -- Off `S`, `F` is analytic and non-vanishing.
  have hoffF : ∀ z ∈ closedBall c R, z ∉ S → AnalyticAt ℂ F z ∧ F z ≠ 0 := by
    intro z hz hzS
    have h0 : meromorphicOrderAt F z = 0 := by
      rw [hordF z hz]; by_contra h; exact hzS (hsupp z hz h)
    exact ⟨(hF_nf hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 h0.symm.le,
      (hF_nf hz).meromorphicOrderAt_eq_zero_iff.1 h0⟩
  -- Reduce to `F` by circle congruence off a discrete set (as in `argumentPrinciple_local`).
  have htransfer : circleIntegral (logDeriv f) c R = circleIntegral (logDeriv F) c R := by
    refine circleIntegral.circleIntegral_congr_codiscreteWithin ?_ hR.ne'
    have hspU : sphere c |R| ⊆ closedBall c R := by
      rw [abs_of_pos hR]; exact sphere_subset_closedBall
    filter_upwards [(toMeromorphicNFOn_eqOn_codiscrete hf).filter_mono
        (Filter.codiscreteWithin_mono hspU), self_mem_codiscreteWithin (sphere c |R|)]
      with z hz_eq hz_mem
    have hne : f =ᶠ[𝓝[≠] z] F := (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (hspU hz_mem)).symm
    exact logDeriv_eq_of_eventuallyEq (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hne hz_eq)
  rw [htransfer]
  -- Sphere points avoid the (interior) pole set `S`.
  have hsphere_notS : ∀ z ∈ sphere c R, z ∉ S := by
    intro z hz hzS
    rw [Metric.mem_sphere] at hz
    exact absurd hz (ne_of_lt (Metric.mem_ball.1 (hS (Finset.mem_coe.2 hzS))))
  have hzs_ne : ∀ z ∈ sphere c R, ∀ s ∈ S, z ≠ s := by
    intro z hz s hsS h; subst h; exact absurd hsS (hsphere_notS z hz)
  -- Principal part `P` and its meromorphy.
  set P : ℂ → ℂ := fun z => ∑ s ∈ S, (ord s : ℂ) * (z - s)⁻¹ with hP_def
  have hP_mero : MeromorphicOn P (closedBall c R) := by
    rw [hP_def]
    refine MeromorphicOn.fun_sum fun s z _ => ?_
    exact (MeromorphicAt.const (ord s : ℂ) z).mul
      (((MeromorphicAt.id z).sub (MeromorphicAt.const s z)).inv)
  have hlogF_mero : MeromorphicOn (logDeriv F) (closedBall c R) := hF_mero.logDeriv
  -- `A := logDeriv F - P` is pole-free, so its circle integral vanishes.
  have hA0 : circleIntegral (fun z => logDeriv F z - P z) c R = 0 := by
    refine circleIntegral_eq_zero_of_nonneg_meromorphicOrderAt hR (hlogF_mero.sub hP_mero) ?_
    intro z hz
    by_cases hzS : z ∈ S
    · -- Pole point: the principal part cancels the simple pole of `logDeriv F`.
      have hz_ord : meromorphicOrderAt F z = (ord z : WithTop ℤ) := (hordF z hz).trans (hord z hzS)
      obtain ⟨g, hg_an, hg_ne, hg_germ⟩ :=
        logDeriv_eventuallyEq_principalPart (hF_mero z hz) hz_ord
      have hA_eq : (fun w => logDeriv F w - P w) =ᶠ[𝓝[≠] z]
          fun w => logDeriv g w - ∑ s ∈ S.erase z, (ord s : ℂ) * (w - s)⁻¹ := by
        filter_upwards [hg_germ] with w hw
        simp only [hP_def, ← Finset.add_sum_erase S (fun s => (ord s : ℂ) * (w - s)⁻¹) hzS]
        rw [hw]; ring
      have hrest_an : AnalyticAt ℂ (fun w => ∑ s ∈ S.erase z, (ord s : ℂ) * (w - s)⁻¹) z :=
        Finset.analyticAt_fun_sum _ fun s hs =>
          analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
            (sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase hs))))
      rw [meromorphicOrderAt_congr hA_eq]
      exact ((analyticAt_logDeriv_of_analyticAt hg_an hg_ne).sub hrest_an).meromorphicOrderAt_nonneg
    · -- Regular point: `A` is analytic there.
      have hz_off := hoffF z hz hzS
      have hP_an : AnalyticAt ℂ P z := by
        rw [hP_def]
        refine Finset.analyticAt_fun_sum _ fun s hsS =>
          analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 ?_))
        rintro rfl; exact hzS hsS
      exact ((analyticAt_logDeriv_of_analyticAt hz_off.1 hz_off.2).sub
        hP_an).meromorphicOrderAt_nonneg
  -- `∮ P = 2πi · ∑ ord`.
  have hP_intble : ∀ s ∈ S, CircleIntegrable (fun z => (ord s : ℂ) * (z - s)⁻¹) c R := fun s hsS =>
    ContinuousOn.circleIntegrable hR.le (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀
        fun z hz => sub_ne_zero.2 (hzs_ne z hz s hsS)))
  have hPint : circleIntegral P c R = 2 * (Real.pi : ℂ) * Complex.I * (∑ z ∈ S, (ord z : ℂ)) := by
    have hterm : ∀ s ∈ S, (∮ z in C(c, R), (ord s : ℂ) * (z - s)⁻¹)
        = (ord s : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := fun s hsS => by
      rw [circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_inv_of_mem_ball (hS (Finset.mem_coe.2 hsS))]
    rw [hP_def, circleIntegral.integral_fun_sum hP_intble, Finset.sum_congr rfl hterm,
      ← Finset.sum_mul]
    ring
  -- Continuity on the circle gives integrability, then split the integral.
  have hlogF_cont : ContinuousOn (logDeriv F) (sphere c R) := fun z hz =>
    (analyticAt_logDeriv_of_analyticAt
      (hoffF z (sphere_subset_closedBall hz) (hsphere_notS z hz)).1
      (hoffF z (sphere_subset_closedBall hz) (hsphere_notS z hz)).2).continuousAt.continuousWithinAt
  have hP_cont : ContinuousOn P (sphere c R) := by
    rw [hP_def]
    exact continuousOn_finsetSum S fun s hsS => continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 (hzs_ne z hz s hsS))
  -- `∮ logDeriv F = ∮ (logDeriv F - P) + ∮ P = 0 + ∮ P`.
  have hsub := (circleIntegral.integral_sub (ContinuousOn.circleIntegrable hR.le hlogF_cont)
    (ContinuousOn.circleIntegrable hR.le hP_cont)).symm
  rw [hA0, sub_eq_zero] at hsub
  rw [hsub, hPint]

end TauCeti.Contour
