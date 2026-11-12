/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import TauCeti.Analysis.Analytic.ZeroCount
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.Analysis.Meromorphic.Order

/-!
# Power sums of the zeros inside a circle

Let `g` be analytic on the closed disc `closedBall c R`, and let `AnalyticOnNhd.zeroMultiset` be
its zeros in the open disc, counted with multiplicity. When `g` has no zero on the circle
`sphere c R`, the residue theorem applied to `φ · g' / g` gives the **weighted argument principle**

`∑_{a ∈ zeros} φ(a) = (2πi)⁻¹ ∮_{C(c,R)} φ(ζ) g'(ζ) / g(ζ) dζ`

for every `φ` analytic on the closed disc. For `φ = 1` this is the argument principle; for
`φ(ζ) = ζᵏ` it expresses the power sums of the zeros as contour integrals. Since the right side
depends analytically on parameters in `g`, so do these sums, and through Newton's identities
the elementary symmetric functions of the zeros: this is how the Weierstrass preparation theorem
and the base-independence of confined divisors are proved.

## Main results

* `TauCeti.Contour.sum_map_zeroMultiset_eq_circleIntegral`: the weighted argument principle.
* `TauCeti.Contour.sum_map_zeroMultiset_eq_circleIntegral_fderiv`: for a slice
  `w ↦ f (x, w)` of a function on `E × ℂ`, the sum of `φ` over its zeros is the contour integral
  of `φ ∂_w f / f`; `TauCeti.Contour.sum_map_pow_zeroMultiset_eq_circleIntegral_fderiv` is the
  case of the power sums.
* `TauCeti.Contour.differentiableOn_sum_map_zeroMultiset` and
  `TauCeti.Contour.differentiableOn_sum_map_pow_zeroMultiset`: in a holomorphic family of slices,
  these sums depend holomorphically on the parameter.
* `TauCeti.Contour.card_zeroMultiset_eq_of_isPreconnected`: the number of zeros is constant on a
  preconnected parameter set.
-/

public section

open Complex Metric Real Set

namespace TauCeti.Contour

/-- **The weighted argument principle.** If `g` is analytic on `closedBall c R` and has no zero on
`sphere c R`, then for every `φ` analytic on the closed disc, the sum of `φ` over the zeros of `g`
in the open disc, counted with multiplicity, is `(2πi)⁻¹ ∮ φ g' / g`. -/
theorem sum_map_zeroMultiset_eq_circleIntegral {g φ : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hsphere : ∀ ζ ∈ sphere c R, g ζ ≠ 0)
    (hφ : AnalyticOnNhd ℂ φ (closedBall c R)) :
    (hg.zeroMultiset.map φ).sum = (2 * π * I)⁻¹ * ∮ ζ in C(c, R), φ ζ * logDeriv g ζ := by
  classical
  set S := hg.zeroMultiset.toFinset
  have hgb : AnalyticOnNhd ℂ g (ball c R) := hg.mono ball_subset_closedBall
  have hS_ball : (S : Set ℂ) ⊆ ball c R := fun z hz ↦
    hg.mem_ball_of_mem_zeroMultiset (Multiset.mem_toFinset.1 hz)
  have hsupp : ∀ z ∈ closedBall c R,
      meromorphicOrderAt (fun ζ ↦ φ ζ * logDeriv g ζ) z < 0 → z ∈ S := by
    intro z hz hneg
    by_contra hzS
    have hc0 : Multiset.count z hg.zeroMultiset = 0 :=
      Multiset.count_eq_zero.2 fun h ↦ hzS (Multiset.mem_toFinset.2 h)
    have hord0 := hg.meromorphicOrderAt_eq_count_zeroMultiset hsphere hz
    rw [hc0, (hg z hz).meromorphicOrderAt_eq] at hord0
    have hgz : g z ≠ 0 := (hg z hz).analyticOrderAt_eq_zero.1 (by simpa using hord0)
    exact not_le_of_gt hneg
      ((hφ z hz).fun_mul (analyticAt_logDeriv_of_analyticAt (hg z hz) hgz)
        |>.meromorphicOrderAt_nonneg)
  have hres := classicalResidueTheorem_circle_of_meromorphicOrderAt_neg
    (f := fun ζ ↦ φ ζ * logDeriv g ζ) hR S
    (hφ.meromorphicOn.mul hg.meromorphicOn.logDeriv) hS_ball hsupp
  have hsum_multiset : (hg.zeroMultiset.map φ).sum =
      ∑ s ∈ S, (MeromorphicOn.divisor g (ball c R) s : ℂ) * φ s := by
    rw [Finset.sum_multiset_map_count]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [nsmul_eq_mul, ← Int.cast_natCast, AnalyticOnNhd.natCast_count_zeroMultiset]
  have hsum_res : ∑ s ∈ S, residue (fun ζ ↦ φ ζ * logDeriv g ζ) s =
      ∑ s ∈ S, (MeromorphicOn.divisor g (ball c R) s : ℂ) * φ s := by
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hsb := hS_ball hs
    have hsc := ball_subset_closedBall hsb
    have hord : meromorphicOrderAt g s = (MeromorphicOn.divisor g (ball c R) s : WithTop ℤ) := by
      rw [hgb.meromorphicOn.divisor_apply hsb, WithTop.coe_untop₀_of_ne_top
        (hg.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero hsphere hsc)]
    have hgs := (hg s hsc).meromorphicAt
    have hlim := ((hφ s hsc).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (tendsto_sub_mul_nhds_residue hgs.logDeriv
        (by simpa using neg_one_le_meromorphicOrderAt_logDeriv hgs))
    rw [residue_logDeriv_eq_meromorphicOrderAt hgs hord, mul_comm (φ s)] at hlim
    exact residue_eq_of_tendsto_sub_mul ((hφ s hsc).meromorphicAt.mul hgs.logDeriv)
      (hlim.congr fun ζ ↦ by ring)
  rw [hres, hsum_res, inv_mul_cancel_left₀ two_pi_I_ne_zero, hsum_multiset]

section Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The weighted argument principle for a slice.** Let `f : E × ℂ → ℂ` be analytic at every
point of `{x} × closedBall c R` with no zero on `{x} × sphere c R`. Then for every `φ` analytic on
the closed disc, the sum of `φ` over the zeros of `w ↦ f (x, w)` in `ball c R`, counted with
multiplicity, is `(2πi)⁻¹ ∮ φ ∂_w f / f`. -/
theorem sum_map_zeroMultiset_eq_circleIntegral_fderiv {f : E × ℂ → ℂ} {φ : ℂ → ℂ} {x : E}
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hf : ∀ ζ ∈ closedBall c R, AnalyticAt ℂ f (x, ζ))
    (hsphere : ∀ ζ ∈ sphere c R, f (x, ζ) ≠ 0) (hφ : AnalyticOnNhd ℂ φ (closedBall c R)) :
    ((AnalyticOnNhd.zeroMultiset (g := fun w ↦ f (x, w)) fun w hw ↦
        (hf w hw).curry_right).map φ).sum =
      (2 * π * I)⁻¹ * ∮ ζ in C(c, R), φ ζ * (fderiv ℂ f (x, ζ) (0, 1) / f (x, ζ)) := by
  refine (sum_map_zeroMultiset_eq_circleIntegral hR (fun w hw ↦ (hf w hw).curry_right) hsphere
    hφ).trans ?_
  refine congrArg (_ * ·) (circleIntegral.integral_congr hR.le fun ζ hζ ↦ ?_)
  have hderiv : deriv (fun w ↦ f (x, w)) ζ = fderiv ℂ f (x, ζ) (0, 1) :=
    ((hf ζ (sphere_subset_closedBall hζ)).differentiableAt.hasFDerivAt.comp_hasDerivAt ζ
      ((hasDerivAt_const ζ x).prodMk (hasDerivAt_id' ζ))).deriv
  rw [logDeriv_apply, hderiv]

/-- **Power sums of the zeros of a slice.** Let `f : E × ℂ → ℂ` be analytic at every point of
`{x} × closedBall c R` with no zero on `{x} × sphere c R`. Then the `k`-th power sum of the zeros
of `w ↦ f (x, w)` in `ball c R`, counted with multiplicity, is `(2πi)⁻¹ ∮ ζᵏ ∂_w f / f`. -/
theorem sum_map_pow_zeroMultiset_eq_circleIntegral_fderiv {f : E × ℂ → ℂ} {x : E} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : ∀ ζ ∈ closedBall c R, AnalyticAt ℂ f (x, ζ))
    (hsphere : ∀ ζ ∈ sphere c R, f (x, ζ) ≠ 0) (k : ℕ) :
    ((AnalyticOnNhd.zeroMultiset (g := fun w ↦ f (x, w)) fun w hw ↦
        (hf w hw).curry_right).map (· ^ k)).sum =
      (2 * π * I)⁻¹ * ∮ ζ in C(c, R), ζ ^ k * (fderiv ℂ f (x, ζ) (0, 1) / f (x, ζ)) :=
  sum_map_zeroMultiset_eq_circleIntegral_fderiv hR hf hsphere (analyticOnNhd_id.pow k)

/-- **Sums over zeros in a holomorphic family.** Let `f : E × ℂ → ℂ` be analytic at every point of
`U ×ˢ closedBall c R`, for an open set `U`, with no zero on `U ×ˢ sphere c R`, and let `φ` be
analytic on the closed disc. If `Z x` is the multiset of zeros of `w ↦ f (x, w)` in `ball c R` for
each `x ∈ U`, then the sum of `φ` over `Z x` is a holomorphic function of `x` on `U`. -/
theorem differentiableOn_sum_map_zeroMultiset {f : E × ℂ → ℂ} {φ : ℂ → ℂ} {U : Set E}
    (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ x ∈ U, ∀ ζ ∈ closedBall c R, AnalyticAt ℂ f (x, ζ))
    (hsphere : ∀ x ∈ U, ∀ ζ ∈ sphere c R, f (x, ζ) ≠ 0)
    (hφ : AnalyticOnNhd ℂ φ (closedBall c R)) {Z : E → Multiset ℂ}
    (hZ : ∀ x (hx : x ∈ U), Z x =
      AnalyticOnNhd.zeroMultiset (g := fun w ↦ f (x, w)) fun w hw ↦ (hf x hx w hw).curry_right) :
    DifferentiableOn ℂ (fun x ↦ ((Z x).map φ).sum) U := by
  intro x hx
  have hint : DifferentiableAt ℂ (fun y ↦ (2 * π * I)⁻¹ *
      ∮ ζ in C(c, R), φ ζ * (fderiv ℂ f (y, ζ) (0, 1) / f (y, ζ))) x := by
    refine (HasFDerivAt.differentiableAt (TauCeti.hasFDerivAt_circleIntegral
      (f := fun q : E × ℂ ↦ φ q.2 * (fderiv ℂ f q (0, 1) / f q)) fun ζ hζ ↦ ?_)).const_mul _
    rw [abs_of_pos hR] at hζ
    have hfx := hf x hx ζ (sphere_subset_closedBall hζ)
    exact ((hφ ζ (sphere_subset_closedBall hζ)).comp_of_eq analyticAt_snd rfl).fun_mul
      ((((ContinuousLinearMap.apply ℂ ℂ ((0 : E), (1 : ℂ))).analyticAt _).comp_of_eq
        hfx.fderiv rfl).fun_div hfx (hsphere x hx ζ hζ))
  refine (hint.congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy ↦ ?_))
    |>.differentiableWithinAt
  rw [hZ y hy]
  exact sum_map_zeroMultiset_eq_circleIntegral_fderiv hR (hf y hy) (hsphere y hy) hφ

/-- **Power sums of zeros in a holomorphic family.** Under the hypotheses of
`TauCeti.Contour.differentiableOn_sum_map_zeroMultiset`, every power sum of the zeros `Z x` of
`w ↦ f (x, w)` in `ball c R` is a holomorphic function of `x` on `U`. -/
theorem differentiableOn_sum_map_pow_zeroMultiset {f : E × ℂ → ℂ} {U : Set E} (hU : IsOpen U)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hf : ∀ x ∈ U, ∀ ζ ∈ closedBall c R, AnalyticAt ℂ f (x, ζ))
    (hsphere : ∀ x ∈ U, ∀ ζ ∈ sphere c R, f (x, ζ) ≠ 0) {Z : E → Multiset ℂ}
    (hZ : ∀ x (hx : x ∈ U), Z x =
      AnalyticOnNhd.zeroMultiset (g := fun w ↦ f (x, w)) fun w hw ↦ (hf x hx w hw).curry_right)
    (k : ℕ) : DifferentiableOn ℂ (fun x ↦ ((Z x).map (· ^ k)).sum) U :=
  differentiableOn_sum_map_zeroMultiset hU hR hf hsphere (analyticOnNhd_id.pow k) hZ

/-- **Constancy of the number of zeros in a holomorphic family.** Under the hypotheses of
`TauCeti.Contour.differentiableOn_sum_map_zeroMultiset`, if `U` is moreover preconnected,
then the number of zeros of `w ↦ f (x, w)` in `ball c R` does not depend on `x ∈ U`. -/
theorem card_zeroMultiset_eq_of_isPreconnected {f : E × ℂ → ℂ} {U : Set E} (hU : IsOpen U)
    (hU_conn : IsPreconnected U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ x ∈ U, ∀ ζ ∈ closedBall c R, AnalyticAt ℂ f (x, ζ))
    (hsphere : ∀ x ∈ U, ∀ ζ ∈ sphere c R, f (x, ζ) ≠ 0) {Z : E → Multiset ℂ}
    (hZ : ∀ x (hx : x ∈ U), Z x =
      AnalyticOnNhd.zeroMultiset (g := fun w ↦ f (x, w)) fun w hw ↦ (hf x hx w hw).curry_right)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) : (Z x).card = (Z y).card := by
  have hcont : ContinuousOn (fun x ↦ (Z x).card) U :=
    Nat.isClosedEmbedding_coe_real.isInducing.continuousOn_iff.2
      ((Complex.continuous_re.comp_continuousOn
        (differentiableOn_sum_map_pow_zeroMultiset hU hR hf hsphere hZ 0).continuousOn).congr
        fun _ _ ↦ by simp)
  exact hU_conn.constant hcont hx hy

end Family

end TauCeti.Contour
