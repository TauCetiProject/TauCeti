/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.Analysis.Contour.Residue.Theorem

/-!
# Power sums of the zeros inside a circle

Let `g` be analytic on the closed disc `closedBall 0 R`. Its zeros in the open disc, counted with
multiplicity, form a finite multiset `TauCeti.Contour.zeroMultiset`, read off from Mathlib's
`MeromorphicOn.divisor`. When `g` has no zero on the circle `sphere 0 R`, the multiplicity of each
point of the closed disc is its order of vanishing, and the residue theorem applied to
`φ · g' / g` gives the **weighted argument principle**

`∑_{a ∈ zeros} φ(a) = (2πi)⁻¹ ∮_{C(0,R)} φ(ζ) g'(ζ) / g(ζ) dζ`

for every `φ` analytic on the closed disc. For `φ = 1` this is the argument principle; for
`φ(ζ) = ζᵏ` it expresses the power sums of the zeros as contour integrals. Since the right side
depends analytically on parameters in `g`, so do the power sums, and through Newton's identities
the elementary symmetric functions of the zeros: this is how the Weierstrass preparation theorem
and the base-independence of confined divisors are proved.

## Main definitions

* `TauCeti.Contour.zeroMultiset hg`: the zeros of `g` in `ball 0 R`, counted with multiplicity
  (`TauCeti.Contour.natCast_count_zeroMultiset`).

## Main results

* `TauCeti.Contour.mem_ball_of_mem_zeroMultiset`: the zeros lie in the open disc.
* `TauCeti.Contour.meromorphicOrderAt_eq_count_zeroMultiset` and
  `TauCeti.Contour.analyticOrderAt_eq_count_zeroMultiset`: on the closed disc, the multiplicity of
  a point is the order of vanishing of `g` there.
* `TauCeti.Contour.sum_map_zeroMultiset_eq_circleIntegral`: the weighted argument principle.
-/

public section

open Complex Metric Real Set

namespace TauCeti.Contour

/-- The multiset of zeros of an analytic function `g` in `ball 0 R`, counted with multiplicity via
`MeromorphicOn.divisor` (see `TauCeti.Contour.natCast_count_zeroMultiset`). -/
noncomputable def zeroMultiset {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) : Multiset ℂ :=
  (Finsupp.ofSupportFinite (fun z ↦ (MeromorphicOn.divisor g (ball 0 R) z).toNat) <|
    (MeromorphicOn.divisor_ball_support_finite hg.meromorphicOn).subset fun z hz ↦
      Function.mem_support.2 fun h0 ↦ Function.mem_support.1 hz (by simp [h0])).toMultiset

/-- The multiplicity of a point in `zeroMultiset` is the value of Mathlib's
`MeromorphicOn.divisor` of `g` on `ball 0 R` there. -/
theorem natCast_count_zeroMultiset {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (z : ℂ) :
    (Multiset.count z (zeroMultiset hg) : ℤ) = MeromorphicOn.divisor g (ball 0 R) z := by
  rw [zeroMultiset, Finsupp.count_toMultiset, Finsupp.ofSupportFinite_coe]
  exact Int.toNat_of_nonneg
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hg.mono ball_subset_closedBall) z)

/-- The zeros counted by `zeroMultiset` lie in the open disc. -/
theorem mem_ball_of_mem_zeroMultiset {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) {α : ℂ} (hα : α ∈ zeroMultiset hg) :
    α ∈ ball 0 R := by
  refine (MeromorphicOn.divisor g (ball 0 R)).supportWithinDomain
    (Function.mem_support.2 fun h0 ↦ ?_)
  have h := natCast_count_zeroMultiset hg α
  rw [h0, Nat.cast_eq_zero, Multiset.count_eq_zero] at h
  exact h hα

/-- If `g` has no zero on `sphere 0 R`, the multiplicity of a point of the closed disc in
`zeroMultiset` is the meromorphic order of `g` there. -/
theorem meromorphicOrderAt_eq_count_zeroMultiset {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hsphere : ∀ ζ ∈ sphere 0 R, g ζ ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall 0 R) :
    meromorphicOrderAt g z = ((Multiset.count z (zeroMultiset hg) : ℕ) : WithTop ℤ) := by
  classical
  rcases (ball_union_sphere (x := (0 : ℂ)) (ε := R) ▸ hz) with hzb | hzs
  · rw [← WithTop.coe_untop₀_of_ne_top
        (hg.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero hsphere hz),
      ← (hg.mono ball_subset_closedBall).meromorphicOn.divisor_apply hzb,
      ← natCast_count_zeroMultiset hg z]
    norm_cast
  · have hc0 : Multiset.count z (zeroMultiset hg) = 0 := Multiset.count_eq_zero.2 fun hmem ↦
      (mem_ball.1 (mem_ball_of_mem_zeroMultiset hg hmem)).ne (mem_sphere.1 hzs)
    rw [(hg z hz).meromorphicOrderAt_eq, (hg z hz).analyticOrderAt_eq_zero.2 (hsphere z hzs), hc0]
    simp

/-- If `g` has no zero on `sphere 0 R`, the multiplicity of a point of the closed disc in
`zeroMultiset` is the order of vanishing of `g` there. -/
theorem analyticOrderAt_eq_count_zeroMultiset {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hsphere : ∀ ζ ∈ sphere 0 R, g ζ ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall 0 R) :
    analyticOrderAt g z = Multiset.count z (zeroMultiset hg) := by
  have h := meromorphicOrderAt_eq_count_zeroMultiset hg hsphere hz
  rw [(hg z hz).meromorphicOrderAt_eq] at h
  exact ENat.map_natCast_injective (by simpa using h)

/-- **The weighted argument principle.** If `g` is analytic on `closedBall 0 R` and has no zero on
`sphere 0 R`, then for every `φ` analytic on the closed disc, the sum of `φ` over the zeros of `g`
in the open disc, counted with multiplicity, is `(2πi)⁻¹ ∮ φ g' / g`. -/
theorem sum_map_zeroMultiset_eq_circleIntegral {g φ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hsphere : ∀ ζ ∈ sphere 0 R, g ζ ≠ 0)
    (hφ : AnalyticOnNhd ℂ φ (closedBall 0 R)) :
    ((zeroMultiset hg).map φ).sum = (2 * π * I)⁻¹ * ∮ ζ in C(0, R), φ ζ * logDeriv g ζ := by
  classical
  set S := (zeroMultiset hg).toFinset
  have hgb : AnalyticOnNhd ℂ g (ball 0 R) := hg.mono ball_subset_closedBall
  have hS_ball : (S : Set ℂ) ⊆ ball 0 R := fun z hz ↦
    mem_ball_of_mem_zeroMultiset hg (Multiset.mem_toFinset.1 hz)
  have hsupp : ∀ z ∈ closedBall 0 R,
      meromorphicOrderAt (fun ζ ↦ φ ζ * logDeriv g ζ) z < 0 → z ∈ S := by
    intro z hz hneg
    by_contra hzS
    have hc0 : Multiset.count z (zeroMultiset hg) = 0 :=
      Multiset.count_eq_zero.2 fun h ↦ hzS (Multiset.mem_toFinset.2 h)
    have hord0 := meromorphicOrderAt_eq_count_zeroMultiset hg hsphere hz
    rw [hc0, (hg z hz).meromorphicOrderAt_eq] at hord0
    have hgz : g z ≠ 0 := (hg z hz).analyticOrderAt_eq_zero.1 (by simpa using hord0)
    exact not_le_of_gt hneg
      ((hφ z hz).fun_mul (analyticAt_logDeriv_of_analyticAt (hg z hz) hgz)
        |>.meromorphicOrderAt_nonneg)
  have hres := classicalResidueTheorem_circle_of_meromorphicOrderAt_neg
    (f := fun ζ ↦ φ ζ * logDeriv g ζ) hR S
    (hφ.meromorphicOn.mul hg.meromorphicOn.logDeriv) hS_ball hsupp
  have hsum_multiset : ((zeroMultiset hg).map φ).sum =
      ∑ s ∈ S, (MeromorphicOn.divisor g (ball 0 R) s : ℂ) * φ s := by
    rw [Finset.sum_multiset_map_count]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [nsmul_eq_mul, ← Int.cast_natCast, natCast_count_zeroMultiset]
  have hsum_res : ∑ s ∈ S, residue (fun ζ ↦ φ ζ * logDeriv g ζ) s =
      ∑ s ∈ S, (MeromorphicOn.divisor g (ball 0 R) s : ℂ) * φ s := by
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hsb := hS_ball hs
    have hsc := ball_subset_closedBall hsb
    have hord : meromorphicOrderAt g s = (MeromorphicOn.divisor g (ball 0 R) s : WithTop ℤ) := by
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

end TauCeti.Contour
