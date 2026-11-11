/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Contour.Argument.PowerSum
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Convex.PathConnected
import TauCeti.RingTheory.Polynomial.PrescribedPowerSums

/-!
# Holomorphic divisors confined in the transverse direction

Let `E` be a complex normed space, the *base*, and let `f : E × ℂ → ℂ` be holomorphic. For each
base point `x`, the transverse slice `w ↦ f (x, w)` is an entire function of one variable, with
its divisor of zeros. Suppose the zeros are **confined**: `f (x, w) ≠ 0` whenever `‖w‖ ≥ K`, for
one constant `K` and every `x`. Then the transverse divisor does not depend on the base point:
there is a single multiset `s` of points of the open disc of radius `K` such that the order of
vanishing of every slice `w ↦ f (x, w)` at every `w` is the multiplicity of `w` in `s`
(`TauCeti.exists_forall_analyticOrderAt_eq_count`).

This is the classification step for the holomorphic zero divisors that arise as rescaled limits
of Seiberg–Witten solutions along a pseudoholomorphic curve. In Taubes's analysis such a limit
lives on `ℂ_base × ℂ_normal`, its zero divisor is holomorphic and confined to a bounded normal
disc, and the conclusion here says that the divisor is the product of `ℂ_base` with a fixed
divisor of `ℂ_normal`. A confined holomorphic divisor of `ℂ × ℂ` is therefore never a nontrivial
holomorphic family of plane divisors.

The proof is the classical one through symmetric functions. Choose `R > K`. For each `x`, the
`k`-th power sum of the zeros of the slice in the disc of radius `R` is the contour integral
`(2πi)⁻¹ ∮ ζᵏ ∂_w f (x, ζ) / f (x, ζ)`
(`TauCeti.Contour.sum_map_pow_zeroMultiset_eq_circleIntegral_fderiv`), which is holomorphic in `x`
(`TauCeti.Contour.differentiableOn_sum_map_pow_zeroMultiset`). For `k = 0` it is
the number of zeros, which is therefore constant, say `N`. The `k`-th power sum is then bounded by
`N Rᵏ`, so it is constant by Liouville's theorem. By Newton's identities the power sums determine
the multiset of zeros (`TauCeti.roots_newtonPolynomial_sum_map_pow`).

## Main results

* `TauCeti.exists_forall_analyticOrderAt_eq_count`: a holomorphic function on `E × ℂ` whose zeros
  are confined to `‖w‖ < K` has a base-independent transverse divisor, given by a multiset of
  points of norm less than `K`.
* `TauCeti.analyticOrderAt_eq_of_forall_le_norm_ne_zero`: the same conclusion, comparing the
  slices over two base points.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1, for the
  symmetric functions of the zeros of a holomorphic family.
-/

public section

open Complex Metric Real Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Base-independence of a confined transverse divisor.** Let `f : E × ℂ → ℂ` be holomorphic,
and suppose that `f (x, w) ≠ 0` whenever `K ≤ ‖w‖`. Then there is a multiset `s` of points of
norm less than `K` such that for every base point `x` and every `w`, the order of vanishing of
`w ↦ f (x, w)` at `w` is the multiplicity of `w` in `s`. -/
theorem exists_forall_analyticOrderAt_eq_count {f : E × ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    {K : ℝ} (hK : ∀ x w, K ≤ ‖w‖ → f (x, w) ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧
      ∀ x w, analyticOrderAt (fun w ↦ f (x, w)) w = s.count w := by
  classical
  set R := max K 0 + 1
  have hR : 0 < R := by positivity
  have hKR : K < R := by grind
  have hf' : ∀ x ∈ (univ : Set E), ∀ ζ ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ f (x, ζ) :=
    fun x _ ζ _ ↦ hf (x, ζ) trivial
  have hslice (x : E) : AnalyticOnNhd ℂ (fun w ↦ f (x, w)) (closedBall 0 R) :=
    fun w _ ↦ (hf (x, w) trivial).curry_right
  have hsphere (x : E) : ∀ ζ ∈ sphere (0 : ℂ) R, f (x, ζ) ≠ 0 := fun ζ hζ ↦
    hK x ζ (by rw [mem_sphere_zero_iff_norm.1 hζ]; exact hKR.le)
  set Z : E → Multiset ℂ := fun x ↦ Contour.zeroMultiset (hslice x)
  have hdiff (k : ℕ) : Differentiable ℂ fun x ↦ ((Z x).map (· ^ k)).sum :=
    differentiableOn_univ.1 <| Contour.differentiableOn_sum_map_pow_zeroMultiset isOpen_univ hR
      hf' (fun x _ ↦ hsphere x) (fun _ _ ↦ rfl) k
  -- The number of zeros is the zeroth power sum: it is continuous and integer valued, hence
  -- constant on the connected base.
  have hcard (x : E) : (Z x).card = (Z 0).card :=
    Contour.card_zeroMultiset_eq_of_isPreconnected isOpen_univ
      (convex_univ : Convex ℝ (univ : Set E)).isPreconnected hR hf' (fun x _ ↦ hsphere x)
      (fun _ _ ↦ rfl) trivial trivial
  -- Every zero lies in `ball 0 R`, so the `k`-th power sum is bounded by `card (Z 0) * R ^ k`,
  -- and Liouville's theorem makes it constant.
  have hpow (k : ℕ) (x : E) : ((Z x).map (· ^ k)).sum = ((Z 0).map (· ^ k)).sum := by
    refine (hdiff k).apply_eq_apply_of_bounded ?_ x 0
    refine isBounded_iff_forall_norm_le.2 ⟨(Z 0).card * R ^ k, ?_⟩
    rintro _ ⟨y, rfl⟩
    refine (norm_multiset_sum_le _).trans ?_
    rw [Multiset.map_map, ← hcard y]
    refine (Multiset.sum_le_card_nsmul _ (R ^ k) fun t ht ↦ ?_).trans_eq (by simp)
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 ht
    rw [Function.comp_apply, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg a)
      (mem_ball_zero_iff.1 (Contour.mem_ball_of_mem_zeroMultiset (hslice y) ha)).le k
  -- Newton's identities recover each multiset of zeros from its power sums.
  have hZ (x : E) : Z x = Z 0 := by
    rw [← roots_newtonPolynomial_sum_map_pow (Z x), ← roots_newtonPolynomial_sum_map_pow (Z 0),
      hcard x, funext fun k ↦ hpow k x]
  have horder (x : E) {w : ℂ} (hw : w ∈ closedBall 0 R) :
      analyticOrderAt (fun w ↦ f (x, w)) w = (Z 0).count w := by
    rw [← hZ x]
    exact Contour.analyticOrderAt_eq_count_zeroMultiset (hslice x) (hsphere x) hw
  have hmem (a : ℂ) (ha : a ∈ Z 0) : ‖a‖ < K := by
    by_contra hKa
    exact hK 0 a (not_lt.1 hKa) ((Contour.mem_zeroMultiset_iff (hslice 0) (hsphere 0)).1 ha).2
  refine ⟨Z 0, hmem, fun x w ↦ ?_⟩
  by_cases hKw : K ≤ ‖w‖
  · rw [(hf (x, w) trivial).curry_right.analyticOrderAt_eq_zero.2 (hK x w hKw),
      Multiset.count_eq_zero.2 fun hw ↦ (hmem w hw).not_ge hKw, Nat.cast_zero]
  · exact horder x (mem_closedBall_zero_iff.2 (by grind))

/-- **Base-independence of a confined transverse divisor, pairwise form.** If `f : E × ℂ → ℂ` is
holomorphic and `f (x, w) ≠ 0` whenever `K ≤ ‖w‖`, then the slices `w ↦ f (x, w)` and
`w ↦ f (y, w)` over any two base points have the same order of vanishing at every point. -/
theorem analyticOrderAt_eq_of_forall_le_norm_ne_zero {f : E × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {K : ℝ} (hK : ∀ x w, K ≤ ‖w‖ → f (x, w) ≠ 0) (x y : E)
    (w : ℂ) :
    analyticOrderAt (fun w ↦ f (x, w)) w = analyticOrderAt (fun w ↦ f (y, w)) w := by
  obtain ⟨s, -, hs⟩ := exists_forall_analyticOrderAt_eq_count hf hK
  rw [hs, hs]

end TauCeti
