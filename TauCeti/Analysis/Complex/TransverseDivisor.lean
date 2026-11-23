/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Contour.Argument.PowerSum
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.RemovableSingularity
import TauCeti.RingTheory.Polynomial.PrescribedPowerSums

/-!
# Holomorphic divisors confined in the transverse direction

Let `E` be a complex normed space, the *base*, and let `f : E × ℂ → ℂ` be holomorphic. For each
base point `x`, the transverse slice `w ↦ f (x, w)` is an entire function of one variable, with
its divisor of zeros. Suppose the zeros are **confined**: `f (x, w) ≠ 0` whenever `‖w‖ ≥ K`, for
one constant `K` and every `x`. Then the transverse divisor does not depend on the base point:
there is a single multiset `s` of points of the open disc of radius `K` such that the order of
vanishing of every slice `w ↦ f (x, w)` at every `w` is the multiplicity of `w` in `s`
(`Differentiable.exists_forall_analyticOrderAt_eq_count`).

This is the classification step for the holomorphic zero divisors that arise as rescaled limits
of Seiberg–Witten solutions along a pseudoholomorphic curve. In Taubes's analysis such a limit
lives on `ℂ_base × ℂ_normal`, its zero divisor is holomorphic and confined to a bounded normal
disc, and the conclusion here says that the divisor is the product of `ℂ_base` with a fixed
divisor of `ℂ_normal`. A confined holomorphic divisor of `ℂ × ℂ` is therefore never a nontrivial
holomorphic family of plane divisors.

Restricting `f` to the complex line through `0` and `x` reduces the statement to a base `ℂ`, where
a holomorphic function is analytic (`DifferentiableOn.analyticOnNhd_of_finiteDimensional`). For an
analytic `f`, the proof is the classical one through symmetric functions. Choose `R > K`. For each
`x`, the `k`-th power sum of the zeros of the slice in the disc of radius `R` is the contour
integral `(2πi)⁻¹ ∮ ζᵏ ∂_w f (x, ζ) / f (x, ζ)`
(`TauCeti.Contour.sum_map_pow_zeroMultiset_eq_circleIntegral_fderiv`), which is holomorphic in `x`
(`TauCeti.Contour.differentiableAt_sum_map_pow_zeroMultiset`). For `k = 0` it is
the number of zeros, which is therefore constant, say `N`. The `k`-th power sum is then bounded by
`N Rᵏ`, so it is constant by Liouville's theorem. By Newton's identities the power sums determine
the multiset of zeros (`TauCeti.roots_newtonPolynomial_sum_map_pow`).

When the base is finite-dimensional, a holomorphic `f` whose transverse divisor is a fixed multiset
`s` is divisible by the polynomial with that divisor: `f (x, w) = ∏_{a ∈ s} (w - a) * u (x, w)` for
a holomorphic `u` with no zeros (`Differentiable.exists_eq_prod_sub_mul`). The roots are divided
out one at a time. If `f` vanishes on the hyperplane `E × {c}`, the quotient `f (x, w) / (w - c)`
has bounded slices near `c`, since each slice is differentiable at `c`, so it extends
holomorphically across the hyperplane by the Riemann extension theorem
`TauCeti.exists_analyticOnNhd_prod_eqOn` (`Differentiable.exists_differentiable_eq_sub_mul`). The
order of vanishing of each slice drops by one at `c` and is unchanged elsewhere.

## Main results

* `Differentiable.exists_forall_analyticOrderAt_eq_count`: a holomorphic function on `E × ℂ` whose
  zeros are confined to `‖w‖ < K` has a base-independent transverse divisor, given by a multiset of
  points of norm less than `K`.
* `Differentiable.analyticOrderAt_eq_of_forall_le_norm_ne_zero`: the same conclusion, comparing the
  slices over two base points.
* `Differentiable.exists_differentiable_eq_sub_mul`: a holomorphic function on `E × ℂ` vanishing on
  `E × {c}` is `w - c` times a holomorphic function.
* `Differentiable.exists_eq_prod_sub_mul`: a holomorphic function on `E × ℂ` whose transverse
  divisor is a multiset `s` is `∏_{a ∈ s} (w - a)` times a holomorphic function with no zeros.

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

/-- The case of `Differentiable.exists_forall_analyticOrderAt_eq_count` where `f` is analytic. -/
private theorem exists_forall_analyticOrderAt_eq_count_of_analyticOnNhd {f : E × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ)
    {K : ℝ} (hK : ∀ x w, K ≤ ‖w‖ → f (x, w) ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧
      ∀ x w, analyticOrderAt (fun w ↦ f (x, w)) w = s.count w := by
  classical
  set R := max K 0 + 1
  have hR : 0 < R := by positivity
  have hKR : K < R := by grind
  have hf' (x : E) : ∀ ζ ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ f (x, ζ) :=
    fun ζ _ ↦ hf (x, ζ) trivial
  have hslice (x : E) : AnalyticOnNhd ℂ (fun w ↦ f (x, w)) (closedBall 0 R) :=
    fun w hw ↦ (hf' x w hw).curry_right
  have hsphere (x : E) : ∀ ζ ∈ sphere (0 : ℂ) R, f (x, ζ) ≠ 0 := fun ζ hζ ↦
    hK x ζ (by rw [mem_sphere_zero_iff_norm.1 hζ]; exact hKR.le)
  set Z : E → Multiset ℂ := fun x ↦ AnalyticOnNhd.zeroMultiset (fun w ↦ f (x, w)) (ball 0 R)
  have hdiff (k : ℕ) : Differentiable ℂ fun x ↦ ((Z x).map (· ^ k)).sum := fun x ↦
    Contour.differentiableAt_sum_map_pow_zeroMultiset (hf' x) (hsphere x) k
  -- The number of zeros is the zeroth power sum: it is continuous and integer valued, hence
  -- constant on the connected base.
  have hcard (x : E) : (Z x).card = (Z 0).card :=
    Contour.card_zeroMultiset_eq_of_isPreconnected isPreconnected_univ (fun x _ ↦ hf' x)
      (fun x _ ↦ hsphere x) trivial trivial
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
      (mem_ball_zero_iff.1 (AnalyticOnNhd.mem_of_mem_zeroMultiset ha)).le k
  -- Newton's identities recover each multiset of zeros from its power sums.
  have hZ (x : E) : Z x = Z 0 := by
    rw [← roots_newtonPolynomial_sum_map_pow (Z x), ← roots_newtonPolynomial_sum_map_pow (Z 0),
      hcard x, funext fun k ↦ hpow k x]
  have horder (x : E) {w : ℂ} (hw : w ∈ closedBall 0 R) :
      analyticOrderAt (fun w ↦ f (x, w)) w = (Z 0).count w := by
    rw [← hZ x]
    exact (hslice x).analyticOrderAt_eq_count_zeroMultiset (hsphere x) hw
  have hmem (a : ℂ) (ha : a ∈ Z 0) : ‖a‖ < K := by
    by_contra hKa
    exact hK 0 a (not_lt.1 hKa) (((hslice 0).mem_zeroMultiset_iff (hsphere 0)).1 ha).2
  refine ⟨Z 0, hmem, fun x w ↦ ?_⟩
  by_cases hKw : K ≤ ‖w‖
  · rw [(hf (x, w) trivial).curry_right.analyticOrderAt_eq_zero.2 (hK x w hKw),
      Multiset.count_eq_zero.2 fun hw ↦ (hmem w hw).not_ge hKw, Nat.cast_zero]
  · exact horder x (mem_closedBall_zero_iff.2 (by grind))

end TauCeti

namespace Differentiable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Base-independence of a confined transverse divisor.** Let `f : E × ℂ → ℂ` be holomorphic,
and suppose that `f (x, w) ≠ 0` whenever `K ≤ ‖w‖`. Then there is a multiset `s` of points of
norm less than `K` such that for every base point `x` and every `w`, the order of vanishing of
`w ↦ f (x, w)` at `w` is the multiplicity of `w` in `s`. -/
theorem exists_forall_analyticOrderAt_eq_count {f : E × ℂ → ℂ} (hf : Differentiable ℂ f)
    {K : ℝ} (hK : ∀ x w, K ≤ ‖w‖ → f (x, w) ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧
      ∀ x w, analyticOrderAt (fun w ↦ f (x, w)) w = s.count w := by
  -- On the complex line through `0` and `x`, `f` is a holomorphic function on `ℂ × ℂ`, hence
  -- analytic.
  have hline (x : E) : ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧
      ∀ (t : ℂ) w, analyticOrderAt (fun w ↦ f (t • x, w)) w = s.count w :=
    TauCeti.exists_forall_analyticOrderAt_eq_count_of_analyticOnNhd
      (f := fun p : ℂ × ℂ ↦ f (p.1 • x, p.2))
      ((hf.comp ((differentiable_fst.smul_const x).prodMk differentiable_snd)).differentiableOn
        |>.analyticOnNhd_of_finiteDimensional isOpen_univ)
      fun t w hw ↦ hK _ w hw
  have hbase (x : E) (w : ℂ) :
      analyticOrderAt (fun w ↦ f (x, w)) w = analyticOrderAt (fun w ↦ f (0, w)) w := by
    obtain ⟨s, -, hs⟩ := hline x
    simpa using (hs 1 w).trans (hs 0 w).symm
  obtain ⟨s, hsK, hs⟩ := hline 0
  exact ⟨s, hsK, fun x w ↦ (hbase x w).trans (by simpa using hs 0 w)⟩

/-- **Base-independence of a confined transverse divisor, pairwise form.** If `f : E × ℂ → ℂ` is
holomorphic and `f (x, w) ≠ 0` whenever `K ≤ ‖w‖`, then the slices `w ↦ f (x, w)` and
`w ↦ f (y, w)` over any two base points have the same order of vanishing at every point. -/
theorem analyticOrderAt_eq_of_forall_le_norm_ne_zero {f : E × ℂ → ℂ}
    (hf : Differentiable ℂ f) {K : ℝ} (hK : ∀ x w, K ≤ ‖w‖ → f (x, w) ≠ 0) (x y : E)
    (w : ℂ) :
    analyticOrderAt (fun w ↦ f (x, w)) w = analyticOrderAt (fun w ↦ f (y, w)) w := by
  obtain ⟨s, -, hs⟩ := hf.exists_forall_analyticOrderAt_eq_count hK
  rw [hs, hs]

/-! ### Dividing out a base-independent transverse divisor -/

variable [FiniteDimensional ℂ E]

/-- **Division by `w - c`.** If `f : E × ℂ → ℂ` is holomorphic on the product of a
finite-dimensional complex space with `ℂ` and vanishes on the hyperplane `E × {c}`, then
`f (x, w) = (w - c) * g (x, w)` for a holomorphic `g`. -/
theorem exists_differentiable_eq_sub_mul {f : E × ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ}
    (hc : ∀ x, f (x, c) = 0) :
    ∃ g : E × ℂ → ℂ, Differentiable ℂ g ∧ ∀ p, f p = (p.2 - c) * g p := by
  have han : AnalyticOnNhd ℂ f univ :=
    hf.differentiableOn.analyticOnNhd_of_finiteDimensional isOpen_univ
  -- Near `c` the quotient `f (x, w) / (w - c)` is the slope of the slice at `c`, which converges,
  -- so it is bounded there.
  have hb (x : E) : ∃ t ∈ nhds c, BddAbove (norm ∘ (fun w ↦ f (x, w) / (w - c)) '' (t \ {c})) := by
    have hd : DifferentiableAt ℂ (fun w ↦ f (x, w)) c :=
      (hf.comp ((differentiable_const x).prodMk differentiable_id)) c
    have hslope := hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt
    set B := ‖_root_.deriv (fun w ↦ f (x, w)) c‖ + 1
    obtain ⟨t, ht, hbound⟩ := (eventually_nhdsWithin_iff.1
      (hslope.norm.eventually (gt_mem_nhds (lt_add_one _)))).exists_mem
    refine ⟨t, ht, B, ?_⟩
    rintro _ ⟨w, ⟨hwt, hwc⟩, rfl⟩
    have h := (hbound w hwt hwc).le
    rwa [slope_def_field, hc, sub_zero] at h
  obtain ⟨g, hg, hgf⟩ := TauCeti.exists_analyticOnNhd_prod_eqOn
    (f := fun p : E × ℂ ↦ f p / (p.2 - c)) (U := univ) (s := univ) (c := c) isOpen_univ
    isOpen_univ (fun p hp ↦ (han p trivial).div (analyticAt_snd.sub analyticAt_const)
      (sub_ne_zero.2 hp.2.2)) fun _ x _ ↦ hb x
  refine ⟨g, fun p ↦ (hg p ⟨trivial, trivial⟩).differentiableAt, fun ⟨x, w⟩ ↦ ?_⟩
  rcases eq_or_ne w c with rfl | hw
  · simp [hc]
  · rw [hgf (⟨trivial, trivial, hw⟩ : (x, w) ∈ univ ×ˢ (univ \ {c})),
      mul_div_cancel₀ _ (sub_ne_zero.2 hw)]

/-- **Division by a base-independent transverse divisor.** Let `f : E × ℂ → ℂ` be holomorphic,
with `E` finite-dimensional, and suppose that for every base point `x` the order of vanishing of
the slice `w ↦ f (x, w)` at each `w` is the multiplicity of `w` in a fixed multiset `s`. Then
`f (x, w) = ∏_{a ∈ s} (w - a) * u (x, w)` for a holomorphic `u` with no zeros. -/
theorem exists_eq_prod_sub_mul {f : E × ℂ → ℂ} (hf : Differentiable ℂ f) {s : Multiset ℂ}
    (hs : ∀ x w, analyticOrderAt (fun w ↦ f (x, w)) w = s.count w) :
    ∃ u : E × ℂ → ℂ, Differentiable ℂ u ∧ (∀ p, u p ≠ 0) ∧
      ∀ p, f p = (s.map fun a ↦ p.2 - a).prod * u p := by
  -- The slices of a holomorphic function are analytic.
  have hslice {g : E × ℂ → ℂ} (hg : Differentiable ℂ g) (x : E) (w : ℂ) :
      AnalyticAt ℂ (fun w ↦ g (x, w)) w :=
    (hg.differentiableOn.analyticOnNhd_of_finiteDimensional isOpen_univ (x, w)
      trivial).curry_right
  induction s using Multiset.induction_on generalizing f with
  | empty =>
    refine ⟨f, hf, fun ⟨x, w⟩ ↦ ?_, fun p ↦ by simp⟩
    exact (hslice hf x w).analyticOrderAt_eq_zero.1 (by simpa using hs x w)
  | cons a s ih =>
    -- `f` vanishes on `E × {a}`, so it is `w - a` times a holomorphic `g`.
    obtain ⟨g, hg, hfg⟩ := hf.exists_differentiable_eq_sub_mul (c := a) fun x ↦ by
      by_contra hne
      have h := hs x a
      rw [(hslice hf x a).analyticOrderAt_eq_zero.2 hne, Multiset.count_cons_self] at h
      exact absurd h (by norm_cast)
    -- Dividing by `w - a` lowers the order of vanishing at `a` by one.
    obtain ⟨u, hu, hu0, hgu⟩ := ih hg fun x w ↦ by
      have h := hs x w
      have ha : AnalyticAt ℂ (· - a) w := by fun_prop
      rw [show (fun w ↦ f (x, w)) = (· - a) * fun w ↦ g (x, w) from funext fun w ↦ hfg (x, w),
        analyticOrderAt_mul ha (hslice hg x w),
        Multiset.count_cons] at h
      rcases eq_or_ne w a with rfl | hwa
      · simp only [analyticOrderAt_id_sub_const_self, ↓reduceIte, Nat.cast_add, Nat.cast_one]
          at h
        exact ENat.add_right_injective_of_ne_top ENat.one_ne_top (h.trans (add_comm _ _))
      · simpa [analyticOrderAt_id_sub_const_of_ne hwa, hwa] using h
    refine ⟨u, hu, hu0, fun p ↦ ?_⟩
    rw [hfg, hgu, Multiset.map_cons, Multiset.prod_cons, mul_assoc]

end Differentiable
