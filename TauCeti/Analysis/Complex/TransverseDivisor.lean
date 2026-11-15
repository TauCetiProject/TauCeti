/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Contour.Argument.PowerSum
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.Weierstrass
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

When the base is finite-dimensional, the base-independent divisor factors out of `f` itself:
`f (x, w) = F (x, w) * ∏_{a ∈ s} (w - a)` with `F` holomorphic and nowhere zero
(`Differentiable.exists_differentiable_ne_zero_eq_mul_prod_sub`). Near a point `(x₀, w₀)`, every
slice vanishes to order exactly the multiplicity `d` of `w₀` in `s`, so the Weierstrass division
theorem gives `f (x, w) = (w - w₀) ^ d * q (x, w)` there, with `q` analytic and nonzero at
`(x₀, w₀)` (`AnalyticAt.exists_eventuallyEq_sub_pow_mul`). Dividing `q` by the factors of the
polynomial for the other roots gives `F` near `(x₀, w₀)`; two such local quotients agree where
they overlap, since they agree off the hyperplane `w = w₀`.

## Main results

* `Differentiable.exists_forall_analyticOrderAt_eq_count`: a holomorphic function on `E × ℂ` whose
  zeros are confined to `‖w‖ < K` has a base-independent transverse divisor, given by a multiset of
  points of norm less than `K`.
* `Differentiable.analyticOrderAt_eq_of_forall_le_norm_ne_zero`: the same conclusion, comparing the
  slices over two base points.
* `Differentiable.exists_differentiable_ne_zero_eq_mul_prod_sub`: over a finite-dimensional base,
  such an `f` is a nowhere vanishing holomorphic function times the polynomial `∏_{a ∈ s} (w - a)`.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1, for the
  symmetric functions of the zeros of a holomorphic family.
-/

public section

open Complex Filter Metric Real Set Topology

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
    Contour.differentiableAt_sum_map_pow_zeroMultiset hR (hf' x) (hsphere x) k
  -- The number of zeros is the zeroth power sum: it is continuous and integer valued, hence
  -- constant on the connected base.
  have hcard (x : E) : (Z x).card = (Z 0).card :=
    Contour.card_zeroMultiset_eq_of_isPreconnected isPreconnected_univ hR (fun x _ ↦ hf' x)
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

omit [NormedSpace ℂ E] in
/-- Gluing local quotients by `P`. Suppose that `P w = (w - w₀) ^ d w₀ * R w₀ w` with `R w₀`
continuous and nonzero at `w₀`, and that near each point `p` the function `f` is
`(y.2 - p.2) ^ d p.2 * q p y` with `q p` continuous near `p`. Then near `p₀`, the quotient `f / P`,
completed on the zeros of `P` by the local quotients `q p p / R p.2 p.2`, is `q p₀ / R p₀.2`. -/
private theorem eventuallyEq_ite_div {f : E × ℂ → ℂ} {P : ℂ → ℂ} {d : ℂ → ℕ}
    {R : ℂ → ℂ → ℂ} {q : E × ℂ → E × ℂ → ℂ} (hsplit : ∀ w₀ w, P w = (w - w₀) ^ d w₀ * R w₀ w)
    (hR : ∀ w₀, ContinuousAt (R w₀) w₀) (hR₀ : ∀ w₀, R w₀ w₀ ≠ 0)
    (hq : ∀ p, ∀ᶠ y in 𝓝 p, ContinuousAt (q p) y)
    (hfq : ∀ p : E × ℂ, f =ᶠ[𝓝 p] fun y ↦ (y.2 - p.2) ^ d p.2 * q p y) (p₀ : E × ℂ) :
    (fun p ↦ if P p.2 = 0 then q p p / R p.2 p.2 else f p / P p.2) =ᶠ[𝓝 p₀]
      fun p ↦ q p₀ p / R p₀.2 p.2 := by
  filter_upwards [hfq p₀, (hfq p₀).eventually_nhds, hq p₀,
    ((hR p₀.2).comp continuousAt_snd).eventually_ne (hR₀ p₀.2)] with p hp hpp hqp hRp
  rw [Function.comp_apply] at hRp
  have hPp' := hsplit p₀.2 p.2
  by_cases hPp : P p.2 = 0
  · -- Then `p` lies over `p₀.2`, and the local quotients `q p` and `q p₀` agree at `p`, since
    -- they agree off the hyperplane `y.2 = p₀.2`, which has dense complement.
    have hw : p.2 = p₀.2 := by
      rw [hPp', mul_eq_zero, or_iff_left hRp] at hPp
      exact sub_eq_zero.1 (pow_eq_zero_iff'.1 hPp).1
    simp only [hPp, ↓reduceIte]
    rw [hw]
    congr 1
    have hdense : Dense {y : E × ℂ | y.2 ≠ p₀.2} :=
      (dense_compl_singleton _).preimage isOpenMap_snd
    have : (𝓝[{y : E × ℂ | y.2 ≠ p₀.2}] p).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 (hdense p)
    refine tendsto_nhds_unique (l := 𝓝[{y : E × ℂ | y.2 ≠ p₀.2}] p)
      ((hq p).self_of_nhds.mono_left nhdsWithin_le_nhds)
      ((hqp.mono_left nhdsWithin_le_nhds).congr' ?_)
    filter_upwards [(hfq p).filter_mono nhdsWithin_le_nhds, hpp.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with y hy hy' hy₀
    rw [hw] at hy
    exact mul_left_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 hy₀)) (hy'.symm.trans hy)
  · have hpow : (p.2 - p₀.2) ^ d p₀.2 ≠ 0 := left_ne_zero_of_mul (hPp' ▸ hPp)
    simp only [hPp, ↓reduceIte]
    rw [hp, hPp', mul_div_mul_left _ _ hpow]

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

variable [FiniteDimensional ℂ E] in
/-- **Factorization of a confined transverse divisor.** Let `E` be finite-dimensional, let
`f : E × ℂ → ℂ` be holomorphic, and suppose that `f (x, w) ≠ 0` whenever `K ≤ ‖w‖`. Then there are
a multiset `s` of points of norm less than `K` and a nowhere vanishing holomorphic `F` with
`f (x, w) = F (x, w) * ∏_{a ∈ s} (w - a)`. -/
theorem exists_differentiable_ne_zero_eq_mul_prod_sub {f : E × ℂ → ℂ}
    (hf : Differentiable ℂ f) {K : ℝ} (hK : ∀ x w, K ≤ ‖w‖ → f (x, w) ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧ ∃ F : E × ℂ → ℂ, Differentiable ℂ F ∧
      (∀ p, F p ≠ 0) ∧ ∀ x w, f (x, w) = F (x, w) * (s.map fun a ↦ w - a).prod := by
  classical
  obtain ⟨s, hsK, hs⟩ := hf.exists_forall_analyticOrderAt_eq_count hK
  have han (p : E × ℂ) : AnalyticAt ℂ f p :=
    hf.differentiableOn.analyticOnNhd_of_finiteDimensional isOpen_univ p trivial
  -- `P w = ∏_{a ∈ s} (w - a)`, and `P' w₀` is the same product over the roots other than `w₀`.
  set P : ℂ → ℂ := fun w ↦ (s.map fun a ↦ w - a).prod with hP
  set P' : ℂ → ℂ → ℂ := fun w₀ w ↦ ((s.filter (· ≠ w₀)).map fun a ↦ w - a).prod with hP'
  have hsplit (w₀ w : ℂ) : P w = (w - w₀) ^ s.count w₀ * P' w₀ w := by
    simp only [hP, hP']
    conv_lhs => rw [← Multiset.filter_add_not (· = w₀) s]
    rw [Multiset.map_add, Multiset.prod_add, Multiset.filter_eq' s w₀, Multiset.map_replicate,
      Multiset.prod_replicate]
  have hP'₀ (w₀ : ℂ) : P' w₀ w₀ ≠ 0 := by
    refine Multiset.prod_ne_zero fun h ↦ ?_
    obtain ⟨a, ha, h0⟩ := Multiset.mem_map.1 h
    exact (Multiset.mem_filter.1 ha).2 (sub_eq_zero.1 h0).symm
  have hP'an (w₀ : ℂ) (p : E × ℂ) : AnalyticAt ℂ (fun p : E × ℂ ↦ P' w₀ p.2) p := by
    have hpoly : P' w₀ = fun w ↦
        ((s.filter (· ≠ w₀)).map fun a ↦ Polynomial.X - Polynomial.C a).prod.eval w := by
      funext w
      simp [hP', Polynomial.eval_multiset_prod]
    exact (hpoly ▸ (Polynomial.differentiable _).analyticAt p.2 :).comp analyticAt_snd
  -- Local division at every point, by the power of `w - w₀` given by the multiplicity of `w₀`.
  choose q hq hq0 hfq using fun p : E × ℂ ↦
    (han p).exists_eventuallyEq_sub_pow_mul (d := s.count p.2)
      (Eventually.of_forall fun x ↦ (hs x p.2).ge)
  -- The quotient `f / P`, completed across the roots by the local quotients.
  set F : E × ℂ → ℂ := fun p ↦ if P p.2 = 0 then q p p / P' p.2 p.2 else f p / P p.2 with hF
  have hloc (p₀ : E × ℂ) : F =ᶠ[𝓝 p₀] fun p ↦ q p₀ p / P' p₀.2 p.2 :=
    TauCeti.eventuallyEq_ite_div hsplit (fun w₀ ↦ (hP'an w₀ (0, w₀)).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt) hP'₀
      (fun p ↦ (hq p).eventually_analyticAt.mono fun _ hy ↦ hy.continuousAt) hfq p₀
  have hfac (x : E) (w : ℂ) : f (x, w) = F (x, w) * P w := by
    by_cases hPw : P w = 0
    · -- `w` is a root, so `f` vanishes over it.
      have hcount : s.count w ≠ 0 := fun h0 ↦
        hP'₀ w (by rwa [hsplit w w, sub_self, h0, pow_zero, one_mul] at hPw)
      have hf0 : f (x, w) = 0 :=
        (analyticOrderAt_ne_zero (f := fun w ↦ f (x, w)) (z₀ := w)).1
          (by rw [hs x w]; exact_mod_cast hcount) |>.2
      rw [hf0, hPw, mul_zero]
    · simp only [hF, hPw, ↓reduceIte]
      rw [div_mul_cancel₀ _ hPw]
  refine ⟨s, hsK, F, fun p ↦ (((hq p).div (hP'an p.2 p) (hP'₀ p.2)).congr
    (hloc p).symm).differentiableAt, fun p ↦ ?_, hfac⟩
  rw [(hloc p).self_of_nhds]
  exact div_ne_zero (hq0 p (hs p.1 p.2)) (hP'₀ p.2)

end Differentiable
