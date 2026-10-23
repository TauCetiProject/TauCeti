/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Algebra
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import TauCeti.Analysis.Fourier.Decay

/-!
# Holomorphic Nemytskii maps on the circle Sobolev spaces

For `s > 1/2` the Fourier-coefficient Sobolev space `H^s` of the circle consists of continuous
functions and is an algebra. This file shows that it is also stable under holomorphic functions:
if `F` is holomorphic on an open set `U ⊆ ℂ` and `u ∈ H^s` takes values in `U`, then `F ∘ u` lies in
`H^s`, and the *Nemytskii map* `u ↦ F ∘ u` is holomorphic on the open set of such `u`. These are
the nonlinear maps of boundary values used in the Hardy decompositions of cut Riemann surfaces, for
instance products and quotients of nonvanishing boundary maps.

The proof expands `F` in Taylor series around a nearby trigonometric polynomial `p`. A
trigonometric polynomial extends to an entire periodic function, which maps a thin strip around the
real axis close to the values of `p`. Composed with the derivatives `F^{(k)}`, it stays holomorphic
and, by Cauchy's estimates, bounded by `k! M / ε ^ k` on that strip, so the Fourier coefficients of
`F^{(k)} ∘ p` decay exponentially (`TauCeti.norm_fourierCoeff_le_of_differentiableOn_strip`) and
`‖F^{(k)} ∘ p‖_{H^s} ≤ k! B / ε ^ k`. The product estimate of `H^s` then makes
`∑ₖ (k!)⁻¹ (F^{(k)} ∘ p) (u - p) ^ k` converge in `H^s` for `u` near `p`, to `F ∘ u`, and the same
series is a power series expansion of the Nemytskii map around `p`.

## Main definitions

* `TauCeti.CircleSobolev.nemytskii F u`: the element of `H^s` whose continuous representative is
  `F ∘ u`, when there is one (and `0` otherwise).

## Main statements

* `TauCeti.CircleSobolev.exists_toContinuousMap_eq_of_differentiableOn_strip`: a function on the
  circle extending to a periodic function holomorphic and bounded on a strip lies in every `H^s`,
  `s > 1/2`, with an explicit norm bound.
* `TauCeti.CircleSobolev.toContinuousMap_nemytskii`: for `F` holomorphic on an open set `U` and
  `u ∈ H^s` with values in `U`, the continuous representative of `nemytskii F u` is `F ∘ u`.
* `TauCeti.CircleSobolev.analyticOnNhd_nemytskii`: the map `nemytskii F` is analytic on the open
  set of `u ∈ H^s` with values in `U`.

## References

* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press,
  2004, Chapter I (Fourier coefficients of functions holomorphic in a strip).
* M. E. Taylor, *Partial Differential Equations III*, Chapter 13, Section 3 (Sobolev spaces as
  algebras and their stability under smooth functions).
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699 (nonlinear maps of boundary Sobolev spaces in Hardy
  decompositions).
-/

public section

noncomputable section

open Complex
open scoped Real

namespace TauCeti

namespace CircleSobolev

variable {s : ℝ} (T : ℝ) [hT : Fact (0 < T)]

/-- **Functions holomorphic in a strip lie in every `H^s`.** A continuous function `f` on
`AddCircle T` which is the restriction of a `T`-periodic function `g`, holomorphic and bounded by
`M` on the closed strip `|Im z| ≤ δ`, is the continuous representative of an element of `H^s`,
`s > 1/2`, of norm at most `M (∑ₙ (1 + |n|) ^ (2 s) e^{-4πδ|n|/T}) ^ (1/2)`. -/
theorem exists_toContinuousMap_eq_of_differentiableOn_strip (hs : 1 / 2 < s)
    (f : C(AddCircle T, ℂ)) {g : ℂ → ℂ} {δ M : ℝ} (hδ : 0 < δ) (hfg : ∀ x : ℝ, f x = g x)
    (hper : ∀ z : ℂ, |z.im| ≤ δ → g (z + T) = g z)
    (hg : DifferentiableOn ℂ g {z | |z.im| ≤ δ}) (hM : ∀ z : ℂ, |z.im| ≤ δ → ‖g z‖ ≤ M) :
    ∃ w : CircleSobolev s ℂ, toContinuousMap T hs w = f ∧
      ‖w‖ ≤ M * √(∑' n, weight (2 * s) n * Real.exp (-(4 * π * δ / T * |(n : ℝ)|))) := by
  have hdecay := norm_fourierCoeff_le_of_differentiableOn_strip hδ.le hfg hper hg hM
  have ha : 0 < 4 * π * δ / T := by have := hT.out; positivity
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp [hδ.le]))
  have hsq (n : ℤ) : (weight s n * ‖fourierCoeff f n‖) ^ 2 ≤
      M ^ 2 * (weight (2 * s) n * Real.exp (-(4 * π * δ / T * |(n : ℝ)|))) := by
    calc (weight s n * ‖fourierCoeff f n‖) ^ 2
        ≤ (weight s n * (M * Real.exp (-(2 * π * |(n : ℝ)| * δ / T)))) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (weight_nonneg s n) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hdecay n) (weight_nonneg s n)) 2
      _ = _ := by
        have hexp : ((2 : ℕ) : ℝ) * -(2 * π * |(n : ℝ)| * δ / T) =
            -(4 * π * δ / T * |(n : ℝ)|) := by
          push_cast
          ring
        rw [show weight (2 * s) n = weight s n ^ 2 by rw [sq, ← weight_add, two_mul], mul_pow,
          mul_pow, ← Real.exp_nat_mul, hexp]
        ring
  have hsum := summable_weight_mul_exp_neg (2 * s) ha
  obtain ⟨w, hw⟩ := (exists_coeff_eq_iff (fourierCoeff f)).2 ((memℓp_weight_smul_iff _).2
    (Summable.of_nonneg_of_le (fun n ↦ sq_nonneg _) hsq (hsum.mul_left _)))
  refine ⟨w, ?_, ?_⟩
  · have hsumm : Summable (fourierCoeff f) := by
      simpa only [hw] using (summable_norm_coeff hs w).of_norm
    refine (hasSum_toContinuousMap T hs w).unique ?_
    convert hasSum_fourier_series_of_summable hsumm using 1
    funext n
    ext x
    simp [hw, mul_comm]
  · have hle : ‖w‖ ^ 2 ≤
        (M * √(∑' n, weight (2 * s) n * Real.exp (-(4 * π * δ / T * |(n : ℝ)|)))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (tsum_nonneg fun n ↦
        mul_nonneg (weight_nonneg _ n) (Real.exp_pos _).le), ← tsum_mul_left]
      exact hasSum_le (fun n ↦ by rw [hw]; exact hsq n) (hasSum_sq_weight_mul_norm_coeff w)
        (hsum.mul_left _).hasSum
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle

/-! ### Trigonometric polynomials in a strip -/

/-- On the real axis, the entire function `z ↦ ∑_{n ∈ S} c n e^{2πinz/T}` is the continuous
representative of the trigonometric polynomial `∑_{n ∈ S} single n (c n)`. -/
private theorem toContinuousMap_sum_single_coe (hs : 1 / 2 < s) (S : Finset ℤ) (c : ℤ → ℂ)
    (x : ℝ) : toContinuousMap T hs (∑ n ∈ S, single n (c n)) x =
      ∑ n ∈ S, c n * cexp (2 * π * I * n * x / T) := by
  simp [map_sum, mul_comm]

omit hT in
/-- In a thin enough strip, the entire extension `z ↦ ∑_{n ∈ S} c n e^{2πinz/T}` of a
trigonometric polynomial stays uniformly close to its values on the real axis. -/
private theorem exists_strip_norm_sub_le (S : Finset ℤ) (c : ℤ → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ℂ, |z.im| ≤ δ → ‖∑ n ∈ S, c n * cexp (2 * π * I * n * z / T) -
      ∑ n ∈ S, c n * cexp (2 * π * I * n * z.re / T)‖ ≤ ε := by
  set h : ℝ → ℝ := fun y ↦ ∑ n ∈ S, ‖c n‖ * ‖cexp (2 * π * I * n * (y * I) / T) - 1‖ with hh
  have hc : Continuous h := by fun_prop
  obtain ⟨δ, hδ, hδh⟩ := Metric.continuous_iff.1 hc 0 ε hε
  refine ⟨δ / 2, by positivity, fun z hz ↦ ?_⟩
  have hterm (n : ℤ) : c n * cexp (2 * π * I * n * z / T) - c n * cexp (2 * π * I * n * z.re / T) =
      c n * cexp (2 * π * I * n * z.re / T) * (cexp (2 * π * I * n * (z.im * I) / T) - 1) := by
    rw [show 2 * π * I * n * z / T = 2 * π * I * n * z.re / T + 2 * π * I * n * (z.im * I) / T by
      conv_lhs => rw [← re_add_im z]
      ring, exp_add]
    ring
  have hnorm (n : ℤ) : ‖cexp (2 * π * I * n * z.re / T)‖ = 1 := by
    rw [show 2 * π * I * n * z.re / T = ((2 * π * n * z.re / T : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]
  have h0 : h 0 = 0 := by simp [hh]
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ n ∈ S, ‖c n * cexp (2 * π * I * n * z / T) -
        c n * cexp (2 * π * I * n * z.re / T)‖ := norm_sum_le _ _
    _ = h z.im := by simp only [hh, hterm, norm_mul, hnorm, mul_one]
    _ ≤ ε := by
      have := hδh z.im (by rw [Real.dist_0_eq_abs]; linarith)
      rw [h0, Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans this.le

/-- The entire extension of a trigonometric polynomial maps a thin enough strip into the closed
`ε`-neighbourhood of the range of the polynomial on the circle. -/
private theorem exists_strip_mem_cthickening (hs : 1 / 2 < s) (S : Finset ℤ) (c : ℤ → ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ z : ℂ, |z.im| ≤ δ → ∑ n ∈ S, c n * cexp (2 * π * I * n * z / T) ∈
      Metric.cthickening ε (Set.range (toContinuousMap T hs (∑ n ∈ S, single n (c n)))) := by
  obtain ⟨δ, hδ, h⟩ := exists_strip_norm_sub_le T S c hε
  refine ⟨δ, hδ, fun z hz ↦
    Metric.mem_cthickening_of_dist_le _ _ ε _ ⟨(z.re : AddCircle T), rfl⟩ ?_⟩
  rw [dist_eq_norm, toContinuousMap_sum_single_coe]
  exact h z hz

/-- If `G` is holomorphic and bounded by `M` on a set `K` containing the image of the strip
`|Im z| ≤ δ` under the entire extension of a trigonometric polynomial `p`, then `G ∘ p` lies in
`H^s`, with the norm bound of `exists_toContinuousMap_eq_of_differentiableOn_strip`. -/
private theorem exists_toContinuousMap_eq_comp_sum_single (hs : 1 / 2 < s) (S : Finset ℤ)
    (c : ℤ → ℂ) {G : ℂ → ℂ} {K : Set ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hmaps : ∀ z : ℂ, |z.im| ≤ δ → ∑ n ∈ S, c n * cexp (2 * π * I * n * z / T) ∈ K)
    (hG : DifferentiableOn ℂ G K) (hM : ∀ z ∈ K, ‖G z‖ ≤ M) :
    ∃ w : CircleSobolev s ℂ,
      (∀ x, toContinuousMap T hs w x = G (toContinuousMap T hs (∑ n ∈ S, single n (c n)) x)) ∧
      ‖w‖ ≤ M * √(∑' n, weight (2 * s) n * Real.exp (-(4 * π * δ / T * |(n : ℝ)|))) := by
  set p : CircleSobolev s ℂ := ∑ n ∈ S, single n (c n)
  set P : ℂ → ℂ := fun z ↦ ∑ n ∈ S, c n * cexp (2 * π * I * n * z / T) with hP
  have hPx (x : ℝ) : toContinuousMap T hs p x = P x := toContinuousMap_sum_single_coe T hs S c x
  have hrange (y : AddCircle T) : toContinuousMap T hs p y ∈ K := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact hPx x ▸ hmaps x (by simp [hδ.le])
  have hper (z : ℂ) : P (z + T) = P z :=
    Finset.sum_congr rfl fun n _ ↦ congrArg (c n * ·) (periodic_cexp_two_pi_mul_I_mul_div n z)
  have hPd : Differentiable ℂ P := by fun_prop
  obtain ⟨w, hw, hwn⟩ := exists_toContinuousMap_eq_of_differentiableOn_strip T hs
    ⟨fun y ↦ G (toContinuousMap T hs p y), hG.continuousOn.comp_continuous
      (toContinuousMap T hs p).continuous hrange⟩ (g := G ∘ P) hδ
    (fun x ↦ by simp only [ContinuousMap.coe_mk, Function.comp_apply, hPx])
    (fun z _ ↦ by simp only [Function.comp_apply, hper])
    (hG.comp hPd.differentiableOn fun z hz ↦ hmaps z hz) fun z hz ↦ hM _ (hmaps z hz)
  exact ⟨w, fun x ↦ by rw [hw, ContinuousMap.coe_mk], hwn⟩

/-! ### The Nemytskii map -/

variable [hs : Fact (1 / 2 < s)]

open Classical in
/-- The **Nemytskii map** of `F : ℂ → ℂ` on `H^s`, `s > 1/2`: it sends `u` to the element of `H^s`
whose continuous representative is `F ∘ u`, if there is one, and to `0` otherwise. The composition
is tested on the circle `AddCircle 1`; it does not depend on the length of the circle
(`nemytskii_eq_of_forall_toContinuousMap_apply`). For `F` holomorphic on an open set containing
the values of `u`, the composition `F ∘ u` always lies in `H^s` (`toContinuousMap_nemytskii`). -/
def nemytskii (F : ℂ → ℂ) (u : CircleSobolev s ℂ) : CircleSobolev s ℂ :=
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  if h : ∃ w : CircleSobolev s ℂ, ∀ x : AddCircle (1 : ℝ),
      toContinuousMap 1 hs.out w x = F (toContinuousMap 1 hs.out u x) then h.choose else 0

/-- Composition identities on one circle transfer to circles of every other length. -/
private theorem forall_toContinuousMap_apply_of_forall (T' : ℝ) [hT' : Fact (0 < T')]
    {F : ℂ → ℂ} {u w : CircleSobolev s ℂ}
    (h : ∀ x, toContinuousMap T hs.out w x = F (toContinuousMap T hs.out u x))
    (x : AddCircle T') : toContinuousMap T' hs.out w x = F (toContinuousMap T' hs.out u x) := by
  obtain ⟨y, rfl⟩ := (AddCircle.equivAddCircle T T' hT.out.ne' hT'.out.ne').surjective x
  rw [toContinuousMap_equivAddCircle, toContinuousMap_equivAddCircle, h]

/-- The Nemytskii map is determined by continuous representatives: if the continuous
representative of `w ∈ H^s` is `F ∘ u` on some circle, then `nemytskii F u = w`. -/
theorem nemytskii_eq_of_forall_toContinuousMap_apply {F : ℂ → ℂ} {u w : CircleSobolev s ℂ}
    (h : ∀ x, toContinuousMap T hs.out w x = F (toContinuousMap T hs.out u x)) :
    nemytskii F u = w := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have h1 := forall_toContinuousMap_apply_of_forall T 1 h
  have hex : ∃ w' : CircleSobolev s ℂ, ∀ x : AddCircle (1 : ℝ),
      toContinuousMap 1 hs.out w' x = F (toContinuousMap 1 hs.out u x) := ⟨w, h1⟩
  rw [nemytskii, dite_eq_left hex]
  exact toContinuousMap_injective 1 hs.out
    (ContinuousMap.ext fun x ↦ (hex.choose_spec x).trans (h1 x).symm)

/-- **Taylor coefficients around a trigonometric polynomial.** Let `F` be holomorphic on `U` and
bounded by `M` on the closed `3ε`-neighbourhood of a set `R`, contained in `U`, and let `p` be a
trigonometric polynomial with values in the closed `ε`-neighbourhood of `R`. Then each `F^{(k)} ∘ p`
is the continuous representative of some `w k ∈ H^s` with `‖w k‖ ≤ k! B / ε ^ k`, and Taylor's
formula `F ∘ (p + y) = ∑ₖ (k!)⁻¹ (F^{(k)} ∘ p) y ^ k` holds at every point where `|y| < 2ε`. -/
private theorem exists_taylor_coeff {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {R : Set ℂ} {ε M : ℝ} (hε : 0 < ε)
    (h3 : Metric.cthickening (3 * ε) R ⊆ U) (hM : ∀ z ∈ Metric.cthickening (3 * ε) R, ‖F z‖ ≤ M)
    (S : Finset ℤ) (c : ℤ → ℂ)
    (hp : ∀ x, toContinuousMap T hs.out (∑ n ∈ S, single n (c n)) x ∈ Metric.cthickening ε R) :
    ∃ (w : ℕ → CircleSobolev s ℂ) (B : ℝ), (∀ k, ‖w k‖ ≤ k.factorial * B / ε ^ k) ∧
      ∀ (y : CircleSobolev s ℂ) (x : AddCircle T), ‖toContinuousMap T hs.out y x‖ < 2 * ε →
        toContinuousMap T hs.out (∑ n ∈ S, single n (c n) + y) x ∈ U ∧
        HasSum (fun k ↦ (k.factorial : ℂ)⁻¹ * toContinuousMap T hs.out (w k) x *
          toContinuousMap T hs.out y x ^ k)
          (F (toContinuousMap T hs.out (∑ n ∈ S, single n (c n) + y) x)) := by
  set p : CircleSobolev s ℂ := ∑ n ∈ S, single n (c n)
  -- Cauchy's estimates bound `F^{(k)}` by `k! M / ε ^ k` on the closed `2ε`-neighbourhood of `R`.
  have hcauchy (k : ℕ) (z : ℂ) (hz : z ∈ Metric.cthickening (2 * ε) R) :
      ‖iteratedDeriv k F z‖ ≤ k.factorial * M / ε ^ k := by
    have hball : Metric.closedBall z ε ⊆ Metric.cthickening (3 * ε) R :=
      (Metric.closedBall_subset_cthickening hz ε).trans <|
        (Metric.cthickening_cthickening_subset hε.le (by positivity) R).trans_eq (by ring_nf)
    exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hε
      ((hF.mono h3).diffContOnCl_ball hball)
      fun w hw ↦ hM w (hball (Metric.sphere_subset_closedBall hw))
  -- The entire extension of `p` maps a strip into the closed `2ε`-neighbourhood of `R`, which
  -- gives `w k` with continuous representative `F^{(k)} ∘ p`.
  obtain ⟨δ, hδ, hmaps⟩ := exists_strip_mem_cthickening T hs.out S c hε
  have h2 : Metric.cthickening (2 * ε) R ⊆ Metric.cthickening (3 * ε) R :=
    Metric.cthickening_mono (by linarith) R
  have hFa := (hF.analyticOnNhd hU).iterated_deriv
  choose w hw hwn using fun k ↦ exists_toContinuousMap_eq_comp_sum_single T hs.out S c
    (G := iteratedDeriv k F) hδ (fun z hz ↦ (Metric.cthickening_subset_of_subset ε
      (Set.range_subset_iff.2 hp)).trans
        ((Metric.cthickening_cthickening_subset hε.le hε.le R).trans_eq (by ring_nf)) (hmaps z hz))
    (by rw [iteratedDeriv_eq_iterate]; exact (hFa k).differentiableOn.mono (h2.trans h3))
    (hcauchy k)
  refine ⟨w, M * √(∑' n, weight (2 * s) n * Real.exp (-(4 * π * δ / T * |(n : ℝ)|))),
    fun k ↦ (hwn k).trans_eq (by ring), fun y x hy ↦ ?_⟩
  -- Taylor's formula for `F` around `p x`, evaluated at `(p + y) x`.
  have hball : Metric.ball (toContinuousMap T hs.out p x) (2 * ε) ⊆ U :=
    Metric.ball_subset_closedBall.trans <| (Metric.closedBall_subset_cthickening (hp x) _).trans <|
      ((Metric.cthickening_cthickening_subset (by positivity) hε.le R).trans_eq
        (by ring_nf)).trans h3
  have hz : toContinuousMap T hs.out (p + y) x ∈
      Metric.ball (toContinuousMap T hs.out p x) (2 * ε) := by
    rwa [Metric.mem_ball, dist_eq_norm, map_add, ContinuousMap.add_apply, add_sub_cancel_left]
  refine ⟨hball hz, ?_⟩
  convert Complex.hasSum_taylorSeries_on_ball (hF.mono hball) hz using 1
  funext k
  rw [hw k x, map_add, ContinuousMap.add_apply, add_sub_cancel_left, smul_eq_mul, smul_eq_mul]
  ring

/-- **Local expansion of the Nemytskii map.** Near every `u₀` with values in `U` there are a
trigonometric polynomial `p`, a radius `ρ` with `‖u₀ - p‖ < ρ`, and elements `w k ∈ H^s` with
`‖w k‖ ≤ k! B / (mulConst s * ρ) ^ k` such that for `‖y‖ < ρ` the function `F ∘ (p + y)` is
pointwise the sum of `(k!)⁻¹ (w k) y ^ k`. -/
private theorem exists_local_expansion {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {u₀ : CircleSobolev s ℂ}
    (hu₀ : ∀ x, toContinuousMap T hs.out u₀ x ∈ U) :
    ∃ (p : CircleSobolev s ℂ) (w : ℕ → CircleSobolev s ℂ) (ρ B : ℝ), 0 < ρ ∧ ‖u₀ - p‖ < ρ ∧
      (∀ k, ‖w k‖ ≤ k.factorial * B / (mulConst s * ρ) ^ k) ∧
      ∀ y : CircleSobolev s ℂ, ‖y‖ < ρ → ∀ x, toContinuousMap T hs.out (p + y) x ∈ U ∧
        HasSum (fun k ↦ (k.factorial : ℂ)⁻¹ * toContinuousMap T hs.out (w k) x *
          toContinuousMap T hs.out y x ^ k) (F (toContinuousMap T hs.out (p + y) x)) := by
  set C := mulConst s with hC
  set K := √(∑' n, weight (-(2 * s)) n) with hK
  have hC1 : 1 ≤ C := one_le_mulConst
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hsup (a : CircleSobolev s ℂ) (x : AddCircle T) :
      ‖toContinuousMap T hs.out a x‖ ≤ K * ‖a‖ :=
    ((toContinuousMap T hs.out a).norm_coe_le_norm x).trans (norm_toContinuousMap_le T hs.out a)
  -- `F` is bounded on the closed `3ε`-neighbourhood of the range `R` of `u₀`, inside `U`.
  set R := Set.range (toContinuousMap T hs.out u₀)
  have hR : IsCompact R := isCompact_range (toContinuousMap T hs.out u₀).continuous
  obtain ⟨δ₀, hδ₀, hsub⟩ := hR.exists_cthickening_subset_open hU (Set.range_subset_iff.2 hu₀)
  set ε := δ₀ / 3 with hε_def
  have hε : 0 < ε := by positivity
  have h3 : Metric.cthickening (3 * ε) R ⊆ U := by rwa [hε_def, mul_div_cancel₀ _ three_ne_zero]
  obtain ⟨M, hM⟩ := hR.cthickening.exists_bound_of_continuousOn (hF.continuousOn.mono h3)
  -- Approximate `u₀` within `ρ` by a partial sum `p` of its Fourier series; then `p` takes values
  -- in the closed `ε`-neighbourhood of `R`, and `‖y‖ < ρ` forces `|y| < 2ε` pointwise.
  set ρ := ε / (C * (K + 1)) with hρ_def
  have hρ : 0 < ρ := by positivity
  have hCK : ε * (K + 1) ≤ ε * (C * (K + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_left hC1 (by positivity : (0 : ℝ) ≤ ε * (K + 1))]
  have hKρ : K * ρ ≤ ε := by
    rw [hρ_def, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hCρ : C * ρ ≤ ε := by
    rw [hρ_def, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hC1 hε.le]
  obtain ⟨S, hS⟩ : ∃ S : Finset ℤ, ‖u₀ - ∑ n ∈ S, single n (u₀.coeff n)‖ < ρ := by
    obtain ⟨S, hS⟩ := Metric.tendsto_atTop.1 (hasSum_single u₀) ρ hρ
    exact ⟨S, by simpa [dist_eq_norm, norm_sub_rev] using hS S le_rfl⟩
  have hp (x : AddCircle T) : toContinuousMap T hs.out (∑ n ∈ S, single n (u₀.coeff n)) x ∈
      Metric.cthickening ε R := by
    refine Metric.mem_cthickening_of_dist_le _ _ ε R ⟨x, rfl⟩ ?_
    rw [dist_eq_norm, ← ContinuousMap.sub_apply, ← map_sub]
    exact (hsup _ x).trans
      ((mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact hS.le) hK0).trans hKρ)
  obtain ⟨w, B, hw, htaylor⟩ := exists_taylor_coeff T hU hF hε h3 hM S u₀.coeff hp
  have hB : 0 ≤ B := by simpa using (norm_nonneg _).trans (hw 0)
  refine ⟨_, w, ρ, B, hρ, hS, fun k ↦ (hw k).trans ?_, fun y hy x ↦ htaylor y x ?_⟩
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by positivity) hCρ k)
  · exact (hsup y x).trans_lt ((mul_le_mul_of_nonneg_left hy.le hK0).trans hKρ |>.trans_lt
      (by linarith))

omit hT in
/-- The power series on `H^s` whose `k`-th term is `(y₁, …, yₖ) ↦ (k!)⁻¹ (w k) y₁ ⋯ yₖ`. -/
private def factorialInvSeries (w : ℕ → CircleSobolev s ℂ) :
    FormalMultilinearSeries ℂ (CircleSobolev s ℂ) (CircleSobolev s ℂ) := fun k ↦
  (k.factorial : ℂ)⁻¹ • (convolution hs.out (.mul ℂ ℂ) (w k)).compContinuousMultilinearMap
    (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k (CircleSobolev s ℂ))

omit hT in
private theorem factorialInvSeries_apply_const (w : ℕ → CircleSobolev s ℂ) (k : ℕ)
    (y : CircleSobolev s ℂ) :
    factorialInvSeries w k (fun _ ↦ y) = (k.factorial : ℂ)⁻¹ • (w k * y ^ k) := by
  simp [factorialInvSeries, List.ofFn_const, List.prod_replicate, mul_def]

omit hT in
/-- The series `factorialInvSeries w` has radius at least `ρ` when
`‖w k‖ ≤ k! B / (mulConst s * ρ) ^ k`. -/
private theorem le_radius_factorialInvSeries {w : ℕ → CircleSobolev s ℂ} {ρ B : ℝ}
    (hρ : 0 < ρ) (hw : ∀ k, ‖w k‖ ≤ k.factorial * B / (mulConst s * ρ) ^ k) :
    (ρ.toNNReal : ENNReal) ≤ (factorialInvSeries w).radius := by
  set C := mulConst s with hC
  have hC0 : 0 < C := one_pos.trans_le one_le_mulConst
  have hB : 0 ≤ B := by simpa using (norm_nonneg _).trans (hw 0)
  refine FormalMultilinearSeries.le_radius_of_bound _ (C * B) fun k ↦ ?_
  have hL : ‖convolution hs.out (.mul ℂ ℂ) (w k)‖ ≤ C * ‖w k‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b ↦ by
      simpa only [mul_def] using norm_mul_le_mulConst (w k) b
  have hm : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ k (CircleSobolev s ℂ)‖ ≤ C ^ k :=
    ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ by
      simpa [List.map_ofFn, List.prod_ofFn] using norm_list_prod_le (List.ofFn m)
  have hqn : ‖factorialInvSeries w k‖ ≤ (k.factorial : ℝ)⁻¹ * (C * ‖w k‖) * C ^ k := by
    rw [factorialInvSeries, norm_smul, norm_inv, Complex.norm_natCast, mul_assoc]
    gcongr
    exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      (mul_le_mul hL hm (norm_nonneg _) (by positivity))
  rw [Real.coe_toNNReal _ hρ.le]
  calc ‖factorialInvSeries w k‖ * ρ ^ k
      ≤ (k.factorial : ℝ)⁻¹ * (C * (k.factorial * B / (C * ρ) ^ k)) * C ^ k * ρ ^ k := by
        gcongr
        exact hqn.trans (by gcongr; exact hw k)
    _ = C * B := by
        rw [mul_pow]
        field_simp

omit hT in
/-- The series `∑ₖ (k!)⁻¹ (w k) y ^ k` converges absolutely in `H^s` when
`‖w k‖ ≤ k! B / (mulConst s * ρ) ^ k` and `‖y‖ < ρ`. -/
private theorem summable_factorial_inv_smul_mul_pow {w : ℕ → CircleSobolev s ℂ} {ρ B : ℝ}
    (hρ : 0 < ρ) (hw : ∀ k, ‖w k‖ ≤ k.factorial * B / (mulConst s * ρ) ^ k)
    {y : CircleSobolev s ℂ} (hy : ‖y‖ < ρ) :
    Summable fun k ↦ (k.factorial : ℂ)⁻¹ • (w k * y ^ k) := by
  have hy' : y ∈ Metric.eball (0 : CircleSobolev s ℂ) (ρ.toNNReal : ENNReal) := by
    rw [Metric.eball_coe, mem_ball_zero_iff, Real.coe_toNNReal _ hρ.le]
    exact hy
  simpa only [factorialInvSeries_apply_const] using ((factorialInvSeries w).summable_norm_apply
    (Metric.eball_subset_eball (le_radius_factorialInvSeries hρ hw) hy')).of_norm

/-- The local expansion of `exists_local_expansion`, summed in `H^s`: near every `u₀` with values
in `U`, `nemytskii F (p + y) = ∑ₖ (k!)⁻¹ (w k) y ^ k` for `‖y‖ < ρ`, and its continuous
representative is `F ∘ (p + y)`. -/
private theorem exists_hasSum_nemytskii {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {u₀ : CircleSobolev s ℂ}
    (hu₀ : ∀ x, toContinuousMap T hs.out u₀ x ∈ U) :
    ∃ (p : CircleSobolev s ℂ) (w : ℕ → CircleSobolev s ℂ) (ρ B : ℝ), 0 < ρ ∧ ‖u₀ - p‖ < ρ ∧
      (∀ k, ‖w k‖ ≤ k.factorial * B / (mulConst s * ρ) ^ k) ∧
      ∀ y : CircleSobolev s ℂ, ‖y‖ < ρ →
        HasSum (fun k ↦ (k.factorial : ℂ)⁻¹ • (w k * y ^ k)) (nemytskii F (p + y)) ∧
        ∀ x, toContinuousMap T hs.out (nemytskii F (p + y)) x =
          F (toContinuousMap T hs.out (p + y) x) := by
  obtain ⟨p, w, ρ, B, hρ, hp, hw, h⟩ := exists_local_expansion T hU hF hu₀
  refine ⟨p, w, ρ, B, hρ, hp, hw, fun y hy ↦ ?_⟩
  have hsum := (summable_factorial_inv_smul_mul_pow hρ hw hy).hasSum
  have hx (x : AddCircle T) : toContinuousMap T hs.out (∑' k, (k.factorial : ℂ)⁻¹ •
      (w k * y ^ k)) x = F (toContinuousMap T hs.out (p + y) x) := by
    refine ((hsum.mapL (toContinuousMap T hs.out)).mapL (ContinuousMap.evalCLM ℂ x)).unique ?_
    convert (h y hy x).2 using 1
    funext k
    simp [toContinuousMap_mul, toContinuousMap_pow, mul_assoc]
  rw [nemytskii_eq_of_forall_toContinuousMap_apply T hx]
  exact ⟨hsum, hx⟩

/-- **Holomorphic functions act on `H^s`, `s > 1/2`.** If `F` is holomorphic on an open set `U`
and the continuous representative of `u ∈ H^s` takes values in `U`, then `F ∘ u` is the continuous
representative of `nemytskii F u ∈ H^s`. -/
theorem toContinuousMap_nemytskii {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {u : CircleSobolev s ℂ}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U) (x : AddCircle T) :
    toContinuousMap T hs.out (nemytskii F u) x = F (toContinuousMap T hs.out u x) := by
  obtain ⟨p, _, ρ, _, _, hp, _, h⟩ := exists_hasSum_nemytskii T hU hF hu
  simpa only [add_sub_cancel] using (h (u - p) hp).2 x

/-- **The holomorphic Nemytskii map is holomorphic.** If `F` is holomorphic on an open set `U`,
then `u ↦ nemytskii F u` is analytic on the open subset of `H^s`, `s > 1/2`, of elements with
values in `U` (`isOpen_setOf_forall_toContinuousMap_mem`). -/
theorem analyticOnNhd_nemytskii {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ (nemytskii F)
      {u : CircleSobolev s ℂ | ∀ x, toContinuousMap T hs.out u x ∈ U} := by
  intro u₀ hu₀
  obtain ⟨p, w, ρ, B, hρ, hp, hw, h⟩ := exists_hasSum_nemytskii T hU hF hu₀
  have hps : HasFPowerSeriesOnBall (nemytskii F) (factorialInvSeries w) p
      (ρ.toNNReal : ENNReal) := {
    r_le := le_radius_factorialInvSeries hρ hw
    r_pos := ENNReal.coe_pos.2 (Real.toNNReal_pos.2 hρ)
    hasSum := fun {y} hy ↦ by
      rw [Metric.eball_coe, mem_ball_zero_iff, Real.coe_toNNReal _ hρ.le] at hy
      simpa only [factorialInvSeries_apply_const] using (h y hy).1 }
  exact hps.analyticAt_of_mem (by
    rw [Metric.eball_coe, mem_ball_iff_norm, Real.coe_toNNReal _ hρ.le]
    exact hp)

end CircleSobolev

end TauCeti
