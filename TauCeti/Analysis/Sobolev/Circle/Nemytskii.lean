/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Algebra
public import Mathlib.Analysis.Analytic.Basic
import TauCeti.Analysis.Complex.PowerSeries.Polydisc
import TauCeti.GroupTheory.Perm.FiberSubgroup
import TauCeti.Algebra.Order.Antidiag.Pi
import TauCeti.Analysis.Fourier.Decay

/-!
# Holomorphic Nemytskii maps on the circle Sobolev spaces

For `s > 1/2` the Fourier-coefficient Sobolev space `H^s` of the circle consists of continuous
functions and is an algebra. This file shows that it is also stable under holomorphic functions of
several variables: if `F` is holomorphic on an open set `U ⊆ ℂⁿ` and `u : Fin n → H^s` takes its
joint values `x ↦ (u i x)ᵢ` in `U`, then `x ↦ F (u x)` lies in `H^s`, and the *Nemytskii map*
`u ↦ F ∘ u` is holomorphic on the open set of such `u`. A boundary map of a circle into `ℂⁿ` of
class `H^s` is such a family of `n` coordinate functions, and the holomorphic transition maps
between coordinate charts act on these boundary maps by Nemytskii maps; a target `ℂᵐ` is treated
one coordinate at a time. The case of one variable gives the scalar Nemytskii map, for instance of
`exp` or of a branch of the logarithm, which is used for products and quotients of nonvanishing
boundary maps in the Hardy decompositions of cut Riemann surfaces.

The proof expands `F` in its multi-index Taylor series around a nearby family `p` of
trigonometric polynomials. A trigonometric polynomial extends to an entire periodic function,
which maps a thin strip around the real axis close to the values of `p`. Composed with the Taylor
coefficients `z ↦ mvTaylorCoeff F z α`, which are holomorphic in `z`
(`AnalyticOnNhd.mvTaylorCoeff`) and bounded by `M ε⁻¹ ^ |α|` by Cauchy's inequality on a
polydisc (`DifferentiableOn.norm_mvTaylorCoeff_le`), it stays holomorphic and bounded on that
strip. So the Fourier coefficients of the Taylor coefficients along `p` decay exponentially
(`TauCeti.norm_fourierCoeff_le_of_differentiableOn_strip`), and they lie in `H^s` with norms at
most `B ε⁻¹ ^ |α|`. The product estimate of `H^s` then makes `∑_α (mvTaylorCoeff F p α) (u - p) ^ α`
converge in `H^s` for `u` near `p`, to `F ∘ u` by Taylor's formula on a polydisc
(`DifferentiableOn.hasSum_mvTaylorCoeff`). Grouped by total degree, the same series is a power
series expansion of the Nemytskii map around `p`.

## Main definitions

* `TauCeti.CircleSobolev.nemytskiiPi F u`: for `F : (Fin n → ℂ) → ℂ` and `u : Fin n → H^s`, the
  element of `H^s` whose continuous representative is `x ↦ F (fun i ↦ u i x)`, when there is one
  (and `0` otherwise).
* `TauCeti.CircleSobolev.nemytskii F u`: for `F : ℂ → ℂ` and `u ∈ H^s`, the element of `H^s` whose
  continuous representative is `F ∘ u`, when there is one (and `0` otherwise). It is the Nemytskii
  map of one variable (`TauCeti.CircleSobolev.nemytskii_eq_nemytskiiPi`).

## Main statements

* `TauCeti.CircleSobolev.exists_toContinuousMap_eq_of_differentiableOn_strip`: a function on the
  circle extending to a periodic function holomorphic and bounded on a strip lies in every `H^s`,
  `s > 1/2`, with an explicit norm bound.
* `TauCeti.CircleSobolev.toContinuousMap_nemytskiiPi`: for `F` holomorphic on an open set
  `U ⊆ ℂⁿ` and `u` with joint values in `U`, the continuous representative of `nemytskiiPi F u` is
  `x ↦ F (fun i ↦ u i x)`.
* `TauCeti.CircleSobolev.analyticOnNhd_nemytskiiPi`: the map `nemytskiiPi F` is analytic on the
  open set of families with joint values in `U`
  (`TauCeti.CircleSobolev.isOpen_setOf_forall_toContinuousMap_pi_mem`).
* `TauCeti.CircleSobolev.hasFDerivAt_nemytskiiPi`: its derivative at `u` sends `v` to
  `∑ᵢ (∂ᵢF ∘ u) vᵢ`.
* `TauCeti.CircleSobolev.toContinuousMap_nemytskii` and
  `TauCeti.CircleSobolev.analyticOnNhd_nemytskii`: the same for one variable.
* `TauCeti.CircleSobolev.hasFDerivAt_nemytskii`: in one variable the derivative at `u` is
  multiplication by `F' ∘ u`; at `u = 0` it is multiplication by the scalar `F'(0)`
  (`TauCeti.CircleSobolev.hasFDerivAt_nemytskii_zero`).

## References

* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press,
  2004, Chapter I (Fourier coefficients of functions holomorphic in a strip).
* M. E. Taylor, *Partial Differential Equations III*, Chapter 13, Section 3 (Sobolev spaces as
  algebras and their stability under smooth functions).
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2 (Cauchy's
  inequalities and Taylor expansions on polydiscs).
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699 (nonlinear maps of boundary Sobolev spaces in Hardy
  decompositions).
-/

public section

noncomputable section

open Complex
open scoped Real Topology

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
          mul_pow, ← Real.exp_natCast_mul, hexp]
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

variable {n : ℕ}

/-- The entire extension of a finite family of trigonometric polynomials maps a thin enough strip
into the closed `ε`-neighbourhood of the range of the family on the circle. -/
private theorem exists_strip_mem_cthickening (hs : 1 / 2 < s) (S : Finset ℤ)
    (c : Fin n → ℤ → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ℂ, |z.im| ≤ δ → (fun i ↦ ∑ m ∈ S, c i m * cexp (2 * π * I * m * z / T)) ∈
      Metric.cthickening ε (Set.range fun x : AddCircle T ↦
        fun i ↦ toContinuousMap T hs (∑ m ∈ S, single m (c i m)) x) := by
  have h (i : Fin n) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z : ℂ, |z.im| ≤ δ →
      ‖∑ m ∈ S, c i m * cexp (2 * π * I * m * z / T) -
        ∑ m ∈ S, c i m * cexp (2 * π * I * m * z.re / T)‖ ≤ ε := by
    obtain ⟨δ, hδ, hδh⟩ := exists_strip_norm_sub_le T S (c i) hε
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht using fun z hz ↦ hδh z (hz.trans ht.2.le)
  obtain ⟨δ, hδ, hδ₀⟩ := ((Filter.eventually_all.2 h).and self_mem_nhdsWithin).exists
  refine ⟨δ, hδ₀, fun z hz ↦ Metric.mem_cthickening_of_dist_le _ _ ε _ ⟨(z.re : AddCircle T), rfl⟩
    ((dist_pi_le_iff hε.le).2 fun i ↦ ?_)⟩
  rw [dist_eq_norm]
  dsimp only
  rw [toContinuousMap_sum_single_coe]
  exact hδ i z hz

/-- If `G` is holomorphic and bounded by `M` on a set `K` containing the image of the strip
`|Im z| ≤ δ` under the entire extension of a family `p` of trigonometric polynomials, then `G ∘ p`
lies in `H^s`, with the norm bound of `exists_toContinuousMap_eq_of_differentiableOn_strip`. -/
private theorem exists_toContinuousMap_eq_comp_sum_single (hs : 1 / 2 < s) (S : Finset ℤ)
    (c : Fin n → ℤ → ℂ) {G : (Fin n → ℂ) → ℂ} {K : Set (Fin n → ℂ)} {δ M : ℝ} (hδ : 0 < δ)
    (hmaps : ∀ z : ℂ, |z.im| ≤ δ →
      (fun i ↦ ∑ m ∈ S, c i m * cexp (2 * π * I * m * z / T)) ∈ K)
    (hG : DifferentiableOn ℂ G K) (hM : ∀ z ∈ K, ‖G z‖ ≤ M) :
    ∃ w : CircleSobolev s ℂ, (∀ x, toContinuousMap T hs w x =
        G (fun i ↦ toContinuousMap T hs (∑ m ∈ S, single m (c i m)) x)) ∧
      ‖w‖ ≤ M * √(∑' m, weight (2 * s) m * Real.exp (-(4 * π * δ / T * |(m : ℝ)|))) := by
  set p : Fin n → CircleSobolev s ℂ := fun i ↦ ∑ m ∈ S, single m (c i m)
  set P : ℂ → Fin n → ℂ := fun z i ↦ ∑ m ∈ S, c i m * cexp (2 * π * I * m * z / T)
  have hPx (x : ℝ) : (fun i ↦ toContinuousMap T hs (p i) x) = P x :=
    funext fun i ↦ toContinuousMap_sum_single_coe T hs S (c i) x
  have hrange (y : AddCircle T) : (fun i ↦ toContinuousMap T hs (p i) y) ∈ K := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact hPx x ▸ hmaps x (by simp [hδ.le])
  have hper (z : ℂ) : P (z + T) = P z := funext fun i ↦
    Finset.sum_congr rfl fun m _ ↦ congrArg (c i m * ·) (periodic_cexp_two_pi_mul_I_mul_div m z)
  have hPd : Differentiable ℂ P := differentiable_pi.2 fun i ↦ by fun_prop
  have hpc : Continuous fun y : AddCircle T ↦ fun i ↦ toContinuousMap T hs (p i) y :=
    continuous_pi fun i ↦ (toContinuousMap T hs (p i)).continuous
  obtain ⟨w, hw, hwn⟩ := exists_toContinuousMap_eq_of_differentiableOn_strip T hs
    ⟨fun y ↦ G (fun i ↦ toContinuousMap T hs (p i) y),
      hG.continuousOn.comp_continuous hpc hrange⟩ (g := G ∘ P) hδ
    (fun x ↦ by simp only [ContinuousMap.coe_mk, Function.comp_apply, hPx])
    (fun z _ ↦ by simp only [Function.comp_apply, hper])
    (hG.comp hPd.differentiableOn fun z hz ↦ hmaps z hz) fun z hz ↦ hM _ (hmaps z hz)
  exact ⟨w, fun x ↦ by rw [hw, ContinuousMap.coe_mk], hwn⟩

/-! ### The Nemytskii map -/

variable [hs : Fact (1 / 2 < s)]

open Classical in
/-- The **Nemytskii map** of `F : (Fin n → ℂ) → ℂ` on families of elements of `H^s`, `s > 1/2`: it
sends `u` to the element of `H^s` whose continuous representative is
`x ↦ F (fun i ↦ u i x)`, if there is one, and to `0` otherwise. The composition is tested on the
circle `AddCircle 1`; it does not depend on the length of the circle
(`nemytskiiPi_eq_of_forall_toContinuousMap_apply`). For `F` holomorphic on an open set containing
the values of `u`, the composition always lies in `H^s` (`toContinuousMap_nemytskiiPi`). -/
def nemytskiiPi (F : (Fin n → ℂ) → ℂ) (u : Fin n → CircleSobolev s ℂ) : CircleSobolev s ℂ :=
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  if h : ∃ w : CircleSobolev s ℂ, ∀ x : AddCircle (1 : ℝ),
      toContinuousMap 1 hs.out w x = F (fun i ↦ toContinuousMap 1 hs.out (u i) x) then h.choose
  else 0

/-- The **Nemytskii map** of `F : ℂ → ℂ` on `H^s`, `s > 1/2`: the Nemytskii map of one variable.
It sends `u` to the element of `H^s` whose continuous representative is `F ∘ u`, if there is one,
and to `0` otherwise (`nemytskii_eq_of_forall_toContinuousMap_apply`). For `F` holomorphic on an
open set containing the values of `u`, the composition `F ∘ u` always lies in `H^s`
(`toContinuousMap_nemytskii`). -/
def nemytskii (F : ℂ → ℂ) (u : CircleSobolev s ℂ) : CircleSobolev s ℂ :=
  nemytskiiPi (fun z : Fin 1 → ℂ ↦ F (z 0)) fun _ ↦ u

/-- The scalar Nemytskii map is the Nemytskii map of one variable. -/
theorem nemytskii_eq_nemytskiiPi (F : ℂ → ℂ) (u : CircleSobolev s ℂ) :
    nemytskii F u = nemytskiiPi (fun z : Fin 1 → ℂ ↦ F (z 0)) (fun _ ↦ u) :=
  (rfl)

/-- Composition identities on one circle transfer to circles of every other length. -/
private theorem forall_toContinuousMap_apply_of_forall (T' : ℝ) [hT' : Fact (0 < T')]
    {F : (Fin n → ℂ) → ℂ} {u : Fin n → CircleSobolev s ℂ} {w : CircleSobolev s ℂ}
    (h : ∀ x, toContinuousMap T hs.out w x = F (fun i ↦ toContinuousMap T hs.out (u i) x))
    (x : AddCircle T') :
    toContinuousMap T' hs.out w x = F (fun i ↦ toContinuousMap T' hs.out (u i) x) := by
  obtain ⟨y, rfl⟩ := (AddCircle.equivAddCircle T T' hT.out.ne' hT'.out.ne').surjective x
  simp_rw [toContinuousMap_equivAddCircle]
  exact h y

/-- The Nemytskii map is determined by continuous representatives: if the continuous
representative of `w ∈ H^s` is `x ↦ F (fun i ↦ u i x)` on some circle, then
`nemytskiiPi F u = w`. -/
theorem nemytskiiPi_eq_of_forall_toContinuousMap_apply {F : (Fin n → ℂ) → ℂ}
    {u : Fin n → CircleSobolev s ℂ} {w : CircleSobolev s ℂ}
    (h : ∀ x, toContinuousMap T hs.out w x = F (fun i ↦ toContinuousMap T hs.out (u i) x)) :
    nemytskiiPi F u = w := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have h1 := forall_toContinuousMap_apply_of_forall T 1 h
  have hex : ∃ w' : CircleSobolev s ℂ, ∀ x : AddCircle (1 : ℝ),
      toContinuousMap 1 hs.out w' x = F (fun i ↦ toContinuousMap 1 hs.out (u i) x) := ⟨w, h1⟩
  rw [nemytskiiPi, dite_eq_left hex]
  exact toContinuousMap_injective 1 hs.out
    (ContinuousMap.ext fun x ↦ (hex.choose_spec x).trans (h1 x).symm)

/-- The Nemytskii map is determined by continuous representatives: if the continuous
representative of `w ∈ H^s` is `F ∘ u` on some circle, then `nemytskii F u = w`. -/
theorem nemytskii_eq_of_forall_toContinuousMap_apply {F : ℂ → ℂ} {u w : CircleSobolev s ℂ}
    (h : ∀ x, toContinuousMap T hs.out w x = F (toContinuousMap T hs.out u x)) :
    nemytskii F u = w :=
  (nemytskii_eq_nemytskiiPi F u).trans
    (nemytskiiPi_eq_of_forall_toContinuousMap_apply T (F := fun z : Fin 1 → ℂ ↦ F (z 0))
      (u := fun _ ↦ u) h)

/-- **Taylor coefficients around a family of trigonometric polynomials.** Let `F` be holomorphic on
`U` and bounded by `M` on the closed `3ε`-neighbourhood of a set `R`, contained in `U`, and let `p`
be a family of trigonometric polynomials with values in the closed `ε`-neighbourhood of `R`. Then
the Taylor coefficient `z ↦ mvTaylorCoeff F z α` composed with `p` is the continuous representative
of some `w α ∈ H^s` with `‖w α‖ ≤ B ε⁻¹ ^ |α|`, and Taylor's formula
`F (p + y) = ∑_α (w α) y ^ α` holds at every point where `‖y‖ < 2ε`. -/
private theorem exists_taylor_coeff {F : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {R : Set (Fin n → ℂ)} {ε M : ℝ} (hε : 0 < ε)
    (h3 : Metric.cthickening (3 * ε) R ⊆ U) (hM : ∀ z ∈ Metric.cthickening (3 * ε) R, ‖F z‖ ≤ M)
    (S : Finset ℤ) (c : Fin n → ℤ → ℂ)
    (hp : ∀ x, (fun i ↦ toContinuousMap T hs.out (∑ m ∈ S, single m (c i m)) x) ∈
      Metric.cthickening ε R) :
    ∃ (w : (Fin n → ℕ) → CircleSobolev s ℂ) (B : ℝ), (∀ α, ‖w α‖ ≤ B * ε⁻¹ ^ (∑ i, α i)) ∧
      ∀ (y : Fin n → CircleSobolev s ℂ) (x : AddCircle T),
        ‖fun i ↦ toContinuousMap T hs.out (y i) x‖ < 2 * ε →
        (fun i ↦ toContinuousMap T hs.out (∑ m ∈ S, single m (c i m) + y i) x) ∈ U ∧
        HasSum (fun α ↦ (∏ i, toContinuousMap T hs.out (y i) x ^ α i) *
          toContinuousMap T hs.out (w α) x)
          (F (fun i ↦ toContinuousMap T hs.out (∑ m ∈ S, single m (c i m) + y i) x)) := by
  set p : Fin n → CircleSobolev s ℂ := fun i ↦ ∑ m ∈ S, single m (c i m)
  have hthick {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {z : Fin n → ℂ}
      (hz : z ∈ Metric.cthickening a R) : Metric.closedBall z b ⊆ Metric.cthickening (a + b) R :=
    (Metric.closedBall_subset_cthickening hz b).trans
      ((Metric.cthickening_cthickening_subset hb ha R).trans_eq (by rw [add_comm]))
  -- Cauchy's inequality bounds the Taylor coefficients on the closed `2ε`-neighbourhood of `R`.
  have hcauchy (α : Fin n → ℕ) (z : Fin n → ℂ) (hz : z ∈ Metric.cthickening (2 * ε) R) :
      ‖mvTaylorCoeff F z α‖ ≤ M * ε⁻¹ ^ (∑ i, α i) := by
    have hball : Metric.closedBall z ε ⊆ Metric.cthickening (3 * ε) R :=
      (hthick (by positivity) hε.le hz).trans_eq (by ring_nf)
    exact (hF.mono (Metric.ball_subset_closedBall.trans (hball.trans h3))).norm_mvTaylorCoeff_le hε
      (fun w hw ↦ hM w (hball (Metric.ball_subset_closedBall hw))) α
  -- The entire extension of `p` maps a strip into the closed `2ε`-neighbourhood of `R`, which
  -- gives `w α` with continuous representative `z ↦ mvTaylorCoeff F z α` composed with `p`.
  obtain ⟨δ, hδ, hmaps⟩ := exists_strip_mem_cthickening T hs.out S c hε
  have h2 : Metric.cthickening (2 * ε) R ⊆ Metric.cthickening (3 * ε) R :=
    Metric.cthickening_mono (by linarith) R
  choose w hw hwn using fun α ↦ exists_toContinuousMap_eq_comp_sum_single T hs.out S c
    (G := fun z ↦ mvTaylorCoeff F z α) hδ (fun z hz ↦ (Metric.cthickening_subset_of_subset ε
      (Set.range_subset_iff.2 hp)).trans
        ((Metric.cthickening_cthickening_subset hε.le hε.le R).trans_eq (by ring_nf)) (hmaps z hz))
    (((hF.analyticOnNhd_of_finiteDimensional hU).mvTaylorCoeff α).differentiableOn.mono
      (h2.trans h3)) (hcauchy α)
  refine ⟨w, M * √(∑' m, weight (2 * s) m * Real.exp (-(4 * π * δ / T * |(m : ℝ)|))),
    fun α ↦ (hwn α).trans_eq (by ring), fun y x hy ↦ ?_⟩
  -- Taylor's formula for `F` around `p x`, evaluated at `(p + y) x`.
  have hball : Metric.closedBall (fun i ↦ toContinuousMap T hs.out (p i) x) (2 * ε) ⊆ U :=
    (hthick hε.le (by positivity) (hp x)).trans ((Metric.cthickening_mono (by linarith) R).trans h3)
  have hadd : (fun i ↦ toContinuousMap T hs.out (p i + y i) x) =
      (fun i ↦ toContinuousMap T hs.out (p i) x) + fun i ↦ toContinuousMap T hs.out (y i) x :=
    funext fun i ↦ by simp
  refine ⟨hball ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm, hadd, add_sub_cancel_left]
    exact hy.le
  · convert (hF.mono (Metric.ball_subset_closedBall.trans hball)).hasSum_mvTaylorCoeff hy using 1
    · funext α
      rw [hw α x, smul_eq_mul]
    · rw [hadd]

omit hT in
/-- A finite family in `H^s` is approximated by partial sums of the Fourier series of its
entries, all over the same finite set of frequencies. -/
private theorem exists_norm_sub_sum_single_lt (u : Fin n → CircleSobolev s ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ S : Finset ℤ, ‖u - fun i ↦ ∑ m ∈ S, single m ((u i).coeff m)‖ < ρ := by
  have h (i : Fin n) : ∀ᶠ S in Filter.atTop, ‖u i - ∑ m ∈ S, single m ((u i).coeff m)‖ < ρ := by
    filter_upwards [Metric.tendsto_nhds.1 (hasSum_single (u i)) ρ hρ] with S hS
    simpa [dist_eq_norm, norm_sub_rev] using hS
  obtain ⟨S, hS⟩ := (Filter.eventually_all.2 h).exists
  exact ⟨S, (pi_norm_lt_iff hρ).2 hS⟩

/-- The joint values of a finite family in `H^s`, `s > 1/2`, are bounded by its norm, with the
constant of `norm_toContinuousMap_le`. -/
private theorem norm_toContinuousMap_pi_le (a : Fin n → CircleSobolev s ℂ) (x : AddCircle T) :
    ‖fun i ↦ toContinuousMap T hs.out (a i) x‖ ≤ √(∑' m, weight (-(2 * s)) m) * ‖a‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦
    (((toContinuousMap T hs.out (a i)).norm_coe_le_norm x).trans
      (norm_toContinuousMap_le T hs.out (a i))).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm a i) (Real.sqrt_nonneg _))

/-- **Local expansion of the Nemytskii map.** Near every `u₀` with values in `U` there are a
family `p` of trigonometric polynomials, a radius `ρ` with `‖u₀ - p‖ < ρ`, and elements
`w α ∈ H^s` with `‖w α‖ ≤ B ((n + 1) mulConst s ρ)⁻¹ ^ |α|` such that for `‖y‖ < ρ` the function
`F (p + y)` is pointwise the sum of `(w α) y ^ α`. -/
private theorem exists_local_expansion {F : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {u₀ : Fin n → CircleSobolev s ℂ}
    (hu₀ : ∀ x, (fun i ↦ toContinuousMap T hs.out (u₀ i) x) ∈ U) :
    ∃ (p : Fin n → CircleSobolev s ℂ) (w : (Fin n → ℕ) → CircleSobolev s ℂ) (ρ B : ℝ),
      0 < ρ ∧ ‖u₀ - p‖ < ρ ∧
      (∀ α, ‖w α‖ ≤ B * ((n + 1) * mulConst s * ρ)⁻¹ ^ (∑ i, α i)) ∧
      ∀ y : Fin n → CircleSobolev s ℂ, ‖y‖ < ρ → ∀ x,
        (fun i ↦ toContinuousMap T hs.out (p i + y i) x) ∈ U ∧
        HasSum (fun α ↦ (∏ i, toContinuousMap T hs.out (y i) x ^ α i) *
          toContinuousMap T hs.out (w α) x)
          (F (fun i ↦ toContinuousMap T hs.out (p i + y i) x)) := by
  set C := mulConst s
  set K := √(∑' m, weight (-(2 * s)) m)
  set N : ℝ := n + 1
  have hC1 : 1 ≤ C := one_le_mulConst
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hN1 : 1 ≤ N := by simp [N]
  have hsup' := norm_toContinuousMap_pi_le (T := T) (s := s) (n := n)
  -- `F` is bounded on the closed `3ε`-neighbourhood of the range `R` of `u₀`, inside `U`.
  set R := Set.range fun x ↦ fun i ↦ toContinuousMap T hs.out (u₀ i) x
  have hR : IsCompact R := isCompact_range
    (continuous_pi fun i ↦ (toContinuousMap T hs.out (u₀ i)).continuous)
  obtain ⟨δ₀, hδ₀, hsub⟩ := hR.exists_cthickening_subset_open hU (Set.range_subset_iff.2 hu₀)
  set ε := δ₀ / 3 with hε_def
  have hε : 0 < ε := by positivity
  have h3 : Metric.cthickening (3 * ε) R ⊆ U := by rwa [hε_def, mul_div_cancel₀ _ three_ne_zero]
  obtain ⟨M, hM⟩ := hR.cthickening.exists_bound_of_continuousOn (hF.continuousOn.mono h3)
  -- Approximate `u₀` within `ρ` by partial sums `p` of the Fourier series of its entries; then `p`
  -- takes values in the closed `ε`-neighbourhood of `R`, and `‖y‖ < ρ` forces `‖y‖ < 2ε`
  -- pointwise.
  set ρ := ε / (N * C * (K + 1)) with hρ_def
  have hρ : 0 < ρ := by positivity
  have hKρ : K * ρ ≤ ε := by
    rw [hρ_def, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hN1 hC1) hε.le]
  have hNCρ : N * C * ρ ≤ ε := by
    rw [hρ_def, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (zero_le_one.trans hN1) (zero_le_one.trans hC1)) hε.le]
  obtain ⟨S, hup⟩ := exists_norm_sub_sum_single_lt u₀ hρ
  set p : Fin n → CircleSobolev s ℂ := fun i ↦ ∑ m ∈ S, single m ((u₀ i).coeff m)
  have hp (x : AddCircle T) : (fun i ↦ toContinuousMap T hs.out (p i) x) ∈
      Metric.cthickening ε R := by
    refine Metric.mem_cthickening_of_dist_le _ _ ε R ⟨x, rfl⟩ ?_
    rw [dist_comm, dist_eq_norm]
    have hsub : (fun i ↦ toContinuousMap T hs.out (u₀ i) x) -
        (fun i ↦ toContinuousMap T hs.out (p i) x) =
        fun i ↦ toContinuousMap T hs.out ((u₀ - p) i) x := funext fun i ↦ by simp
    rw [hsub]
    exact (hsup' _ x).trans ((mul_le_mul_of_nonneg_left hup.le hK0).trans hKρ)
  obtain ⟨w, B, hw, htaylor⟩ := exists_taylor_coeff T hU hF hε h3 hM S
    (fun i m ↦ (u₀ i).coeff m) hp
  have hB : 0 ≤ B := by simpa using (norm_nonneg _).trans (hw 0)
  refine ⟨p, w, ρ, B, hρ, hup, fun α ↦ (hw α).trans ?_, fun y hy x ↦ htaylor y x ?_⟩
  · gcongr
  · exact (hsup' y x).trans_lt ((mul_le_mul_of_nonneg_left hy.le hK0).trans hKρ |>.trans_lt
      (by linarith))

omit hT in
/-- The multilinear map `(y₁, …, yₖ) ↦ w (y₁ (g 1)) ⋯ (yₖ (g k))` on families of elements of
`H^s`. -/
private def monomialMap (w : CircleSobolev s ℂ) {k : ℕ} (g : Fin k → Fin n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k ↦ Fin n → CircleSobolev s ℂ) (CircleSobolev s ℂ) :=
  (convolution hs.out (.mul ℂ ℂ) w).compContinuousMultilinearMap
    ((ContinuousMultilinearMap.mkPiAlgebraFin ℂ k (CircleSobolev s ℂ)).compContinuousLinearMap
      fun j ↦ ContinuousLinearMap.proj (g j))

omit hT in
private theorem monomialMap_apply_const (w : CircleSobolev s ℂ) {k : ℕ} (g : Fin k → Fin n)
    (α : Fin n → ℕ) (hg : ∀ i, (Finset.univ.filter fun j ↦ g j = i).card = α i)
    (y : Fin n → CircleSobolev s ℂ) :
    monomialMap w g (fun _ ↦ y) = w * ∏ i, y i ^ α i := by
  classical
  simp only [monomialMap, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.proj_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn, ← mul_def]
  congr 1
  rw [← Finset.prod_fiberwise Finset.univ g (fun j ↦ y (g j))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Finset.prod_congr rfl fun j hj ↦ by rw [(Finset.mem_filter.1 hj).2], Finset.prod_const,
    hg i]

omit hT in
private theorem norm_monomialMap_le (w : CircleSobolev s ℂ) {k : ℕ} (g : Fin k → Fin n) :
    ‖monomialMap w g‖ ≤ mulConst s * ‖w‖ * mulConst s ^ k := by
  set C := mulConst s
  have hC0 : 0 < C := one_pos.trans_le one_le_mulConst
  have hL : ‖convolution hs.out (.mul ℂ ℂ) w‖ ≤ C * ‖w‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b ↦ by
      simpa only [mul_def] using norm_mul_le_mulConst w b
  have hm : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ k (CircleSobolev s ℂ)‖ ≤ C ^ k :=
    ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ by
      simp only [ContinuousMultilinearMap.mkPiAlgebraFin_apply]
      refine (norm_list_prod_le (List.ofFn m)).trans ?_
      simp only [List.length_ofFn, List.map_ofFn, List.prod_ofFn]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ one_le_mulConst (Nat.sub_le k 1))
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
  have hproj : ‖ContinuousMultilinearMap.compContinuousLinearMap
      (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k (CircleSobolev s ℂ))
      (fun j ↦ ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ CircleSobolev s ℂ) (g j))‖
      ≤ C ^ k :=
    (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans <|
      (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
        fun i _ ↦ ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y ↦ by
          simpa using norm_le_pi_norm y (g i))).trans hm
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (mul_le_mul hL hproj (norm_nonneg _) (by positivity))

omit hT in
open Classical in
/-- The power series on families in `H^s` whose degree-`k` term is `y ↦ ∑_{|α| = k} (w α) y ^ α`,
with one chosen ordering of the factors for each multi-index. -/
private def mvSeries (w : (Fin n → ℕ) → CircleSobolev s ℂ) :
    FormalMultilinearSeries ℂ (Fin n → CircleSobolev s ℂ) (CircleSobolev s ℂ) := fun k ↦
  ∑ α ∈ Finset.univ.piAntidiag k,
    if hα : ∑ i, α i = k then
      monomialMap (w α) (exists_forall_card_filter_eq (α := Fin k)
        (hα.trans (Fintype.card_fin k).symm)).choose
    else 0

omit hT in
private theorem mvSeries_apply_const (w : (Fin n → ℕ) → CircleSobolev s ℂ) (k : ℕ)
    (y : Fin n → CircleSobolev s ℂ) :
    mvSeries w k (fun _ ↦ y) = ∑ α ∈ Finset.univ.piAntidiag k, w α * ∏ i, y i ^ α i := by
  classical
  simp only [mvSeries, FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  have hαk : ∑ i, α i = k := (Finset.mem_piAntidiag.1 hα).1
  rw [dite_eq_left_of_eq_true (eq_true hαk)]
  exact monomialMap_apply_const _ _ α (exists_forall_card_filter_eq (α := Fin k)
    (hαk.trans (Fintype.card_fin k).symm)).choose_spec y

omit hT in
/-- The series `mvSeries w` has radius at least `ρ` when
`‖w α‖ ≤ B ((n + 1) mulConst s ρ)⁻¹ ^ |α|`. -/
private theorem le_radius_mvSeries {w : (Fin n → ℕ) → CircleSobolev s ℂ} {ρ B : ℝ}
    (hρ : 0 < ρ) (hw : ∀ α, ‖w α‖ ≤ B * ((n + 1) * mulConst s * ρ)⁻¹ ^ (∑ i, α i)) :
    (ρ.toNNReal : ENNReal) ≤ (mvSeries w).radius := by
  classical
  set C := mulConst s
  have hC0 : 0 < C := one_pos.trans_le one_le_mulConst
  have hB : 0 ≤ B := by simpa using (norm_nonneg _).trans (hw 0)
  refine FormalMultilinearSeries.le_radius_of_bound _ (C * B) fun k ↦ ?_
  rw [Real.coe_toNNReal _ hρ.le]
  have hterm (α) (hα : α ∈ Finset.univ.piAntidiag k) :
      ‖if hα : ∑ i, α i = k then monomialMap (w α) (exists_forall_card_filter_eq (α := Fin k)
        (hα.trans (Fintype.card_fin k).symm)).choose else 0‖ ≤
        C * (B * ((n + 1) * C * ρ)⁻¹ ^ k) * C ^ k := by
    have hαk : ∑ i, α i = k := (Finset.mem_piAntidiag.1 hα).1
    rw [dite_eq_left_of_eq_true (eq_true hαk)]
    refine (norm_monomialMap_le _ _).trans ?_
    gcongr
    exact hαk ▸ hw α
  calc ‖mvSeries w k‖ * ρ ^ k
      ≤ (n ^ k * (C * (B * ((n + 1) * C * ρ)⁻¹ ^ k) * C ^ k)) * ρ ^ k := by
        gcongr
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast Fintype.card_fin n ▸ Finset.card_piAntidiag_univ_le (ι := Fin n) k
    _ = C * B * (n / (n + 1)) ^ k := by
        rw [div_pow, inv_pow, mul_pow, mul_pow]
        field_simp
    _ ≤ C * B := mul_le_of_le_one_right (by positivity)
        (pow_le_one₀ (by positivity) ((div_le_one (by positivity)).2 (by linarith)))

/-- The local expansion of `exists_local_expansion`, summed in `H^s`: near every `u₀` with values
in `U`, the Nemytskii map has the power series `mvSeries w` around `p`, and the continuous
representative of `nemytskiiPi F (p + y)` is `F ∘ (p + y)`. -/
private theorem exists_hasFPowerSeriesOnBall_nemytskiiPi {F : (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {u₀ : Fin n → CircleSobolev s ℂ}
    (hu₀ : ∀ x, (fun i ↦ toContinuousMap T hs.out (u₀ i) x) ∈ U) :
    ∃ (p : Fin n → CircleSobolev s ℂ) (w : (Fin n → ℕ) → CircleSobolev s ℂ) (ρ : ℝ),
      0 < ρ ∧ ‖u₀ - p‖ < ρ ∧
      HasFPowerSeriesOnBall (nemytskiiPi F) (mvSeries w) p (ρ.toNNReal : ENNReal) ∧
      ∀ y : Fin n → CircleSobolev s ℂ, ‖y‖ < ρ → ∀ x,
        toContinuousMap T hs.out (nemytskiiPi F (p + y)) x =
          F (fun i ↦ toContinuousMap T hs.out (p i + y i) x) := by
  classical
  obtain ⟨p, w, ρ, B, hρ, hp, hw, h⟩ := exists_local_expansion T hU hF hu₀
  have hrad := le_radius_mvSeries hρ hw
  -- For `‖y‖ < ρ` the series converges in `H^s`, and its sum has the right continuous
  -- representative, obtained by evaluating the multi-index expansion pointwise.
  have hy (y : Fin n → CircleSobolev s ℂ) (hy : ‖y‖ < ρ) :
      HasSum (fun k ↦ mvSeries w k (fun _ ↦ y)) (nemytskiiPi F (p + y)) ∧
      ∀ x, toContinuousMap T hs.out (nemytskiiPi F (p + y)) x =
        F (fun i ↦ toContinuousMap T hs.out (p i + y i) x) := by
    have hy' : y ∈ Metric.eball (0 : Fin n → CircleSobolev s ℂ) (ρ.toNNReal : ENNReal) := by
      rw [Metric.eball_coe, mem_ball_zero_iff, Real.coe_toNNReal _ hρ.le]
      exact hy
    have hsum := ((mvSeries w).summable_norm_apply
      (Metric.eball_subset_eball hrad hy')).of_norm.hasSum
    have hx (x : AddCircle T) : toContinuousMap T hs.out (∑' k, mvSeries w k (fun _ ↦ y)) x =
        F (fun i ↦ toContinuousMap T hs.out (p i + y i) x) := by
      refine ((hsum.mapL (toContinuousMap T hs.out)).mapL (ContinuousMap.evalCLM ℂ x)).unique ?_
      -- Group the pointwise multi-index expansion by total degree.
      refine ((Finset.sigmaPiAntidiagUnivEquiv (Fin n) ℕ).hasSum_iff.2 (h y hy x).2).sigma
        fun k ↦ ?_
      have hprod (α : Fin n → ℕ) : toContinuousMap T hs.out (∏ i, y i ^ α i) x =
          ∏ i, toContinuousMap T hs.out (y i) x ^ α i := by
        simp only [← coe_toContinuousMapAlgHom T, map_prod, map_pow, ContinuousMap.coe_prod,
          Finset.prod_apply, ContinuousMap.coe_pow, Pi.pow_apply]
      simp only [Function.comp_apply, ContinuousMap.evalCLM_apply, mvSeries_apply_const, map_sum,
        toContinuousMap_mul, ContinuousMap.mul_apply, hprod]
      simp_rw [mul_comm (toContinuousMap T hs.out (w _) x)]
      rw [← Finset.sum_coe_sort]
      exact hasSum_fintype _
    rw [nemytskiiPi_eq_of_forall_toContinuousMap_apply T (u := p + y) (by simpa using hx)]
    exact ⟨hsum, hx⟩
  refine ⟨p, w, ρ, hρ, hp, ⟨hrad, ENNReal.coe_pos.2 (Real.toNNReal_pos.2 hρ), fun {y} hy' ↦ ?_⟩,
    fun y hy' ↦ (hy y hy').2⟩
  rw [Metric.eball_coe, mem_ball_zero_iff, Real.coe_toNNReal _ hρ.le] at hy'
  exact (hy y hy').1

/-- **Holomorphic functions of several variables act on `H^s`, `s > 1/2`.** If `F` is holomorphic
on an open set `U ⊆ ℂⁿ` and the continuous representatives of `u : Fin n → H^s` take their joint
values in `U`, then `x ↦ F (fun i ↦ u i x)` is the continuous representative of
`nemytskiiPi F u ∈ H^s`. -/
theorem toContinuousMap_nemytskiiPi {F : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {u : Fin n → CircleSobolev s ℂ}
    (hu : ∀ x, (fun i ↦ toContinuousMap T hs.out (u i) x) ∈ U) (x : AddCircle T) :
    toContinuousMap T hs.out (nemytskiiPi F u) x =
      F (fun i ↦ toContinuousMap T hs.out (u i) x) := by
  obtain ⟨p, _, ρ, _, hp, _, h⟩ := exists_hasFPowerSeriesOnBall_nemytskiiPi T hU hF hu
  simpa only [add_sub_cancel, Pi.sub_apply] using h (u - p) hp x

/-- **The holomorphic Nemytskii map is holomorphic.** If `F` is holomorphic on an open set
`U ⊆ ℂⁿ`, then `u ↦ nemytskiiPi F u` is analytic on the open set of families `u : Fin n → H^s`,
`s > 1/2`, with joint values in `U` (`isOpen_setOf_forall_toContinuousMap_pi_mem`). -/
theorem analyticOnNhd_nemytskiiPi {F : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ (nemytskiiPi F)
      {u : Fin n → CircleSobolev s ℂ | ∀ x, (fun i ↦ toContinuousMap T hs.out (u i) x) ∈ U} := by
  intro u₀ hu₀
  obtain ⟨p, w, ρ, hρ, hp, hps, -⟩ := exists_hasFPowerSeriesOnBall_nemytskiiPi T hU hF hu₀
  exact hps.analyticAt_of_mem (by
    rw [Metric.eball_coe, mem_ball_iff_norm, Real.coe_toNNReal _ hρ.le]
    exact hp)

/-- The Nemytskii map of any `F` sends the zero family to the constant function `F 0`. -/
@[simp]
theorem nemytskiiPi_zero (F : (Fin n → ℂ) → ℂ) :
    nemytskiiPi F (0 : Fin n → CircleSobolev s ℂ) = single 0 (F 0) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact nemytskiiPi_eq_of_forall_toContinuousMap_apply 1 fun x ↦ by simp [Pi.zero_def]

/-- **The derivative of the holomorphic Nemytskii map.** If `F` is holomorphic on an open set
`U ⊆ ℂⁿ` and `u : Fin n → H^s` takes its joint values in `U`, then the derivative of
`nemytskiiPi F` at `u` sends `v` to `∑ᵢ (∂ᵢF ∘ u) vᵢ`, where `∂ᵢF ∘ u` is the element
`nemytskiiPi (fun z ↦ fderiv ℂ F z (Pi.single i 1)) u` of `H^s`. -/
theorem hasFDerivAt_nemytskiiPi {F : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {u : Fin n → CircleSobolev s ℂ}
    (hu : ∀ x, (fun i ↦ toContinuousMap T hs.out (u i) x) ∈ U) :
    HasFDerivAt (nemytskiiPi F) (∑ i, (convolution hs.out (.mul ℂ ℂ)
      (nemytskiiPi (fun z ↦ fderiv ℂ F z (Pi.single i 1)) u)).comp
        (ContinuousLinearMap.proj i)) u := by
  have hD := (analyticOnNhd_nemytskiiPi T hU hF u hu).differentiableAt.hasFDerivAt
  refine hD.congr_fderiv (ContinuousLinearMap.ext fun v ↦ toContinuousMap_injective T hs.out <|
    ContinuousMap.ext fun x ↦ ?_)
  -- Both sides are the derivative at `t = 0` of `t ↦ F (u x + t v x)`.
  set ev : CircleSobolev s ℂ →L[ℂ] ℂ := (ContinuousMap.evalCLM ℂ x).comp (toContinuousMap T hs.out)
  set ux : Fin n → ℂ := fun i ↦ toContinuousMap T hs.out (u i) x
  set vx : Fin n → ℂ := fun i ↦ toContinuousMap T hs.out (v i) x
  have hline : HasDerivAt (fun t : ℂ ↦ u + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add u
  have h₁ : HasDerivAt (ev ∘ nemytskiiPi F ∘ fun t : ℂ ↦ u + t • v)
      (ev (fderiv ℂ (nemytskiiPi F) u v)) 0 :=
    ev.hasFDerivAt.comp_hasDerivAt 0 (hD.comp_hasDerivAt_of_eq 0 hline (by simp))
  have hmem : ∀ᶠ t : ℂ in 𝓝 0, ∀ y, (fun i ↦ toContinuousMap T hs.out ((u + t • v) i) y) ∈ U :=
    hline.continuousAt.preimage_mem_nhds
      ((isOpen_setOf_forall_toContinuousMap_pi_mem T hs.out hU).mem_nhds (by simpa using hu))
  have hl : HasDerivAt (fun t : ℂ ↦ ux + t • vx) vx 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const vx).const_add ux
  have h₂ : HasDerivAt (ev ∘ nemytskiiPi F ∘ fun t : ℂ ↦ u + t • v)
      (fderiv ℂ F ux vx) 0 := by
    refine ((hF.differentiableAt (hU.mem_nhds (hu x))).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl
      (by rw [zero_smul, add_zero])).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with t ht
    simp only [ev, Function.comp_apply, ContinuousLinearMap.coe_comp, ContinuousMap.evalCLM_apply,
      toContinuousMap_nemytskiiPi T hU hF ht]
    congr 1
    funext i
    simp [ux, vx]
  have hpart (i : Fin n) : DifferentiableOn ℂ (fun z ↦ fderiv ℂ F z (Pi.single i 1)) U :=
    ((hF.analyticOnNhd_of_finiteDimensional hU).fderiv.differentiableOn).clm_apply
      (differentiableOn_const _)
  have h := h₂.unique h₁
  simp only [ev, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply] at h
  have hsum : fderiv ℂ F ux vx = ∑ i, fderiv ℂ F ux (Pi.single i 1) * vx i := by
    conv_lhs => rw [pi_eq_sum_univ' vx]
    simp [map_sum, map_smul, mul_comm]
  rw [← h, hsum, FunLike.coe_sum, Finset.sum_apply, map_sum, ContinuousMap.coe_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    toContinuousMap_convolution_apply, toContinuousMap_nemytskiiPi T hU (hpart i) hu,
    ContinuousLinearMap.mul_apply', ux, vx]

/-- A function `F` holomorphic on an open set `U ⊆ ℂ` gives the function `z ↦ F (z 0)` on
`Fin 1 → ℂ`, holomorphic on the open preimage of `U`: the one-variable case of the
several-variable hypotheses. -/
private theorem isOpen_and_differentiableOn_comp_apply_zero {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    IsOpen ((fun z : Fin 1 → ℂ ↦ z 0) ⁻¹' U) ∧
      DifferentiableOn ℂ (fun z : Fin 1 → ℂ ↦ F (z 0)) ((fun z : Fin 1 → ℂ ↦ z 0) ⁻¹' U) :=
  ⟨hU.preimage (continuous_apply 0),
    hF.comp (differentiable_apply 0).differentiableOn fun _ hz ↦ hz⟩

omit hT in
/-- The scalar Nemytskii map is the Nemytskii map of one variable composed with the diagonal
embedding `H^s → (Fin 1 → H^s)`. -/
private theorem nemytskii_eq_comp (F : ℂ → ℂ) :
    nemytskii F = nemytskiiPi (fun z : Fin 1 → ℂ ↦ F (z 0)) ∘
      ContinuousLinearMap.pi (fun _ ↦ ContinuousLinearMap.id ℂ (CircleSobolev s ℂ)) :=
  funext fun u ↦ nemytskii_eq_nemytskiiPi F u

/-- **Holomorphic functions act on `H^s`, `s > 1/2`.** If `F` is holomorphic on an open set `U`
and the continuous representative of `u ∈ H^s` takes values in `U`, then `F ∘ u` is the continuous
representative of `nemytskii F u ∈ H^s`. -/
theorem toContinuousMap_nemytskii {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {u : CircleSobolev s ℂ}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U) (x : AddCircle T) :
    toContinuousMap T hs.out (nemytskii F u) x = F (toContinuousMap T hs.out u x) := by
  obtain ⟨hU₁, hF₁⟩ := isOpen_and_differentiableOn_comp_apply_zero hU hF
  rw [nemytskii_eq_nemytskiiPi]
  exact toContinuousMap_nemytskiiPi T hU₁ hF₁ (u := fun _ ↦ u) (fun x ↦ hu x) x

/-- **The holomorphic Nemytskii map is holomorphic.** If `F` is holomorphic on an open set `U`,
then `u ↦ nemytskii F u` is analytic on the open subset of `H^s`, `s > 1/2`, of elements with
values in `U` (`isOpen_setOf_forall_toContinuousMap_mem`). -/
theorem analyticOnNhd_nemytskii {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ (nemytskii F)
      {u : CircleSobolev s ℂ | ∀ x, toContinuousMap T hs.out u x ∈ U} := by
  obtain ⟨hU₁, hF₁⟩ := isOpen_and_differentiableOn_comp_apply_zero hU hF
  rw [nemytskii_eq_comp]
  exact (analyticOnNhd_nemytskiiPi T hU₁ hF₁).comp (ContinuousLinearMap.analyticOnNhd _ _)
    fun u hu x ↦ hu x

/-- The Nemytskii map of an entire function is analytic on all of `H^s`, `s > 1/2`. -/
theorem analyticAt_nemytskii {F : ℂ → ℂ} (hF : Differentiable ℂ F) (u : CircleSobolev s ℂ) :
    AnalyticAt ℂ (nemytskii F) u := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact analyticOnNhd_nemytskii 1 isOpen_univ hF.differentiableOn u fun _ ↦ Set.mem_univ _

/-- The Nemytskii map of any `F` sends the zero function to the constant function `F 0`. -/
@[simp]
theorem nemytskii_zero (F : ℂ → ℂ) : nemytskii F (0 : CircleSobolev s ℂ) = single 0 (F 0) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact nemytskii_eq_of_forall_toContinuousMap_apply 1 fun x ↦ by simp

/-- **The derivative of the holomorphic Nemytskii map.** If `F` is holomorphic on an open set `U`
and `u ∈ H^s` takes values in `U`, then the derivative of `nemytskii F` at `u` is multiplication by
`nemytskii (deriv F) u`, the element of `H^s` with continuous representative `F' ∘ u`. -/
theorem hasFDerivAt_nemytskii {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {u : CircleSobolev s ℂ}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U) :
    HasFDerivAt (nemytskii F) (convolution hs.out (.mul ℂ ℂ) (nemytskii (deriv F) u)) u := by
  obtain ⟨hU₁, hF₁⟩ := isOpen_and_differentiableOn_comp_apply_zero hU hF
  -- The partial derivative of `z ↦ F (z 0)` is `F'` at `z 0`.
  have hderiv (z : Fin 1 → ℂ) :
      fderiv ℂ (fun z : Fin 1 → ℂ ↦ F (z 0)) z (Pi.single 0 1) = deriv F (z 0) := by
    simpa [Function.comp_def] using congr($((ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
      ).comp_right_fderiv (f := F) (x := z)) (Pi.single 0 1))
  have hdiag := (ContinuousLinearMap.pi fun _ : Fin 1 ↦
    ContinuousLinearMap.id ℂ (CircleSobolev s ℂ)).hasFDerivAt (x := u)
  rw [nemytskii_eq_comp]
  convert (hasFDerivAt_nemytskiiPi T hU₁ hF₁ (u := fun _ ↦ u) fun x ↦ hu x).comp u hdiag using 1
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [hderiv, nemytskii_eq_nemytskiiPi]

/-- At the zero function, the derivative of the Nemytskii map of `F` is multiplication by the
scalar `F'(0)`. -/
theorem hasFDerivAt_nemytskii_zero {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (h₀ : 0 ∈ U) :
    HasFDerivAt (nemytskii F) (deriv F 0 • ContinuousLinearMap.id ℂ (CircleSobolev s ℂ)) 0 := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  refine (hasFDerivAt_nemytskii 1 hU hF (u := 0) fun _ ↦ by simpa using h₀).congr_fderiv
    (ContinuousLinearMap.ext fun v ↦ ?_)
  rw [nemytskii_zero, ← mul_def]
  simpa [algebraMap_eq_single] using (Algebra.smul_def (deriv F 0) v).symm

end CircleSobolev

end TauCeti
