/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Normed.Module.Multilinear.Asymptotics
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# H. Cartan's uniqueness theorem

Let `U` be a bounded connected neighbourhood of a point `p` in a complex normed space. **Cartan's
uniqueness theorem** says that a holomorphic self-map `f` of `U` which fixes `p` and has derivative
the identity at `p` is the identity on `U`.

Two consequences follow. A biholomorphism of a bounded connected neighbourhood `U` of `0` which is
circular (stable under multiplication by complex numbers of modulus one) and which fixes `0` is the
restriction of its derivative at `0`: it commutes with the rotations, by the uniqueness theorem, and
a holomorphic map commuting with the rotations has no homogeneous terms of degree other than one.
For the open ball, a continuous linear map sending `ball 0 r` into itself has operator norm at most
one (`ContinuousLinearMap.opNorm_le_one_of_mapsTo_ball`), so two mutually inverse such maps are
isometries, and a biholomorphism of a ball fixing its centre `0` is the restriction of a linear
isometric equivalence. On the unit ball of `EuclideanSpace ℂ (Fin n)` these are the unitary maps.
Combined with a group of biholomorphisms acting transitively on the ball, such as the fractional
linear maps of `U(1, n)`, this is the step towards describing every biholomorphism of the ball.

## Main results

* `AnalyticOnNhd.eqOn_id_of_fderiv_eq_id`: **Cartan's uniqueness theorem.**
* `AnalyticAt.eventuallyEq_fderiv_of_map_smul`: a holomorphic map fixing `0` and commuting with
  the rotations `z ↦ a • z`, `‖a‖ = 1`, agrees near `0` with its derivative at `0`.
* `AnalyticOnNhd.eqOn_fderiv_of_invOn`: **Cartan's linearity theorem.** A biholomorphism of a
  bounded circular domain fixing `0` agrees with its derivative at `0`.
* `AnalyticOnNhd.exists_linearIsometryEquiv_eqOn_ball`: a biholomorphism of `ball 0 r` fixing `0`
  is the restriction of a linear isometric equivalence.

Holomorphy is stated as analyticity, which in finite dimension follows from complex
differentiability on an open set by Tau Ceti's `DifferentiableOn.analyticOnNhd_of_finiteDimensional`
(in `TauCeti.Analysis.Complex.CauchyIntegralPolydisc`).

## The argument

Write `f (p + y) = p + y + P y + O(‖y‖ ^ (k + 1))`, where `P` is the first nonzero homogeneous term
of `f - id` at `p`, of degree `k ≥ 2`. Then the `j`-th iterate satisfies
`f^[j] (p + y) = p + y + j • P y + O(‖y‖ ^ (k + 1))`. The iterates map `U` into itself, so
`f^[j] - id` is bounded on a ball `ball p r` by a constant independent of `j`, and it vanishes to
order `k` at `p`; the higher-order Schwarz lemma
(`Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO`) bounds it by a constant multiple of
`‖y‖ ^ k`, uniformly in `j`. Comparing with `j • P y` along a line through `p` gives
`j * ‖P v‖ ≤ C` for all `j`, so `P = 0`. Hence all homogeneous terms of `f - id` vanish,
`f = id` near `p`, and by the identity theorem on all of `U`.

## References

* H. Cartan, *Sur les groupes de transformations analytiques*, Actualités scientifiques et
  industrielles 198, Hermann, Paris, 1935.
* W. Rudin, *Function Theory in the Unit Ball of `ℂⁿ`*, Grundlehren 241, Springer, 1980,
  Section 2.1.
* W. M. Goldman, *Complex Hyperbolic Geometry*, Oxford University Press, 1999, Chapter 3.
-/

public section

open Set Filter Topology Metric Asymptotics Bornology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

namespace TauCeti.CartanUniqueness

/-- If `f (p + y) = p + y + P y + O(‖y‖ ^ (k + 1))` with `P` homogeneous of degree `k ≥ 2` and
`f p = p`, then `f^[j] (p + y) = p + y + j • P y + O(‖y‖ ^ (k + 1))`. -/
private lemma isBigO_iterate_sub {f : E → E} {p : E} {k : ℕ} (hk : 2 ≤ k)
    (q : ContinuousMultilinearMap ℂ (fun _ : Fin k => E) E)
    (hf : (fun y => f (p + y) - (p + y) - q fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^ (k + 1))
    (j : ℕ) :
    (fun y => f^[j] (p + y) - (p + y) - (j : ℂ) • q fun _ => y) =O[𝓝 0]
      fun y => ‖y‖ ^ (k + 1) := by
  induction j with
  | zero => simpa using isBigO_zero _ _
  | succ j ih =>
    -- `w y` is the displacement of the `j`-th iterate, `f^[j] (p + y) = p + w y`.
    set w : E → E := fun y => f^[j] (p + y) - p with hw_def
    have hwy : (fun y => w y - y) =O[𝓝 0] fun y => ‖y‖ ^ k := by
      simpa only [hw_def, sub_sub] using q.isBigO_of_isBigO_sub_smul_apply_const ih
    have hw1 : w =O[𝓝 0] fun y => ‖y‖ := isBigO_norm_of_isBigO_sub_norm_pow (by omega) hwy
    have hw0 : Tendsto w (𝓝 0) (𝓝 0) := hw1.trans_tendsto tendsto_norm_zero
    have key : (fun y => f^[j + 1] (p + y) - (p + y) - ((j + 1 : ℕ) : ℂ) • q fun _ => y) =
        fun y => (f (p + w y) - (p + w y) - q fun _ => w y) +
          (f^[j] (p + y) - (p + y) - (j : ℂ) • q fun _ => y) +
            ((q fun _ => w y) - q fun _ => y) := by
      ext y
      simp only [hw_def, Function.iterate_succ_apply', add_sub_cancel, Nat.cast_succ, add_smul,
        one_smul]
      abel
    rw [key]
    exact (((hf.comp_tendsto hw0).trans (hw1.norm_left.pow (k + 1))).add ih).add
      (q.isBigO_apply_const_sub hk hwy)

/-- **Schwarz's lemma for the iterates.** Under the hypotheses of `isBigO_iterate_sub`, if
`f` is a holomorphic self-map of `U` with `ball p r ⊆ U ⊆ closedBall p R`, then
`‖f^[j] z - z‖ ≤ (R + r) * (‖z - p‖ / r) ^ k` on `ball p r`, for every `j`. -/
private lemma norm_iterate_sub_le {f : E → E} {U : Set E} {p : E} {k : ℕ} (hk : 2 ≤ k)
    (q : ContinuousMultilinearMap ℂ (fun _ : Fin k => E) E) (hfd : DifferentiableOn ℂ f U)
    (hmaps : MapsTo f U U) (hfp : f p = p)
    (hf : (fun y => f (p + y) - (p + y) - q fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^ (k + 1))
    {r R : ℝ} (hrU : ball p r ⊆ U) (hR : U ⊆ closedBall p R) (j : ℕ) {z : E}
    (hz : z ∈ ball p r) : ‖f^[j] z - z‖ ≤ (R + r) * (‖z - p‖ / r) ^ k := by
  have hjd : DifferentiableOn ℂ f^[j] U := hfd.iterate hmaps j
  have hmaps' : MapsTo (fun z => f^[j] z - z) (ball p r) (closedBall (f^[j] p - p) (R + r)) := by
    intro z hz
    rw [Function.iterate_fixed hfp, sub_self, mem_closedBall, dist_zero_right]
    have h1 := hR (hmaps.iterate j (hrU hz))
    rw [mem_closedBall, dist_eq_norm] at h1
    rw [mem_ball, dist_eq_norm] at hz
    calc ‖f^[j] z - z‖ = ‖(f^[j] z - p) - (z - p)‖ := by congr 1; abel
      _ ≤ R + r := (norm_sub_le _ _).trans (add_le_add h1 hz.le)
  -- `f^[j] - id` vanishes to order `k` at `p`, by `isBigO_iterate_sub`.
  have hlo : (fun z => (f^[j] z - z) - (f^[j] p - p)) =o[𝓝 p] fun z => ‖z - p‖ ^ (k - 1) := by
    have h0 : (fun y => f^[j] (p + y) - (p + y)) =o[𝓝 0] fun y => ‖y‖ ^ (k - 1) :=
      (q.isBigO_of_isBigO_sub_smul_apply_const (isBigO_iterate_sub hk q hf j)).trans_isLittleO
        (isLittleO_norm_pow_norm_pow (by omega))
    have := h0.comp_tendsto (tendsto_sub_nhds_zero_iff.2 (tendsto_id (x := 𝓝 p)))
    simpa [Function.iterate_fixed hfp, Function.comp_def] using this
  have := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    ((hjd.mono hrU).sub differentiableOn_id) hmaps' hlo hz
  simpa [Function.iterate_fixed hfp, dist_eq_norm, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    using this

/-- A holomorphic self-map `f` of a bounded neighbourhood `U` of `p` with `f p = p` and
`f (p + y) = p + y + P y + O(‖y‖ ^ (k + 1))`, for `P` homogeneous of degree `k ≥ 2`, has `P = 0`:
by `norm_iterate_sub_le`, `j * ‖P v‖` is bounded independently of `j`. -/
private lemma apply_eq_zero_of_isBigO {f : E → E} {U : Set E} {p : E} {k : ℕ} (hk : 2 ≤ k)
    (q : ContinuousMultilinearMap ℂ (fun _ : Fin k => E) E) (hfd : DifferentiableOn ℂ f U)
    (hU : U ∈ 𝓝 p) (hUb : IsBounded U) (hmaps : MapsTo f U U) (hfp : f p = p)
    (hf : (fun y => f (p + y) - (p + y) - q fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^ (k + 1))
    (v : E) : (q fun _ => v) = 0 := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨R, hR⟩ := hUb.subset_closedBall p
  set C := (R + r) * (‖v‖ / r) ^ k + ‖v‖ ^ k
  have hbound (j : ℕ) : (j : ℝ) * ‖q fun _ => v‖ ≤ C := by
    -- Compare `j • P y` with `f^[j] (p + y) - (p + y)` at a point `y = t • v` close to `0`.
    have hlo := ((isBigO_iterate_sub hk q hf j).trans_isLittleO
      (isLittleO_norm_pow_norm_pow (E' := E) (lt_add_one k))).bound one_pos
    have hball : ∀ᶠ y in 𝓝 (0 : E), p + y ∈ ball p r := by
      filter_upwards [ball_mem_nhds (0 : E) hr] with y hy
      simpa [mem_ball, dist_eq_norm] using hy
    have ht : Tendsto (fun t : ℂ => t • v) (𝓝[≠] 0) (𝓝 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      have : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
      simpa using this.tendsto 0
    obtain ⟨t, ⟨h1, h2⟩, ht0⟩ := ((ht.eventually (hlo.and hball)).and self_mem_nhdsWithin).exists
    have hsch := norm_iterate_sub_le hk q hfd hmaps hfp hf hrU hR j h2
    have hsmul : (q fun _ => t • v) = t ^ k • q fun _ => v := by
      simpa using q.map_smul_univ (fun _ => t) fun _ => v
    have h1' : ‖f^[j] (p + t • v) - (p + t • v) - ((j : ℂ) * t ^ k) • q fun _ => v‖ ≤
        ‖t • v‖ ^ k := by
      simpa [hsmul, smul_smul] using h1
    rw [add_sub_cancel_left] at hsch
    have htk : 0 < ‖t‖ ^ k := pow_pos (norm_pos_iff.2 ht0) k
    refine le_of_mul_le_mul_left ?_ htk
    calc ‖t‖ ^ k * (j * ‖q fun _ => v‖) = ‖((j : ℂ) * t ^ k) • q fun _ => v‖ := by
          simp only [norm_smul, norm_mul, norm_pow, Complex.norm_natCast]
          ring
      _ ≤ ‖f^[j] (p + t • v) - (p + t • v)‖ +
          ‖f^[j] (p + t • v) - (p + t • v) - ((j : ℂ) * t ^ k) • q fun _ => v‖ := by
          rw [norm_sub_rev (f^[j] (p + t • v) - (p + t • v))]
          exact norm_le_norm_add_norm_sub' _ _
      _ ≤ (R + r) * (‖t • v‖ / r) ^ k + ‖t • v‖ ^ k := add_le_add hsch h1'
      _ = ‖t‖ ^ k * C := by
          simp only [C, norm_smul]
          ring
  by_contra hv
  obtain ⟨j, hj⟩ := exists_nat_gt (C / ‖q fun _ => v‖)
  have hpos : 0 < ‖q fun _ => v‖ := norm_pos_iff.2 hv
  exact absurd (hbound j) (not_le.2 ((div_lt_iff₀ hpos).1 hj))

end TauCeti.CartanUniqueness

open TauCeti.CartanUniqueness

/-- **H. Cartan's uniqueness theorem.** Let `U` be a bounded connected neighbourhood of `p` in a
complex normed space. A holomorphic map `f` sending `U` into itself, fixing `p` and with derivative
the identity at `p`, is the identity on `U`. -/
theorem AnalyticOnNhd.eqOn_id_of_fderiv_eq_id {f : E → E} {U : Set E} {p : E}
    (hf : AnalyticOnNhd ℂ f U) (hU : U ∈ 𝓝 p) (hUc : IsPreconnected U) (hUb : IsBounded U)
    (hmaps : MapsTo f U U) (hfp : f p = p) (hDf : fderiv ℂ f p = ContinuousLinearMap.id ℂ E) :
    EqOn f id U := by
  have hp : p ∈ U := mem_of_mem_nhds hU
  obtain ⟨q, hq⟩ : AnalyticAt ℂ (fun z => f z - z) p := (hf p hp).sub analyticAt_id
  -- It suffices that every homogeneous term of `f - id` at `p` vanishes.
  suffices h : ∀ n y, (q n fun _ => y) = 0 by
    refine hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_id hUc hp ?_
    filter_upwards [hq.eventually_hasSum_sub] with z hz
    exact sub_eq_zero.1 (hz.unique (by simp [h]))
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n, ih with
  | 0, _ => exact fun y => by simpa [hfp] using hq.coeff_zero fun _ => y
  | 1, _ =>
    intro y
    have hD : fderiv ℂ (fun z => f z - z) p = 0 := by
      rw [fderiv_fun_sub (hf p hp).differentiableAt differentiableAt_fun_id, hDf, fderiv_fun_id,
        sub_self]
    simpa [Matrix.vec_single_eq_const] using congr($(hq.fderiv_eq.symm.trans hD) y)
  | k + 2, ih =>
    -- The lower terms vanish, so `f (p + y) = p + y + q (k + 2) y + O(‖y‖ ^ (k + 3))`.
    have hsum (y : E) : q.partialSum (k + 3) y = q (k + 2) fun _ => y := by
      rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
        Finset.sum_eq_zero fun m hm => ih m (by simp at hm; omega) y, zero_add]
    have hO := hq.isBigO_sub_partialSum_pow (k + 3)
    simp only [hsum] at hO
    exact apply_eq_zero_of_isBigO (by omega) (q (k + 2)) hf.differentiableOn hU hUb hmaps hfp hO

/-- A holomorphic map near `0` fixing `0` and commuting with the rotations `z ↦ a • z`, `‖a‖ = 1`,
agrees near `0` with its derivative at `0`. -/
theorem AnalyticAt.eventuallyEq_fderiv_of_map_smul {f : E → F} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0)
    (h : ∀ a : ℂ, ‖a‖ = 1 → ∀ᶠ z in 𝓝 0, f (a • z) = a • f z) :
    f =ᶠ[𝓝 0] fderiv ℂ f 0 := by
  obtain ⟨q, hq⟩ := hf
  have hrot (a : ℂ) (ha : ‖a‖ = 1) (n : ℕ) (y : E) :
      a ^ n • (q n fun _ => y) = a • q n fun _ => y := by
    set u := a • ContinuousLinearMap.id ℂ E
    have hq' : HasFPowerSeriesAt f q (u 0) := by simpa [u] using hq
    -- `z ↦ f (a • z) - a • f z` vanishes near `0`, and its series has terms `(a ^ n - a) • P`:
    -- each homogeneous term `P` of degree `n` satisfies `a ^ n • P y = a • P y`.
    have h0 := ((hq'.compContinuousLinearMap.sub (hq.const_smul (c := a))).congr
      (g := 0) (by filter_upwards [h a ha] with z hz; simp [u, hz])).apply_eq_zero n y
    have hsmul := (q n).map_smul_univ (fun _ => a) fun _ => y
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hsmul
    simp only [FormalMultilinearSeries.sub_apply, FormalMultilinearSeries.smul_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply, sub_apply, smul_apply,
      Function.comp_def, u, ContinuousLinearMap.id_apply, hsmul, sub_eq_zero] at h0
    exact h0
  have hzero (n : ℕ) (hn : n ≠ 1) (y : E) : (q n fun _ => y) = 0 := by
    match n, hn with
    | 0, _ => simpa [hf0] using hq.coeff_zero fun _ => y
    | m + 2, _ =>
      -- For `a = exp (π i / (m + 1))`, `a ^ (m + 2) = -a`.
      set a := Complex.exp (Real.pi / (m + 1) * Complex.I)
      have ha : ‖a‖ = 1 := by simpa [a] using Complex.norm_exp_ofReal_mul_I (Real.pi / (m + 1))
      have hpow : a ^ (m + 2) = -a := by
        rw [pow_succ, ← Complex.exp_natCast_mul]
        have : ((m + 1 : ℕ) : ℂ) * (Real.pi / (m + 1) * Complex.I) = Real.pi * Complex.I := by
          push_cast
          field_simp
        rw [this, Complex.exp_pi_mul_I]
        ring
      have h2 := hrot a ha (m + 2) y
      rw [hpow] at h2
      have h2' : (2 * a) • (q (m + 2) fun _ => y) = 0 := by
        linear_combination (norm := module) -h2
      exact (smul_eq_zero.1 h2').resolve_left (mul_ne_zero two_ne_zero (by simp [a]))
  filter_upwards [hq.eventually_hasSum] with y hy
  rw [zero_add] at hy
  refine hy.unique ?_
  convert hasSum_single (f := fun n => q n fun _ => y) 1 fun n hn => hzero n hn y using 1
  simp [hq.fderiv_eq, Matrix.vec_single_eq_const]

namespace TauCeti.CartanUniqueness

/-- If `g` is a left inverse of `f` on a neighbourhood `U` of `0` and `f 0 = 0`, the derivatives
satisfy `Dg(0) ∘ Df(0) = id`. -/
private lemma fderiv_comp_fderiv_eq_id {f g : E → E} {U : Set E} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hU : U ∈ 𝓝 0) (hinv : LeftInvOn g f U) (hf0 : f 0 = 0) :
    (fderiv ℂ g 0).comp (fderiv ℂ f 0) = ContinuousLinearMap.id ℂ E := by
  have h0 : (0 : E) ∈ U := mem_of_mem_nhds hU
  have := fderiv_comp_fderiv_eq_id_of_eqOn_comp_id (uniqueDiffWithinAt_of_mem_nhds hU)
    (hf 0 h0).differentiableAt (by rw [hf0]; exact (hg 0 h0).differentiableAt) hinv.eqOn h0
  rwa [hf0] at this

/-- A biholomorphism `f` of a bounded connected circular neighbourhood `U` of `0` fixing `0`
commutes with the rotations: `g ∘ (a⁻¹ • ·) ∘ f ∘ (a • ·)` fixes `0` with derivative the identity,
so it is the identity on `U` by Cartan's uniqueness theorem. -/
private lemma map_smul_of_invOn {f g : E → E} {U : Set E} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hU : U ∈ 𝓝 0) (hUc : IsPreconnected U) (hUb : IsBounded U)
    (hcirc : ∀ a : ℂ, ‖a‖ = 1 → MapsTo (a • ·) U U) (hfU : MapsTo f U U) (hgU : MapsTo g U U)
    (hinv : InvOn g f U U) (hf0 : f 0 = 0) {a : ℂ} (ha : ‖a‖ = 1) {z : E} (hz : z ∈ U) :
    f (a • z) = a • f z := by
  have h0 : (0 : E) ∈ U := mem_of_mem_nhds hU
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have ha' : ‖a⁻¹‖ = 1 := by simp [ha]
  have hg0 : g 0 = 0 := by simpa [hf0] using hinv.1 h0
  have hmem {z : E} (hz : z ∈ U) : a⁻¹ • f (a • z) ∈ U := hcirc _ ha' (hfU (hcirc a ha hz))
  set h : E → E := fun z => g (a⁻¹ • f (a • z))
  have hhU : MapsTo h U U := fun z hz => hgU (hmem hz)
  have hsm (c : ℂ) (x : E) : AnalyticAt ℂ (fun z : E => c • z) x := by fun_prop
  have hh : AnalyticOnNhd ℂ h U := fun z hz => by
    have h1 : AnalyticAt ℂ (fun z => f (a • z)) z := (hf _ (hcirc a ha hz)).comp (hsm a z)
    have h2 : AnalyticAt ℂ (fun z => a⁻¹ • f (a • z)) z := (hsm a⁻¹ _).comp h1
    exact (hg _ (hmem hz)).comp_of_eq h2 rfl
  -- The derivative of `h` at `0` is `Dg(0) ∘ Df(0)`, the identity since `g ∘ f = id` near `0`.
  have hgf := fderiv_comp_fderiv_eq_id hf hg hU hinv.1 hf0
  have hDh : fderiv ℂ h 0 = ContinuousLinearMap.id ℂ E := by
    have hS (c : ℂ) (x : E) : HasFDerivAt (fun z : E => c • z) (c • ContinuousLinearMap.id ℂ E) x :=
      (hasFDerivAt_id x).const_smul c
    have hDf' : HasFDerivAt f (fderiv ℂ f 0) (a • (0 : E)) := by
      rw [smul_zero]
      exact (hf 0 h0).differentiableAt.hasFDerivAt
    have hDg' : HasFDerivAt g (fderiv ℂ g 0) (a⁻¹ • f (a • (0 : E))) := by
      rw [smul_zero, hf0, smul_zero]
      exact (hg 0 h0).differentiableAt.hasFDerivAt
    have hDh' : HasFDerivAt h ((fderiv ℂ g 0).comp
        (a⁻¹ • (fderiv ℂ f 0).comp (a • ContinuousLinearMap.id ℂ E))) 0 :=
      hDg'.comp 0 ((hDf'.comp 0 (hS a 0)).const_smul a⁻¹)
    rw [hDh'.fderiv]
    ext y
    have := congr($hgf y)
    simpa [smul_smul, inv_mul_cancel₀ ha0] using this
  have hid := hh.eqOn_id_of_fderiv_eq_id hU hUc hUb hhU (by simp [h, hf0, hg0]) hDh hz
  have := congrArg f hid
  simp only [h, id, hinv.2 (hmem hz)] at this
  rw [← this, smul_inv_smul₀ ha0]

end TauCeti.CartanUniqueness

/-- **H. Cartan's linearity theorem.** Let `U` be a bounded connected neighbourhood of `0` in a
complex normed space which is circular: `a • z ∈ U` for `z ∈ U` and `‖a‖ = 1`. A biholomorphism `f`
of `U` with inverse `g` and `f 0 = 0` agrees on `U` with its derivative at `0`. -/
theorem AnalyticOnNhd.eqOn_fderiv_of_invOn {f g : E → E} {U : Set E} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hU : U ∈ 𝓝 0) (hUc : IsPreconnected U) (hUb : IsBounded U)
    (hcirc : ∀ a : ℂ, ‖a‖ = 1 → MapsTo (a • ·) U U) (hfU : MapsTo f U U) (hgU : MapsTo g U U)
    (hinv : InvOn g f U U) (hf0 : f 0 = 0) : EqOn f (fderiv ℂ f 0) U :=
  hf.eqOn_of_preconnected_of_eventuallyEq ((fderiv ℂ f 0).analyticOnNhd U) hUc (mem_of_mem_nhds hU)
    ((hf 0 (mem_of_mem_nhds hU)).eventuallyEq_fderiv_of_map_smul hf0 fun _a ha =>
      eventually_of_mem hU fun _z hz =>
        map_smul_of_invOn hf hg hU hUc hUb hcirc hfU hgU hinv hf0 ha hz)

/-- A biholomorphism of a ball `ball 0 r` in a complex normed space fixing `0` is the restriction
of a linear isometric equivalence. For the unit ball of `EuclideanSpace ℂ (Fin n)` these are the
unitary maps. -/
theorem AnalyticOnNhd.exists_linearIsometryEquiv_eqOn_ball {f g : E → E} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 r)) (hg : AnalyticOnNhd ℂ g (ball 0 r))
    (hfU : MapsTo f (ball 0 r) (ball 0 r)) (hgU : MapsTo g (ball 0 r) (ball 0 r))
    (hinv : InvOn g f (ball 0 r) (ball 0 r)) (hf0 : f 0 = 0) :
    ∃ L : E ≃ₗᵢ[ℂ] E, EqOn f L (ball 0 r) := by
  rcases le_or_gt r 0 with hr | hr
  · exact ⟨LinearIsometryEquiv.refl ℂ E, by simp [ball_eq_empty.2 hr]⟩
  have hU : ball (0 : E) r ∈ 𝓝 0 := ball_mem_nhds 0 hr
  have hcirc : ∀ a : ℂ, ‖a‖ = 1 → MapsTo (a • ·) (ball (0 : E) r) (ball 0 r) :=
    fun a ha z hz => by simpa [norm_smul, ha] using hz
  have hg0 : g 0 = 0 := by simpa [hf0] using hinv.1 (mem_ball_self hr)
  have hfL := hf.eqOn_fderiv_of_invOn hg hU (convex_ball 0 r).isPreconnected isBounded_ball hcirc
    hfU hgU hinv hf0
  have hgL := hg.eqOn_fderiv_of_invOn hf hU (convex_ball 0 r).isPreconnected isBounded_ball hcirc
    hgU hfU hinv.symm hg0
  -- `Df(0)` and `Dg(0)` are mutually inverse and map the ball into itself, so they are isometries.
  have h21 := fderiv_comp_fderiv_eq_id hf hg hU hinv.1 hf0
  have h12 := fderiv_comp_fderiv_eq_id hg hf hU hinv.2 hg0
  have hnorm (L : E →L[ℂ] E) (hL : MapsTo L (ball 0 r) (ball 0 r)) (x : E) : ‖L x‖ ≤ ‖x‖ :=
    (L.le_of_opNorm_le (L.opNorm_le_one_of_mapsTo_ball hr hL) x).trans_eq (one_mul _)
  have hf1 := hnorm (fderiv ℂ f 0) fun x hx => hfL hx ▸ hfU hx
  have hg1 := hnorm (fderiv ℂ g 0) fun x hx => hgL hx ▸ hgU hx
  have hgf (x : E) : fderiv ℂ g 0 (fderiv ℂ f 0 x) = x := by simpa using congr($h21 x)
  refine ⟨{ (ContinuousLinearEquiv.ofContinuousLinearMap _ _ h12 h21).toLinearEquiv with
    norm_map' := fun x => le_antisymm (hf1 x) ?_ }, hfL⟩
  calc ‖x‖ = ‖fderiv ℂ g 0 (fderiv ℂ f 0 x)‖ := by rw [hgf]
    _ ≤ ‖fderiv ℂ f 0 x‖ := hg1 _
