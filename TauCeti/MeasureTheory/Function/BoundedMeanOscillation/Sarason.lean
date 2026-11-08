/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
public import Mathlib.Analysis.Convolution
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Convolution.Basic

/-!
# Sarason's characterization of vanishing mean oscillation

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`. A function
`f : E → F` has vanishing mean oscillation (`TauCeti.MemVMO`) when it has bounded mean oscillation
and its VMO modulus `η_f(r)`, the supremum of its mean oscillations over balls of radius at most
`r`, tends to `0` with `r`. **Sarason's theorem** identifies these functions as the closure, for
the BMO seminorm, of the uniformly continuous functions of bounded mean oscillation:
`f` has vanishing mean oscillation if and only if it is locally integrable and there are uniformly
continuous `gₖ` of bounded mean oscillation with `‖f - gₖ‖_{BMO} → 0`
(`TauCeti.memVMO_iff_exists_tendsto_bmoSeminorm_sub`). The reverse implication is the closedness
of VMO (`TauCeti.memVMO_of_tendsto_bmoSeminorm`) together with `UniformContinuous.memVMO`; this
file proves the forward one (`TauCeti.MemVMO.exists_tendsto_bmoSeminorm_sub`).

The approximants are the mollifications `ψ ⋆ f` of `f`, and the forward implication rests on two
estimates for a kernel `ψ`.

* If `ψ ≥ 0` is continuous, has integral one, vanishes off the closed ball of radius `t` and is
  bounded by `M`, then for every locally integrable `f`
  `‖f - ψ ⋆ f‖_{BMO} ≤ (3 + 4ⁿ⁺¹ M μ(B(0, t))) η_f(t)`, where `n` is the dimension of `E`
  (`TauCeti.bmoSeminorm_sub_convolution_le`). The factor `M μ(B(0, t))` is invariant under the
  rescalings `t⁻ⁿ ψ(·/t)`, so the bound tends to `0` along such a family as `t → 0` exactly when
  `η_f(t)` does.
* If `ψ` is continuous with compact support and `f` has bounded mean oscillation, then `ψ ⋆ f` is
  uniformly continuous (`TauCeti.MemBMO.uniformContinuous_convolution`): the increments of `ψ ⋆ f`
  only see `f` minus its average on a ball, whose integral the BMO seminorm controls.

On a ball `B(c, r)` with `r ≤ t`, both `f` and `ψ ⋆ f` oscillate by multiples of `η_f(t)`, the
latter because `ψ ⋆ f` is an average of translates of `f`. On a ball with `r > t`, the mean
oscillation of `f - ψ ⋆ f` is at most twice its mean size, and `|f x - (ψ ⋆ f) x|` is bounded by
the average of `|f x - f w|` over `w ∈ closedBall x t`. Integrating over `x ∈ B(c, r)`, each pair
`(x, w)` lies in `B(y, t)` for every `y` within `t / 2` of its midpoint, so averaging over `y`
bounds the double integral by the mean oscillations of `f` on the balls `B(y, t)`.

## Main declarations

* `TauCeti.bmoSeminorm_sub_convolution_le`: the distance in BMO from `f` to its mollification is
  controlled by the VMO modulus at the scale of the kernel.
* `TauCeti.MemBMO.uniformContinuous_convolution`: mollifying a function of bounded mean
  oscillation by a continuous kernel with compact support gives a uniformly continuous function.
* `TauCeti.MemVMO.exists_tendsto_bmoSeminorm_sub` and
  `TauCeti.memVMO_iff_exists_tendsto_bmoSeminorm_sub`: Sarason's theorem.

## References

* D. Sarason, *Functions of vanishing mean oscillation*, Trans. Amer. Math. Soc. **207** (1975),
  391–405, Theorem 1.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Set Module ContinuousLinearMap
open scoped ENNReal NNReal Topology Convolution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}

/-! ### Integrals over pairs of nearby points -/

/-- The integral of `‖f x - f w‖ₑ` over pairs of points of a ball of radius `t` is at most
`μ(B(0, t))² · 2 η_f(t)`. -/
private theorem lintegral_lintegral_ball_enorm_sub_le (y : E) (t : ℝ) :
    ∫⁻ x in ball y t, ∫⁻ w in ball y t, ‖f x - f w‖ₑ ∂μ ∂μ ≤
      μ (ball (0 : E) t) ^ 2 * (2 * vmoModulus f μ t) := by
  have hfin : μ (ball y t) ≠ ∞ := measure_ball_lt_top.ne
  calc ∫⁻ x in ball y t, ∫⁻ w in ball y t, ‖f x - f w‖ₑ ∂μ ∂μ
      = μ (ball y t) * (μ (ball y t) *
          ⨍⁻ x in ball y t, ⨍⁻ w in ball y t, ‖f x - f w‖ₑ ∂μ ∂μ) := by
        rw [lintegral_congr fun x => (measure_mul_setLAverage _ hfin).symm,
          lintegral_const_mul' _ _ hfin, measure_mul_setLAverage _ hfin]
    _ ≤ μ (ball y t) * (μ (ball y t) * (2 * vmoModulus f μ t)) := by
        gcongr
        exact setLAverage_setLAverage_enorm_sub_le.trans
          (by gcongr; exact setLAverage_enorm_sub_setAverage_le_vmoModulus f μ y le_rfl)
    _ = μ (ball (0 : E) t) ^ 2 * (2 * vmoModulus f μ t) := by
        rw [Measure.addHaar_ball_center μ y t, ← mul_assoc, sq]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `y` within `t / 2` of the midpoint of `x ∈ B(c, r)` and `w ∈ closedBall x t`, both `x`
and `w` lie in `B(y, t)`, and `y ∈ B(c, r + t)`. -/
private theorem dist_lt_of_mem_ball_midpoint {c x w y : E} {r t : ℝ} (hx : x ∈ ball c r)
    (hw : w ∈ closedBall x t) (hy : y ∈ ball (midpoint ℝ x w) (t / 2)) :
    dist y c < r + t ∧ dist x y < t ∧ dist w y < t := by
  have hxw : dist w x ≤ t := hw
  have hxm : dist x (midpoint ℝ x w) ≤ t / 2 := by
    rw [dist_left_midpoint, Real.norm_ofNat, dist_comm]
    linarith
  have hwm : dist w (midpoint ℝ x w) ≤ t / 2 := by
    rw [dist_right_midpoint, Real.norm_ofNat, dist_comm]
    linarith
  have hym : dist y (midpoint ℝ x w) < t / 2 := hy
  have hxc : dist x c < r := hx
  refine ⟨?_, ?_, ?_⟩
  · linarith [dist_triangle y (midpoint ℝ x w) c, dist_triangle (midpoint ℝ x w) x c,
      dist_comm (midpoint ℝ x w) x]
  · linarith [dist_triangle x (midpoint ℝ x w) y, dist_comm (midpoint ℝ x w) y]
  · linarith [dist_triangle w (midpoint ℝ x w) y, dist_comm (midpoint ℝ x w) y]

/-- The integrand of the averaging argument below: `‖f x - f w‖ₑ` when `y ∈ B(c, r + t)` and
`x, w ∈ B(y, t)`, and `0` otherwise. -/
private noncomputable def nearPairIntegrand (f : E → F) (c : E) (r t : ℝ) (y x w : E) : ℝ≥0∞ :=
  if dist y c < r + t ∧ dist x y < t ∧ dist w y < t then ‖f x - f w‖ₑ else 0

omit [NormedSpace ℝ F] in
private theorem measurable_nearPairIntegrand (hf : StronglyMeasurable f) (c : E) (r t : ℝ) :
    Measurable fun q : (E × E) × E => nearPairIntegrand f c r t q.1.1 q.1.2 q.2 := by
  refine Measurable.ite ?_ ((hf.comp_measurable measurable_fst.snd).sub
    (hf.comp_measurable measurable_snd)).enorm measurable_const
  exact (measurableSet_lt (measurable_fst.fst.dist measurable_const) measurable_const).inter
    ((measurableSet_lt (measurable_fst.snd.dist measurable_fst.fst) measurable_const).inter
      (measurableSet_lt (measurable_snd.dist measurable_fst.fst) measurable_const))

/-- For fixed `y ∈ B(c, r + t)`, the double integral of `nearPairIntegrand f c r t y` is the
integral of `‖f x - f w‖ₑ` over `B(y, t) × B(y, t)`. -/
private theorem lintegral_lintegral_nearPairIntegrand_le (c : E) (r t : ℝ) (y : E) :
    ∫⁻ x, ∫⁻ w, nearPairIntegrand f c r t y x w ∂μ ∂μ ≤
      (ball c (r + t)).indicator (fun _ => μ (ball (0 : E) t) ^ 2 * (2 * vmoModulus f μ t)) y := by
  by_cases hy : dist y c < r + t
  · rw [indicator_of_mem (mem_ball.2 hy)]
    refine le_of_eq_of_le ?_ (lintegral_lintegral_ball_enorm_sub_le y t)
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun x => ?_
    by_cases hx : dist x y < t
    · rw [indicator_of_mem (mem_ball.2 hx), ← lintegral_indicator measurableSet_ball]
      refine lintegral_congr fun w => ?_
      by_cases hw : dist w y < t
      · simp [nearPairIntegrand, hy, hx, hw]
      · simp [nearPairIntegrand, hw]
    · simp [nearPairIntegrand, hx]
  · simp [nearPairIntegrand, hy]

omit [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- For `x ∈ B(c, r)` and `w ∈ closedBall x t`, the integral of `nearPairIntegrand f c r t · x w`
is at least `μ(B(0, t / 2)) ‖f x - f w‖ₑ`. -/
private theorem mul_enorm_sub_le_lintegral_nearPairIntegrand {c x w : E} {r t : ℝ}
    (hx : x ∈ ball c r) (hw : w ∈ closedBall x t) :
    μ (ball (0 : E) (t / 2)) * ‖f x - f w‖ₑ ≤ ∫⁻ y, nearPairIntegrand f c r t y x w ∂μ := by
  have hle : (ball (midpoint ℝ x w) (t / 2)).indicator (fun _ => ‖f x - f w‖ₑ) ≤
      fun y => nearPairIntegrand f c r t y x w := by
    intro y
    by_cases hy : y ∈ ball (midpoint ℝ x w) (t / 2)
    · simp [nearPairIntegrand, indicator_of_mem hy, dist_lt_of_mem_ball_midpoint hx hw hy]
    · simp [indicator_of_notMem hy]
  have h := lintegral_mono (μ := μ) hle
  rwa [lintegral_indicator_const measurableSet_ball, Measure.addHaar_ball_center, mul_comm] at h

/-- The integral of `‖f x - f w‖ₑ` over the pairs `x ∈ B(c, r)`, `w ∈ closedBall x t` is
controlled by the VMO modulus at scale `t`. Each such pair lies in `B(y, t)` for every `y` in the
ball of radius `t / 2` about its midpoint, so averaging over these `y` reduces the estimate to the
mean oscillation of `f` on the balls `B(y, t)`, `y ∈ B(c, r + t)`. -/
private theorem lintegral_lintegral_closedBall_enorm_sub_le (hf : StronglyMeasurable f) {t : ℝ}
    (ht : 0 < t) (c : E) (r : ℝ) :
    ∫⁻ x in ball c r, ∫⁻ w in closedBall x t, ‖f x - f w‖ₑ ∂μ ∂μ ≤
      (μ (ball (0 : E) (t / 2)))⁻¹ *
        (μ (ball c (r + t)) * (μ (ball (0 : E) t) ^ 2 * (2 * vmoModulus f μ t))) := by
  set ρ := μ (ball (0 : E) (t / 2))
  have hρ0 : ρ ≠ 0 := (measure_ball_pos μ _ (half_pos ht)).ne'
  have hρtop : ρ ≠ ∞ := measure_ball_lt_top.ne
  set Φ := nearPairIntegrand f c r t
  have hΦm := measurable_nearPairIntegrand hf c r t
  calc ∫⁻ x in ball c r, ∫⁻ w in closedBall x t, ‖f x - f w‖ₑ ∂μ ∂μ
      ≤ ∫⁻ x in ball c r, ∫⁻ w in closedBall x t, ρ⁻¹ * ∫⁻ y, Φ y x w ∂μ ∂μ ∂μ := by
        refine setLIntegral_mono' measurableSet_ball fun x hx =>
          setLIntegral_mono' measurableSet_closedBall fun w hw => ?_
        calc ‖f x - f w‖ₑ = ρ⁻¹ * (ρ * ‖f x - f w‖ₑ) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hρ0 hρtop, one_mul]
          _ ≤ ρ⁻¹ * ∫⁻ y, Φ y x w ∂μ := by
              gcongr
              exact mul_enorm_sub_le_lintegral_nearPairIntegrand hx hw
    _ ≤ ∫⁻ x, ∫⁻ w, ρ⁻¹ * ∫⁻ y, Φ y x w ∂μ ∂μ ∂μ :=
        (setLIntegral_le_lintegral _ _).trans
          (lintegral_mono fun x => setLIntegral_le_lintegral _ _)
    _ = ρ⁻¹ * ∫⁻ x, ∫⁻ w, ∫⁻ y, Φ y x w ∂μ ∂μ ∂μ := by
        simp_rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hρ0)]
    _ = ρ⁻¹ * ∫⁻ y, ∫⁻ x, ∫⁻ w, Φ y x w ∂μ ∂μ ∂μ := by
        congr 1
        have hswap (x : E) : ∫⁻ w, ∫⁻ y, Φ y x w ∂μ ∂μ = ∫⁻ y, ∫⁻ w, Φ y x w ∂μ ∂μ :=
          lintegral_lintegral_swap
            (hΦm.comp ((measurable_snd.prodMk measurable_const).prodMk
              measurable_fst)).aemeasurable
        simp_rw [hswap]
        exact lintegral_lintegral_swap
          (hΦm.lintegral_prod_right'.comp measurable_swap).aemeasurable
    _ ≤ ρ⁻¹ * (μ (ball c (r + t)) * (μ (ball (0 : E) t) ^ 2 * (2 * vmoModulus f μ t))) := by
        gcongr
        refine (lintegral_mono (lintegral_lintegral_nearPairIntegrand_le c r t)).trans ?_
        rw [lintegral_indicator_const measurableSet_ball, mul_comm]

/-! ### Mollification -/

/-- On a ball of radius at most `r`, the average of `‖g x - g y‖ₑ` over pairs of points, for
`g = ψ ⋆ f`, is at most `2 η_f(r)`: `g` is an average of translates of `f`. -/
private theorem setLAverage_setLAverage_enorm_convolution_sub_le {ψ : E → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∫ x, ψ x ∂μ = 1)
    (hf : StronglyMeasurable f) (hfi : LocallyIntegrable f μ) (c : E) {s r : ℝ} (hs : s ≤ r) :
    ⨍⁻ x in ball c s, ⨍⁻ y in ball c s,
        ‖(ψ ⋆[lsmul ℝ ℝ, μ] f) x - (ψ ⋆[lsmul ℝ ℝ, μ] f) y‖ₑ ∂μ ∂μ ≤
      2 * vmoModulus f μ r := by
  set ν := (μ (ball c s))⁻¹ • μ.restrict (ball c s)
  set K : E → E → E → ℝ≥0∞ := fun x y z => ENNReal.ofReal (ψ z) * ‖f (x - z) - f (y - z)‖ₑ
    with hK
  have hKm : Measurable fun q : (E × E) × E => K q.1.1 q.1.2 q.2 :=
    (ENNReal.measurable_ofReal.comp (hψ.measurable.comp measurable_snd)).mul
      ((hf.comp_measurable (measurable_fst.fst.sub measurable_snd)).sub
        (hf.comp_measurable (measurable_fst.snd.sub measurable_snd))).enorm
  have hψl : ∫⁻ z, ENNReal.ofReal (ψ z) ∂μ = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hψ.integrable_of_hasCompactSupport hψc)
      (ae_of_all _ hψ0), hψ1, ENNReal.ofReal_one]
  calc ⨍⁻ x in ball c s, ⨍⁻ y in ball c s,
        ‖(ψ ⋆[lsmul ℝ ℝ, μ] f) x - (ψ ⋆[lsmul ℝ ℝ, μ] f) y‖ₑ ∂μ ∂μ
      ≤ ∫⁻ x, ∫⁻ y, ∫⁻ z, K x y z ∂μ ∂ν ∂ν := by
        simp only [setLAverage_eq']
        exact lintegral_mono fun x => lintegral_mono fun y =>
          (enorm_convolution_lsmul_sub_convolution_lsmul_le hψ hψc hfi x y).trans_eq
            (lintegral_congr fun z => by rw [Real.enorm_of_nonneg (hψ0 z)])
    _ = ∫⁻ z, ENNReal.ofReal (ψ z) * ∫⁻ x, ∫⁻ y, ‖f (x - z) - f (y - z)‖ₑ ∂ν ∂ν ∂μ := by
        have hswap (x : E) : ∫⁻ y, ∫⁻ z, K x y z ∂μ ∂ν = ∫⁻ z, ∫⁻ y, K x y z ∂ν ∂μ :=
          lintegral_lintegral_swap
            (hKm.comp ((measurable_const.prodMk measurable_fst).prodMk
              measurable_snd)).aemeasurable
        have hH : Measurable fun p : E × E => ∫⁻ y, K p.1 y p.2 ∂ν :=
          (hKm.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk
            measurable_fst.snd)).lintegral_prod_right'
        simp_rw [hswap]
        rw [lintegral_lintegral_swap hH.aemeasurable]
        simp_rw [hK, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ z, ENNReal.ofReal (ψ z) * (2 * vmoModulus f μ r) ∂μ := by
        refine lintegral_mono fun z => mul_le_mul_right ?_ _
        simp only [ν, ← setLAverage_eq']
        refine setLAverage_setLAverage_enorm_sub_le.trans (mul_le_mul_right ?_ _)
        simpa only [sub_eq_add_neg, vmoModulus_comp_add_right] using
          setLAverage_enorm_sub_setAverage_le_vmoModulus (fun x => f (x + -z)) μ c hs
    _ = 2 * vmoModulus f μ r := by
        rw [lintegral_mul_const _ hψ.measurable.ennreal_ofReal, hψl, one_mul]

/-! ### The distance in BMO from `f` to its mollification -/

variable [CompleteSpace F]

/-- On a ball of radius `r ≤ t`, the mean oscillation of `f - ψ ⋆ f` is at most `3 η_f(t)`. -/
private theorem setLAverage_enorm_sub_convolution_sub_setAverage_le_of_le {ψ : E → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψ1 : ∫ x, ψ x ∂μ = 1) (hf : StronglyMeasurable f) (hfi : LocallyIntegrable f μ) (c : E)
    {r t : ℝ} (hrt : r ≤ t) :
    ⨍⁻ y in ball c r, ‖(f - ψ ⋆[lsmul ℝ ℝ, μ] f) y -
        ⨍ z in ball c r, (f - ψ ⋆[lsmul ℝ ℝ, μ] f) z ∂μ‖ₑ ∂μ ≤ 3 * vmoModulus f μ t := by
  set g := ψ ⋆[lsmul ℝ ℝ, μ] f with hg_def
  have hg : Continuous g := hψc.continuous_convolution_left (lsmul ℝ ℝ) hψ hfi
  have hosc_g : ⨍⁻ y in ball c r, ‖g y - ⨍ z in ball c r, g z ∂μ‖ₑ ∂μ ≤ 2 * vmoModulus f μ t := by
    refine (setLAverage_enorm_sub_setAverage_le_setLAverage_setLAverage
      hg.aestronglyMeasurable).trans ?_
    have h := setLAverage_setLAverage_enorm_convolution_sub_le hψ hψc hψ0 hψ1 hf hfi c hrt
    rwa [← hg_def] at h
  have hneg : ⨍⁻ y in ball c r, ‖-g y - ⨍ z in ball c r, -g z ∂μ‖ₑ ∂μ =
      ⨍⁻ y in ball c r, ‖g y - ⨍ z in ball c r, g z ∂μ‖ₑ ∂μ := by
    simpa using setLAverage_enorm_const_smul_sub_setAverage (μ := μ) (f := g) (-1 : ℝ)
      (ball c r)
  have hadd := setLAverage_enorm_add_sub_le (μ := μ) (s := ball c r)
    hf.aestronglyMeasurable (hg.aestronglyMeasurable.neg (f := g))
  simp only [Pi.neg_apply, ← sub_eq_add_neg, hneg] at hadd
  simp only [Pi.sub_apply]
  calc ⨍⁻ y in ball c r, ‖f y - g y - ⨍ z in ball c r, (f z - g z) ∂μ‖ₑ ∂μ
      ≤ vmoModulus f μ t + 2 * vmoModulus f μ t := hadd.trans (add_le_add
        (setLAverage_enorm_sub_setAverage_le_vmoModulus f μ c hrt) hosc_g)
    _ = 3 * vmoModulus f μ t := by ring

/-- On a ball of radius `r ≥ t`, the integral of `‖f - ψ ⋆ f‖ₑ` is at most
`2 · 4ⁿ M μ(B(0, t)) η_f(t)` times the measure of the ball. -/
private theorem setLIntegral_enorm_sub_convolution_le {ψ : E → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψ1 : ∫ x, ψ x ∂μ = 1) {t : ℝ} (ht : 0 < t) (hψt : Function.support ψ ⊆ closedBall 0 t)
    {M : ℝ} (hψM : ∀ x, ψ x ≤ M) (hf : StronglyMeasurable f) (hfi : LocallyIntegrable f μ)
    (c : E) {r : ℝ} (htr : t ≤ r) :
    ∫⁻ x in ball c r, ‖f x - (ψ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ∂μ ≤
      2 * 4 ^ finrank ℝ E * (ENNReal.ofReal M * μ (ball (0 : E) t) * vmoModulus f μ t) *
        μ (ball c r) := by
  set n := finrank ℝ E
  set ρ := μ (ball (0 : E) (t / 2))
  have hρ0 : ρ ≠ 0 := (measure_ball_pos μ _ (half_pos ht)).ne'
  have hρtop : ρ ≠ ∞ := measure_ball_lt_top.ne
  have hBt : μ (ball (0 : E) t) = 2 ^ n * ρ := by
    have h := Measure.addHaar_ball_mul_of_pos μ (0 : E) two_pos (t / 2)
    rwa [mul_div_cancel₀ t two_ne_zero, ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat] at h
  have hV : μ (ball c (r + t)) ≤ 2 ^ n * μ (ball c r) := by
    calc μ (ball c (r + t)) ≤ μ (ball c (2 * r)) := measure_mono (ball_subset_ball (by linarith))
      _ = 2 ^ n * μ (ball c r) := by
          rw [Measure.addHaar_ball_mul_of_pos μ c two_pos, ENNReal.ofReal_pow zero_le_two,
            ENNReal.ofReal_ofNat, ← Measure.addHaar_ball_center μ c r]
  calc ∫⁻ x in ball c r, ‖f x - (ψ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ∂μ
      ≤ ∫⁻ x in ball c r, ENNReal.ofReal M * ∫⁻ w in closedBall x t, ‖f x - f w‖ₑ ∂μ ∂μ :=
        lintegral_mono (enorm_sub_convolution_lsmul_le_mul_lintegral hψ hψc hψ1 hψt
          (fun x => (Real.norm_of_nonneg (hψ0 x)).trans_le (hψM x)) hfi)
    _ = ENNReal.ofReal M * ∫⁻ x in ball c r, ∫⁻ w in closedBall x t, ‖f x - f w‖ₑ ∂μ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal M *
          (ρ⁻¹ * (μ (ball c (r + t)) * (μ (ball (0 : E) t) ^ 2 * (2 * vmoModulus f μ t)))) := by
        gcongr
        exact lintegral_lintegral_closedBall_enorm_sub_le hf ht c r
    _ ≤ ENNReal.ofReal M *
          (ρ⁻¹ * (2 ^ n * μ (ball c r) * (μ (ball (0 : E) t) ^ 2 * (2 * vmoModulus f μ t)))) := by
        gcongr
    _ = ENNReal.ofReal M * (ρ⁻¹ * ρ) *
          (2 * (2 ^ n * 2 ^ n) * (2 ^ n * ρ) * vmoModulus f μ t * μ (ball c r)) := by
        rw [hBt]
        ring
    _ = 2 * 4 ^ n * (ENNReal.ofReal M * μ (ball (0 : E) t) * vmoModulus f μ t) *
          μ (ball c r) := by
        rw [ENNReal.inv_mul_cancel hρ0 hρtop, ← mul_pow, hBt]
        norm_num
        ring

/-- `TauCeti.bmoSeminorm_sub_convolution_le` for a strongly measurable `f`. -/
private theorem bmoSeminorm_sub_convolution_le_of_stronglyMeasurable {ψ : E → ℝ}
    (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∫ x, ψ x ∂μ = 1) {t : ℝ} (ht : 0 < t)
    (hψt : Function.support ψ ⊆ closedBall 0 t) {M : ℝ} (hψM : ∀ x, ψ x ≤ M)
    (hf : StronglyMeasurable f) (hfi : LocallyIntegrable f μ) :
    bmoSeminorm (f - ψ ⋆[lsmul ℝ ℝ, μ] f) μ ≤
      (3 + 4 ^ (finrank ℝ E + 1) * ENNReal.ofReal M * μ (ball (0 : E) t)) *
        vmoModulus f μ t := by
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.intro (isCompact_closedBall 0 t) fun x hx =>
      Function.notMem_support.1 fun h => hx (hψt h)
  refine bmoSeminorm_le fun c r => ?_
  rcases le_or_gt r t with hrt | htr
  · calc _ ≤ 3 * vmoModulus f μ t :=
          setLAverage_enorm_sub_convolution_sub_setAverage_le_of_le hψ hψc hψ0 hψ1 hf hfi c hrt
      _ ≤ _ := by
          gcongr
          exact le_self_add
  -- On a ball of radius `r > t`, the mean oscillation is at most twice the mean of `‖f - ψ ⋆ f‖`.
  have hint : IntegrableOn (f - ψ ⋆[lsmul ℝ ℝ, μ] f) (ball c r) μ :=
    ((hfi.sub (hψc.continuous_convolution_left (lsmul ℝ ℝ) hψ hfi).locallyIntegrable)
      |>.integrableOn_isCompact (isCompact_closedBall c r)).mono_set ball_subset_closedBall
  calc _ ≤ 2 * ⨍⁻ y in ball c r, ‖(f - ψ ⋆[lsmul ℝ ℝ, μ] f) y - 0‖ₑ ∂μ :=
        setLAverage_enorm_sub_setAverage_le hint 0
    _ ≤ 2 * (2 * 4 ^ finrank ℝ E *
          (ENNReal.ofReal M * μ (ball (0 : E) t) * vmoModulus f μ t)) := by
        gcongr
        simp only [Pi.sub_apply, sub_zero]
        rw [setLAverage_eq]
        exact ENNReal.div_le_of_le_mul
          (setLIntegral_enorm_sub_convolution_le hψ hψc hψ0 hψ1 ht hψt hψM hf hfi c htr.le)
    _ = 4 ^ (finrank ℝ E + 1) * ENNReal.ofReal M * μ (ball (0 : E) t) * vmoModulus f μ t := by
        ring
    _ ≤ _ := by
        gcongr
        exact le_add_self

/-- **The distance in BMO from a function to its mollification.** Let `ψ ≥ 0` be continuous with
integral one, bounded by `M` and vanishing off the closed ball of radius `t > 0`. For every locally
integrable `f`, the BMO seminorm of `f - ψ ⋆ f` is at most `3 + 4ⁿ⁺¹ M μ(B(0, t))` times the VMO
modulus `η_f(t)`, where `n` is the dimension of `E`. -/
theorem bmoSeminorm_sub_convolution_le {ψ : E → ℝ} (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψ1 : ∫ x, ψ x ∂μ = 1) {t : ℝ} (ht : 0 < t) (hψt : Function.support ψ ⊆ closedBall 0 t)
    {M : ℝ} (hψM : ∀ x, ψ x ≤ M) (hf : LocallyIntegrable f μ) :
    bmoSeminorm (f - ψ ⋆[lsmul ℝ ℝ, μ] f) μ ≤
      (3 + 4 ^ (finrank ℝ E + 1) * ENNReal.ofReal M * μ (ball (0 : E) t)) *
        vmoModulus f μ t := by
  obtain ⟨f', hf'm, hff'⟩ := hf.aestronglyMeasurable
  rw [convolution_congr (lsmul ℝ ℝ) (EventuallyEq.refl _ ψ) hff',
    bmoSeminorm_congr_ae (hff'.sub (EventuallyEq.refl _ _)), vmoModulus_congr_ae hff']
  exact bmoSeminorm_sub_convolution_le_of_stronglyMeasurable hψ hψ0 hψ1 ht hψt hψM hf'm
    (hf.congr hff')

/-! ### Uniform continuity of mollifications -/

/-- For a kernel `ψ` vanishing off `closedBall 0 t`, `f` of bounded mean oscillation and
`dist x y < t`, if `ψ (x - ·)` and `ψ (y - ·)` differ by at most `η` everywhere, then
`(ψ ⋆ f) x` and `(ψ ⋆ f) y` differ by at most `η μ(B(0, 2t)) ‖f‖_{BMO}`. Subtracting the average
`m` of `f` on `B(x, 2t)` costs nothing, since `ψ (x - ·)` and `ψ (y - ·)` have the same
integral. -/
private theorem edist_convolution_le (hf : MemBMO f μ) {ψ : E → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) {t : ℝ} (hψ0 : ∀ z, t < ‖z‖ → ψ z = 0) {x y : E}
    (hxy : dist x y < t) {η : ℝ≥0∞} (hη : ∀ w, ‖ψ (x - w) - ψ (y - w)‖ₑ ≤ η) :
    edist ((ψ ⋆[lsmul ℝ ℝ, μ] f) x) ((ψ ⋆[lsmul ℝ ℝ, μ] f) y) ≤
      η * μ (ball (0 : E) (2 * t)) * bmoSeminorm f μ := by
  have ht : 0 < t := dist_nonneg.trans_lt hxy
  set m := ⨍ w in ball x (2 * t), f w ∂μ
  have hψi : Integrable ψ μ := hψ.integrable_of_hasCompactSupport hψc
  have hix : Integrable (fun w => ψ (x - w) • f w) μ :=
    (hψc.convolutionExists_left (lsmul ℝ ℝ) hψ hf.locallyIntegrable x).integrable_swap
  have hiy : Integrable (fun w => ψ (y - w) • f w) μ :=
    (hψc.convolutionExists_left (lsmul ℝ ℝ) hψ hf.locallyIntegrable y).integrable_swap
  have hd : Integrable (fun w => ψ (x - w) - ψ (y - w)) μ :=
    (hψi.comp_sub_left x).sub (hψi.comp_sub_left y)
  have heq : (ψ ⋆[lsmul ℝ ℝ, μ] f) x - (ψ ⋆[lsmul ℝ ℝ, μ] f) y =
      ∫ w, (ψ (x - w) - ψ (y - w)) • (f w - m) ∂μ := by
    have hm : ∫ w, (ψ (x - w) - ψ (y - w)) • m ∂μ = 0 := by
      rw [integral_smul_const, integral_sub (hψi.comp_sub_left x) (hψi.comp_sub_left y),
        integral_sub_left_eq_self ψ μ x, integral_sub_left_eq_self ψ μ y, sub_self, zero_smul]
    simp only [convolution_eq_swap, lsmul_apply, smul_sub]
    rw [integral_sub ((hix.sub hiy).congr (ae_of_all _ fun w => (sub_smul _ _ _).symm))
      (hd.smul_const m), hm, sub_zero, ← integral_sub hix hiy]
    simp only [sub_smul]
  have hball : μ (ball x (2 * t)) = μ (ball (0 : E) (2 * t)) := Measure.addHaar_ball_center μ x _
  rw [edist_eq_enorm_sub, heq]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ w, ‖(ψ (x - w) - ψ (y - w)) • (f w - m)‖ₑ ∂μ
      ≤ ∫⁻ w, (ball x (2 * t)).indicator (fun w => η * ‖f w - m‖ₑ) w ∂μ := by
        refine lintegral_mono fun w => ?_
        rw [enorm_smul]
        by_cases hw : w ∈ ball x (2 * t)
        · rw [indicator_of_mem hw]
          gcongr
          exact hη w
        · rw [indicator_of_notMem hw]
          have hxw : 2 * t ≤ ‖x - w‖ := by
            simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hw
          have hyw : t < ‖y - w‖ := by
            have h1 : ‖x - w‖ ≤ ‖x - y‖ + ‖y - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
            rw [← dist_eq_norm x y] at h1
            linarith
          simp [hψ0 _ (by linarith : t < ‖x - w‖), hψ0 _ hyw]
    _ = η * (μ (ball x (2 * t)) * ⨍⁻ w in ball x (2 * t), ‖f w - m‖ₑ ∂μ) := by
        have hm : AEMeasurable (fun w => ‖f w - m‖ₑ) (μ.restrict (ball x (2 * t))) :=
          (hf.locallyIntegrable.aestronglyMeasurable.sub aestronglyMeasurable_const).enorm.restrict
        rw [lintegral_indicator measurableSet_ball, lintegral_const_mul'' _ hm,
          measure_mul_setLAverage _ measure_ball_lt_top.ne]
    _ ≤ η * (μ (ball (0 : E) (2 * t)) * bmoSeminorm f μ) := by
        rw [hball]
        gcongr
        exact setLAverage_enorm_sub_setAverage_le_bmoSeminorm f μ x _
    _ = η * μ (ball (0 : E) (2 * t)) * bmoSeminorm f μ := by ring

/-- **Mollifications of functions of bounded mean oscillation are uniformly continuous.** If `f`
has bounded mean oscillation and `ψ` is continuous with compact support, then `ψ ⋆ f` is uniformly
continuous. -/
theorem MemBMO.uniformContinuous_convolution (hf : MemBMO f μ) {ψ : E → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) :
    UniformContinuous (ψ ⋆[lsmul ℝ ℝ, μ] f) := by
  obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : E)
  set t := max R 1
  have ht : 0 < t := lt_max_of_lt_right one_pos
  have hψ0 (z : E) (hz : t < ‖z‖) : ψ z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => by
      have := mem_closedBall_zero_iff.1 (hR h)
      linarith [le_max_left R 1]
  set C := μ (ball (0 : E) (2 * t)) * bmoSeminorm f μ with hC_def
  have hC : C ≠ ∞ := ENNReal.mul_ne_top measure_ball_lt_top.ne hf.bmoSeminorm_ne_top
  refine Metric.uniformContinuous_iff.2 fun ε hε => ?_
  set η := ε / (C.toReal + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hψδ⟩ :=
    Metric.uniformContinuous_iff.1 (hψc.uniformContinuous_of_continuous hψ) η hη
  refine ⟨min t δ, lt_min ht hδ, fun {x y} hxy => ?_⟩
  have hw (w : E) : ‖ψ (x - w) - ψ (y - w)‖ₑ ≤ ENNReal.ofReal η := by
    rw [← edist_eq_enorm_sub, edist_dist]
    refine ENNReal.ofReal_le_ofReal (hψδ ?_).le
    rw [dist_sub_right]
    exact hxy.trans_le (min_le_right _ _)
  have h := edist_convolution_le hf hψ hψc hψ0 (hxy.trans_le (min_le_left _ _)) hw
  rw [mul_assoc, ← hC_def, edist_dist, ← ENNReal.ofReal_toReal hC,
    ← ENNReal.ofReal_mul hη.le, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  calc dist ((ψ ⋆[lsmul ℝ ℝ, μ] f) x) ((ψ ⋆[lsmul ℝ ℝ, μ] f) y) ≤ η * C.toReal := h
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [ENNReal.toReal_nonneg (a := C)]

/-! ### Sarason's theorem -/

/-- Mollifying by the normalized bump `φ.normed μ` of outer radius `φ.rOut ≤ 2 φ.rIn` moves `f`
in BMO by at most `(3 + 4ⁿ⁺¹ 2ⁿ) η_f(φ.rOut)`. -/
private theorem bmoSeminorm_sub_normed_convolution_le (φ : ContDiffBump (0 : E))
    (hφ : φ.rOut ≤ 2 * φ.rIn) (hf : LocallyIntegrable f μ) :
    bmoSeminorm (f - φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) μ ≤
      (3 + 4 ^ (finrank ℝ E + 1) * 2 ^ finrank ℝ E) * vmoModulus f μ φ.rOut := by
  refine (bmoSeminorm_sub_convolution_le φ.continuous_normed φ.nonneg_normed φ.integral_normed
    φ.rOut_pos (φ.support_normed_eq.trans_subset ball_subset_closedBall)
    (φ.normed_le_div_measure_closedBall_rOut μ 2 hφ) hf).trans
      (mul_le_mul_left (add_le_add_right ?_ 3) _)
  have hcb : μ (closedBall (0 : E) φ.rOut) ≠ 0 := (measure_closedBall_pos μ _ φ.rOut_pos).ne'
  have hcbtop : μ (closedBall (0 : E) φ.rOut) ≠ ∞ := measure_closedBall_lt_top.ne
  calc 4 ^ (finrank ℝ E + 1) *
        ENNReal.ofReal (2 ^ finrank ℝ E / μ.real (closedBall (0 : E) φ.rOut)) *
        μ (ball (0 : E) φ.rOut)
      ≤ 4 ^ (finrank ℝ E + 1) *
        ENNReal.ofReal (2 ^ finrank ℝ E / μ.real (closedBall (0 : E) φ.rOut)) *
        μ (closedBall (0 : E) φ.rOut) := by
        gcongr
        exact ball_subset_closedBall
    _ = 4 ^ (finrank ℝ E + 1) * 2 ^ finrank ℝ E := by
        rw [mul_assoc, measureReal_def,
          ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hcb hcbtop),
          ENNReal.ofReal_toReal hcbtop, ENNReal.div_mul_cancel hcb hcbtop,
          ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- **Sarason's theorem**, the approximation half: a function of vanishing mean oscillation is a
limit, in the BMO seminorm, of uniformly continuous functions of bounded mean oscillation. The
approximants are mollifications of `f` at scales tending to `0`. -/
theorem MemVMO.exists_tendsto_bmoSeminorm_sub (hf : MemVMO f μ) :
    ∃ g : ℕ → E → F, (∀ k, UniformContinuous (g k)) ∧ (∀ k, MemBMO (g k) μ) ∧
      Tendsto (fun k => bmoSeminorm (f - g k) μ) atTop (𝓝 0) := by
  -- Normalized bumps of outer radius `1 / (k + 1)` and inner radius half of that.
  let φ (k : ℕ) : ContDiffBump (0 : E) := ContDiffBump.shrinking one_pos k
  set C : ℝ≥0∞ := 3 + 4 ^ (finrank ℝ E + 1) * 2 ^ finrank ℝ E
  have hC : C ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.ofNat_ne_top,
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)⟩
  have hfi := hf.memBMO.locallyIntegrable
  have hbound (k : ℕ) :
      bmoSeminorm (f - (φ k).normed μ ⋆[lsmul ℝ ℝ, μ] f) μ ≤ C * vmoModulus f μ (φ k).rOut :=
    bmoSeminorm_sub_normed_convolution_le (φ k)
      (ContDiffBump.rOut_shrinking_eq_two_mul_rIn one_pos k).le hfi
  refine ⟨fun k => (φ k).normed μ ⋆[lsmul ℝ ℝ, μ] f, fun k => ?_, fun k => ?_, ?_⟩
  · exact hf.memBMO.uniformContinuous_convolution (φ k).continuous_normed
      (φ k).hasCompactSupport_normed
  · have hg : Continuous ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] f) :=
      (φ k).hasCompactSupport_normed.continuous_convolution_left (lsmul ℝ ℝ)
        (φ k).continuous_normed hfi
    refine memBMO_iff.2 ⟨hg.locallyIntegrable, ?_⟩
    have h := bmoSeminorm_sub_le (μ := μ) hfi.aestronglyMeasurable
      (hfi.aestronglyMeasurable.sub hg.aestronglyMeasurable)
    rw [sub_sub_cancel] at h
    refine h.trans_lt (ENNReal.add_lt_top.2 ⟨hf.memBMO.bmoSeminorm_lt_top, ?_⟩)
    exact (hbound k).trans_lt (ENNReal.mul_lt_top hC.lt_top
      ((vmoModulus_le_bmoSeminorm f μ _).trans_lt hf.memBMO.bmoSeminorm_lt_top))
  · have htk : Tendsto (fun k => (φ k).rOut) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨ContDiffBump.tendsto_rOut_shrinking one_pos,
        Eventually.of_forall fun k => (φ k).rOut_pos⟩
    have h := ENNReal.Tendsto.const_mul (hf.tendsto_vmoModulus.comp htk) (Or.inr hC)
    rw [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
      hbound

/-- **Sarason's theorem.** A function has vanishing mean oscillation if and only if it is locally
integrable and a limit, in the BMO seminorm, of uniformly continuous functions of bounded mean
oscillation. -/
theorem memVMO_iff_exists_tendsto_bmoSeminorm_sub :
    MemVMO f μ ↔ LocallyIntegrable f μ ∧ ∃ g : ℕ → E → F, (∀ k, UniformContinuous (g k)) ∧
      (∀ k, MemBMO (g k) μ) ∧ Tendsto (fun k => bmoSeminorm (f - g k) μ) atTop (𝓝 0) :=
  ⟨fun hf => ⟨hf.memBMO.locallyIntegrable, hf.exists_tendsto_bmoSeminorm_sub⟩,
    fun ⟨hfi, _, hgu, hgb, h⟩ =>
      memVMO_of_tendsto_bmoSeminorm hfi (fun k => (hgu k).memVMO (hgb k)) h⟩

end TauCeti
