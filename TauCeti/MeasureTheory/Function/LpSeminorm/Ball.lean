/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Normed.Module.CoveringNumber
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# `Lᵖ` seminorms on all balls of one radius

For an additive Haar measure `μ` on a proper normed additive group, the balls `B(y, r)` of a fixed
radius cover every point equally often when `y` runs over the whole space: by Tonelli's theorem,

`∫⁻ y, ∫⁻ x in B(y, r), G x ∂μ ∂μ = μ (B(0, r)) * ∫⁻ x, G x ∂μ`.

Applied to `G = ‖g‖ₑ ^ p`, the `p`-th powers of the `Lᵖ` seminorms of `g` on the balls of radius `r`
integrate to `μ (B(0, r))` times the `p`-th power of its `Lᵖ` seminorm. Consequently a local
estimate `‖g‖_{Lᵖ(B(y, r))} ≤ ‖h‖_{Lᵖ(B(y, R))}` holding at (almost) every centre `y` becomes the
global estimate

`‖g‖_{Lᵖ} ≤ (μ (B(0, R)) / μ (B(0, r))) ^ (1 / p) ‖h‖_{Lᵖ}`.

On a finite-dimensional real normed space of dimension `d` the volume ratio for `R = κ r` is
`κ ^ d`. In this setting, local estimates of the form
`‖g‖_{Lᵖ(B(y, r))} ≤ c₁ ‖f₁‖_{Lᵖ(B(y, κ r))} + c₂ ‖f₂‖_{Lᵖ(B(y, κ r))}` at almost every centre
give `‖g‖_{Lᵖ} ≤ 2 κ ^ d (c₁ ‖f₁‖_{Lᵖ} + c₂ ‖f₂‖_{Lᵖ})`, with a constant independent of `r`.

On the same balls, Hölder's inequality compares the `L^q` and `Lᵖ` seminorms for `q ≤ p`:
`μ (B(x, r)) ^ (1 / p - 1 / q) ‖f‖_{L^q(B(x, c r))} ≤ c ^ d ‖f‖_{Lᵖ(B(x, c r))}` for `c ≥ 1`, with
both sides scaling in the same way under dilations.

This is how interior estimates on balls with constants independent of the centre, such as the
Calderón–Zygmund estimates for elliptic equations, pass to estimates on the whole space. It
replaces a covering of the space by balls with bounded overlap: averaging over all centres is an
exact form of the bounded-overlap count.

## Main declarations

* `TauCeti.lintegral_setLIntegral_ball`: the Tonelli identity above.
* `TauCeti.lintegral_eLpNorm_restrict_ball_rpow`: its form for `Lᵖ` seminorms.
* `TauCeti.eLpNorm_le_of_ae_eLpNorm_restrict_ball_le`: local estimates on balls of one radius give
  a global estimate.
* `TauCeti.lintegral_rpow_le_of_forall_setLAverage_rpow_le`: the same for local reverse Hölder
  inequalities, whose right-hand side is a power of a mean rather than a mean.
* `TauCeti.eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add`: the same for local estimates by two
  functions on concentric balls of radii `r` and `κ r`, with the explicit constant `2 κ ^ d`.
* `TauCeti.lpNorm_le_of_ae_lpNorm_restrict_ball_le_add`: its case `κ = 2` for `lpNorm`, with the
  constant `2 ^ (d + 1)`.
* `TauCeti.eLpNorm_restrict_le_of_forall_ball_inter_nonempty`: the local form of
  `TauCeti.eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add`, an estimate on a set `V` from local
  estimates on the balls meeting `V`, whose enlargements lie in a set `T`.
* `TauCeti.eLpNorm_le_of_forall_eLpNorm_restrict_ball_le`: estimates on the balls `B(0, R/2)`
  whose error term carries a factor `μ (B(0, R)) ^ e` with `e < 0`, which vanishes as `R → ∞`,
  give a global estimate without that term.
* `TauCeti.measure_ball_rpow_mul_eLpNorm_restrict_ball_le`: Hölder's inequality on a ball, scaled
  by the volume of a concentric smaller ball.
* `MeasureTheory.Measure.exists_mem_ball_norm_le_rpow_neg_mul_toReal_eLpNorm`: Chebyshev point
  selection on a ball, finding `w ∈ B(x₀, r)` with
  `‖f w‖ ≤ |B(0, 1)|^(-1/p) r^(-n/p) ‖f‖_{L^p(B(x₀, r))}`.
* `MeasureTheory.Measure.exists_mem_ball_norm_le_rpow_neg_mul_toReal_eLpNorm_of_dist_le`:
  off-centre Chebyshev point selection in `B(q', r) ∩ B(q, r)` from the `Lᵖ` norm on `B(q, r)`
  when `dist q' q ≤ r / 2`.
* `TauCeti.eLpNorm_restrict_ball_le_of_forall_mem_closedBall`: covering `closedBall x₀ r` by
  balls of radius `s` upgrades uniform local `Lᵖ` bounds in `ℝ≥0∞` to a bound on `B(x₀, r)`.
* `TauCeti.toReal_eLpNorm_restrict_ball_le_of_forall_mem_closedBall`: real-valued covering bound
  on `B(x₀, r)` from uniform finite local `Lᵖ` bounds.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Integrating the integrals of `G` over the balls `B(y, r)` against `μ (dy)` gives
`μ (B(0, r))` times the integral of `G`: every point lies in the balls whose centres form a ball of
the same radius around it. -/
theorem lintegral_setLIntegral_ball {G : E → ℝ≥0∞} (hG : AEMeasurable G μ) (r : ℝ) :
    ∫⁻ y, ∫⁻ x in ball y r, G x ∂μ ∂μ = μ (ball (0 : E) r) * ∫⁻ x, G x ∂μ := by
  have hS : MeasurableSet {z : E × E | dist z.2 z.1 < r} :=
    measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const
  have hjoint : AEMeasurable (Function.uncurry fun y x => (ball y r).indicator G x)
      (μ.prod μ) := by
    have : (Function.uncurry fun y x => (ball y r).indicator G x) =
        {z : E × E | dist z.2 z.1 < r}.indicator fun z => G z.2 := by
      ext ⟨y, x⟩
      simp only [Function.uncurry_apply_pair, Set.indicator, mem_ball, Set.mem_ofPred_eq]
    rw [this]
    exact (hG.comp_snd (μ := μ)).indicator hS
  calc ∫⁻ y, ∫⁻ x in ball y r, G x ∂μ ∂μ
      = ∫⁻ y, ∫⁻ x, (ball y r).indicator G x ∂μ ∂μ := by
        simp_rw [lintegral_indicator measurableSet_ball]
    _ = ∫⁻ x, ∫⁻ y, (ball y r).indicator G x ∂μ ∂μ := lintegral_lintegral_swap hjoint
    _ = ∫⁻ x, μ (ball (0 : E) r) * G x ∂μ := by
        refine lintegral_congr fun x => ?_
        have : (fun y => (ball y r).indicator G x) = (ball x r).indicator fun _ => G x := by
          ext y
          by_cases hxy : x ∈ ball y r
          · rw [Set.indicator_of_mem hxy, Set.indicator_of_mem (mem_ball_comm.1 hxy)]
          · rw [Set.indicator_of_notMem hxy,
              Set.indicator_of_notMem fun h => hxy (mem_ball_comm.1 h)]
        rw [this, lintegral_indicator_const measurableSet_ball, Measure.addHaar_ball_center,
          mul_comm]
    _ = μ (ball (0 : E) r) * ∫⁻ x, G x ∂μ :=
        lintegral_const_mul' _ _ measure_ball_lt_top.ne

variable {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}

/-- The `p`-th powers of the `Lᵖ` seminorms of `g` on the balls `B(y, r)` integrate, against
`μ (dy)`, to `μ (B(0, r))` times the `p`-th power of the `Lᵖ` seminorm of `g`. -/
theorem lintegral_eLpNorm_restrict_ball_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) {g : E → F}
    (hg : AEStronglyMeasurable g μ) (r : ℝ) :
    ∫⁻ y, eLpNorm g p (μ.restrict (ball y r)) ^ p.toReal ∂μ =
      μ (ball (0 : E) r) * eLpNorm g p μ ^ p.toReal := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hpow : ∀ ν : Measure E, AEStronglyMeasurable g ν →
      eLpNorm g p ν ^ p.toReal = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂ν := fun ν hν => by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hν, ← ENNReal.rpow_mul,
      one_div_mul_cancel hq.ne', ENNReal.rpow_one]
  simp_rw [hpow _ hg.restrict, hpow μ hg]
  exact lintegral_setLIntegral_ball (hg.eNorm.pow_const _) r

/-- **Global estimates from local ones on balls of one radius.** If `0 < r` and, for almost every
centre `y`, the `Lᵖ` seminorm of `g` on `B(y, r)` is at most that of `h` on `B(y, R)`, then

`‖g‖_{Lᵖ} ≤ (μ (B(0, R)) / μ (B(0, r))) ^ (1 / p) ‖h‖_{Lᵖ}`. -/
theorem eLpNorm_le_of_ae_eLpNorm_restrict_ball_le (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {G : Type*} [NormedAddCommGroup G] {g : E → F} {h : E → G} (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) {r R : ℝ} (hr : 0 < r)
    (hle : ∀ᵐ y ∂μ, eLpNorm g p (μ.restrict (ball y r)) ≤ eLpNorm h p (μ.restrict (ball y R))) :
    eLpNorm g p μ ≤ (μ (ball (0 : E) R) / μ (ball (0 : E) r)) ^ p.toReal⁻¹ * eLpNorm h p μ := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hr0 : μ (ball (0 : E) r) ≠ 0 := (measure_ball_pos μ 0 hr).ne'
  have hrtop : μ (ball (0 : E) r) ≠ ∞ := measure_ball_lt_top.ne
  -- Integrate the `p`-th power of the local estimate over all centres.
  have hint : μ (ball (0 : E) r) * eLpNorm g p μ ^ p.toReal ≤
      μ (ball (0 : E) R) * eLpNorm h p μ ^ p.toReal := by
    rw [← lintegral_eLpNorm_restrict_ball_rpow hp0 hp hg,
      ← lintegral_eLpNorm_restrict_ball_rpow hp0 hp hh]
    exact lintegral_mono_ae (hle.mono fun y hy => ENNReal.rpow_le_rpow hy hq.le)
  have hdiv : eLpNorm g p μ ^ p.toReal ≤
      μ (ball (0 : E) R) / μ (ball (0 : E) r) * eLpNorm h p μ ^ p.toReal := by
    calc eLpNorm g p μ ^ p.toReal
        = (μ (ball (0 : E) r))⁻¹ * (μ (ball (0 : E) r) * eLpNorm g p μ ^ p.toReal) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hr0 hrtop, one_mul]
      _ ≤ (μ (ball (0 : E) r))⁻¹ * (μ (ball (0 : E) R) * eLpNorm h p μ ^ p.toReal) := by
          gcongr
      _ = _ := by rw [ENNReal.div_eq_inv_mul, mul_assoc]
  calc eLpNorm g p μ = (eLpNorm g p μ ^ p.toReal) ^ p.toReal⁻¹ := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hq.ne', ENNReal.rpow_one]
    _ ≤ (μ (ball (0 : E) R) / μ (ball (0 : E) r) * eLpNorm h p μ ^ p.toReal) ^ p.toReal⁻¹ :=
        ENNReal.rpow_le_rpow hdiv (inv_nonneg.2 hq.le)
    _ = (μ (ball (0 : E) R) / μ (ball (0 : E) r)) ^ p.toReal⁻¹ * eLpNorm h p μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hq.le), ← ENNReal.rpow_mul,
          mul_inv_cancel₀ hq.ne', ENNReal.rpow_one]

/-- **Global estimates from local reverse Hölder inequalities on balls of one radius.** Let
`0 < t ≤ p` and `0 < r`, and let `g`, `k` be nonnegative functions such that at every centre `y`

`⨍_{B(y, r/2)} g^p ≤ C ((⨍_{B(y, r)} g^t)^(p/t) + ⨍_{B(y, r)} k^p)`.

Then `∫ g^p ≤ C (μ (B(0, r))^(1 - p/t) (∫ g^t)^(p/t) + ∫ k^p)`. This turns the local higher
integrability given by Gehring's lemma into a global estimate. -/
theorem lintegral_rpow_le_of_forall_setLAverage_rpow_le {g k : E → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hk : AEMeasurable k μ) {t p r : ℝ} (ht : 0 < t) (htp : t ≤ p) (hr : 0 < r) {C : ℝ≥0}
    (hloc : ∀ y, ⨍⁻ x in ball y (r / 2), g x ^ p ∂μ ≤
      C * ((⨍⁻ x in ball y r, g x ^ t ∂μ) ^ (p / t) + ⨍⁻ x in ball y r, k x ^ p ∂μ)) :
    ∫⁻ x, g x ^ p ∂μ ≤
      C * ((μ (ball (0 : E) r))⁻¹ ^ (p / t - 1) * (∫⁻ x, g x ^ t ∂μ) ^ (p / t) +
        ∫⁻ x, k x ^ p ∂μ) := by
  set m := μ (ball (0 : E) (r / 2))
  set M := μ (ball (0 : E) r)
  set G := ∫⁻ x, g x ^ t ∂μ
  set e := p / t - 1 with he_def
  have he : 0 ≤ e := by rw [he_def, sub_nonneg, le_div_iff₀ ht]; linarith
  have hpt : p / t = e + 1 := by rw [he_def]; ring
  have hmtop : m ≠ ∞ := measure_ball_lt_top.ne
  have hMM : M * M⁻¹ = 1 := ENNReal.mul_inv_cancel (measure_ball_pos μ 0 hr).ne'
    measure_ball_lt_top.ne
  -- On each ball, write the means as integrals and split `(⨍ g^t)^(p/t)` as
  -- `(⨍ g^t)^e · ⨍ g^t`, the first factor bounded through `G`. What remains is linear in `g^t`
  -- and in `k^p`, so it integrates over the centres.
  have hloc' : ∀ y, ∫⁻ x in ball y (r / 2), g x ^ p ∂μ ≤
      m * C * ∫⁻ x in ball y r, ((M⁻¹ * G) ^ e * M⁻¹ * g x ^ t + M⁻¹ * k x ^ p) ∂μ := fun y => by
    have hA : ∫⁻ x in ball y r, g x ^ t ∂μ ≤ G := setLIntegral_le_lintegral _ _
    have hmy : μ (ball y (r / 2)) = m := Measure.addHaar_ball_center _ _ _
    have hMy : μ (ball y r) = M := Measure.addHaar_ball_center _ _ _
    calc ∫⁻ x in ball y (r / 2), g x ^ p ∂μ = m * ⨍⁻ x in ball y (r / 2), g x ^ p ∂μ := by
          rw [← hmy, measure_mul_setLAverage _ measure_ball_lt_top.ne]
      _ ≤ m * (C * ((⨍⁻ x in ball y r, g x ^ t ∂μ) ^ (p / t) + ⨍⁻ x in ball y r, k x ^ p ∂μ)) :=
          mul_le_mul_of_nonneg_left (hloc y) zero_le
      _ = m * C * ((M⁻¹ * ∫⁻ x in ball y r, g x ^ t ∂μ) ^ e *
            (M⁻¹ * ∫⁻ x in ball y r, g x ^ t ∂μ) + M⁻¹ * ∫⁻ x in ball y r, k x ^ p ∂μ) := by
          rw [setLAverage_eq, setLAverage_eq, hMy, hpt,
            ENNReal.rpow_add_of_nonneg _ _ he zero_le_one, ENNReal.rpow_one,
            ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_assoc]
      _ ≤ m * C * ((M⁻¹ * G) ^ e * (M⁻¹ * ∫⁻ x in ball y r, g x ^ t ∂μ) +
            M⁻¹ * ∫⁻ x in ball y r, k x ^ p ∂μ) := by gcongr
      _ = m * C * ∫⁻ x in ball y r, ((M⁻¹ * G) ^ e * M⁻¹ * g x ^ t + M⁻¹ * k x ^ p) ∂μ := by
          rw [lintegral_add_left' (((hg.pow_const _).const_mul _).restrict),
            lintegral_const_mul'' _ (hg.pow_const _).restrict,
            lintegral_const_mul'' _ (hk.pow_const _).restrict, mul_assoc _ M⁻¹]
  -- Integrate over all centres `y` and cancel `m`.
  have hint : ∫⁻ x, ((M⁻¹ * G) ^ e * M⁻¹ * g x ^ t + M⁻¹ * k x ^ p) ∂μ =
      (M⁻¹ * G) ^ e * M⁻¹ * G + M⁻¹ * ∫⁻ x, k x ^ p ∂μ := by
    rw [lintegral_add_left' ((hg.pow_const _).const_mul _),
      lintegral_const_mul'' _ (hg.pow_const _), lintegral_const_mul'' _ (hk.pow_const _)]
  have key : m * ∫⁻ x, g x ^ p ∂μ ≤ m * (C * ((M⁻¹ * G) ^ e * G + ∫⁻ x, k x ^ p ∂μ)) :=
    calc m * ∫⁻ x, g x ^ p ∂μ = ∫⁻ y, ∫⁻ x in ball y (r / 2), g x ^ p ∂μ ∂μ :=
          (lintegral_setLIntegral_ball (hg.pow_const _) _).symm
      _ ≤ ∫⁻ y, m * C * ∫⁻ x in ball y r,
            ((M⁻¹ * G) ^ e * M⁻¹ * g x ^ t + M⁻¹ * k x ^ p) ∂μ ∂μ := lintegral_mono hloc'
      _ = m * C * ((M⁻¹ * G) ^ e * G * (M * M⁻¹) + (M * M⁻¹) * ∫⁻ x, k x ^ p ∂μ) := by
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hmtop ENNReal.coe_ne_top),
            lintegral_setLIntegral_ball (G := fun x =>
              (M⁻¹ * G) ^ e * M⁻¹ * g x ^ t + M⁻¹ * k x ^ p)
              (((hg.pow_const _).const_mul _).add ((hk.pow_const _).const_mul _)), hint]
          ring
      _ = m * (C * ((M⁻¹ * G) ^ e * G + ∫⁻ x, k x ^ p ∂μ)) := by rw [hMM]; ring
  calc ∫⁻ x, g x ^ p ∂μ ≤ C * ((M⁻¹ * G) ^ e * G + ∫⁻ x, k x ^ p ∂μ) :=
        (ENNReal.mul_le_mul_iff_right (measure_ball_pos μ 0 (by positivity)).ne' hmtop).1 key
    _ = C * (M⁻¹ ^ e * G ^ (p / t) + ∫⁻ x, k x ^ p ∂μ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ he, hpt, ENNReal.rpow_add_of_nonneg _ _ he zero_le_one,
          ENNReal.rpow_one, mul_assoc]

/-- **From balls around the origin to the whole space.** Let `μ` be an additive Haar measure on a
noncompact space, `e < 0`, and `B, C < ∞`. If for every `R > 0` the `Lᵖ` seminorm of `g` on
`B(0, R/2)` is at most `C (A + μ (B(0, R)) ^ e B)`, then `‖g‖_{Lᵖ} ≤ C A`: the factor
`μ (B(0, R)) ^ e` tends to zero as `R → ∞`, and Fatou's lemma along the balls `B(0, k + 1)` passes
the bound to the whole space. -/
theorem eLpNorm_le_of_forall_eLpNorm_restrict_ball_le [NoncompactSpace E] {g : E → F}
    (hg : AEStronglyMeasurable g μ) {e : ℝ} (he : e < 0) {A B C : ℝ≥0∞} (hB : B ≠ ∞)
    (hC : C ≠ ∞) (h : ∀ R : ℝ, 0 < R → eLpNorm g p (μ.restrict (ball 0 (R / 2))) ≤
      C * (A + μ (ball (0 : E) R) ^ e * B)) :
    eLpNorm g p μ ≤ C * A := by
  have hV : Tendsto (fun k : ℕ => μ (ball (0 : E) (2 * ((k : ℝ) + 1))) ^ e) atTop (𝓝 0) := by
    have hmono : Monotone fun k : ℕ => ball (0 : E) (2 * ((k : ℝ) + 1)) :=
      fun k l hkl => ball_subset_ball (by gcongr)
    have hunion : (⋃ k : ℕ, ball (0 : E) (2 * ((k : ℝ) + 1))) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
      obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
      exact ⟨k, mem_ball_zero_iff.2 (by linarith)⟩
    have hvol := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion, measure_univ_of_isAddLeftInvariant] at hvol
    have h := (ENNReal.continuous_rpow_const (y := e)).tendsto ∞ |>.comp hvol
    rwa [Function.comp_def, ENNReal.top_rpow_of_neg he] at h
  have hlim : Tendsto (fun k : ℕ => C * (A + μ (ball (0 : E) (2 * ((k : ℝ) + 1))) ^ e * B))
      atTop (𝓝 (C * A)) := by
    have h := ENNReal.Tendsto.const_mul (a := C) ((tendsto_const_nhds (x := A)).add
      (ENNReal.Tendsto.mul_const hV (Or.inr hB))) (Or.inr hC)
    simpa only [zero_mul, add_zero] using h
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
    (f := fun k : ℕ => (ball (0 : E) ((k : ℝ) + 1)).indicator g)
    (fun k => hg.indicator (measurableSet_ball (x := (0 : E)) (ε := (k : ℝ) + 1))) g hg
    (ae_of_all _ fun x => ?_)).trans ?_
  · obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun k hk => ?_)
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    exact (Set.indicator_of_mem (mem_ball_zero_iff.2 (by linarith)) g).symm
  · rw [← hlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet]
    have hk := h (2 * ((k : ℝ) + 1)) (by positivity)
    rwa [mul_div_cancel_left₀ _ two_ne_zero] at hk

section FiniteDimensional

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G₁ G₂ : Type*} [NormedAddCommGroup G₁]
  [NormedAddCommGroup G₂]

/-- **Hölder's inequality on a ball, scaled by the volume of a smaller ball.** Let `μ` be an
additive Haar measure on a finite-dimensional real normed space `E`. For `1 ≤ q ≤ p`, `1 ≤ c` and
`0 < r`,

`μ (B(x, r)) ^ (1 / p - 1 / q) ‖f‖_{L^q(B(x, c r))} ≤ c ^ dim E ‖f‖_{Lᵖ(B(x, c r))}`.

The factor `μ (B(x, r)) ^ (1 / p - 1 / q)` makes both sides scale in the same way under dilations,
so the constant does not depend on `r`. Unlike `MeasureTheory.Measure.eLpNorm_ball_le_mul_rpow`,
which has real exponents and the real volume factor of a single ball, the exponents here are
extended, `p = ∞` included, and the constant is the dilation factor `c ^ dim E`. -/
theorem measure_ball_rpow_mul_eLpNorm_restrict_ball_le {q : ℝ≥0∞} (hq : 1 ≤ q) (hqp : q ≤ p)
    {x : E} {c r : ℝ} (hc : 1 ≤ c) (hr : 0 < r) {f : E → F}
    (hf : AEStronglyMeasurable f (μ.restrict (ball x (c * r)))) :
    μ (ball x r) ^ (p.toReal⁻¹ - q.toReal⁻¹) * eLpNorm f q (μ.restrict (ball x (c * r))) ≤
      ENNReal.ofReal c ^ finrank ℝ E * eLpNorm f p (μ.restrict (ball x (c * r))) := by
  set e : ℝ := q.toReal⁻¹ - p.toReal⁻¹ with he_def
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have he0 : 0 ≤ e := by
    rw [he_def, ← ENNReal.toReal_inv, ← ENNReal.toReal_inv]
    exact sub_nonneg.2 (ENNReal.toReal_mono (ENNReal.inv_ne_top.2 hq0) (ENNReal.inv_le_inv.2 hqp))
  have he1 : e ≤ 1 := by
    have hq1 : q.toReal⁻¹ ≤ 1 := by
      rw [← ENNReal.toReal_inv]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using ENNReal.inv_le_one.2 hq)
    have : 0 ≤ p.toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
    rw [he_def]
    linarith
  set V := μ (ball (0 : E) r)
  have hHolder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp hf
  rw [Measure.restrict_apply_univ, Measure.addHaar_ball_mul_of_pos μ x (zero_lt_one.trans_le hc),
    one_div, one_div, ENNReal.ofReal_pow (zero_le_one.trans hc),
    ENNReal.mul_rpow_of_nonneg _ _ he0] at hHolder
  rw [Measure.addHaar_ball_center, show p.toReal⁻¹ - q.toReal⁻¹ = -e by ring]
  calc V ^ (-e) * eLpNorm f q (μ.restrict (ball x (c * r)))
      ≤ V ^ (-e) * (eLpNorm f p (μ.restrict (ball x (c * r))) *
          ((ENNReal.ofReal c ^ finrank ℝ E) ^ e * V ^ e)) := by gcongr
    _ = (ENNReal.ofReal c ^ finrank ℝ E) ^ e * V ^ (-e + e) *
          eLpNorm f p (μ.restrict (ball x (c * r))) := by
        rw [ENNReal.rpow_add _ _ (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne]
        ring
    _ ≤ ENNReal.ofReal c ^ finrank ℝ E * eLpNorm f p (μ.restrict (ball x (c * r))) := by
        rw [neg_add_cancel, ENNReal.rpow_zero, mul_one]
        gcongr
        exact ENNReal.rpow_le_self_of_one_le (one_le_pow₀ (ENNReal.one_le_ofReal.2 hc)) he1

/-- **Global estimates from local ones by two functions on concentric balls.** Let `μ` be an
additive Haar measure on a finite-dimensional real normed space `E`, let `1 ≤ p < ∞`, `1 ≤ κ`
and `0 < r`. If, at almost every centre `y`,

`‖g‖_{Lᵖ(B(y, r))} ≤ c₁ ‖f₁‖_{Lᵖ(B(y, κ r))} + c₂ ‖f₂‖_{Lᵖ(B(y, κ r))}`,

then `‖g‖_{Lᵖ} ≤ 2 κ ^ dim E (c₁ ‖f₁‖_{Lᵖ} + c₂ ‖f₂‖_{Lᵖ})`. The constant does not depend on `r`,
and no integrability is assumed: the seminorms may be infinite. The constants enter only through
`ENNReal.ofReal`, so a negative constant acts as `0`. -/
theorem eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add (hp1 : 1 ≤ p) (hp : p ≠ ∞) {g : E → F}
    {f₁ : E → G₁} {f₂ : E → G₂} (hg : AEStronglyMeasurable g μ)
    (hf₁ : AEStronglyMeasurable f₁ μ) (hf₂ : AEStronglyMeasurable f₂ μ) {c₁ c₂ κ r : ℝ}
    (hκ : 1 ≤ κ) (hr : 0 < r)
    (hle : ∀ᵐ y ∂μ, eLpNorm g p (μ.restrict (ball y r)) ≤
      ENNReal.ofReal c₁ * eLpNorm f₁ p (μ.restrict (ball y (κ * r))) +
        ENNReal.ofReal c₂ * eLpNorm f₂ p (μ.restrict (ball y (κ * r)))) :
    eLpNorm g p μ ≤ 2 * ENNReal.ofReal κ ^ finrank ℝ E *
      (ENNReal.ofReal c₁ * eLpNorm f₁ p μ + ENNReal.ofReal c₂ * eLpNorm f₂ p μ) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  -- Both terms of each local bound are dominated by the local seminorm of one function `h`.
  -- Since `ENNReal.ofReal c = ENNReal.ofReal (max c 0)`, the constants may be taken nonnegative.
  set h₁ : E → ℝ := max c₁ 0 • fun x => ‖f₁ x‖
  set h₂ : E → ℝ := max c₂ 0 • fun x => ‖f₂ x‖
  have hh₁ : AEStronglyMeasurable h₁ μ := hf₁.norm.const_smul _
  have hh₂ : AEStronglyMeasurable h₂ μ := hf₂.norm.const_smul _
  have hsmul : ∀ (ν : Measure E), AEStronglyMeasurable f₁ ν → AEStronglyMeasurable f₂ ν →
      eLpNorm h₁ p ν = ENNReal.ofReal c₁ * eLpNorm f₁ p ν ∧
        eLpNorm h₂ p ν = ENNReal.ofReal c₂ * eLpNorm f₂ p ν := fun ν h₁ν h₂ν => by
    simp only [h₁, h₂, eLpNorm_const_smul, eLpNorm_norm _ h₁ν, eLpNorm_norm _ h₂ν,
      Real.eNorm_eq_ofReal (le_max_right _ 0), ENNReal.ofReal_max, ENNReal.ofReal_zero,
      max_zero, and_self]
  have hdom : ∀ x, ‖h₁ x‖ ≤ (h₁ + h₂) x ∧ ‖h₂ x‖ ≤ (h₁ + h₂) x := fun x => by
    have h₁x : 0 ≤ h₁ x := by simp only [h₁, Pi.smul_apply, smul_eq_mul]; positivity
    have h₂x : 0 ≤ h₂ x := by simp only [h₂, Pi.smul_apply, smul_eq_mul]; positivity
    rw [Real.norm_of_nonneg h₁x, Real.norm_of_nonneg h₂x, Pi.add_apply]
    constructor <;> linarith
  have hlocal : ∀ᵐ y ∂μ, eLpNorm g p (μ.restrict (ball y r)) ≤
      eLpNorm ((2 : ℝ) • (h₁ + h₂)) p (μ.restrict (ball y (κ * r))) := hle.mono fun y hy => by
    obtain ⟨e₁, e₂⟩ := hsmul _ hf₁.restrict hf₂.restrict
    rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal zero_le_two, ENNReal.ofReal_ofNat, two_mul]
    rw [← e₁, ← e₂] at hy
    exact hy.trans (add_le_add (eLpNorm_mono_real hh₁.restrict fun x => (hdom x).1)
      (eLpNorm_mono_real hh₂.restrict fun x => (hdom x).2))
  -- Average the local estimates; the volume ratio of the two balls is `κ ^ dim E`.
  have hglobal := eLpNorm_le_of_ae_eLpNorm_restrict_ball_le hp0 hp hg
    ((hh₁.add hh₂).const_smul (2 : ℝ)) hr hlocal
  rw [Measure.addHaar_ball_mul_of_pos μ 0 (zero_lt_one.trans_le hκ),
    ENNReal.mul_div_cancel_right (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne,
    ENNReal.ofReal_pow (zero_le_one.trans hκ), eLpNorm_const_smul,
    Real.eNorm_eq_ofReal zero_le_two, ENNReal.ofReal_ofNat] at hglobal
  obtain ⟨e₁, e₂⟩ := hsmul μ hf₁ hf₂
  have hp1' : p.toReal⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp).2 hp1)
  refine hglobal.trans ?_
  rw [← e₁, ← e₂]
  calc (ENNReal.ofReal κ ^ finrank ℝ E) ^ p.toReal⁻¹ * (2 * eLpNorm (h₁ + h₂) p μ)
      ≤ ENNReal.ofReal κ ^ finrank ℝ E * (2 * (eLpNorm h₁ p μ + eLpNorm h₂ p μ)) := by
        gcongr
        · exact ENNReal.rpow_le_self_of_one_le (one_le_pow₀ (ENNReal.one_le_ofReal.2 hκ)) hp1'
        · exact eLpNorm_add_le hp1
    _ = _ := by ring

/-- **Estimates on a set from local ones on the balls meeting it.** Let `μ` be an additive Haar
measure on a finite-dimensional real normed space `E`, let `1 ≤ p < ∞`, `1 ≤ κ` and `0 < r`, and let
`V` and `T` be measurable. If every ball `B(y, r)` that meets `V` satisfies `B(y, κ r) ⊆ T` and

`‖g‖_{Lᵖ(B(y, r))} ≤ c₁ ‖f₁‖_{Lᵖ(B(y, κ r))} + c₂ ‖f₂‖_{Lᵖ(B(y, κ r))}`,

then `‖g‖_{Lᵖ(V)} ≤ 2 κ ^ dim E (c₁ ‖f₁‖_{Lᵖ(T)} + c₂ ‖f₂‖_{Lᵖ(T)})`. Nothing is assumed on the
balls that miss `V`, and the functions need only be measurable on `V` and on `T`. This is
`TauCeti.eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add` for the restriction of `g` to `V` and those
of `f₁`, `f₂` to `T`. -/
theorem eLpNorm_restrict_le_of_forall_ball_inter_nonempty (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {V T : Set E} (hV : MeasurableSet V) (hT : MeasurableSet T) {g : E → F} {f₁ : E → G₁}
    {f₂ : E → G₂} (hg : AEStronglyMeasurable g (μ.restrict V))
    (hf₁ : AEStronglyMeasurable f₁ (μ.restrict T)) (hf₂ : AEStronglyMeasurable f₂ (μ.restrict T))
    {c₁ c₂ κ r : ℝ} (hκ : 1 ≤ κ) (hr : 0 < r)
    (hle : ∀ y, (ball y r ∩ V).Nonempty → ball y (κ * r) ⊆ T ∧
      eLpNorm g p (μ.restrict (ball y r)) ≤
        ENNReal.ofReal c₁ * eLpNorm f₁ p (μ.restrict (ball y (κ * r))) +
          ENNReal.ofReal c₂ * eLpNorm f₂ p (μ.restrict (ball y (κ * r)))) :
    eLpNorm g p (μ.restrict V) ≤ 2 * ENNReal.ofReal κ ^ finrank ℝ E *
      (ENNReal.ofReal c₁ * eLpNorm f₁ p (μ.restrict T) +
        ENNReal.ofReal c₂ * eLpNorm f₂ p (μ.restrict T)) := by
  have hglobal := eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add (c₁ := c₁) (c₂ := c₂) hp1 hp
    ((aestronglyMeasurable_indicator_iff hV).2 hg) ((aestronglyMeasurable_indicator_iff hT).2 hf₁)
    ((aestronglyMeasurable_indicator_iff hT).2 hf₂) hκ hr (Filter.Eventually.of_forall fun y => ?_)
  · rwa [eLpNorm_indicator_eq_eLpNorm_restrict hV.nullMeasurableSet,
      eLpNorm_indicator_eq_eLpNorm_restrict hT.nullMeasurableSet,
      eLpNorm_indicator_eq_eLpNorm_restrict hT.nullMeasurableSet] at hglobal
  by_cases hy : (ball y r ∩ V).Nonempty
  · obtain ⟨hyT, hy⟩ := hle y hy
    -- On `B(y, κ r) ⊆ T` the functions agree with their restrictions to `T`.
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hT.nullMeasurableSet,
      eLpNorm_indicator_eq_eLpNorm_restrict hT.nullMeasurableSet, Measure.restrict_restrict hT,
      Set.inter_eq_right.2 hyT]
    exact (eLpNorm_indicator_le _ hV.nullMeasurableSet).trans hy
  · -- A ball missing `V` does not see the restriction of `g` to `V`.
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hV.nullMeasurableSet, Measure.restrict_restrict hV,
      Set.inter_comm, Set.not_nonempty_iff_eq_empty.1 hy, Measure.restrict_empty,
      eLpNorm_measure_zero]
    exact zero_le

/-- **Global estimates from local ones on concentric balls.** Let `μ` be an additive Haar measure
on a finite-dimensional real normed space `E`, let `1 ≤ p < ∞`, and let `g`, `f₁`, `f₂` be in
`Lᵖ(μ)`. If `0 < r`, `0 ≤ c₁`, `0 ≤ c₂` and, at almost every centre `y`,

`‖g‖_{Lᵖ(B(y, r))} ≤ c₁ ‖f₁‖_{Lᵖ(B(y, 2r))} + c₂ ‖f₂‖_{Lᵖ(B(y, 2r))}`,

then `‖g‖_{Lᵖ} ≤ 2 ^ (dim E + 1) (c₁ ‖f₁‖_{Lᵖ} + c₂ ‖f₂‖_{Lᵖ})`. The constant does not depend
on `r`. This is the case `κ = 2` of `eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add`. -/
theorem lpNorm_le_of_ae_lpNorm_restrict_ball_le_add (hp1 : 1 ≤ p) (hp : p ≠ ∞) {g : E → F}
    {f₁ : E → G₁} {f₂ : E → G₂} (hg : MemLp g p μ) (hf₁ : MemLp f₁ p μ) (hf₂ : MemLp f₂ p μ)
    {c₁ c₂ r : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hr : 0 < r)
    (hle : ∀ᵐ y ∂μ, lpNorm g p (μ.restrict (ball y r)) ≤
      c₁ * lpNorm f₁ p (μ.restrict (ball y (2 * r))) +
        c₂ * lpNorm f₂ p (μ.restrict (ball y (2 * r)))) :
    lpNorm g p μ ≤ 2 ^ (finrank ℝ E + 1) * (c₁ * lpNorm f₁ p μ + c₂ * lpNorm f₂ p μ) := by
  -- In terms of `eLpNorm`, both sides are `ENNReal.ofReal` of the real bounds.
  have hofReal : ∀ ν : Measure E, MemLp f₁ p ν → MemLp f₂ p ν →
      ENNReal.ofReal c₁ * eLpNorm f₁ p ν + ENNReal.ofReal c₂ * eLpNorm f₂ p ν =
        ENNReal.ofReal (c₁ * lpNorm f₁ p ν + c₂ * lpNorm f₂ p ν) := fun ν h₁ν h₂ν => by
    rw [ENNReal.ofReal_add (mul_nonneg hc₁ lpNorm_nonneg) (mul_nonneg hc₂ lpNorm_nonneg),
      ENNReal.ofReal_mul hc₁, ENNReal.ofReal_mul hc₂, ofReal_lpNorm h₁ν, ofReal_lpNorm h₂ν]
  have hglobal := eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add hp1 hp hg.aestronglyMeasurable
    hf₁.aestronglyMeasurable hf₂.aestronglyMeasurable one_le_two hr
    (hle.mono fun y hy => by
      rw [← ofReal_lpNorm (hg.restrict _), hofReal _ (hf₁.restrict _) (hf₂.restrict _)]
      exact ENNReal.ofReal_le_ofReal hy)
  rw [← ofReal_lpNorm hg, hofReal μ hf₁ hf₂, ENNReal.ofReal_ofNat] at hglobal
  have hreal := ENNReal.toReal_mono (by finiteness) hglobal
  simpa [ENNReal.toReal_ofReal lpNorm_nonneg, pow_succ', ENNReal.toReal_ofReal
    (add_nonneg (mul_nonneg hc₁ lpNorm_nonneg) (mul_nonneg hc₂ lpNorm_nonneg))] using hreal

end FiniteDimensional

/-- **Chebyshev point selection on a ball.** For `p > 0`, `r > 0`, and `f ∈ L^p(B(x₀, r))` in
dimension `n`, there is a point `w ∈ B(x₀, r)` at which
`‖f w‖ ≤ |B(0, 1)|^(-1/p) r^(-n/p) ‖f‖_{L^p(B(x₀, r))}`. -/
theorem _root_.MeasureTheory.Measure.exists_mem_ball_norm_le_rpow_neg_mul_toReal_eLpNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] {f : E → F} {p r : ℝ} {x₀ : E}
    (hp : 0 < p) (hr : 0 < r)
    (hf : MemLp f (ENNReal.ofReal p) (mu.restrict (ball x₀ r))) :
    ∃ w ∈ ball x₀ r,
      ‖f w‖ ≤ mu.real (ball (0 : E) 1) ^ (-p⁻¹) *
        (r ^ (-((finrank ℝ E : ℝ) / p)) *
          (eLpNorm f (ENNReal.ofReal p) (mu.restrict (ball x₀ r))).toReal) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  have hpos : 0 < mu (ball x₀ r) := isOpen_ball.measure_pos mu (nonempty_ball.2 hr)
  obtain ⟨w, hw, hle⟩ := exists_mem_measure_rpow_mul_enorm_le_eLpNorm f hp0 ENNReal.ofReal_ne_top
    hpos.ne' measure_ball_lt_top.ne
  have hreal := ENNReal.toReal_mono hf.eLpNorm_ne_top hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hp.le, toReal_eNorm,
    ← measureReal_def] at hreal
  have hmr : 0 < mu.real (ball x₀ r) := Metric.measureReal_ball_pos mu x₀ hr
  have hinv : ‖f w‖ ≤ mu.real (ball x₀ r) ^ (-p⁻¹) *
      (eLpNorm f (ENNReal.ofReal p) (mu.restrict (ball x₀ r))).toReal := by
    rw [Real.rpow_neg hmr.le, inv_mul_eq_div, le_div_iff₀' (Real.rpow_pos_of_pos hmr _)]
    exact hreal
  have hvol : mu.real (ball x₀ r) = r ^ finrank ℝ E * mu.real (ball 0 1) := by
    rw [measureReal_def, mu.addHaar_ball_of_pos x₀ hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ← measureReal_def]
  have hexp : (finrank ℝ E : ℝ) * -p⁻¹ = -((finrank ℝ E : ℝ) / p) := by ring
  have hpow : mu.real (ball x₀ r) ^ (-p⁻¹) =
      mu.real (ball (0 : E) 1) ^ (-p⁻¹) * r ^ (-((finrank ℝ E : ℝ) / p)) :=
    calc mu.real (ball x₀ r) ^ (-p⁻¹)
        = (r ^ finrank ℝ E * mu.real (ball (0 : E) 1)) ^ (-p⁻¹) := by rw [hvol]
      _ = (r ^ (finrank ℝ E : ℝ)) ^ (-p⁻¹) * mu.real (ball (0 : E) 1) ^ (-p⁻¹) := by
          rw [Real.mul_rpow (by positivity) measureReal_nonneg, Real.rpow_natCast]
      _ = mu.real (ball (0 : E) 1) ^ (-p⁻¹) * r ^ (-((finrank ℝ E : ℝ) / p)) := by
          rw [← Real.rpow_mul hr.le, hexp, mul_comm]
  refine ⟨w, hw, hinv.trans_eq ?_⟩
  rw [hpow, mul_assoc]

/-- **Off-centre Chebyshev point selection on a ball.** For `p > 0`, `r > 0`, `dist q' q ≤ r / 2`,
and `f ∈ L^p(B(q, r))` in dimension `n`, there is a point `w ∈ B(q', r) ∩ B(q, r)` at which
`‖f w‖ ≤ 2^(n/p) |B(0, 1)|^(-1/p) r^(-n/p) ‖f‖_{L^p(B(q, r))}`. -/
theorem _root_.MeasureTheory.Measure.exists_mem_ball_norm_le_rpow_neg_mul_toReal_eLpNorm_of_dist_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] {f : E → F} {p r : ℝ} {q' q : E}
    (hp : 0 < p) (hr : 0 < r) (hdist : dist q' q ≤ r / 2)
    (hf : MemLp f (ENNReal.ofReal p) (mu.restrict (ball q r))) :
    ∃ w ∈ ball q' r ∩ ball q r,
      ‖f w‖ ≤ 2 ^ ((finrank ℝ E : ℝ) / p) * mu.real (ball (0 : E) 1) ^ (-p⁻¹) *
        (r ^ (-((finrank ℝ E : ℝ) / p)) *
          (eLpNorm f (ENNReal.ofReal p) (mu.restrict (ball q r))).toReal) := by
  have hsub : ball q' (r / 2) ⊆ ball q r := ball_subset_ball' (by linarith)
  obtain ⟨w, hw, hfw⟩ := mu.exists_mem_ball_norm_le_rpow_neg_mul_toReal_eLpNorm hp (half_pos hr)
    (hf.mono_measure (Measure.restrict_mono hsub le_rfl))
  refine ⟨w, ⟨ball_subset_ball (half_lt_self hr).le hw, hsub hw⟩, ?_⟩
  have hmono : (eLpNorm f (ENNReal.ofReal p) (mu.restrict (ball q' (r / 2)))).toReal ≤
      (eLpNorm f (ENNReal.ofReal p) (mu.restrict (ball q r))).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
  have hrpow : (r / 2) ^ (-((finrank ℝ E : ℝ) / p)) =
      2 ^ ((finrank ℝ E : ℝ) / p) * r ^ (-((finrank ℝ E : ℝ) / p)) := by
    rw [Real.div_rpow_eq_rpow_neg_mul_rpow hr.le two_pos, neg_neg]
  set G : ℝ := r ^ (-((finrank ℝ E : ℝ) / p)) *
    (eLpNorm f (ENNReal.ofReal p) (mu.restrict (ball q r))).toReal
  calc ‖f w‖ ≤ mu.real (ball (0 : E) 1) ^ (-p⁻¹) *
          ((r / 2) ^ (-((finrank ℝ E : ℝ) / p)) *
            (eLpNorm f (ENNReal.ofReal p) (mu.restrict (ball q' (r / 2)))).toReal) := hfw
    _ ≤ mu.real (ball (0 : E) 1) ^ (-p⁻¹) * (2 ^ ((finrank ℝ E : ℝ) / p) * G) := by
        rw [hrpow, mul_assoc (2 ^ ((finrank ℝ E : ℝ) / p))]
        dsimp only [G]
        gcongr
    _ = 2 ^ ((finrank ℝ E : ℝ) / p) * mu.real (ball (0 : E) 1) ^ (-p⁻¹) * G := by ring

section Covering

variable {E ε : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [TopologicalSpace ε] [ENorm ε]
  [TopologicalSpace.PseudoMetrizableSpace ε]

/-- **Covering bound for `eLpNorm` on a ball.** Let `E` be a finite-dimensional real normed space
and `0 < p < ∞`. If `r ≥ 0`, `s > 0`, and on every ball `B(c, s)` with `c ∈ closedBall x₀ r` the
function `f` has `Lᵖ` seminorm at most `B : ℝ≥0∞`, then covering `closedBall x₀ r` by at most
`(1 + 4 r / s) ^ dim E` balls `B(c, s)` gives

`eLpNorm f p (μ.restrict (ball x₀ r)) ≤`
`  ENNReal.ofReal ((1 + 4 * r / s) ^ dim E) ^ p.toReal⁻¹ * B`. -/
theorem eLpNorm_restrict_ball_le_of_forall_mem_closedBall {μ : Measure E} (f : E → ε)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {x₀ : E} {r s : ℝ} {B : ℝ≥0∞} (hr : 0 ≤ r)
    (hs : 0 < s) (hle : ∀ c ∈ closedBall x₀ r, eLpNorm f p (μ.restrict (ball c s)) ≤ B) :
    eLpNorm f p (μ.restrict (ball x₀ r)) ≤
      ENNReal.ofReal ((1 + 4 * r / s) ^ finrank ℝ E) ^ p.toReal⁻¹ * B := by
  set ε₀ : ℝ≥0 := NNReal.mk (s / 2) (half_pos hs).le
  have hε₀ : ε₀ ≠ 0 := mt (congrArg NNReal.toReal) (half_pos hs).ne'
  obtain ⟨S, hSsub, hScov, hScard⟩ := exists_finset_isCover_of_subset_closedBall
    (r := NNReal.mk r hr) hε₀ (Set.Subset.rfl : closedBall x₀ r ⊆ _)
  have hS_le : (S.card : ℝ) ≤ (1 + 4 * r / s) ^ finrank ℝ E := by
    refine hScard.trans_eq ?_
    simp only [ε₀, NNReal.coe_mk]
    congr 1
    field_simp
    ring
  have hcover : ball x₀ r ⊆ ⋃ c ∈ S, ball c s :=
    ball_subset_closedBall.trans <| hScov.subset_iUnion_closedBall.trans <|
      Set.iUnion₂_mono fun _ _ => closedBall_subset_ball (half_lt_self hs)
  have hcov_le := eLpNorm_restrict_le_card_rpow_mul_of_subset_biUnion f hp0 hp hcover
    fun c hc => hle c (hSsub hc)
  refine hcov_le.trans (mul_le_mul' (ENNReal.rpow_le_rpow ?_ (by positivity)) le_rfl)
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hS_le

/-- **Real-valued covering bound for `eLpNorm` on a ball.** Let `E` be a finite-dimensional real
normed space and `0 < p < ∞`. If `r ≥ 0`, `s > 0`, and on every ball `B(c, s)` with
`c ∈ closedBall x₀ r` the function `f` has finite `Lᵖ` seminorm at most `B ≥ 0`, then covering
`closedBall x₀ r` by at most `(1 + 4 r / s) ^ dim E` balls `B(c, s)` gives

`(eLpNorm f p (μ.restrict (ball x₀ r))).toReal ≤ ((1 + 4 * r / s) ^ dim E) ^ p.toReal⁻¹ * B`. -/
theorem toReal_eLpNorm_restrict_ball_le_of_forall_mem_closedBall {μ : Measure E} (f : E → ε)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {x₀ : E} {r s B : ℝ} (hr : 0 ≤ r) (hs : 0 < s)
    (hB : 0 ≤ B)
    (hfin : ∀ c ∈ closedBall x₀ r, eLpNorm f p (μ.restrict (ball c s)) ≠ ∞)
    (hle : ∀ c ∈ closedBall x₀ r, (eLpNorm f p (μ.restrict (ball c s))).toReal ≤ B) :
    (eLpNorm f p (μ.restrict (ball x₀ r))).toReal ≤
      ((1 + 4 * r / s) ^ finrank ℝ E) ^ p.toReal⁻¹ * B := by
  have hcov : eLpNorm f p (μ.restrict (ball x₀ r)) ≤
      ENNReal.ofReal ((1 + 4 * r / s) ^ finrank ℝ E) ^ p.toReal⁻¹ * ENNReal.ofReal B :=
    eLpNorm_restrict_ball_le_of_forall_mem_closedBall f hp0 hp hr hs fun c hc =>
      (ENNReal.le_ofReal_iff_toReal_le (hfin c hc) hB).2 (hle c hc)
  calc (eLpNorm f p (μ.restrict (ball x₀ r))).toReal
      ≤ (ENNReal.ofReal ((1 + 4 * r / s) ^ finrank ℝ E) ^ p.toReal⁻¹ * ENNReal.ofReal B).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg
          (by positivity) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) hcov
    _ = ((1 + 4 * r / s) ^ finrank ℝ E) ^ p.toReal⁻¹ * B := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
          ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hB]

end Covering

end TauCeti
