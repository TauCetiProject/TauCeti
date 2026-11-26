/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.BrownianMotion.Basic
public import TauCeti.Probability.DysonBrownianMotion.Drift
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Algebra.Order.BigOperators.Ring.Finset
import TauCeti.Analysis.Calculus.Deriv.PositivePart
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Pathwise solutions and uniqueness of Dyson Brownian motion

Because the noise in Dyson Brownian motion is additive, the interacting `n`-particle system
`dX_t(i) = √(2 / (β n)) dB_t(i) + n⁻¹ ∑_{j ≠ i} (X_t(i) - X_t(j))⁻¹ dt` can be formulated pathwise
as the integral identity
`X t i = x i + w t i + ∫ s in (0 : ℝ)..t, dysonDrift n (X s.toNNReal) i`,
together with continuity of `X`, strict decreasing order `StrictAnti (X t)` at strictly positive
times `t > 0`, and local integrability of the repulsion sum on `[0, t]`. An ordered boundary start
`Antitone x` with coincident coordinates is allowed because the singular drift need only be
integrable down to `0` while `StrictAnti (X t)` holds for `t > 0`.

This file introduces both the deterministic path predicate `IsDysonPath` and the almost-sure
measure-level predicate `IsDysonSolution`, proves pairwise inverse-gap integrability, the
Rogers–Shi entrance bound, and time-shift restart invariance, establishes the pathwise `ℓ²` energy
identity, contraction, and uniqueness, and constructs concrete witnesses for `n ≤ 1` and for
zero-noise `n = 2` (including coincident initial states).
Globally Lipschitz chamber truncations and localization live in
`TauCeti.Probability.DysonBrownianMotion.Truncation`.

## Main declarations

* `TauCeti.Probability.IsDysonPath`: deterministic pathwise solution predicate for a driving path,
  with time-shift restart `TauCeti.Probability.IsDysonPath.shift`.
* `TauCeti.Probability.IsDysonSolution`: almost-sure solution predicate driven by `B` at parameter
  `β`.
* `TauCeti.Probability.IsDysonPath.intervalIntegrable_sub_inv` and
  `TauCeti.Probability.IsDysonPath.integral_sum_Ioi_sub_inv_le`: individual inverse-gap
  integrability and Rogers–Shi entrance bound.
* `TauCeti.Probability.IsDysonPath.le_of_le` and `TauCeti.Probability.IsDysonSolution.ae_le_of_le`:
  coordinatewise comparison principle (AGZ Lemma 4.3.6).
* `TauCeti.Probability.IsDysonPath.sum_sub_sq_eq`,
  `TauCeti.Probability.IsDysonPath.sum_sub_sq_le_of_le`, `TauCeti.Probability.IsDysonPath.eq`, and
  `TauCeti.Probability.IsDysonSolution.ae_eq`: `ℓ²` energy identity, contraction, and pathwise /
  almost-sure uniqueness.
* `TauCeti.Probability.dysonSystem_exists_unique_of_le_one`,
  `TauCeti.Probability.twoParticleDysonPath`, and
  `TauCeti.Probability.isDysonPath_twoParticleDysonPath`: non-vacuous witnesses.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, Lemma 4.3.3, Proposition 4.3.5 and Lemma 4.3.6.
* L. C. G. Rogers, Z. Shi, *Interacting Brownian particles and the Wigner law*, Probab. Theory
  Related Fields 95 (1993), 555–570.
* E. Cépa, D. Lépingle, *Diffusing particles with electrostatic repulsion*, Probab. Theory Related
  Fields 107 (1997), 429–449.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-! ### Deterministic Dyson trajectories -/

/-- **A deterministic Dyson trajectory** of `n` particles started at `x` and driven by an additive
forcing path `w : ℝ≥0 → Fin n → ℝ`: `X` is continuous on `[0, ∞)`, lies in the open decreasing Weyl
chamber `{z | StrictAnti z}` at every strictly positive time `t > 0`, has locally integrable
repulsion sums on `[0, t]`, and satisfies the Dyson integral equation coordinatewise. -/
structure IsDysonPath (n : ℕ) (x : Fin n → ℝ) (w : ℝ≥0 → Fin n → ℝ)
    (X : ℝ≥0 → Fin n → ℝ) : Prop where
  /-- The trajectory `X` is continuous on `[0, ∞)`. -/
  continuous : Continuous X
  /-- At every strictly positive time, the coordinates are strictly decreasing. -/
  strictAnti : ∀ t : ℝ≥0, 0 < t → StrictAnti (X t)
  /-- Each coordinate's singular repulsion sum is interval-integrable on `[0, t]`. -/
  intervalIntegrable : ∀ (t : ℝ≥0) (i : Fin n),
    IntervalIntegrable
      (fun s : ℝ ↦ ∑ j ∈ Finset.univ.erase i, (X s.toNNReal i - X s.toNNReal j)⁻¹) volume 0 t
  /-- Each coordinate satisfies the Dyson integral equation driven by `w`. -/
  eq_integral : ∀ (t : ℝ≥0) (i : Fin n),
    X t i = x i + w t i + ∫ s in (0 : ℝ)..t, dysonDrift n (X s.toNNReal) i

namespace IsDysonPath

variable {n : ℕ} {x y : Fin n → ℝ} {w : ℝ≥0 → Fin n → ℝ} {X Y : ℝ≥0 → Fin n → ℝ}

/-- Coordinatewise interval integrability of `dysonDrift` along a Dyson trajectory. -/
theorem intervalIntegrable_dysonDrift (hX : IsDysonPath n x w X) (t : ℝ≥0) (i : Fin n) :
    IntervalIntegrable (fun s : ℝ ↦ dysonDrift n (X s.toNNReal) i) volume 0 t := by
  simp_rw [dysonDrift_apply]
  exact (hX.intervalIntegrable t i).const_mul (n : ℝ)⁻¹

/-- Value of a Dyson trajectory at time `0`. -/
theorem eval_zero_apply (hX : IsDysonPath n x w X) (i : Fin n) : X 0 i = x i + w 0 i := by
  simpa using hX.eq_integral 0 i

/-- Vector form of the initial condition `X 0 = x + w 0`. -/
theorem eval_zero (hX : IsDysonPath n x w X) : X 0 = x + w 0 :=
  funext hX.eval_zero_apply

/-- When the driving path starts at `0`, `X 0 = x`. -/
theorem eval_zero_of_eq_zero (hX : IsDysonPath n x w X) (hw : w 0 = 0) : X 0 = x := by
  simp [hX.eval_zero, hw]

/-- The initial configuration `X 0` of a Dyson trajectory is antitone. -/
theorem antitone_zero (hX : IsDysonPath n x w X) : Antitone (X 0) :=
  isClosed_antitone.mem_of_tendsto
    (hX.continuous.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    (eventually_nhdsWithin_of_forall fun t ht ↦ (hX.strictAnti t (mem_Ioi.1 ht)).antitone)

/-- Every Dyson trajectory forces its driving path `w` to be continuous. -/
theorem continuous_driving (hX : IsDysonPath n x w X) : Continuous w := by
  refine continuous_pi fun i ↦ continuous_iff_continuousAt.2 fun t ↦ ?_
  set T : ℝ≥0 := t + 1
  have hprim_contOn : ContinuousOn
      (fun u : ℝ≥0 ↦ ∫ s in (0 : ℝ)..u, dysonDrift n (X s.toNNReal) i) (Iic T) :=
    (intervalIntegral.continuousOn_primitive_interval'
      (hX.intervalIntegrable_dysonDrift T i) left_mem_uIcc).comp NNReal.continuous_coe.continuousOn
      fun u hu ↦ by rw [uIcc_of_le T.coe_nonneg]; exact ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hu⟩
  have hprim_at : ContinuousAt
      (fun u : ℝ≥0 ↦ ∫ s in (0 : ℝ)..u, dysonDrift n (X s.toNNReal) i) t :=
    hprim_contOn.continuousAt
      (mem_of_superset (Iio_mem_nhds (lt_add_one t)) Iio_subset_Iic_self)
  have hw_eq : (fun u : ℝ≥0 ↦ w u i) = fun u : ℝ≥0 ↦
      X u i - x i - ∫ s in (0 : ℝ)..u, dysonDrift n (X s.toNNReal) i :=
    funext fun u ↦ by linarith [hX.eq_integral u i]
  rw [hw_eq]
  exact ((((continuous_apply i).comp hX.continuous).continuousAt).sub continuousAt_const).sub
    hprim_at

/-- **Center-of-mass conservation.** Summing the coordinates of a Dyson trajectory cancels the
repulsive drift at every time `t`. -/
theorem sum_eq (hX : IsDysonPath n x w X) (t : ℝ≥0) :
    ∑ i : Fin n, X t i = (∑ i : Fin n, x i) + ∑ i : Fin n, w t i := by
  simp_rw [hX.eq_integral t, Finset.sum_add_distrib]
  rw [← intervalIntegral.integral_finsetSum fun i _ ↦ hX.intervalIntegrable_dysonDrift t i]
  simp [sum_dysonDrift_eq_zero]

/-- **Pairwise integrability of inverse gaps.** Even though `IsDysonPath` assumes integrability only
for the signed sum `∑ j ∈ Finset.univ.erase i, (X s i - X s j)⁻¹`, every individual inverse gap
`(X s.toNNReal i - X s.toNNReal j)⁻¹` is interval-integrable on `[0, t]` (for `i = j` the integrand
vanishes since `(0 : ℝ)⁻¹ = 0`). -/
theorem intervalIntegrable_sub_inv (hX : IsDysonPath n x w X) (t : ℝ≥0) (i j : Fin n) :
    IntervalIntegrable (fun s : ℝ ↦ (X s.toNNReal i - X s.toNNReal j)⁻¹) volume 0 t := by
  have hmeas (u v : Fin n) : Measurable fun s : ℝ ↦ (X s.toNNReal u - X s.toNNReal v)⁻¹ :=
    ((((continuous_apply u).comp hX.continuous).comp continuous_real_toNNReal).sub
      (((continuous_apply v).comp hX.continuous).comp continuous_real_toNNReal)).measurable.inv
  have hswap (u v : Fin n) : (fun s : ℝ ↦ (X s.toNNReal u - X s.toNNReal v)⁻¹) =
      fun s : ℝ ↦ -(X s.toNNReal v - X s.toNNReal u)⁻¹ :=
    funext fun s ↦ by rw [← neg_sub (X s.toNNReal v) (X s.toNNReal u), inv_neg]
  have hordered : ∀ u v : Fin n, u < v →
      IntegrableOn (fun s : ℝ ↦ (X s.toNNReal u - X s.toNNReal v)⁻¹) (Ioc 0 t) volume := by
    intro u
    induction u using WellFoundedLT.induction with
    | ind u ih =>
      intro v huv
      have hlt_sum : IntegrableOn
          (fun s : ℝ ↦ ∑ r ∈ Finset.Iio u, (X s.toNNReal u - X s.toNNReal r)⁻¹)
          (Ioc 0 t) volume :=
        integrable_finsetSum _ fun r hr ↦ by
          rw [hswap u r]; exact (ih r (Finset.mem_Iio.1 hr) u (Finset.mem_Iio.1 hr)).neg
      have hall_sum :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).1 (hX.intervalIntegrable t u)
      have hgt_sum : IntegrableOn
          (fun s : ℝ ↦ ∑ r ∈ Finset.Ioi u, (X s.toNNReal u - X s.toNNReal r)⁻¹)
          (Ioc 0 t) volume :=
        (hall_sum.sub hlt_sum).congr_fun (fun s _ ↦ by
          simp only [Pi.sub_apply]
          rw [Finset.sum_erase_univ_eq_sum_Ioi_add_sum_Iio, add_sub_cancel_right]) measurableSet_Ioc
      refine hgt_sum.mono' (hmeas u v).aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs ↦ ?_)
      have hnonneg : ∀ r ∈ Finset.Ioi u, 0 ≤ (X s.toNNReal u - X s.toNNReal r)⁻¹ := fun r hr ↦
        inv_nonneg.2 (sub_pos.2 (hX.strictAnti s.toNNReal (Real.toNNReal_pos.2 hs.1)
          (Finset.mem_Ioi.1 hr))).le
      rw [Real.norm_of_nonneg (hnonneg v (Finset.mem_Ioi.2 huv))]
      exact Finset.single_le_sum hnonneg (Finset.mem_Ioi.2 huv)
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).2 (hordered i j hlt)
  · simp
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg, hswap i j]
    exact (hordered j i hgt).neg

/-- **Quantitative Rogers–Shi entrance-law bound.** Along any Dyson trajectory `X`, the `L¹` norm of
all ordered inverse gaps on `[0, t]` is bounded solely by `X t`, `x`, and `w t`, uniformly even
when coordinates of `x` coincide at time `0`. -/
theorem integral_sum_Ioi_sub_inv_le (hX : IsDysonPath n x w X) (t : ℝ≥0) :
    ∫ s in (0 : ℝ)..t, ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        (X s.toNNReal i - X s.toNNReal j)⁻¹ ≤
      ((n : ℝ) / 2) * ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℝ)) * (X t i - x i - w t i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hint_lhs : IntervalIntegrable
      (fun s : ℝ ↦ ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (X s.toNNReal i - X s.toNNReal j)⁻¹)
      volume 0 t :=
    (IntervalIntegrable.sum Finset.univ fun i _ ↦
      IntervalIntegrable.sum (Finset.Ioi i) fun j _ ↦
        hX.intervalIntegrable_sub_inv t i j).congr fun _ _ ↦ by simp
  have hint_rhs : IntervalIntegrable
      (fun s : ℝ ↦ ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℝ)) * dysonDrift n (X s.toNNReal) i)
      volume 0 t :=
    (IntervalIntegrable.sum Finset.univ fun i _ ↦
      (hX.intervalIntegrable_dysonDrift t i).const_mul ((n : ℝ) - 1 - 2 * (i : ℝ))).congr
      fun _ _ ↦ by simp
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo t.coe_nonneg (hint_lhs.const_mul _)
    hint_rhs fun s hs ↦ mul_sum_Ioi_sub_inv_le_sum_sub_two_mul_mul_dysonDrift
      (hX.strictAnti s.toNNReal (Real.toNNReal_pos.2 hs.1)).antitone
  have hrhs_eq :
      (∑ i : Fin n, ∫ s in (0 : ℝ)..t,
        ((n : ℝ) - 1 - 2 * (i : ℝ)) * dysonDrift n (X s.toNNReal) i) =
      ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℝ)) * (X t i - x i - w t i) :=
    Finset.sum_congr rfl fun i _ ↦ by
      rw [intervalIntegral.integral_const_mul]; congr 1; linarith [hX.eq_integral t i]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum fun i _ ↦
      (hX.intervalIntegrable_dysonDrift t i).const_mul _, hrhs_eq] at hmono
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hcancel : ((n : ℝ) / 2) * (2 * (n : ℝ)⁻¹) = 1 := by field_simp [hn_pos.ne']
  have hmul := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
  rwa [← mul_assoc, hcancel, one_mul] at hmul

private theorem uIcc_subset_uIcc_zero_add (t₀ t : ℝ≥0) :
    uIcc (t₀ : ℝ) ((t₀ + t : ℝ≥0) : ℝ) ⊆ uIcc 0 ((t₀ + t : ℝ≥0) : ℝ) := by
  rw [uIcc_of_le (NNReal.coe_le_coe.2 le_self_add), uIcc_of_le (t₀ + t).coe_nonneg]
  exact Icc_subset_Icc t₀.coe_nonneg le_rfl

/-- **Time-shift invariance (semigroup restart).** Shifting a Dyson trajectory `X` forward by any
`t₀ : ℝ≥0` yields a Dyson trajectory started at `X t₀` and driven by the increment path
`t ↦ w (t₀ + t) - w t₀`. When `0 < t₀`, the restarted initial state `X t₀` lies in the open Weyl
chamber `{z | StrictAnti z}` even if `X 0` had coincident coordinates. -/
theorem shift (hX : IsDysonPath n x w X) (t₀ : ℝ≥0) :
    IsDysonPath n (X t₀) (fun t i ↦ w (t₀ + t) i - w t₀ i) (fun t ↦ X (t₀ + t)) where
  continuous := hX.continuous.comp (continuous_const.add continuous_id)
  strictAnti _ ht := hX.strictAnti _ (add_pos_of_nonneg_of_pos _root_.zero_le ht)
  intervalIntegrable t i := by
    have hint := (hX.intervalIntegrable (t₀ + t) i).mono_set (uIcc_subset_uIcc_zero_add t₀ t)
    have hshift : IntervalIntegrable
        (fun s : ℝ ↦ ∑ j ∈ Finset.univ.erase i,
          (X ((t₀ : ℝ) + s).toNNReal i - X ((t₀ : ℝ) + s).toNNReal j)⁻¹)
        volume 0 t := by
      simpa [NNReal.coe_add] using hint.comp_add_left (t₀ : ℝ)
    refine hshift.congr fun s hs ↦ ?_
    rw [uIoc_of_le t.coe_nonneg] at hs
    simp [Real.toNNReal_add t₀.coe_nonneg hs.1.le, Real.toNNReal_coe]
  eq_integral t i := by
    have h1 := hX.eq_integral (t₀ + t) i
    have h2 := hX.eq_integral t₀ i
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hX.intervalIntegrable_dysonDrift t₀ i)
      ((hX.intervalIntegrable_dysonDrift (t₀ + t) i).mono_set (uIcc_subset_uIcc_zero_add t₀ t))
    have hchg : (∫ s in (0 : ℝ)..t, dysonDrift n (X (t₀ + s.toNNReal)) i) =
        ∫ u in (t₀ : ℝ)..((t₀ + t : ℝ≥0) : ℝ), dysonDrift n (X u.toNNReal) i := by
      have hcongr : (∫ s in (0 : ℝ)..t, dysonDrift n (X (t₀ + s.toNNReal)) i) =
          ∫ s in (0 : ℝ)..t, dysonDrift n (X ((t₀ : ℝ) + s).toNNReal) i :=
        intervalIntegral.integral_congr fun s hs ↦ by
          rw [uIcc_of_le t.coe_nonneg] at hs
          simp [Real.toNNReal_add t₀.coe_nonneg hs.1, Real.toNNReal_coe]
      rw [hcongr,
        intervalIntegral.integral_comp_add_left
          (fun u : ℝ ↦ dysonDrift n (X u.toNNReal) i) (t₀ : ℝ),
        add_zero, NNReal.coe_add]
    linarith

private theorem eq_integral_of_mem_uIcc (hX : IsDysonPath n x w X) {s t : ℝ≥0} {r : ℝ}
    (hr : r ∈ uIcc (s : ℝ) t) (i : Fin n) :
    X r.toNNReal i = x i + w r.toNNReal i +
      ∫ u in (0 : ℝ)..r, dysonDrift n (X u.toNNReal) i := by
  simpa only [Real.coe_toNNReal r ((le_min s.coe_nonneg t.coe_nonneg).trans hr.1)] using
    hX.eq_integral r.toNNReal i

/-- **Pathwise `ℓ²` energy identity.** For any two Dyson trajectories `X` and `Y` driven by the
same path `w` and any times `s, t : ℝ≥0`, the change in squared Euclidean distance from `s` to `t`
equals twice the integrated drift-difference pairing over `s..t`. -/
theorem sum_sub_sq_eq (hX : IsDysonPath n x w X) (hY : IsDysonPath n y w Y) (s t : ℝ≥0) :
    (∑ i : Fin n, (X t i - Y t i) ^ 2) - ∑ i : Fin n, (X s i - Y s i) ^ 2 =
      2 * ∫ r in (s : ℝ)..t, ∑ i : Fin n,
        (dysonDrift n (X r.toNNReal) i - dysonDrift n (Y r.toNNReal) i) *
          (X r.toNNReal i - Y r.toNNReal i) := by
  simpa only [Real.toNNReal_coe] using
    TauCeti.intervalIntegral.sum_sq_sub_eq_of_eq_add_integral (Finset.univ : Finset (Fin n))
      (fun i _ ↦ hX.intervalIntegrable_dysonDrift s i)
      (fun i _ ↦ hX.intervalIntegrable_dysonDrift t i)
      (fun i _ ↦ hY.intervalIntegrable_dysonDrift s i)
      (fun i _ ↦ hY.intervalIntegrable_dysonDrift t i)
      (fun _ hr i _ ↦ hX.eq_integral_of_mem_uIcc hr i)
      (fun _ hr i _ ↦ hY.eq_integral_of_mem_uIcc hr i)

/-- **Pathwise `ℓ²` contraction.** Any two Dyson trajectories `X` and `Y` driven by the same path
`w` have nonincreasing squared Euclidean distance on `[0, ∞)`. -/
theorem sum_sub_sq_le_of_le (hX : IsDysonPath n x w X) (hY : IsDysonPath n y w Y)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∑ i : Fin n, (X t i - Y t i) ^ 2 ≤ ∑ i : Fin n, (X s i - Y s i) ^ 2 := by
  simpa only [Real.toNNReal_coe] using
    TauCeti.intervalIntegral.sum_sq_sub_le_of_eq_add_integral (Finset.univ : Finset (Fin n))
      (NNReal.coe_le_coe.2 hst)
      (fun i _ ↦ hX.intervalIntegrable_dysonDrift s i)
      (fun i _ ↦ hX.intervalIntegrable_dysonDrift t i)
      (fun i _ ↦ hY.intervalIntegrable_dysonDrift s i)
      (fun i _ ↦ hY.intervalIntegrable_dysonDrift t i)
      (fun _ hr i _ ↦ hX.eq_integral_of_mem_uIcc hr i)
      (fun _ hr i _ ↦ hY.eq_integral_of_mem_uIcc hr i)
      fun r hr ↦ sum_dysonDrift_sub_mul_sub_nonpos
        (hX.strictAnti r.toNNReal (Real.toNNReal_pos.2 (s.coe_nonneg.trans_lt hr.1)))
        (hY.strictAnti r.toNNReal (Real.toNNReal_pos.2 (s.coe_nonneg.trans_lt hr.1)))

/-- Squared `ℓ²` distance between two Dyson trajectories driven by the same path is antitone on
`[0, ∞)`. -/
theorem antitone_sum_sub_sq (hX : IsDysonPath n x w X) (hY : IsDysonPath n y w Y) :
    Antitone fun t ↦ ∑ i : Fin n, (X t i - Y t i) ^ 2 :=
  fun _ _ hst ↦ hX.sum_sub_sq_le_of_le hY hst

/-- **Continuous dependence on the initial configuration.** The squared `ℓ²` distance at any time
`t` is bounded by the initial squared `ℓ²` distance `∑ i, (x i - y i) ^ 2`. -/
theorem sum_sub_sq_le (hX : IsDysonPath n x w X) (hY : IsDysonPath n y w Y) (t : ℝ≥0) :
    ∑ i : Fin n, (X t i - Y t i) ^ 2 ≤ ∑ i : Fin n, (x i - y i) ^ 2 :=
  (hX.sum_sub_sq_le_of_le hY _root_.zero_le).trans_eq <|
    Finset.sum_congr rfl fun i _ ↦ by rw [hX.eval_zero_apply, hY.eval_zero_apply]; ring

/-- **Pathwise uniqueness.** Two Dyson trajectories started at the same configuration `x` and driven
by the same forcing path `w` are identical. -/
theorem eq (hX : IsDysonPath n x w X) (hY : IsDysonPath n x w Y) : X = Y :=
  funext fun t ↦ TauCeti.eq_of_sum_sq_sub_le_zero <| by
    simpa only [sub_self, zero_pow two_ne_zero, Finset.sum_const_zero] using hX.sum_sub_sq_le hY t

/-- Coordinates of a Dyson trajectory lie in the closed decreasing chamber at every time. -/
protected theorem antitone (hX : IsDysonPath n x w X) (t : ℝ≥0) : Antitone (X t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · exact hX.antitone_zero
  · exact (hX.strictAnti t (pos_iff_ne_zero.2 ht)).antitone

/-- If the driving path vanishes at `0`, the initial configuration lies in the closed decreasing
chamber. -/
theorem antitone_init (hX : IsDysonPath n x w X) (hw : w 0 = 0) : Antitone x := by
  simpa only [hX.eval_zero_of_eq_zero hw] using hX.antitone_zero

/-- Subtracting the driving path leaves a function differentiable at every positive time `u`, with
derivative `dysonDrift n (X u.toNNReal) i`. -/
theorem hasDerivAt_sub_driving (hX : IsDysonPath n x w X) (i : Fin n) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun s : ℝ ↦ X s.toNNReal i - w s.toNNReal i)
      (dysonDrift n (X u.toNNReal) i) u := by
  set f : ℝ → ℝ := fun s ↦ dysonDrift n (X s.toNNReal) i
  have hcont : ∀ v ∈ Ioi (0 : ℝ), ContinuousAt f v := fun v hv ↦ by
    have hXv : ContinuousAt (fun s : ℝ ↦ X s.toNNReal) v :=
      (hX.continuous.comp continuous_real_toNNReal).continuousAt
    have hdr : ContinuousAt (fun s : ℝ ↦ dysonDrift n (X s.toNNReal)) v :=
      ContinuousAt.comp
        (continuousAt_dysonDrift (hX.strictAnti _ (Real.toNNReal_pos.2 hv)).injective) hXv
    exact ContinuousAt.comp (continuous_apply i).continuousAt hdr
  have hint : IntervalIntegrable f volume 0 u := by
    simpa [f, Real.coe_toNNReal u hu.le] using hX.intervalIntegrable_dysonDrift u.toNNReal i
  have hd : HasDerivAt (fun s : ℝ ↦ x i + ∫ r in (0 : ℝ)..s, f r) (f u) u :=
    (intervalIntegral.integral_hasDerivAt_right hint
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hcont u hu) (hcont u hu)).const_add (x i)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hu] with s (hs : 0 < s)
  have heq := hX.eq_integral s.toNNReal i
  rw [Real.coe_toNNReal s hs.le] at heq
  linarith

/-- For two Dyson trajectories driven by the same path, the difference cancels the forcing and has
derivative `dysonDrift n (X u.toNNReal) i - dysonDrift n (Y u.toNNReal) i` at every `u > 0`. -/
theorem hasDerivAt_sub (hX : IsDysonPath n x w X) (hY : IsDysonPath n y w Y) (i : Fin n)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun s : ℝ ↦ X s.toNNReal i - Y s.toNNReal i)
      (dysonDrift n (X u.toNNReal) i - dysonDrift n (Y u.toNNReal) i) u :=
  ((hX.hasDerivAt_sub_driving i hu).sub (hY.hasDerivAt_sub_driving i hu)).congr_of_eventuallyEq
    (Eventually.of_forall fun _ ↦ by simp)

/-- **One-sided `ℓ²` dissipativity.** For two Dyson trajectories driven by the same path,
`t ↦ ∑ i, max (X t i - Y t i) 0 ^ 2` is antitone. -/
theorem antitone_sum_max_sub_zero_sq (hX : IsDysonPath n x w X) (hY : IsDysonPath n y w Y) :
    Antitone fun t : ℝ≥0 ↦ ∑ i : Fin n, max (X t i - Y t i) 0 ^ 2 := by
  set φ : ℝ → ℝ := fun u ↦ ∑ i : Fin n, max (X u.toNNReal i - Y u.toNNReal i) 0 ^ 2
  have hφ_cont : Continuous φ :=
    continuous_finsetSum _ fun i _ ↦
      ((((continuous_apply i).comp hX.continuous).sub
        ((continuous_apply i).comp hY.continuous)).comp continuous_real_toNNReal).max
          continuous_const |>.pow 2
  have hφ_deriv : ∀ u : ℝ, 0 < u → HasDerivAt φ
      (2 * ∑ i : Fin n, (dysonDrift n (X u.toNNReal) i - dysonDrift n (Y u.toNNReal) i) *
        max (X u.toNNReal i - Y u.toNNReal i) 0) u := by
    intro u hu
    have hsum := HasDerivAt.sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
      (hX.hasDerivAt_sub hY i hu).max_zero_pow (by decide : 2 ≠ 1)
    convert hsum using 1
    · ext y
      simp [φ]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      push_cast
      ring
  have hanti : AntitoneOn φ (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hφ_cont.continuousOn ?_ ?_
    · rw [interior_Ici]
      exact fun u hu ↦ (hφ_deriv u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro u (hu : 0 < u)
      rw [(hφ_deriv u hu).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos zero_le_two
        (sum_dysonDrift_sub_mul_max_sub_zero_nonpos
          (hX.strictAnti _ (Real.toNNReal_pos.2 hu)) (hY.strictAnti _ (Real.toNNReal_pos.2 hu)))
  intro s t hst
  simpa [φ] using hanti (NNReal.coe_nonneg s) (NNReal.coe_nonneg t) (NNReal.coe_le_coe.2 hst)

/-- One-sided `ℓ²` bound in terms of the initial configurations. -/
theorem sum_max_sub_zero_sq_le (hX : IsDysonPath n x w X) (hY : IsDysonPath n y w Y)
    (t : ℝ≥0) :
    ∑ i : Fin n, max (X t i - Y t i) 0 ^ 2 ≤ ∑ i : Fin n, max (x i - y i) 0 ^ 2 := by
  have hle := hX.antitone_sum_max_sub_zero_sq hY (_root_.zero_le : 0 ≤ t)
  simpa only [hX.eval_zero, hY.eval_zero, Pi.add_apply, add_sub_add_right_eq_sub] using hle

/-- **Coordinatewise comparison principle** (AGZ Lemma 4.3.6). If `x ≤ y`, two Dyson trajectories
from `x` and `y` driven by the same path satisfy `X t ≤ Y t` at every time. -/
theorem le_of_le (hX : IsDysonPath n x w X) (hY : IsDysonPath n y w Y) (hxy : x ≤ y)
    (t : ℝ≥0) : X t ≤ Y t := by
  intro i
  have h0 : ∑ k : Fin n, max (x k - y k) 0 ^ 2 = 0 :=
    Finset.sum_eq_zero fun k _ ↦ by simp [max_eq_right (sub_nonpos.2 (hxy k))]
  have hle : max (X t i - Y t i) 0 ^ 2 ≤ 0 :=
    calc max (X t i - Y t i) 0 ^ 2
        ≤ ∑ k : Fin n, max (X t k - Y t k) 0 ^ 2 :=
          Finset.single_le_sum (f := fun k ↦ max (X t k - Y t k) 0 ^ 2)
            (fun k _ ↦ sq_nonneg _) (Finset.mem_univ i)
      _ ≤ ∑ k : Fin n, max (x k - y k) 0 ^ 2 := hX.sum_max_sub_zero_sq_le hY t
      _ = 0 := h0
  have hmax : max (X t i - Y t i) 0 = 0 := sq_eq_zero_iff.1 ((sq_nonneg _).antisymm' hle)
  exact sub_nonpos.1 ((le_max_left _ 0).trans_eq hmax)

end IsDysonPath

/-! ### Measure-level Dyson solutions -/

section MeasureLevel

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A pathwise solution of the `n`-particle Dyson system** with parameter `β` started at `x` and
driven by `B` under `P`: almost surely, `t ↦ X t ω` is continuous, lies in the open decreasing Weyl
chamber at positive times, has locally integrable repulsion drift, and satisfies
`X t ω i = x i + √(2 / (β n)) B i t ω + ∫_0^t dysonDrift n (X s ω) i ds`. Adaptedness to a
filtration is not part of this predicate. -/
def IsDysonSolution (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (P : Measure Ω)
    (B : Fin n → ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∀ᵐ ω ∂P, IsDysonPath n x (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) (fun t ↦ X t ω)

/-- Definitional unfolding of `IsDysonSolution` in terms of `IsDysonPath`. -/
theorem isDysonSolution_def {β : ℝ} {n : ℕ} {x : Fin n → ℝ} {P : Measure Ω}
    {B : Fin n → ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → Fin n → ℝ} :
    IsDysonSolution β n x P B X ↔
      ∀ᵐ ω ∂P, IsDysonPath n x
        (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) (fun t ↦ X t ω) :=
  Iff.rfl

/-- Explicit expanded form of `IsDysonSolution` in terms of sample-path continuity, strictly
decreasing coordinates (`StrictAnti`) at positive times, drift integrability, and the coordinatewise
integral equation. -/
theorem isDysonSolution_iff {β : ℝ} {n : ℕ} {x : Fin n → ℝ} {P : Measure Ω}
    {B : Fin n → ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → Fin n → ℝ} :
    IsDysonSolution β n x P B X ↔
      ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω) ∧ (∀ t, 0 < t → StrictAnti (X t ω)) ∧
        ∀ (t : ℝ≥0) (i : Fin n),
          IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ Finset.univ.erase i,
            (X s.toNNReal ω i - X s.toNNReal ω j)⁻¹) volume 0 t ∧
          X t ω i = x i + Real.sqrt (2 / (β * n)) * B i t ω +
            ∫ s in (0 : ℝ)..t, (n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
              (X s.toNNReal ω i - X s.toNNReal ω j)⁻¹ := by
  refine eventually_congr (.of_forall fun _ ↦ ⟨fun h ↦ ⟨h.continuous, h.strictAnti, fun t i ↦
    ⟨h.intervalIntegrable t i, ?_⟩⟩, fun ⟨hc, hsa, hi⟩ ↦ ⟨hc, hsa, fun t i ↦ (hi t i).1,
      fun t i ↦ ?_⟩⟩)
  · simpa [dysonDrift_apply] using h.eq_integral t i
  · simpa [dysonDrift_apply] using (hi t i).2

namespace IsDysonSolution

variable {β : ℝ} {n : ℕ} {x y : Fin n → ℝ} {P : Measure Ω}
  {B : Fin n → ℝ≥0 → Ω → ℝ} {X Y : ℝ≥0 → Ω → Fin n → ℝ}

/-- Almost every sample path of an `IsDysonSolution` is a deterministic `IsDysonPath`. -/
theorem ae_isDysonPath (hX : IsDysonSolution β n x P B X) :
    ∀ᵐ ω ∂P, IsDysonPath n x (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) (fun t ↦ X t ω) :=
  hX

/-- Congruence of `IsDysonSolution` under indistinguishable modifications of the driving process
`B` and the solution process `X`. -/
theorem congr {B' : Fin n → ℝ≥0 → Ω → ℝ} (hX : IsDysonSolution β n x P B X)
    (hB : ∀ i, ∀ᵐ ω ∂P, ∀ t, B i t ω = B' i t ω)
    (hXY : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) :
    IsDysonSolution β n x P B' Y := by
  filter_upwards [hX, ae_all_iff.2 hB, hXY] with ω hω hωB hωX
  have hB_eq : (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) =
      fun t i ↦ Real.sqrt (2 / (β * n)) * B' i t ω := by
    ext t i; rw [hωB i t]
  rwa [← hB_eq, ← funext hωX]

/-- **Almost-sure pathwise uniqueness for `IsDysonSolution`.** Any two solutions started at `x` and
driven by the same process `B` agree at all times almost surely, for every `β : ℝ` and `n : ℕ`
without distributional or independence assumptions on `B`. -/
theorem ae_eq (hX : IsDysonSolution β n x P B X) (hY : IsDysonSolution β n x P B Y) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  filter_upwards [hX, hY] with _ hωX hωY
  exact congrFun (hωX.eq hωY)

/-- Almost every sample path of an `IsDysonSolution` lies in the closed decreasing Weyl chamber at
all times `t ≥ 0`. -/
theorem ae_antitone (hX : IsDysonSolution β n x P B X) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Antitone (X t ω) := by
  filter_upwards [hX] with _ hω t
  exact hω.antitone t

/-- Almost surely, the squared `ℓ²` distance between two solutions driven by the same process `B` is
antitone in time. -/
theorem ae_antitone_sum_sub_sq (hX : IsDysonSolution β n x P B X)
    (hY : IsDysonSolution β n y P B Y) :
    ∀ᵐ ω ∂P, Antitone fun t : ℝ≥0 ↦ ∑ i : Fin n, (X t ω i - Y t ω i) ^ 2 := by
  filter_upwards [hX, hY] with _ hωX hωY
  exact hωX.antitone_sum_sub_sq hωY

/-- Almost-sure `ℓ²` stability in the initial configuration `x, y` for solutions driven by the same
process `B`. -/
theorem ae_sum_sub_sq_le (hX : IsDysonSolution β n x P B X) (hY : IsDysonSolution β n y P B Y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∑ i : Fin n, (X t ω i - Y t ω i) ^ 2 ≤ ∑ i : Fin n, (x i - y i) ^ 2 := by
  filter_upwards [hX, hY] with _ hωX hωY t
  exact hωX.sum_sub_sq_le hωY t

/-- Almost-sure center-of-mass identity for `IsDysonSolution`. -/
theorem ae_sum_eq (hX : IsDysonSolution β n x P B X) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ∑ i : Fin n, X t ω i =
        (∑ i : Fin n, x i) + Real.sqrt (2 / (β * n)) * ∑ i : Fin n, B i t ω := by
  filter_upwards [hX] with ω hω t
  rw [hω.sum_eq t, Finset.mul_sum]

/-- When each driving coordinate starts at `0` almost surely, `X 0 = x` almost surely. -/
theorem ae_eval_zero (hX : IsDysonSolution β n x P B X) (hB0 : ∀ i, ∀ᵐ ω ∂P, B i 0 ω = 0) :
    ∀ᵐ ω ∂P, X 0 ω = x := by
  filter_upwards [hX, ae_all_iff.2 hB0] with _ hω hω0
  exact hω.eval_zero_of_eq_zero (funext fun i ↦ by simp [hω0 i])

/-- When each coordinate of `B` is pre-Brownian, `B i 0 = 0` almost surely and hence `X 0 = x`
almost surely. -/
theorem ae_eval_zero_of_isPreBrownianReal (hX : IsDysonSolution β n x P B X)
    (hB : ∀ i, IsPreBrownianReal (B i) P) : ∀ᵐ ω ∂P, X 0 ω = x :=
  hX.ae_eval_zero fun i ↦ (hB i).eval_zero_ae_eq_zero

/-- **Necessity of an ordered initial state.** Under a nonzero measure `P`, if a Dyson solution
exists for driving coordinates starting almost surely at `0`, then the initial configuration `x`
must be antitone. -/
theorem antitone [NeZero P] (hX : IsDysonSolution β n x P B X)
    (hB0 : ∀ i, ∀ᵐ ω ∂P, B i 0 ω = 0) : Antitone x := by
  have hae : ∀ᵐ _ ∂P, Antitone x := by
    filter_upwards [hX, hX.ae_eval_zero hB0] with _ hω hω0
    exact hω0 ▸ hω.antitone_zero
  exact hae.exists.choose_spec

/-- If a Dyson solution exists for pre-Brownian driving coordinates `B`, then the initial
configuration `x` is antitone (for `n = 0` vacuously, and for `0 < n` because `B 0` forces `P` to
be a probability measure). -/
theorem antitone_of_isPreBrownianReal (hX : IsDysonSolution β n x P B X)
    (hB : ∀ i, IsPreBrownianReal (B i) P) : Antitone x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact fun i ↦ Fin.elim0 i
  · have : IsProbabilityMeasure P := (hB ⟨0, hn⟩).isGaussianProcess.isProbabilityMeasure
    exact hX.antitone fun i ↦ (hB i).eval_zero_ae_eq_zero

/-- **Almost-sure comparison principle.** If `x ≤ y`, two Dyson solutions from `x` and `y` driven by
the same `B` satisfy `X t ω ≤ Y t ω` for all `t`, almost surely. -/
theorem ae_le_of_le (hX : IsDysonSolution β n x P B X) (hY : IsDysonSolution β n y P B Y)
    (hxy : x ≤ y) : ∀ᵐ ω ∂P, ∀ t, X t ω ≤ Y t ω := by
  filter_upwards [hX.ae_isDysonPath, hY.ae_isDysonPath] with ω hωX hωY
  exact hωX.le_of_le hωY hxy

end IsDysonSolution

end MeasureLevel

/-! ### Concrete witnesses and explicit low-dimensional solutions -/

section Witnesses

/-- For at most one particle (`n ≤ 1`), there is no pairwise repulsion, so `t ↦ x + w t` is a
Dyson trajectory for every continuous forcing path `w`. -/
theorem isDysonPath_of_le_one {n : ℕ} (hn : n ≤ 1) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    IsDysonPath n x w (fun t ↦ x + w t) where
  continuous := continuous_const.add hw
  strictAnti _ _ i j hij :=
    have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 hn
    absurd (Subsingleton.elim i j) hij.ne
  intervalIntegrable _ i := by
    have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 hn
    have hempty : Finset.univ.erase i = ∅ := by ext j; simp [Subsingleton.elim j i]
    simp [hempty]
  eq_integral _ _ := by simp [dysonDrift_of_le_one hn]

/-- At `n = 0`, the unique empty path is a Dyson trajectory for every forcing path `w`. -/
theorem isDysonPath_zero (x : Fin 0 → ℝ) (w : ℝ≥0 → Fin 0 → ℝ) :
    IsDysonPath 0 x w (fun _ ↦ Fin.elim0) := by
  have heq : (fun _ : ℝ≥0 ↦ (Fin.elim0 : Fin 0 → ℝ)) = fun t ↦ x + w t := by
    ext _ i; exact Fin.elim0 i
  rw [heq]
  exact isDysonPath_of_le_one (Nat.zero_le 1) x (continuous_pi fun i ↦ Fin.elim0 i)

/-- At `n = 1`, there is no pairwise repulsion, so `t ↦ x + w t` is a Dyson trajectory for every
continuous forcing path `w`. -/
theorem isDysonPath_one (x : Fin 1 → ℝ) {w : ℝ≥0 → Fin 1 → ℝ} (hw : Continuous w) :
    IsDysonPath 1 x w (fun t ↦ x + w t) :=
  isDysonPath_of_le_one le_rfl x hw

/-- **Complete existence and uniqueness of `IsDysonSolution` for `n ≤ 1`.** For `n = 0` or `n = 1`,
every coordinate family `B` with almost-surely continuous sample paths (in particular any Brownian
coordinate family via `IsBrownianReal.cont`) drives an almost-surely unique Dyson solution for any
parameter `β : ℝ` and initial configuration `x : Fin n → ℝ`. -/
theorem dysonSystem_exists_unique_of_le_one {Ω : Type*} [MeasurableSpace Ω] (β : ℝ) {n : ℕ}
    (hn : n ≤ 1) (x : Fin n → ℝ) (P : Measure Ω) (B : Fin n → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, ∀ᵐ ω ∂P, Continuous fun t ↦ B i t ω) :
    (∃ X : ℝ≥0 → Ω → Fin n → ℝ, IsDysonSolution β n x P B X) ∧
      ∀ X Y : ℝ≥0 → Ω → Fin n → ℝ, IsDysonSolution β n x P B X → IsDysonSolution β n x P B Y →
        ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  refine ⟨⟨fun t ω i ↦ x i + Real.sqrt (2 / (β * n)) * B i t ω, ?_⟩,
    fun _ _ hX hY ↦ hX.ae_eq hY⟩
  filter_upwards [ae_all_iff.2 hB] with ω hω
  exact isDysonPath_of_le_one hn x (continuous_pi fun i ↦ continuous_const.mul (hω i))

/-- **Explicit two-particle zero-noise Dyson trajectory** from an ordered initial configuration
`x : Fin 2 → ℝ`:
`X t = ![(x 0 + x 1 + √((x 0 - x 1)^2 + 2 t)) / 2, (x 0 + x 1 - √((x 0 - x 1)^2 + 2 t)) / 2]`.
When `x 0 = x 1`, the two particles separate instantaneously as `x 0 ± √(t / 2)` with inverse gap
`(2 * t)⁻¹/²` and coordinate drift `±(2 * √(2 * t))⁻¹` at `t = 0`. -/
noncomputable def twoParticleDysonPath (x : Fin 2 → ℝ) (t : ℝ≥0) (i : Fin 2) : ℝ :=
  if i = 0 then (x 0 + x 1 + Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ))) / 2
  else (x 0 + x 1 - Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ))) / 2

/-- First coordinate of `twoParticleDysonPath`. -/
@[simp]
theorem twoParticleDysonPath_apply_zero (x : Fin 2 → ℝ) (t : ℝ≥0) :
    twoParticleDysonPath x t 0 =
      (x 0 + x 1 + Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ))) / 2 := by
  simp [twoParticleDysonPath]

/-- Second coordinate of `twoParticleDysonPath`. -/
@[simp]
theorem twoParticleDysonPath_apply_one (x : Fin 2 → ℝ) (t : ℝ≥0) :
    twoParticleDysonPath x t 1 =
      (x 0 + x 1 - Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ))) / 2 := by
  simp [twoParticleDysonPath]

/-- Gap between the two coordinates of `twoParticleDysonPath`. -/
theorem twoParticleDysonPath_apply_zero_sub_apply_one (x : Fin 2 → ℝ) (t : ℝ≥0) :
    twoParticleDysonPath x t 0 - twoParticleDysonPath x t 1 =
      Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ)) := by
  rw [twoParticleDysonPath_apply_zero, twoParticleDysonPath_apply_one]; ring

/-- `twoParticleDysonPath x` is continuous on `[0, ∞)` for every initial configuration `x`. -/
theorem continuous_twoParticleDysonPath (x : Fin 2 → ℝ) :
    Continuous (twoParticleDysonPath x) := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, twoParticleDysonPath_apply_zero,
    twoParticleDysonPath_apply_one] <;> fun_prop

/-- `twoParticleDysonPath x t` is strictly decreasing at every strictly positive time `t > 0`. -/
theorem strictAnti_twoParticleDysonPath (x : Fin 2 → ℝ) {t : ℝ≥0} (ht : 0 < t) :
    StrictAnti (twoParticleDysonPath x t) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij.ne
  · simp only [Fin.zero_eta, Fin.mk_one]
    have hpos : 0 < Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ)) := Real.sqrt_pos.2 (by positivity)
    linarith [twoParticleDysonPath_apply_zero_sub_apply_one x t]
  · exact absurd hij (by decide)
  · exact absurd rfl hij.ne

private theorem intervalIntegrable_and_integral_twoParticleGap {x : Fin 2 → ℝ} (hx : Antitone x)
    (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt ((x 0 - x 1) ^ 2 + 2 * s))⁻¹) volume 0 t ∧
      ∫ s in (0 : ℝ)..t, (2 : ℝ)⁻¹ * (Real.sqrt ((x 0 - x 1) ^ 2 + 2 * s))⁻¹ =
        (Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ)) - (x 0 - x 1)) / 2 := by
  have hx01 : 0 ≤ x 0 - x 1 := sub_nonneg.2 (hx (by decide : (0 : Fin 2) ≤ 1))
  let u : ℝ → ℝ := fun s ↦ (x 0 - x 1) ^ 2 + 2 * s
  let F : ℝ → ℝ := fun s ↦ Real.sqrt (u s) / 2
  have hF_cont : Continuous F := by unfold F u; fun_prop
  have hF_deriv (s : ℝ) (hs : 0 < s) : HasDerivAt F ((2 : ℝ)⁻¹ * (Real.sqrt (u s))⁻¹) s := by
    have hu_pos : 0 < u s := by dsimp [u]; positivity
    have hu_d : HasDerivAt u 2 s := by
      simpa [u] using ((hasDerivAt_id s).const_mul (2 : ℝ)).const_add ((x 0 - x 1) ^ 2)
    have hne : Real.sqrt (u s) ≠ 0 := (Real.sqrt_pos.2 hu_pos).ne'
    exact ((hu_d.sqrt hu_pos.ne').div_const 2).congr_deriv (by field_simp [hne])
  have hint_half : IntervalIntegrable (fun s : ℝ ↦ (2 : ℝ)⁻¹ * (Real.sqrt (u s))⁻¹) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).2
      (_root_.intervalIntegral.integrableOn_deriv_of_nonneg hF_cont.continuousOn
        (fun s hs ↦ hF_deriv s hs.1) (fun _ _ ↦ by positivity))
  refine ⟨(hint_half.const_mul 2).congr fun _ _ ↦ by dsimp only [u]; ring, ?_⟩
  rw [TauCeti.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg t.coe_nonneg
    hF_cont.continuousOn (fun s hs ↦ hF_deriv s hs.1) (fun _ _ ↦ by positivity)]
  dsimp only [F, u]; simp only [mul_zero, add_zero, Real.sqrt_sq hx01]; ring

/-- **Non-vacuous singular-drift witness for `IsDysonPath`.** For every antitone initial state
`x : Fin 2 → ℝ` (including coincident `x 0 = x 1`), `twoParticleDysonPath x` is a zero-noise Dyson
trajectory started at `x` (unique by `IsDysonPath.eq`). -/
theorem isDysonPath_twoParticleDysonPath {x : Fin 2 → ℝ} (hx : Antitone x) :
    IsDysonPath 2 x 0 (twoParticleDysonPath x) := by
  have herase0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have herase1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  have hgap {s : ℝ} (hs : 0 ≤ s) :
      twoParticleDysonPath x s.toNNReal 0 - twoParticleDysonPath x s.toNNReal 1 =
        Real.sqrt ((x 0 - x 1) ^ 2 + 2 * s) := by
    rw [twoParticleDysonPath_apply_zero_sub_apply_one, Real.coe_toNNReal s hs]
  refine
    { continuous := continuous_twoParticleDysonPath x
      strictAnti := fun _ ht ↦ strictAnti_twoParticleDysonPath x ht
      intervalIntegrable := fun t i ↦ ?_
      eq_integral := fun t i ↦ ?_ }
  · have hint := (intervalIntegrable_and_integral_twoParticleGap hx t).1
    fin_cases i
    · simp only [Fin.zero_eta, herase0, Finset.sum_singleton]
      exact hint.congr fun s hs ↦ by rw [uIoc_of_le t.coe_nonneg] at hs; rw [hgap hs.1.le]
    · simp only [Fin.mk_one, herase1, Finset.sum_singleton]
      exact hint.neg.congr fun s hs ↦ by
        rw [uIoc_of_le t.coe_nonneg] at hs
        simp only [Pi.neg_apply]
        rw [← neg_sub (twoParticleDysonPath x s.toNNReal 0), inv_neg, hgap hs.1.le]
  · have hval := (intervalIntegrable_and_integral_twoParticleGap hx t).2
    fin_cases i
    · simp only [Fin.zero_eta, Pi.zero_apply, add_zero, dysonDrift_apply, Nat.cast_ofNat,
        herase0, Finset.sum_singleton]
      rw [intervalIntegral.integral_congr
          (g := fun s ↦ (2 : ℝ)⁻¹ * (Real.sqrt ((x 0 - x 1) ^ 2 + 2 * s))⁻¹)
          fun s hs ↦ by rw [uIcc_of_le t.coe_nonneg] at hs; rw [hgap hs.1],
        hval, twoParticleDysonPath_apply_zero]
      ring
    · simp only [Fin.mk_one, Pi.zero_apply, add_zero, dysonDrift_apply, Nat.cast_ofNat,
        herase1, Finset.sum_singleton]
      rw [intervalIntegral.integral_congr
          (g := fun s ↦ -((2 : ℝ)⁻¹ * (Real.sqrt ((x 0 - x 1) ^ 2 + 2 * s))⁻¹))
          fun s hs ↦ by
            rw [uIcc_of_le t.coe_nonneg] at hs
            rw [← neg_sub (twoParticleDysonPath x s.toNNReal 0), inv_neg, hgap hs.1, mul_neg],
        intervalIntegral.integral_neg, hval, twoParticleDysonPath_apply_one]
      ring

/-- Non-vacuous measure-level witness for `IsDysonSolution` at `n = 2` from any `Antitone x`
(including coincident `x 0 = x 1`) with zero noise. -/
theorem isDysonSolution_twoParticleDysonPath {Ω : Type*} [MeasurableSpace Ω] (β : ℝ)
    {x : Fin 2 → ℝ} (hx : Antitone x) (P : Measure Ω) :
    IsDysonSolution β 2 x P 0 (fun t _ ↦ twoParticleDysonPath x t) :=
  .of_forall fun _ ↦ by simpa [Pi.zero_def] using isDysonPath_twoParticleDysonPath hx

end Witnesses

end TauCeti.Probability
