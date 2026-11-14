/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.BrownianMotion.Basic
public import TauCeti.Probability.DysonBrownianMotion.Drift
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.Analysis.ODE.Nonautonomous
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Pathwise solutions, uniqueness, and chamber truncations of Dyson Brownian motion

Because the noise in Dyson Brownian motion is additive, the interacting `n`-particle system
`dX_t(i) = √(2 / (β n)) dB_t(i) + n⁻¹ ∑_{j ≠ i} (X_t(i) - X_t(j))⁻¹ dt` can be formulated pathwise
as the integral identity
`X t i = x i + w t i + ∫ s in (0 : ℝ)..t, dysonDrift n (X s.toNNReal) i`,
together with continuity of `X`, strict decreasing order `StrictAnti (X t)` at strictly positive
times `t > 0`, and local integrability of the repulsion sum on `[0, t]`. An ordered boundary start
`Antitone x` with coincident coordinates is allowed because the singular drift need only be
integrable down to `0` while `StrictAnti (X t)` holds for `t > 0`.

This file introduces both the deterministic path predicate `IsDysonPath` and the almost-sure
measure-level predicate `IsDysonSolution`, and proves the pathwise analytical core of the Dyson
system:

* **Pairwise integrability and entrance bound.** Although `IsDysonPath` assumes integrability only
  for the signed sum `∑ j ∈ Finset.univ.erase i, (X s i - X s j)⁻¹`, every individual inverse gap
  `(X s i - X s j)⁻¹` (`i ≠ j`) along a Dyson trajectory is interval-integrable on `[0, t]`, with
  an explicit Rogers–Shi `L¹` bound down to `s = 0` (`IsDysonPath.intervalIntegrable_sub_inv`,
  `IsDysonPath.integral_sum_Ioi_sub_inv_le`).
* **Pathwise `ℓ²` contraction and uniqueness.** For any two Dyson paths `X` and `Y` driven by the
  same trajectory `w`, the noise cancels from `X - Y`, which is absolutely continuous on every
  `[0, t]`, and open-chamber monotone dissipativity yields
  `∑ i, (X t i - Y t i) ^ 2 ≤ ∑ i, (X s i - Y s i) ^ 2` for `s ≤ t` (`IsDysonPath.sum_sq_sub_le`).
  Setting `s = 0` gives pathwise uniqueness (`IsDysonPath.eq`) and almost-sure uniqueness for
  `IsDysonSolution` (`IsDysonSolution.ae_eq`) for every `β : ℝ` and `n : ℕ`.
* **Globally Lipschitz chamber truncations.** Shifting by a continuous driving path `w` reduces the
  `ε`-truncated Dyson equation to a nonautonomous globally Lipschitz ODE solved on `ℝ` by
  `ODE.nonautonomousSolution`, producing `truncatedDysonPath`. Truncated trajectories satisfy global
  `ℓ²` contraction, agree across cutoffs `ε₁, ε₂` before chamber exit, and coincide with any
  `IsDysonPath` while its gaps stay at least `ε`.
* **Concrete witnesses.** In addition to complete existence and uniqueness for `n ≤ 1` driven by
  arbitrary Brownian motion (`dysonSystem_exists_unique_of_le_one`), `twoParticleDysonPath` gives an
  explicit closed-form `n = 2` Dyson trajectory from any `Antitone x` (coincident `x 0 = x 1`
  included, where the drift has a genuine `t⁻¹/²` singularity at `t = 0`).

## Main declarations

* `TauCeti.Probability.IsDysonPath`: deterministic pathwise solution predicate for a driving path.
* `TauCeti.Probability.IsDysonSolution`: almost-sure solution predicate driven by `B` at parameter
  `β`.
* `TauCeti.Probability.IsDysonPath.intervalIntegrable_sub_inv` and
  `TauCeti.Probability.IsDysonPath.integral_sum_Ioi_sub_inv_le`: individual inverse-gap
  integrability and Rogers–Shi entrance bound.
* `TauCeti.Probability.IsDysonPath.sum_sq_sub_le`, `TauCeti.Probability.IsDysonPath.eq`, and
  `TauCeti.Probability.IsDysonSolution.ae_eq`: `ℓ²` contraction and pathwise / a.s. uniqueness.
* `TauCeti.Probability.truncatedDysonPath`: global `ε`-truncated trajectory driven by continuous
  `w`, with consistency and localization theorems.
* `TauCeti.Probability.dysonSystem_exists_unique_of_le_one` and
  `TauCeti.Probability.isDysonPath_twoParticleDysonPath`: non-vacuous witnesses.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, Lemma 4.3.3 and Proposition 4.3.5.
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
theorem eval_zero_apply (hX : IsDysonPath n x w X) (i : Fin n) :
    X 0 i = x i + w 0 i := by
  simpa using hX.eq_integral 0 i

/-- Vector form of the initial condition `X 0 = x + w 0`. -/
theorem eval_zero (hX : IsDysonPath n x w X) : X 0 = x + w 0 :=
  funext hX.eval_zero_apply

/-- When the driving path starts at `0`, `X 0 = x`. -/
theorem eval_zero_of_eq_zero (hX : IsDysonPath n x w X) (hw : w 0 = 0) : X 0 = x := by
  simp [hX.eval_zero, hw]

/-- The initial configuration `X 0` of a Dyson trajectory is antitone. -/
theorem antitone_zero (hX : IsDysonPath n x w X) : Antitone (X 0) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  let u : ℕ → ℝ≥0 := fun k ↦ ((k : ℝ≥0) + 1)⁻¹
  have hu_pos : ∀ k : ℕ, 0 < u k := fun k ↦ inv_pos.2 (by positivity)
  have hu_tendsto : Tendsto u atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    simpa [u, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcont_i : Continuous fun t : ℝ≥0 ↦ X t i := (continuous_apply i).comp hX.continuous
  have hcont_j : Continuous fun t : ℝ≥0 ↦ X t j := (continuous_apply j).comp hX.continuous
  exact le_of_tendsto_of_tendsto (hcont_j.continuousAt.tendsto.comp hu_tendsto)
    (hcont_i.continuousAt.tendsto.comp hu_tendsto)
    (.of_forall fun k ↦ (hX.strictAnti (u k) (hu_pos k) hlt).le)

/-- Every Dyson trajectory forces its driving path `w` to be continuous. -/
theorem continuous_driving (hX : IsDysonPath n x w X) : Continuous w := by
  refine continuous_pi fun i ↦ continuous_iff_continuousAt.2 fun t ↦ ?_
  set T : ℝ≥0 := t + 1
  have hprim_ac : AbsolutelyContinuousOnInterval
      (fun r : ℝ ↦ ∫ s in (0 : ℝ)..r, dysonDrift n (X s.toNNReal) i) 0 T :=
    (hX.intervalIntegrable_dysonDrift T i).absolutelyContinuousOnInterval_intervalIntegral'
      left_mem_uIcc
  have hprim_contOn : ContinuousOn
      (fun u : ℝ≥0 ↦ ∫ s in (0 : ℝ)..u, dysonDrift n (X s.toNNReal) i) (Iic T) :=
    hprim_ac.continuousOn.comp NNReal.continuous_coe.continuousOn fun u hu ↦ by
      rw [uIcc_of_le T.coe_nonneg]
      exact ⟨u.coe_nonneg, hu⟩
  have hprim_at : ContinuousAt
      (fun u : ℝ≥0 ↦ ∫ s in (0 : ℝ)..u, dysonDrift n (X s.toNNReal) i) t :=
    hprim_contOn.continuousAt
      (mem_of_superset (Iio_mem_nhds (lt_add_one t)) Iio_subset_Iic_self)
  have hX_at : ContinuousAt (fun u : ℝ≥0 ↦ X u i) t :=
    ((continuous_apply i).comp hX.continuous).continuousAt
  have heq : (fun u : ℝ≥0 ↦ w u i) = fun u : ℝ≥0 ↦
      X u i - x i - ∫ s in (0 : ℝ)..u, dysonDrift n (X s.toNNReal) i := by
    ext u
    linarith [hX.eq_integral u i]
  rw [heq]
  exact (hX_at.sub continuousAt_const).sub hprim_at

/-- **Center-of-mass conservation.** Summing the coordinates of a Dyson trajectory cancels the
repulsive drift at every time `t`. -/
theorem sum_eq (hX : IsDysonPath n x w X) (t : ℝ≥0) :
    ∑ i : Fin n, X t i = (∑ i : Fin n, x i) + ∑ i : Fin n, w t i := by
  simp_rw [hX.eq_integral t, Finset.sum_add_distrib]
  rw [← intervalIntegral.integral_finsetSum fun i _ ↦ hX.intervalIntegrable_dysonDrift t i]
  simp [sum_dysonDrift_eq_zero]

/-- **Pairwise integrability of inverse gaps.** Even though `IsDysonPath` assumes integrability only
for the signed sum `∑ j ∈ Finset.univ.erase i, (X s i - X s j)⁻¹`, every individual inverse gap
`(X s.toNNReal i - X s.toNNReal j)⁻¹` (`i ≠ j`) is interval-integrable on `[0, t]`. -/
theorem intervalIntegrable_sub_inv (hX : IsDysonPath n x w X) (t : ℝ≥0) {i j : Fin n}
    (hij : i ≠ j) :
    IntervalIntegrable (fun s : ℝ ↦ (X s.toNNReal i - X s.toNNReal j)⁻¹) volume 0 t := by
  have hmeas : ∀ u v : Fin n,
      Measurable fun s : ℝ ↦ (X s.toNNReal u - X s.toNNReal v)⁻¹ := fun u v ↦
    ((((continuous_apply u).comp hX.continuous).comp continuous_real_toNNReal).sub
      (((continuous_apply v).comp hX.continuous).comp continuous_real_toNNReal)).measurable.inv
  have hordered : ∀ k : ℕ, ∀ u : Fin n, u.val = k → ∀ v : Fin n, u < v →
      IntegrableOn (fun s : ℝ ↦ (X s.toNNReal u - X s.toNNReal v)⁻¹) (Ioc 0 t) volume := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro u huk v huv
      have hlt_sum : IntegrableOn
          (fun s : ℝ ↦ ∑ r ∈ Finset.Iio u, (X s.toNNReal u - X s.toNNReal r)⁻¹)
          (Ioc 0 t) volume := by
        refine integrable_finsetSum _ fun r hr ↦ ?_
        have hru : r < u := Finset.mem_Iio.1 hr
        have hneg : (fun s : ℝ ↦ (X s.toNNReal u - X s.toNNReal r)⁻¹) =
            fun s : ℝ ↦ -(X s.toNNReal r - X s.toNNReal u)⁻¹ := by
          ext s; rw [← neg_sub (X s.toNNReal r) (X s.toNNReal u), inv_neg]
        rw [hneg]
        exact (ih r.val (huk ▸ hru) r rfl u hru).neg
      have hall_sum : IntegrableOn
          (fun s : ℝ ↦ ∑ r ∈ Finset.univ.erase u, (X s.toNNReal u - X s.toNNReal r)⁻¹)
          (Ioc 0 t) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).1 (hX.intervalIntegrable t u)
      have hgt_sum : IntegrableOn
          (fun s : ℝ ↦ ∑ r ∈ Finset.Ioi u, (X s.toNNReal u - X s.toNNReal r)⁻¹)
          (Ioc 0 t) volume := by
        refine (hall_sum.sub hlt_sum).congr_fun (fun s _ ↦ ?_) measurableSet_Ioc
        simp only [Pi.sub_apply]
        rw [← Finset.compl_singleton, ← Finset.Ioi_disjUnion_Iio, Finset.sum_disjUnion,
          add_sub_cancel_right]
      refine hgt_sum.mono' (hmeas u v).aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs ↦ ?_
      have hanti : StrictAnti (X s.toNNReal) := hX.strictAnti s.toNNReal (Real.toNNReal_pos.2 hs.1)
      have hnonneg : ∀ r ∈ Finset.Ioi u,
          0 ≤ (X s.toNNReal u - X s.toNNReal r)⁻¹ := fun r hr ↦
        inv_nonneg.2 (sub_pos.2 (hanti (Finset.mem_Ioi.1 hr))).le
      rw [Real.norm_of_nonneg (hnonneg v (Finset.mem_Ioi.2 huv))]
      exact Finset.single_le_sum hnonneg (Finset.mem_Ioi.2 huv)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hordered i.val i rfl j hlt
  · have hneg : (fun s : ℝ ↦ (X s.toNNReal i - X s.toNNReal j)⁻¹) =
        fun s : ℝ ↦ -(X s.toNNReal j - X s.toNNReal i)⁻¹ := by
      ext s; rw [← neg_sub (X s.toNNReal j) (X s.toNNReal i), inv_neg]
    rw [hneg]
    exact (hordered j.val j rfl i hgt).neg

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
    (IntervalIntegrable.sum (Finset.univ : Finset (Fin n)) fun i _ ↦
      IntervalIntegrable.sum (Finset.Ioi i) fun j hj ↦
        hX.intervalIntegrable_sub_inv t (Finset.mem_Ioi.1 hj).ne).congr fun _ _ ↦ by simp
  have hint_rhs : IntervalIntegrable
      (fun s : ℝ ↦ ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℝ)) * dysonDrift n (X s.toNNReal) i)
      volume 0 t :=
    (IntervalIntegrable.sum (Finset.univ : Finset (Fin n)) fun i _ ↦
      (hX.intervalIntegrable_dysonDrift t i).const_mul ((n : ℝ) - 1 - 2 * (i : ℝ))).congr
        fun _ _ ↦ by simp
  have hmono : ∫ s in (0 : ℝ)..t,
        2 * (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
          (X s.toNNReal i - X s.toNNReal j)⁻¹ ≤
      ∫ s in (0 : ℝ)..t,
        ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℝ)) * dysonDrift n (X s.toNNReal) i :=
    intervalIntegral.integral_mono_on_of_le_Ioo t.coe_nonneg (hint_lhs.const_mul _) hint_rhs
      fun s hs ↦ le_sum_entranceWeight_mul_dysonDrift
        (hX.strictAnti s.toNNReal (Real.toNNReal_pos.2 hs.1))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum fun i _ ↦
      (hX.intervalIntegrable_dysonDrift t i).const_mul _] at hmono
  have hrhs : (∑ i : Fin n, ∫ s in (0 : ℝ)..t,
        ((n : ℝ) - 1 - 2 * (i : ℝ)) * dysonDrift n (X s.toNNReal) i) =
      ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℝ)) * (X t i - x i - w t i) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [intervalIntegral.integral_const_mul]
    congr 1
    linarith [hX.eq_integral t i]
  rw [hrhs] at hmono
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hmul := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
  have hcancel : ((n : ℝ) / 2) *
      (2 * (n : ℝ)⁻¹ * ∫ s in (0 : ℝ)..t, ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        (X s.toNNReal i - X s.toNNReal j)⁻¹) =
      ∫ s in (0 : ℝ)..t, ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        (X s.toNNReal i - X s.toNNReal j)⁻¹ := by
    field_simp [hn_pos.ne']
  rwa [hcancel] at hmul

private theorem sq_sub_eq_two_mul_integral_and_integrable (hX : IsDysonPath n x w X)
    (hY : IsDysonPath n y w Y) {s t : ℝ≥0} (hst : s ≤ t) (i : Fin n) :
    ((X t i - Y t i) ^ 2 - (X s i - Y s i) ^ 2 =
      2 * ∫ r in (s : ℝ)..t, (X r.toNNReal i - Y r.toNNReal i) *
        (dysonDrift n (X r.toNNReal) i - dysonDrift n (Y r.toNNReal) i)) ∧
    IntervalIntegrable (fun r : ℝ ↦ (X r.toNNReal i - Y r.toNNReal i) *
      (dysonDrift n (X r.toNNReal) i - dysonDrift n (Y r.toNNReal) i)) volume s t := by
  have hstR : (s : ℝ) ≤ t := hst
  let g : ℝ → ℝ := fun r ↦ dysonDrift n (X r.toNNReal) i - dysonDrift n (Y r.toNNReal) i
  let d : ℝ → ℝ := fun r ↦ (x i - y i) + ∫ u in (0 : ℝ)..r, g u
  have hg_int0 : IntervalIntegrable g volume 0 t :=
    (hX.intervalIntegrable_dysonDrift t i).sub (hY.intervalIntegrable_dysonDrift t i)
  have hsub_uIcc : uIcc (s : ℝ) t ⊆ uIcc 0 t := by
    rw [uIcc_of_le hstR, uIcc_of_le t.coe_nonneg]
    exact Icc_subset_Icc s.coe_nonneg le_rfl
  have hd_ac : AbsolutelyContinuousOnInterval d s t :=
    (((LipschitzWith.const (x i - y i)).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (hg_int0.absolutelyContinuousOnInterval_intervalIntegral' left_mem_uIcc)).mono hsub_uIcc
  have hd_deriv : ∀ᵐ r, r ∈ uIoc (s : ℝ) t → HasDerivAt d (g r) r := by
    filter_upwards [hg_int0.ae_hasDerivAt_integral] with r hr hmem
    simpa [d] using (hr (hsub_uIcc (uIoc_subset_uIcc hmem)) 0 left_mem_uIcc).const_add (x i - y i)
  have hd_val : ∀ u : ℝ≥0, d u = X u i - Y u i := fun u ↦ by
    have hsub := intervalIntegral.integral_sub (hX.intervalIntegrable_dysonDrift u i)
      (hY.intervalIntegrable_dysonDrift u i)
    dsimp [d]
    linarith [hX.eq_integral u i, hY.eq_integral u i]
  have heqOn : EqOn (fun r : ℝ ↦ d r * g r)
      (fun r : ℝ ↦ (X r.toNNReal i - Y r.toNNReal i) * g r) (uIcc (s : ℝ) t) := fun r hr ↦ by
    rw [uIcc_of_le hstR] at hr
    have hdr : d r = X r.toNNReal i - Y r.toNNReal i := by
      simpa only [Real.coe_toNNReal r (s.coe_nonneg.trans hr.1)] using hd_val r.toNNReal
    exact congrArg (· * g r) hdr
  have hibp := hd_ac.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt hd_ac hd_deriv hd_deriv
  have hcongr₁ : ∫ r in (s : ℝ)..t, d r * g r =
      ∫ r in (s : ℝ)..t, (X r.toNNReal i - Y r.toNNReal i) * g r :=
    intervalIntegral.integral_congr heqOn
  have hcongr₂ : ∫ r in (s : ℝ)..t, g r * d r =
      ∫ r in (s : ℝ)..t, (X r.toNNReal i - Y r.toNNReal i) * g r :=
    intervalIntegral.integral_congr fun r hr ↦ (mul_comm _ _).trans (heqOn hr)
  rw [hcongr₁, hcongr₂, hd_val t, hd_val s, ← sq, ← sq] at hibp
  refine ⟨by linarith, ?_⟩
  exact ((hg_int0.mono_set hsub_uIcc).continuousOn_mul hd_ac.continuousOn).congr
    (heqOn.mono uIoc_subset_uIcc)

/-- **Pathwise `ℓ²` contraction.** Any two Dyson trajectories `X` and `Y` driven by the same path
`w` have nonincreasing squared Euclidean distance on `[0, ∞)`. -/
theorem sum_sq_sub_le (hX : IsDysonPath n x w X) (hY : IsDysonPath n y w Y)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∑ i : Fin n, (X t i - Y t i) ^ 2 ≤ ∑ i : Fin n, (X s i - Y s i) ^ 2 := by
  have hstR : (s : ℝ) ≤ t := hst
  have hstep := hX.sq_sub_eq_two_mul_integral_and_integrable hY hst
  have hdiff : (∑ i : Fin n, (X t i - Y t i) ^ 2) - ∑ i : Fin n, (X s i - Y s i) ^ 2 =
      2 * ∫ r in (s : ℝ)..t, ∑ i : Fin n, (X r.toNNReal i - Y r.toNNReal i) *
        (dysonDrift n (X r.toNNReal) i - dysonDrift n (Y r.toNNReal) i) := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [fun i ↦ (hstep i).1, ← Finset.mul_sum,
      intervalIntegral.integral_finsetSum fun i _ ↦ (hstep i).2]
  have hint_nonpos : ∫ r in (s : ℝ)..t, (∑ i : Fin n, (X r.toNNReal i - Y r.toNNReal i) *
      (dysonDrift n (X r.toNNReal) i - dysonDrift n (Y r.toNNReal) i)) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hstR]
    refine setIntegral_nonpos measurableSet_Ioc fun r hr ↦ ?_
    have hr_pos : 0 < r := s.coe_nonneg.trans_lt hr.1
    have hcomm : (∑ i : Fin n, (X r.toNNReal i - Y r.toNNReal i) *
        (dysonDrift n (X r.toNNReal) i - dysonDrift n (Y r.toNNReal) i)) =
        ∑ i : Fin n, (dysonDrift n (X r.toNNReal) i - dysonDrift n (Y r.toNNReal) i) *
          (X r.toNNReal i - Y r.toNNReal i) :=
      Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    rw [hcomm]
    exact sum_dysonDrift_sub_mul_sub_nonpos
      (hX.strictAnti r.toNNReal (Real.toNNReal_pos.2 hr_pos))
      (hY.strictAnti r.toNNReal (Real.toNNReal_pos.2 hr_pos))
  linarith

/-- **Continuous dependence on the initial configuration.** The `ℓ²` distance at any time `t` is
bounded by the initial `ℓ²` distance `∑ i, (x i - y i) ^ 2`. -/
theorem sum_sq_sub_le_start (hX : IsDysonPath n x w X) (hY : IsDysonPath n y w Y) (t : ℝ≥0) :
    ∑ i : Fin n, (X t i - Y t i) ^ 2 ≤ ∑ i : Fin n, (x i - y i) ^ 2 := by
  refine (hX.sum_sq_sub_le hY _root_.zero_le).trans_eq ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hX.eval_zero_apply, hY.eval_zero_apply]
  ring

/-- **Pathwise uniqueness.** Two Dyson trajectories started at the same configuration `x` and driven
by the same forcing path `w` are identical. -/
theorem eq (hX : IsDysonPath n x w X) (hY : IsDysonPath n x w Y) : X = Y := by
  ext t i
  have hle := hX.sum_sq_sub_le_start hY t
  simp only [sub_self, zero_pow two_ne_zero, Finset.sum_const_zero] at hle
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin n)), (X t j - Y t j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg _).1
      (le_antisymm hle (Finset.sum_nonneg fun j _ ↦ sq_nonneg _))
  exact sub_eq_zero.1 (sq_eq_zero_iff.1 (hzero i (Finset.mem_univ i)))

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

/-- Explicit expanded form of `IsDysonSolution` in terms of sample-path continuity, strict
monotonicity in `(0, ∞)`, drift integrability, and the coordinatewise integral equation. -/
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
  refine eventually_congr (.of_forall fun ω ↦ ⟨fun h ↦ ⟨h.continuous, h.strictAnti, fun t i ↦
    ⟨h.intervalIntegrable t i, ?_⟩⟩, fun ⟨hc, hsa, hi⟩ ↦ ⟨hc, hsa, fun t i ↦ (hi t i).1,
      fun t i ↦ ?_⟩⟩)
  · simpa [dysonDrift_apply] using h.eq_integral t i
  · simpa [dysonDrift_apply] using (hi t i).2

namespace IsDysonSolution

variable {β : ℝ} {n : ℕ} {x y : Fin n → ℝ} {P : Measure Ω}
  {B : Fin n → ℝ≥0 → Ω → ℝ} {X Y : ℝ≥0 → Ω → Fin n → ℝ}

/-- **Almost-sure pathwise uniqueness for `IsDysonSolution`.** Any two solutions started at `x` and
driven by the same process `B` agree at all times almost surely, for every `β : ℝ` and `n : ℕ`
without distributional or independence assumptions on `B`. -/
theorem ae_eq (hX : IsDysonSolution β n x P B X) (hY : IsDysonSolution β n x P B Y) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  filter_upwards [hX, hY] with ω hωX hωY
  exact congrFun (hωX.eq hωY)

/-- Almost-sure `ℓ²` stability in the initial configuration `x, y` for solutions driven by the same
process `B`. -/
theorem ae_sum_sq_sub_le (hX : IsDysonSolution β n x P B X) (hY : IsDysonSolution β n y P B Y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∑ i : Fin n, (X t ω i - Y t ω i) ^ 2 ≤ ∑ i : Fin n, (x i - y i) ^ 2 := by
  filter_upwards [hX, hY] with ω hωX hωY t
  exact hωX.sum_sq_sub_le_start hωY t

/-- Almost-sure center-of-mass identity for `IsDysonSolution`. -/
theorem ae_sum_eq (hX : IsDysonSolution β n x P B X) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ∑ i : Fin n, X t ω i =
        (∑ i : Fin n, x i) + Real.sqrt (2 / (β * n)) * ∑ i : Fin n, B i t ω := by
  filter_upwards [hX] with ω hω t
  rw [hω.sum_eq t, Finset.mul_sum]

/-- When each coordinate of `B` is pre-Brownian, `B i 0 = 0` almost surely and hence `X 0 = x`
almost surely. -/
theorem ae_eval_zero_of_isPreBrownianReal (hX : IsDysonSolution β n x P B X)
    (hB : ∀ i, IsPreBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, X 0 ω = x := by
  have hB0 : ∀ᵐ ω ∂P, ∀ i : Fin n, B i 0 ω = 0 :=
    ae_all_iff.2 fun i ↦ (hB i).eval_zero_ae_eq_zero
  filter_upwards [hX, hB0] with ω hω hω0
  refine hω.eval_zero_of_eq_zero ?_
  ext i
  simp [hω0 i]

/-- **Necessity of an ordered initial state.** Under a nonzero measure `P`, if a Dyson solution
exists for pre-Brownian driving coordinates `B`, then the initial configuration `x` must be
antitone. -/
theorem antitone_of_isPreBrownianReal [NeZero P] (hX : IsDysonSolution β n x P B X)
    (hB : ∀ i, IsPreBrownianReal (B i) P) : Antitone x := by
  have hae : ∀ᵐ _ ∂P, Antitone x := by
    filter_upwards [hX, hX.ae_eval_zero_of_isPreBrownianReal hB] with _ hω hω0
    exact hω0 ▸ hω.antitone_zero
  rcases hae.exists with ⟨_, h⟩
  exact h

end IsDysonSolution

end MeasureLevel

/-! ### Globally Lipschitz chamber-truncated Dyson trajectories -/

section Truncated

private noncomputable def shiftedTruncatedField (ε : ℝ) (n : ℕ) (w : ℝ≥0 → Fin n → ℝ)
    (s : ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  truncatedDysonDrift ε n (z + w s.toNNReal)

private theorem continuous_uncurry_shiftedTruncatedField {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    Continuous (Function.uncurry (shiftedTruncatedField ε n w)) := by
  unfold Function.uncurry shiftedTruncatedField
  exact (continuous_truncatedDysonDrift hε n).comp
    (continuous_snd.add (hw.comp (continuous_real_toNNReal.comp continuous_fst)))

private theorem lipschitzWith_shiftedTruncatedField {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (w : ℝ≥0 → Fin n → ℝ) (s : ℝ) :
    LipschitzWith ⟨2 * ε⁻¹ ^ 2, by positivity⟩ (shiftedTruncatedField ε n w s) :=
  LipschitzWith.of_dist_le_mul fun y z ↦ by
    simpa [shiftedTruncatedField, dist_add_right] using
      (lipschitzWith_truncatedDysonDrift hε n).dist_le_mul (y + w s.toNNReal) (z + w s.toNNReal)

private noncomputable def shiftedTruncatedCurve {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) : ℝ → Fin n → ℝ :=
  ODE.nonautonomousSolution (shiftedTruncatedField ε n w)
    (continuous_uncurry_shiftedTruncatedField hε n hw)
    (lipschitzWith_shiftedTruncatedField hε n w) 0 x

@[simp]
private theorem shiftedTruncatedCurve_zero {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) :
    shiftedTruncatedCurve hε n x w hw 0 = x :=
  ODE.nonautonomousSolution_self _ _ _ 0 x

/-- **Global `ε`-truncated Dyson trajectory** started at `x` and driven by a continuous path `w`.
Defined on `[0, ∞)` by solving `Z' s = truncatedDysonDrift ε n (Z s + w s.toNNReal)` globally via
`ODE.nonautonomousSolution` and setting `X_ε t = Z t + w t`. -/
noncomputable def truncatedDysonPath {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) (t : ℝ≥0) : Fin n → ℝ :=
  shiftedTruncatedCurve hε n x w hw t + w t

/-- `truncatedDysonPath` is continuous on `[0, ∞)`. -/
theorem continuous_truncatedDysonPath {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) :
    Continuous (truncatedDysonPath hε n x w hw) :=
  ((ODE.continuous_nonautonomousSolution_apply _ _ _ 0 x).comp NNReal.continuous_coe).add hw

/-- Value of `truncatedDysonPath` at time `0`. -/
@[simp]
theorem truncatedDysonPath_zero {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) :
    truncatedDysonPath hε n x w hw 0 = x + w 0 := by
  simp [truncatedDysonPath]

/-- **Integral equation of `truncatedDysonPath`.** Every coordinate satisfies the `ε`-truncated
Dyson integral equation driven by `w`. -/
theorem truncatedDysonPath_eq_integral {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) (t : ℝ≥0) (i : Fin n) :
    truncatedDysonPath hε n x w hw t i =
      x i + w t i +
        ∫ s in (0 : ℝ)..t,
          truncatedDysonDrift ε n (truncatedDysonPath hε n x w hw s.toNNReal) i := by
  have hZ := ODE.nonautonomousSolution_eq_integral (shiftedTruncatedField ε n w)
    (continuous_uncurry_shiftedTruncatedField hε n hw)
    (lipschitzWith_shiftedTruncatedField hε n w) 0 x t
  have hcont : Continuous fun s : ℝ ↦
      shiftedTruncatedField ε n w s (shiftedTruncatedCurve hε n x w hw s) :=
    (continuous_uncurry_shiftedTruncatedField hε n hw).comp
      (continuous_id.prodMk (ODE.continuous_nonautonomousSolution_apply _ _ _ 0 x))
  have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).intervalIntegral_comp_comm
    (hcont.intervalIntegrable (μ := volume) 0 t)
  simp only [ContinuousLinearMap.proj_apply] at hproj
  have hZ_i : shiftedTruncatedCurve hε n x w hw t i =
      x i + (∫ s in (0 : ℝ)..t,
        shiftedTruncatedField ε n w s (shiftedTruncatedCurve hε n x w hw s)) i := by
    simpa only [shiftedTruncatedCurve, Pi.add_apply] using congrFun hZ i
  have hcongr : ∫ s in (0 : ℝ)..t,
        shiftedTruncatedField ε n w s (shiftedTruncatedCurve hε n x w hw s) i =
      ∫ s in (0 : ℝ)..t,
        truncatedDysonDrift ε n (truncatedDysonPath hε n x w hw s.toNNReal) i := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hs_nn : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs.1
    simp only [shiftedTruncatedField, truncatedDysonPath]
    rw [hs_nn]
  rw [truncatedDysonPath, Pi.add_apply, hZ_i, ← hproj, hcongr]
  ring

/-- Center-of-mass conservation for `truncatedDysonPath`. -/
theorem sum_truncatedDysonPath {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) (t : ℝ≥0) :
    ∑ i : Fin n, truncatedDysonPath hε n x w hw t i =
      (∑ i : Fin n, x i) + ∑ i : Fin n, w t i := by
  have hint : ∀ i : Fin n, IntervalIntegrable
      (fun s : ℝ ↦ truncatedDysonDrift ε n (truncatedDysonPath hε n x w hw s.toNNReal) i)
      volume 0 t := fun i ↦
    (((continuous_apply i).comp
      ((continuous_truncatedDysonDrift hε n).comp
        ((continuous_truncatedDysonPath hε n x w hw).comp
          continuous_real_toNNReal))).intervalIntegrable (μ := volume) 0 t)
  simp_rw [truncatedDysonPath_eq_integral hε n x w hw t, Finset.sum_add_distrib]
  rw [← intervalIntegral.integral_finsetSum fun i _ ↦ hint i]
  simp [sum_truncatedDysonDrift_eq_zero]

/-- **Global `ℓ²` contraction for `truncatedDysonPath`.** Holds for arbitrary initial configurations
`x, y : Fin n → ℝ` without any chamber restriction. -/
theorem sum_sq_truncatedDysonPath_sub_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x y : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) {s t : ℝ≥0} (hst : s ≤ t) :
    ∑ i : Fin n,
        (truncatedDysonPath hε n x w hw t i - truncatedDysonPath hε n y w hw t i) ^ 2 ≤
      ∑ i : Fin n,
        (truncatedDysonPath hε n x w hw s i - truncatedDysonPath hε n y w hw s i) ^ 2 := by
  let Zx := shiftedTruncatedCurve hε n x w hw
  let Zy := shiftedTruncatedCurve hε n y w hw
  let φ : ℝ → ℝ := fun r ↦ ∑ i : Fin n, (Zx r i - Zy r i) ^ 2
  have hZx : ∀ r, HasDerivAt Zx (shiftedTruncatedField ε n w r (Zx r)) r :=
    ODE.hasDerivAt_nonautonomousSolution _ _ _ 0 x
  have hZy : ∀ r, HasDerivAt Zy (shiftedTruncatedField ε n w r (Zy r)) r :=
    ODE.hasDerivAt_nonautonomousSolution _ _ _ 0 y
  have hφ_deriv : ∀ r : ℝ, HasDerivAt φ
      (2 * ∑ i : Fin n,
        (shiftedTruncatedField ε n w r (Zx r) i - shiftedTruncatedField ε n w r (Zy r) i) *
          (Zx r i - Zy r i)) r := fun r ↦ by
    have hcoord : ∀ i : Fin n, HasDerivAt (fun u ↦ (Zx u i - Zy u i) ^ 2)
        (2 * ((shiftedTruncatedField ε n w r (Zx r) i - shiftedTruncatedField ε n w r (Zy r) i) *
          (Zx r i - Zy r i))) r := fun i ↦ by
      have hdiff : HasDerivAt (fun u ↦ Zx u i - Zy u i)
          (shiftedTruncatedField ε n w r (Zx r) i - shiftedTruncatedField ε n w r (Zy r) i) r :=
        (hasDerivAt_pi.1 (hZx r) i).sub (hasDerivAt_pi.1 (hZy r) i)
      simpa only [sq] using (hdiff.fun_mul hdiff).congr_deriv (by ring)
    dsimp only [φ]
    simpa only [Finset.mul_sum] using HasDerivAt.fun_sum fun i _ ↦ hcoord i
  have hφ_nonpos : ∀ r : ℝ,
      2 * ∑ i : Fin n,
        (shiftedTruncatedField ε n w r (Zx r) i - shiftedTruncatedField ε n w r (Zy r) i) *
          (Zx r i - Zy r i) ≤ 0 := fun r ↦ by
    refine mul_nonpos_of_nonneg_of_nonpos zero_le_two ?_
    have hadd : ∀ i : Fin n, Zx r i - Zy r i =
        (Zx r + w r.toNNReal) i - (Zy r + w r.toNNReal) i := fun i ↦ by simp
    simp_rw [shiftedTruncatedField, hadd]
    exact sum_truncatedDysonDrift_sub_mul_sub_nonpos hε n _ _
  have hanti : Antitone φ :=
    antitone_of_deriv_nonpos (fun r ↦ (hφ_deriv r).differentiableAt)
      (fun r ↦ (hφ_deriv r).deriv.symm ▸ hφ_nonpos r)
  have hcancel : ∀ u : ℝ≥0,
      (∑ i : Fin n,
        (truncatedDysonPath hε n x w hw u i - truncatedDysonPath hε n y w hw u i) ^ 2) = φ u :=
    fun u ↦ Finset.sum_congr rfl fun i _ ↦ by
      dsimp only [truncatedDysonPath, Zx, Zy, φ, Pi.add_apply]; ring
  rw [hcancel t, hcancel s]
  exact hanti hst

/-- **Consistency of chamber truncations before exit.** If `truncatedDysonPath hε₁ n x w hw` stays
inside `{z | ∀ i < j, max ε₁ ε₂ ≤ z i - z j}` on `[0, T]`, then the `ε₁`- and `ε₂`-truncated paths
coincide on `[0, T]`. -/
theorem truncatedDysonPath_eq_of_le_gap {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) {n : ℕ}
    {x : Fin n → ℝ} {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) {T : ℝ≥0}
    (hgap : ∀ s ≤ T, ∀ i j : Fin n, i < j →
      max ε₁ ε₂ ≤ truncatedDysonPath hε₁ n x w hw s i - truncatedDysonPath hε₁ n x w hw s j)
    {t : ℝ≥0} (ht : t ≤ T) :
    truncatedDysonPath hε₁ n x w hw t = truncatedDysonPath hε₂ n x w hw t := by
  have hZ₁_deriv2 : ∀ r ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (shiftedTruncatedCurve hε₁ n x w hw)
        (shiftedTruncatedField ε₂ n w r (shiftedTruncatedCurve hε₁ n x w hw r)) (Ici r) r := by
    intro r hr
    have hr_nn_le : r.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hr.2.le
    have hr_coe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr.1
    have hX₁_eq : shiftedTruncatedCurve hε₁ n x w hw r + w r.toNNReal =
        truncatedDysonPath hε₁ n x w hw r.toNNReal := by
      rw [truncatedDysonPath, hr_coe]
    have hdrift : shiftedTruncatedField ε₁ n w r (shiftedTruncatedCurve hε₁ n x w hw r) =
        shiftedTruncatedField ε₂ n w r (shiftedTruncatedCurve hε₁ n x w hw r) := by
      simp only [shiftedTruncatedField, hX₁_eq]
      rw [truncatedDysonDrift_eq_dysonDrift fun i j hij ↦
          (le_max_left _ _).trans (hgap r.toNNReal hr_nn_le i j hij),
        truncatedDysonDrift_eq_dysonDrift fun i j hij ↦
          (le_max_right _ _).trans (hgap r.toNNReal hr_nn_le i j hij)]
    rw [← hdrift]
    exact (ODE.hasDerivAt_nonautonomousSolution _ _ _ 0 x r).hasDerivWithinAt
  have heq : EqOn (shiftedTruncatedCurve hε₁ n x w hw) (shiftedTruncatedCurve hε₂ n x w hw)
      (Icc (0 : ℝ) T) :=
    ODE_solution_unique_of_mem_Icc_right (s := fun _ ↦ univ)
      (fun r _ ↦ (lipschitzWith_shiftedTruncatedField hε₂ n w r).lipschitzOnWith)
      (ODE.continuous_nonautonomousSolution_apply _ _ _ 0 x).continuousOn
      hZ₁_deriv2 (fun _ _ ↦ trivial)
      (ODE.continuous_nonautonomousSolution_apply _ _ _ 0 x).continuousOn
      (fun r _ ↦ (ODE.hasDerivAt_nonautonomousSolution _ _ _ 0 x r).hasDerivWithinAt)
      (fun _ _ ↦ trivial) (by simp)
  rw [truncatedDysonPath, truncatedDysonPath, heq ⟨t.coe_nonneg, ht⟩]

/-- **Localization of `IsDysonPath` to `truncatedDysonPath`.** Any Dyson trajectory `X` whose
ordered gaps remain at least `ε > 0` on `[0, T]` coincides on `[0, T]` with
`truncatedDysonPath hε n x w hw`. -/
theorem IsDysonPath.eq_truncatedDysonPath_of_le_gap {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    {x : Fin n → ℝ} {w X : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (hX : IsDysonPath n x w X)
    {T : ℝ≥0} (hgap : ∀ s ≤ T, ∀ i j : Fin n, i < j → ε ≤ X s i - X s j)
    {t : ℝ≥0} (ht : t ≤ T) :
    X t = truncatedDysonPath hε n x w hw t := by
  let g : ℝ → Fin n → ℝ := fun s ↦ truncatedDysonDrift ε n (X s.toNNReal)
  have hg_cont : Continuous g :=
    (continuous_truncatedDysonDrift hε n).comp (hX.continuous.comp continuous_real_toNNReal)
  let Z : ℝ → Fin n → ℝ := fun r ↦ x + ∫ s in (0 : ℝ)..r, g s
  have hZ_deriv : ∀ r : ℝ, HasDerivAt Z (g r) r := fun r ↦
    ((intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable (μ := volume) 0 r)
      (hg_cont.stronglyMeasurableAtFilter _ _) hg_cont.continuousAt).const_add x)
  have hZX : ∀ u : ℝ≥0, u ≤ T → Z u + w u = X u := fun u hu ↦ by
    ext i
    have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).intervalIntegral_comp_comm
      (hg_cont.intervalIntegrable (μ := volume) 0 u)
    simp only [ContinuousLinearMap.proj_apply] at hproj
    have hcongr : ∫ s in (0 : ℝ)..u, g s i =
        ∫ s in (0 : ℝ)..u, dysonDrift n (X s.toNNReal) i := by
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [uIcc_of_le u.coe_nonneg] at hs
      have hs_le : s.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe.2 hs.2).trans hu
      exact congrFun (truncatedDysonDrift_eq_dysonDrift (hgap s.toNNReal hs_le)) i
    dsimp only [Z, Pi.add_apply]
    rw [← hproj, hcongr, hX.eq_integral u i]
    ring
  have hZ_ode : ∀ r ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt Z (shiftedTruncatedField ε n w r (Z r)) (Ici r) r := by
    intro r hr
    have hr_le : r.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hr.2.le
    have hr_coe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr.1
    have hZr : Z r + w r.toNNReal = X r.toNNReal := by
      simpa only [hr_coe] using hZX r.toNNReal hr_le
    have hdrift : g r = shiftedTruncatedField ε n w r (Z r) := by
      dsimp only [g, shiftedTruncatedField]
      rw [hZr]
    rw [← hdrift]
    exact (hZ_deriv r).hasDerivWithinAt
  have heq : EqOn Z (shiftedTruncatedCurve hε n x w hw) (Icc (0 : ℝ) T) :=
    ODE_solution_unique_of_mem_Icc_right (s := fun _ ↦ univ)
      (fun r _ ↦ (lipschitzWith_shiftedTruncatedField hε n w r).lipschitzOnWith)
      (Differentiable.continuous fun r ↦ (hZ_deriv r).differentiableAt).continuousOn
      hZ_ode (fun _ _ ↦ trivial)
      (ODE.continuous_nonautonomousSolution_apply _ _ _ 0 x).continuousOn
      (fun r _ ↦ (ODE.hasDerivAt_nonautonomousSolution _ _ _ 0 x r).hasDerivWithinAt)
      (fun _ _ ↦ trivial) (by dsimp only [Z]; simp)
  rw [← hZX t ht, truncatedDysonPath, heq ⟨t.coe_nonneg, ht⟩]

/-- **Constructing a Dyson trajectory from non-colliding chamber truncations.** If for every
horizon `T : ℝ≥0` there exists `ε > 0` such that `X` agrees on `[0, T]` with
`truncatedDysonPath hε n x w hw` and keeps ordered gaps at least `ε` on `[0, T]`, then `X` is a
global `IsDysonPath`. -/
theorem isDysonPath_of_forall_exists_truncatedDysonPath {n : ℕ} {x : Fin n → ℝ}
    {w X : ℝ≥0 → Fin n → ℝ} (hw : Continuous w)
    (hloc : ∀ T : ℝ≥0, ∃ (ε : ℝ) (hε : 0 < ε),
      (∀ t ≤ T, X t = truncatedDysonPath hε n x w hw t) ∧
      ∀ t ≤ T, ∀ i j : Fin n, i < j → ε ≤ X t i - X t j) :
    IsDysonPath n x w X := by
  have hcont_X : Continuous X :=
    continuous_iff_continuousAt.2 fun t ↦ by
      obtain ⟨ε, hε, hEq, _⟩ := hloc (t + 1)
      refine (continuous_truncatedDysonPath hε n x w hw).continuousAt.congr ?_
      filter_upwards [Iio_mem_nhds (lt_add_one t)] with s hs
      exact (hEq s hs.le).symm
  refine
    { continuous := hcont_X
      strictAnti := fun t _ i j hij ↦ ?_
      intervalIntegrable := fun t i ↦ ?_
      eq_integral := fun t i ↦ ?_ }
  · obtain ⟨ε, hε, _, hgap⟩ := hloc t
    linarith [hgap t le_rfl i j hij]
  · obtain ⟨_, _, _, hgap⟩ := hloc t
    refine ContinuousOn.intervalIntegrable (μ := volume) ?_
    rw [uIcc_of_le t.coe_nonneg]
    refine continuousOn_finsetSum _ fun j hj ↦ ?_
    have hsub_cont : Continuous fun s : ℝ ↦ X s.toNNReal i - X s.toNNReal j :=
      (((continuous_apply i).comp hcont_X).comp continuous_real_toNNReal).sub
        (((continuous_apply j).comp hcont_X).comp continuous_real_toNNReal)
    refine hsub_cont.continuousOn.inv₀ fun s hs ↦ ?_
    have hs_le : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj).symm with hij | hji
    · linarith [hgap s.toNNReal hs_le i j hij]
    · linarith [hgap s.toNNReal hs_le j i hji]
  · obtain ⟨ε, hε, hEq, hgap⟩ := hloc t
    rw [hEq t le_rfl, truncatedDysonPath_eq_integral hε n x w hw t i]
    congr 1
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hs_le : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
    rw [← hEq s.toNNReal hs_le,
      truncatedDysonDrift_eq_dysonDrift (hgap s.toNNReal hs_le)]

end Truncated

/-! ### Concrete witnesses and explicit low-dimensional solutions -/

section Witnesses

/-- At `n = 0`, the unique empty path is a Dyson trajectory for every forcing path `w`. -/
theorem isDysonPath_zero (x : Fin 0 → ℝ) (w : ℝ≥0 → Fin 0 → ℝ) :
    IsDysonPath 0 x w (fun _ ↦ Fin.elim0) where
  continuous := continuous_pi fun i ↦ Fin.elim0 i
  strictAnti _ _ i := Fin.elim0 i
  intervalIntegrable _ i := Fin.elim0 i
  eq_integral _ i := Fin.elim0 i

/-- At `n = 1`, there is no pairwise repulsion, so `t ↦ x + w t` is a Dyson trajectory for every
continuous forcing path `w`. -/
theorem isDysonPath_one (x : Fin 1 → ℝ) {w : ℝ≥0 → Fin 1 → ℝ} (hw : Continuous w) :
    IsDysonPath 1 x w (fun t ↦ x + w t) where
  continuous := continuous_const.add hw
  strictAnti _ _ i j hij := absurd (Subsingleton.elim i j) hij.ne
  intervalIntegrable t i := by
    have hempty : Finset.univ.erase i = ∅ := by
      ext j
      simp [Subsingleton.elim j i]
    rw [hempty]
    simp
  eq_integral t i := by
    simp [dysonDrift_one]

/-- **Complete existence and uniqueness of `IsDysonSolution` for `n ≤ 1`.** For `n = 0` or `n = 1`,
every Brownian coordinate family `B` drives an almost-surely unique Dyson solution for any
parameter `β : ℝ` and initial configuration `x : Fin n → ℝ`. -/
theorem dysonSystem_exists_unique_of_le_one {Ω : Type*} [MeasurableSpace Ω] (β : ℝ) {n : ℕ}
    (hn : n ≤ 1) (x : Fin n → ℝ) (P : Measure Ω) (B : Fin n → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsBrownianReal (B i) P) :
    (∃ X : ℝ≥0 → Ω → Fin n → ℝ, IsDysonSolution β n x P B X) ∧
      ∀ X Y : ℝ≥0 → Ω → Fin n → ℝ, IsDysonSolution β n x P B X → IsDysonSolution β n x P B Y →
        ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  refine ⟨?_, fun _ _ hX hY ↦ hX.ae_eq hY⟩
  interval_cases n
  · refine ⟨fun _ _ ↦ Fin.elim0, .of_forall fun _ ↦ isDysonPath_zero x _⟩
  · refine ⟨fun t ω ↦ x + fun i ↦ Real.sqrt (2 / (β * (1 : ℕ))) * B i t ω, ?_⟩
    filter_upwards [(hB 0).cont] with ω hω
    have hw : Continuous (fun t (i : Fin 1) ↦ Real.sqrt (2 / (β * (1 : ℕ))) * B i t ω) := by
      refine continuous_pi fun i ↦ ?_
      rw [Subsingleton.elim i 0]
      exact continuous_const.mul hω
    exact isDysonPath_one x hw

/-- **Explicit two-particle zero-noise Dyson trajectory** from an ordered initial configuration
`x : Fin 2 → ℝ`:
`X t = ![(x 0 + x 1 + √((x 0 - x 1)^2 + 2 t)) / 2, (x 0 + x 1 - √((x 0 - x 1)^2 + 2 t)) / 2]`.
When `x 0 = x 1`, the two particles separate instantaneously as `±√(t / 2)` with genuinely singular
integrable drift `(2 t)⁻¹/²` at `t = 0`. -/
noncomputable def twoParticleDysonPath (x : Fin 2 → ℝ) (t : ℝ≥0) (i : Fin 2) : ℝ :=
  if i = 0 then (x 0 + x 1 + Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ))) / 2
  else (x 0 + x 1 - Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ))) / 2

/-- First coordinate of `twoParticleDysonPath`. -/
@[simp]
theorem twoParticleDysonPath_zero_coord (x : Fin 2 → ℝ) (t : ℝ≥0) :
    twoParticleDysonPath x t 0 =
      (x 0 + x 1 + Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ))) / 2 := by
  simp [twoParticleDysonPath]

/-- Second coordinate of `twoParticleDysonPath`. -/
@[simp]
theorem twoParticleDysonPath_one_coord (x : Fin 2 → ℝ) (t : ℝ≥0) :
    twoParticleDysonPath x t 1 =
      (x 0 + x 1 - Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ))) / 2 := by
  simp [twoParticleDysonPath]

/-- Gap between the two coordinates of `twoParticleDysonPath`. -/
theorem twoParticleDysonPath_sub (x : Fin 2 → ℝ) (t : ℝ≥0) :
    twoParticleDysonPath x t 0 - twoParticleDysonPath x t 1 =
      Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ)) := by
  rw [twoParticleDysonPath_zero_coord, twoParticleDysonPath_one_coord]
  ring

/-- `twoParticleDysonPath x` is continuous on `[0, ∞)` for every initial configuration `x`. -/
theorem continuous_twoParticleDysonPath (x : Fin 2 → ℝ) :
    Continuous (twoParticleDysonPath x) := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i
  · simp only [Fin.zero_eta, twoParticleDysonPath_zero_coord]
    fun_prop
  · simp only [Fin.mk_one, twoParticleDysonPath_one_coord]
    fun_prop

/-- `twoParticleDysonPath x t` is strictly decreasing at every strictly positive time `t > 0`. -/
theorem strictAnti_twoParticleDysonPath (x : Fin 2 → ℝ) {t : ℝ≥0} (ht : 0 < t) :
    StrictAnti (twoParticleDysonPath x t) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij.ne
  · simp only [Fin.zero_eta, Fin.mk_one]
    have hpos : 0 < Real.sqrt ((x 0 - x 1) ^ 2 + 2 * (t : ℝ)) :=
      Real.sqrt_pos.2 (by positivity)
    linarith [twoParticleDysonPath_sub x t]
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
  have hu_pos : ∀ s : ℝ, 0 < s → 0 < u s := fun s hs ↦ by dsimp [u]; positivity
  have hF_deriv : ∀ s : ℝ, 0 < s → HasDerivAt F ((2 : ℝ)⁻¹ * (Real.sqrt (u s))⁻¹) s := fun s hs ↦ by
    have hu_d : HasDerivAt u 2 s := by
      simpa [u] using ((hasDerivAt_id s).const_mul (2 : ℝ)).const_add ((x 0 - x 1) ^ 2)
    have hne : Real.sqrt (u s) ≠ 0 := (Real.sqrt_pos.2 (hu_pos s hs)).ne'
    exact ((hu_d.sqrt (hu_pos s hs).ne').div_const 2).congr_deriv (by field_simp [hne])
  have hint_half : IntervalIntegrable (fun s : ℝ ↦ (2 : ℝ)⁻¹ * (Real.sqrt (u s))⁻¹) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).2
      (_root_.intervalIntegral.integrableOn_deriv_of_nonneg hF_cont.continuousOn
        (fun s hs ↦ hF_deriv s hs.1) (fun _ _ ↦ by positivity))
  refine ⟨(hint_half.const_mul 2).congr fun s _ ↦ by dsimp only [u]; ring, ?_⟩
  rw [TauCeti.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg t.coe_nonneg
    hF_cont.continuousOn (fun s hs ↦ hF_deriv s hs.1) (fun _ _ ↦ by positivity)]
  dsimp only [F, u]
  simp only [mul_zero, add_zero, Real.sqrt_sq hx01]
  ring

/-- **Non-vacuous singular-drift witness for `IsDysonPath`.** For every antitone initial state
`x : Fin 2 → ℝ` (including coincident `x 0 = x 1`), `twoParticleDysonPath x` is the unique
zero-noise Dyson trajectory started at `x`. -/
theorem isDysonPath_twoParticleDysonPath {x : Fin 2 → ℝ} (hx : Antitone x) :
    IsDysonPath 2 x 0 (twoParticleDysonPath x) := by
  have herase0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have herase1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  refine
    { continuous := continuous_twoParticleDysonPath x
      strictAnti := fun _ ht ↦ strictAnti_twoParticleDysonPath x ht
      intervalIntegrable := fun t i ↦ ?_
      eq_integral := fun t i ↦ ?_ }
  · have hint := (intervalIntegrable_and_integral_twoParticleGap hx t).1
    fin_cases i
    · simp only [Fin.zero_eta, herase0, Finset.sum_singleton]
      refine hint.congr fun s hs ↦ ?_
      rw [uIoc_of_le t.coe_nonneg] at hs
      rw [twoParticleDysonPath_sub, Real.coe_toNNReal s hs.1.le]
    · simp only [Fin.mk_one, herase1, Finset.sum_singleton]
      refine hint.neg.congr fun s hs ↦ ?_
      rw [uIoc_of_le t.coe_nonneg] at hs
      simp only [Pi.neg_apply]
      rw [← neg_sub (twoParticleDysonPath x s.toNNReal 0), inv_neg,
        twoParticleDysonPath_sub, Real.coe_toNNReal s hs.1.le]
  · have hval := (intervalIntegrable_and_integral_twoParticleGap hx t).2
    fin_cases i
    · simp only [Fin.zero_eta, Pi.zero_apply, add_zero, dysonDrift_apply, Nat.cast_ofNat,
        herase0, Finset.sum_singleton]
      have hcongr : ∫ s in (0 : ℝ)..t,
            (2 : ℝ)⁻¹ * (twoParticleDysonPath x s.toNNReal 0 -
              twoParticleDysonPath x s.toNNReal 1)⁻¹ =
          ∫ s in (0 : ℝ)..t, (2 : ℝ)⁻¹ * (Real.sqrt ((x 0 - x 1) ^ 2 + 2 * s))⁻¹ := by
        refine intervalIntegral.integral_congr fun s hs ↦ ?_
        rw [uIcc_of_le t.coe_nonneg] at hs
        rw [twoParticleDysonPath_sub, Real.coe_toNNReal s hs.1]
      rw [hcongr, hval, twoParticleDysonPath_zero_coord]
      ring
    · simp only [Fin.mk_one, Pi.zero_apply, add_zero, dysonDrift_apply, Nat.cast_ofNat,
        herase1, Finset.sum_singleton]
      have hcongr : ∫ s in (0 : ℝ)..t,
            (2 : ℝ)⁻¹ * (twoParticleDysonPath x s.toNNReal 1 -
              twoParticleDysonPath x s.toNNReal 0)⁻¹ =
          -(∫ s in (0 : ℝ)..t, (2 : ℝ)⁻¹ * (Real.sqrt ((x 0 - x 1) ^ 2 + 2 * s))⁻¹) := by
        rw [← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_congr fun s hs ↦ ?_
        rw [uIcc_of_le t.coe_nonneg] at hs
        rw [← neg_sub (twoParticleDysonPath x s.toNNReal 0), inv_neg,
          twoParticleDysonPath_sub, Real.coe_toNNReal s hs.1, mul_neg]
      rw [hcongr, hval, twoParticleDysonPath_one_coord]
      ring

/-- Non-vacuous measure-level witness for `IsDysonSolution` at `n = 2` from any `Antitone x`
(including coincident `x 0 = x 1`) with zero noise. -/
theorem isDysonSolution_twoParticleDysonPath {Ω : Type*} [MeasurableSpace Ω] (β : ℝ)
    {x : Fin 2 → ℝ} (hx : Antitone x) (P : Measure Ω) :
    IsDysonSolution β 2 x P 0 (fun t _ ↦ twoParticleDysonPath x t) := by
  refine .of_forall fun _ ↦ ?_
  simpa [Pi.zero_def] using isDysonPath_twoParticleDysonPath hx

end Witnesses

end TauCeti.Probability
