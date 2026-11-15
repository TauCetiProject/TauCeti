/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Probability.DysonBrownianMotion.Drift
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Pathwise solutions, contraction, and uniqueness for the Dyson system

Because the noise in the Dyson system is additive, a sample path `X : ℝ≥0 → Fin n → ℝ` driven by a
path `w : ℝ≥0 → Fin n → ℝ` from initial configuration `x : Fin n → ℝ` can be formulated directly
via the integral equation
`X t i = x i + w t i + ∫ s in (0 : ℝ)..t, dysonDrift (X s.toNNReal) i`,
together with continuity of `X`, strict decreasing order `StrictAnti (X t)` at all positive times
`t > 0`, and local integrability of the drift on `[0, t]`.

This file introduces both the deterministic pathwise predicate `IsPathwiseDysonSolution` and the
measure-theoretic solution predicate `IsDysonSolution` for Brownian-scaled noise
`√(2 / (β * n)) * B i t ω`, and develops their deterministic consequences:

* **Chamber closure, trace identity, and time shifts:** every solution lies in the closed chamber
  `Antitone (X t)` at all times `t ≥ 0` (forcing `Antitone x` whenever `w 0 = 0`), satisfies
  `∑ i, X t i = ∑ i, x i + ∑ i, w t i`, forces `Continuous w`, and is invariant under time shifts
  `t ↦ t₀ + t`.
* **Uniform `L¹` control of individual singular reciprocals:** although `IsPathwiseDysonSolution`
  only assumes integrability of the signed sum `∑_{j ≠ i} (X_i - X_j)⁻¹`, every individual pairwise
  reciprocal `(X_i - X_j)⁻¹` (`i ≠ j`) is interval integrable on `0..t`, with a quantitative `L¹`
  staircase bound on `n⁻¹ ∑_{i < j} ∫₀ᵗ (X_i - X_j)⁻¹`.
* **Pathwise `ℓ²`-dissipation, contraction, and uniqueness (AGZ Proposition 4.3.5):** for any two
  solutions `X` and `Y` driven by the same path `w`, the squared Euclidean distance
  `t ↦ ∑ i, (X t i - Y t i) ^ 2` is antitone on `ℝ≥0`, hence bounded by `∑ i, (x i - y i) ^ 2`. In
  particular, `IsPathwiseDysonSolution.eq_of_init_eq` gives pathwise uniqueness and
  `IsDysonSolution.ae_eq` gives almost-sure uniqueness with no adaptedness or Brownian hypotheses.
* **Explicit witnesses:** trivial existence for `n ≤ 1`, and the explicit `n = 2` square-root
  repulsion family `![a + 2⁻¹ * √(r₀² + 2t), a - 2⁻¹ * √(r₀² + 2t)]` for all `r₀ ≥ 0`, including
  coincident initial data `r₀ = 0` where the singular drift `(2√(2s))⁻¹` is genuinely nonzero.

## Main definitions

* `TauCeti.Probability.IsPathwiseDysonSolution`: deterministic pathwise solution of the Dyson
  integral equation in the open decreasing chamber at positive times.
* `TauCeti.Probability.IsDysonSolution`: almost-sure Dyson solution driven by `B` with parameter
  `β`.

## Main results

* `TauCeti.Probability.IsPathwiseDysonSolution.intervalIntegrable_inv_sub`: local integrability of
  each individual pairwise reciprocal `(X_i - X_j)⁻¹` (`i ≠ j`).
* `TauCeti.Probability.IsPathwiseDysonSolution.antitone_sum_sq_sub` and
  `TauCeti.Probability.IsPathwiseDysonSolution.sum_sq_sub_le`: `ℓ²`-contraction in initial data.
* `TauCeti.Probability.IsPathwiseDysonSolution.eq_of_init_eq` and
  `TauCeti.Probability.IsDysonSolution.ae_eq`: pathwise and almost-sure uniqueness.
* `TauCeti.Probability.isPathwiseDysonSolution_fin_two_sqrt`: explicit `n = 2` non-colliding
  solution, including coincident initial position `r₀ = 0`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.1, Lemma 4.3.3 and Proposition 4.3.5.
-/

public section

noncomputable section

open Finset Filter MeasureTheory Set
open scoped NNReal Topology Interval

namespace TauCeti.Probability

section Pathwise

variable {n : ℕ}

/-- A deterministic continuous path `X : ℝ≥0 → Fin n → ℝ` solving the Dyson integral equation from
initial configuration `x` with additive driving path `w`, lying in the open decreasing chamber
`{y | StrictAnti y}` at all strictly positive times. -/
structure IsPathwiseDysonSolution (x : Fin n → ℝ) (w X : ℝ≥0 → Fin n → ℝ) : Prop where
  continuous_path : Continuous X
  strictAnti : ∀ ⦃t : ℝ≥0⦄, 0 < t → StrictAnti (X t)
  intervalIntegrable_sum_inv_sub : ∀ (t : ℝ≥0) (i : Fin n),
    IntervalIntegrable
      (fun s : ℝ ↦ ∑ j ∈ univ.erase i, (X s.toNNReal i - X s.toNNReal j)⁻¹) volume 0 t
  eq_add_integral : ∀ (t : ℝ≥0) (i : Fin n),
    X t i = x i + w t i + ∫ s in (0 : ℝ)..t, dysonDrift (X s.toNNReal) i

namespace IsPathwiseDysonSolution

variable {x y : Fin n → ℝ} {w X Y : ℝ≥0 → Fin n → ℝ}

/-- Each coordinate trajectory `t ↦ X t i` of a pathwise Dyson solution is continuous. -/
theorem continuous_coord (hX : IsPathwiseDysonSolution x w X) (i : Fin n) :
    Continuous (fun t ↦ X t i) :=
  (continuous_apply i).comp hX.continuous_path

/-- Each coordinate of `s ↦ dysonDrift (X s.toNNReal)` is interval integrable on `0..t`. -/
theorem intervalIntegrable_dysonDrift (hX : IsPathwiseDysonSolution x w X) (t : ℝ≥0)
    (i : Fin n) :
    IntervalIntegrable (fun s : ℝ ↦ dysonDrift (X s.toNNReal) i) volume 0 t := by
  simp_rw [dysonDrift_apply]
  exact (hX.intervalIntegrable_sum_inv_sub t i).const_mul (n : ℝ)⁻¹

/-- Each coordinate of `s ↦ dysonDrift (X s.toNNReal)` is interval integrable on `t₁..t₂` for
`t₁ ≤ t₂`. -/
theorem intervalIntegrable_dysonDrift_Icc (hX : IsPathwiseDysonSolution x w X) {t₁ t₂ : ℝ≥0}
    (ht : t₁ ≤ t₂) (i : Fin n) :
    IntervalIntegrable (fun s : ℝ ↦ dysonDrift (X s.toNNReal) i) volume t₁ t₂ := by
  refine (hX.intervalIntegrable_dysonDrift t₂ i).mono_set ?_
  rw [uIcc_of_le (NNReal.coe_le_coe.2 ht), uIcc_of_le t₂.coe_nonneg]
  exact Icc_subset_Icc t₁.coe_nonneg le_rfl

/-- At `t = 0`, a pathwise Dyson solution satisfies `X 0 i = x i + w 0 i`. -/
theorem apply_zero (hX : IsPathwiseDysonSolution x w X) (i : Fin n) :
    X 0 i = x i + w 0 i := by
  simpa using hX.eq_add_integral 0 i

/-- When the driving path starts at `0`, a pathwise Dyson solution starts at `X 0 = x`. -/
theorem zero_eq_of_zero_eq_zero (hX : IsPathwiseDysonSolution x w X) (hw0 : w 0 = 0) :
    X 0 = x := by
  ext i
  simp [hX.apply_zero, hw0]

/-- The cumulative drift integral `t ↦ ∫ s in 0..t, dysonDrift (X s.toNNReal) i` of a pathwise
Dyson solution is continuous on `ℝ≥0`. -/
theorem continuous_integral_dysonDrift (hX : IsPathwiseDysonSolution x w X) (i : Fin n) :
    Continuous (fun t : ℝ≥0 ↦ ∫ s in (0 : ℝ)..t, dysonDrift (X s.toNNReal) i) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  set T : ℝ≥0 := t₀ + 1
  have hcont : ContinuousOn (fun u : ℝ ↦ ∫ s in (0 : ℝ)..u, dysonDrift (X s.toNNReal) i)
      (uIcc 0 (T : ℝ)) :=
    ((hX.intervalIntegrable_dysonDrift T i).absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc).continuousOn
  have hcont_nn : ContinuousOn (fun t : ℝ≥0 ↦ ∫ s in (0 : ℝ)..t, dysonDrift (X s.toNNReal) i)
      (Iic T) := by
    refine hcont.comp NNReal.continuous_coe.continuousOn fun t ht ↦ ?_
    rw [uIcc_of_le T.coe_nonneg]
    exact ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩
  refine hcont_nn.continuousAt (Iic_mem_nhds ?_)
  exact lt_add_of_pos_right t₀ zero_lt_one

/-- Any driving path `w` admitting a pathwise Dyson solution is necessarily continuous. -/
theorem continuous_driving (hX : IsPathwiseDysonSolution x w X) : Continuous w := by
  rw [continuous_pi_iff]
  intro i
  have heq : (fun t ↦ w t i) = fun t ↦
      X t i - x i - ∫ s in (0 : ℝ)..t, dysonDrift (X s.toNNReal) i := by
    ext t
    linarith [hX.eq_add_integral t i]
  rw [heq]
  exact ((hX.continuous_coord i).sub continuous_const).sub (hX.continuous_integral_dysonDrift i)

/-- Every pathwise Dyson solution lies in the closed decreasing chamber `{z | Antitone z}` at all
times `t ≥ 0` (including at `t = 0`). -/
theorem antitone (hX : IsPathwiseDysonSolution x w X) (t : ℝ≥0) : Antitone (X t) := by
  rcases eq_zero_or_pos t with rfl | ht
  · intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · let u : ℕ → ℝ≥0 := fun m ↦ ⟨((m : ℝ) + 1)⁻¹, by positivity⟩
      have hu_pos : ∀ m, 0 < u m := fun m ↦ NNReal.coe_pos.1 (inv_pos.2 (by positivity))
      have hu_tendsto : Tendsto u atTop (𝓝 0) := by
        rw [← NNReal.tendsto_coe]
        exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      exact le_of_tendsto_of_tendsto
        ((hX.continuous_coord j).continuousAt.tendsto.comp hu_tendsto)
        ((hX.continuous_coord i).continuousAt.tendsto.comp hu_tendsto)
        (Eventually.of_forall fun m ↦ (hX.strictAnti (hu_pos m) hlt).le)
  · exact (hX.strictAnti ht).antitone

/-- If `w 0 = 0`, the initial configuration `x` of any pathwise Dyson solution must be antitone. -/
theorem antitone_init (hX : IsPathwiseDysonSolution x w X) (hw0 : w 0 = 0) : Antitone x := by
  simpa only [hX.zero_eq_of_zero_eq_zero hw0] using hX.antitone 0

/-- **Center-of-mass conservation.** The coordinate sum of `X t` equals `∑ i, x i + ∑ i, w t i` at
every time `t`. -/
theorem sum_apply (hX : IsPathwiseDysonSolution x w X) (t : ℝ≥0) :
    ∑ i, X t i = ∑ i, x i + ∑ i, w t i := by
  simp_rw [hX.eq_add_integral t, sum_add_distrib]
  rw [← intervalIntegral.integral_finsetSum fun i _ ↦ hX.intervalIntegrable_dysonDrift t i]
  simp

/-- **Uniform `L¹` integrability of individual pairwise reciprocals.** Every single off-diagonal
gap reciprocal `(X s.toNNReal i - X s.toNNReal j)⁻¹` (`i ≠ j`) is interval integrable on `0..t`. -/
theorem intervalIntegrable_inv_sub (hX : IsPathwiseDysonSolution x w X) (t : ℝ≥0) {i j : Fin n}
    (hij : i ≠ j) :
    IntervalIntegrable (fun s : ℝ ↦ (X s.toNNReal i - X s.toNNReal j)⁻¹) volume 0 t := by
  suffices hlt : ∀ ⦃a b : Fin n⦄, a < b →
      IntervalIntegrable (fun s : ℝ ↦ (X s.toNNReal a - X s.toNNReal b)⁻¹) volume 0 t by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlt h
    · have hneg : (fun s : ℝ ↦ (X s.toNNReal i - X s.toNNReal j)⁻¹) =
          fun s : ℝ ↦ -(X s.toNNReal j - X s.toNNReal i)⁻¹ := by
        ext s
        rw [← neg_sub (X s.toNNReal j) (X s.toNNReal i), inv_neg]
      rw [hneg]
      exact (hlt h).neg
  intro a b hab
  have hn_pos : 0 < n := a.pos
  have hmaj_sum : IntervalIntegrable
      (fun s : ℝ ↦ ∑ k : Fin n, (k : ℝ) * dysonDrift (X s.toNNReal) k) volume 0 t :=
    (IntervalIntegrable.sum univ fun k _ ↦
      (hX.intervalIntegrable_dysonDrift t k).const_mul (k : ℝ)).congr
      fun u _ ↦ Finset.sum_apply u univ _
  have hmaj_int : IntervalIntegrable
      (fun s : ℝ ↦ (n : ℝ) * (-∑ k : Fin n, (k : ℝ) * dysonDrift (X s.toNNReal) k))
      volume 0 t :=
    hmaj_sum.neg.const_mul (n : ℝ)
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ ↦ (X s.toNNReal a - X s.toNNReal b)⁻¹) (volume.restrict (Ι 0 (t : ℝ))) := by
    have hcont : Continuous (fun s : ℝ ↦ (X s.toNNReal a - X s.toNNReal b)) :=
      ((hX.continuous_coord a).comp continuous_real_toNNReal).sub
        ((hX.continuous_coord b).comp continuous_real_toNNReal)
    exact hcont.measurable.inv.aestronglyMeasurable
  refine hmaj_int.mono_fun' hmeas ?_
  rw [Filter.EventuallyLE, uIoc_of_le t.coe_nonneg]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hs_pos : 0 < s.toNNReal := Real.toNNReal_pos.2 hs.1
  have hanti : StrictAnti (X s.toNNReal) := hX.strictAnti hs_pos
  have hpos : 0 < (X s.toNNReal a - X s.toNNReal b)⁻¹ := inv_pos.2 (sub_pos.2 (hanti hab))
  rw [Real.norm_of_nonneg hpos.le]
  have hle_sum : (X s.toNNReal a - X s.toNNReal b)⁻¹ ≤
      ∑ k : Fin n, ∑ l ∈ Ioi k, (X s.toNNReal k - X s.toNNReal l)⁻¹ := by
    have h1 : (X s.toNNReal a - X s.toNNReal b)⁻¹ ≤
        ∑ l ∈ Finset.Ioi a, (X s.toNNReal a - X s.toNNReal l)⁻¹ :=
      single_le_sum (f := fun l ↦ (X s.toNNReal a - X s.toNNReal l)⁻¹)
        (fun l hl ↦ inv_nonneg.2 (sub_nonneg.2 (hanti (Finset.mem_Ioi.1 hl)).le))
        (Finset.mem_Ioi.2 hab)
    exact h1.trans <| single_le_sum
      (f := fun k ↦ ∑ l ∈ Finset.Ioi k, (X s.toNNReal k - X s.toNNReal l)⁻¹)
      (fun k _ ↦ sum_nonneg fun l hl ↦
        inv_nonneg.2 (sub_nonneg.2 (hanti (Finset.mem_Ioi.1 hl)).le))
      (mem_univ a)
  have hstair := sum_Ioi_inv_sub_le_neg_sum_natCast_mul_dysonDrift hanti
  have hn_real : (0 : ℝ) < n := Nat.cast_pos.2 hn_pos
  have hmul := mul_le_mul_of_nonneg_left hstair hn_real.le
  rw [← mul_assoc, mul_inv_cancel₀ hn_real.ne', one_mul] at hmul
  exact hle_sum.trans hmul

/-- **Quantitative `L¹` staircase estimate on singular pairwise reciprocals.** On `[0, t]`, the
average of all upper-triangular gap integrals `n⁻¹ ∑_{i < j} ∫₀ᵗ (X_i - X_j)⁻¹` is bounded by
`∑ i, i * (x i + w t i - X t i)`. -/
theorem sum_Ioi_integral_inv_sub_le (hX : IsPathwiseDysonSolution x w X) (t : ℝ≥0) :
    (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        ∫ s in (0 : ℝ)..t, (X s.toNNReal i - X s.toNNReal j)⁻¹ ≤
      ∑ i : Fin n, (i : ℝ) * (x i + w t i - X t i) := by
  have hint_pair (i : Fin n) :
      IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ Finset.Ioi i, (X s.toNNReal i - X s.toNNReal j)⁻¹)
        volume 0 t :=
    (IntervalIntegrable.sum (Finset.Ioi i) fun j hj ↦
      hX.intervalIntegrable_inv_sub t (Finset.mem_Ioi.1 hj).ne).congr
      fun u _ ↦ Finset.sum_apply u (Finset.Ioi i) _
  have hsum_eq :
      (n : ℝ)⁻¹ * (∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        ∫ s in (0 : ℝ)..t, (X s.toNNReal i - X s.toNNReal j)⁻¹) =
      ∫ s in (0 : ℝ)..t, (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        (X s.toNNReal i - X s.toNNReal j)⁻¹ := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum fun i _ ↦ hint_pair i]
    congr 1
    refine sum_congr rfl fun i _ ↦ (intervalIntegral.integral_finsetSum fun j hj ↦
      hX.intervalIntegrable_inv_sub t (Finset.mem_Ioi.1 hj).ne).symm
  have hrhs_eq : ∑ i : Fin n, (i : ℝ) * (x i + w t i - X t i) =
      ∫ s in (0 : ℝ)..t, -∑ i : Fin n, (i : ℝ) * dysonDrift (X s.toNNReal) i := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_finsetSum fun i _ ↦
      (hX.intervalIntegrable_dysonDrift t i).const_mul (i : ℝ), ← sum_neg_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [intervalIntegral.integral_const_mul, hX.eq_add_integral t i]
    ring
  rw [hsum_eq, hrhs_eq]
  have hint_lhs : IntervalIntegrable
      (fun s : ℝ ↦ (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        (X s.toNNReal i - X s.toNNReal j)⁻¹) volume 0 t :=
    ((IntervalIntegrable.sum univ fun i _ ↦ hint_pair i).congr
      fun u _ ↦ Finset.sum_apply u univ _).const_mul (n : ℝ)⁻¹
  have hint_rhs : IntervalIntegrable
      (fun s : ℝ ↦ -∑ i : Fin n, (i : ℝ) * dysonDrift (X s.toNNReal) i) volume 0 t :=
    ((IntervalIntegrable.sum univ fun i _ ↦
      (hX.intervalIntegrable_dysonDrift t i).const_mul (i : ℝ)).congr
      fun u _ ↦ Finset.sum_apply u univ _).neg
  refine intervalIntegral.integral_mono_on_of_le_Ioo t.coe_nonneg hint_lhs hint_rhs fun s hs ↦ ?_
  exact sum_Ioi_inv_sub_le_neg_sum_natCast_mul_dysonDrift
    (hX.strictAnti (Real.toNNReal_pos.2 hs.1))

/-- **Time-shift invariance.** Shifting a pathwise Dyson solution by any `t₀ : ℝ≥0` yields a
pathwise Dyson solution started at `X t₀` and driven by `t ↦ w (t₀ + t) - w t₀`. -/
theorem shift (hX : IsPathwiseDysonSolution x w X) (t₀ : ℝ≥0) :
    IsPathwiseDysonSolution (X t₀) (fun t i ↦ w (t₀ + t) i - w t₀ i) (fun t ↦ X (t₀ + t)) where
  continuous_path := hX.continuous_path.comp (continuous_const.add continuous_id)
  strictAnti _ ht := hX.strictAnti (add_pos_of_nonneg_of_pos t₀.2 ht)
  intervalIntegrable_sum_inv_sub t i := by
    have hsub : uIcc (t₀ : ℝ) ((t₀ + t : ℝ≥0) : ℝ) ⊆ uIcc 0 ((t₀ + t : ℝ≥0) : ℝ) := by
      rw [uIcc_of_le (NNReal.coe_le_coe.2 le_self_add), uIcc_of_le (t₀ + t).coe_nonneg]
      exact Icc_subset_Icc t₀.coe_nonneg le_rfl
    have hint := (hX.intervalIntegrable_sum_inv_sub (t₀ + t) i).mono_set hsub
    have hshift : IntervalIntegrable
        (fun s : ℝ ↦ ∑ j ∈ univ.erase i,
          (X ((t₀ : ℝ) + s).toNNReal i - X ((t₀ : ℝ) + s).toNNReal j)⁻¹)
        volume 0 t := by
      simpa [NNReal.coe_add] using hint.comp_add_left (t₀ : ℝ) eNorm_ne_top
    refine hshift.congr ?_
    rw [uIoc_of_le t.coe_nonneg]
    intro s hs
    have hnn : ((t₀ : ℝ) + s).toNNReal = t₀ + s.toNNReal := by
      ext
      simp [Real.coe_toNNReal s hs.1.le,
        Real.coe_toNNReal ((t₀ : ℝ) + s) (add_nonneg t₀.coe_nonneg hs.1.le)]
    simp [hnn]
  eq_add_integral t i := by
    have h1 := hX.eq_add_integral (t₀ + t) i
    have h2 := hX.eq_add_integral t₀ i
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hX.intervalIntegrable_dysonDrift t₀ i)
      (hX.intervalIntegrable_dysonDrift_Icc (le_self_add : t₀ ≤ t₀ + t) i)
    have hchg : (∫ s in (0 : ℝ)..t, dysonDrift (X (t₀ + s.toNNReal)) i) =
        ∫ u in (t₀ : ℝ)..((t₀ + t : ℝ≥0) : ℝ), dysonDrift (X u.toNNReal) i := by
      have hcongr : (∫ s in (0 : ℝ)..t, dysonDrift (X (t₀ + s.toNNReal)) i) =
          ∫ s in (0 : ℝ)..t, dysonDrift (X ((t₀ : ℝ) + s).toNNReal) i := by
        refine intervalIntegral.integral_congr_ae ?_
        rw [uIoc_of_le t.coe_nonneg]
        refine Eventually.of_forall fun s hs ↦ ?_
        have hnn : ((t₀ : ℝ) + s).toNNReal = t₀ + s.toNNReal := by
          ext
          simp [Real.coe_toNNReal s hs.1.le,
            Real.coe_toNNReal ((t₀ : ℝ) + s) (add_nonneg t₀.coe_nonneg hs.1.le)]
        simp [hnn]
      rw [hcongr,
        intervalIntegral.integral_comp_add_left (fun u : ℝ ↦ dysonDrift (X u.toNNReal) i) (t₀ : ℝ),
        add_zero, NNReal.coe_add]
    linarith

/-- **Pathwise `ℓ²`-energy identity.** For two pathwise Dyson solutions `X` and `Y` driven by the
same path `w`, the change in `∑ i, (X t i - Y t i) ^ 2` across `[t₁, t₂]` equals twice the
integrated drift-difference pairing. -/
theorem sum_sq_sub_eq (hX : IsPathwiseDysonSolution x w X) (hY : IsPathwiseDysonSolution y w Y)
    {t₁ t₂ : ℝ≥0} (ht : t₁ ≤ t₂) :
    ∑ i, (X t₂ i - Y t₂ i) ^ 2 - ∑ i, (X t₁ i - Y t₁ i) ^ 2 =
      2 * ∫ s in (t₁ : ℝ)..(t₂ : ℝ),
        ∑ i, (dysonDrift (X s.toNNReal) i - dysonDrift (Y s.toNNReal) i) *
          (X s.toNNReal i - Y s.toNNReal i) := by
  -- Express `X t i - Y t i` as an indefinite integral `g i` so the shared path `w` cancels.
  let f : Fin n → ℝ → ℝ := fun i s ↦ dysonDrift (X s.toNNReal) i - dysonDrift (Y s.toNNReal) i
  let g : Fin n → ℝ → ℝ := fun i u ↦ (x i - y i) + ∫ s in (0 : ℝ)..u, f i s
  have hf_int0 (i : Fin n) : IntervalIntegrable (f i) volume 0 t₂ :=
    (hX.intervalIntegrable_dysonDrift t₂ i).sub (hY.intervalIntegrable_dysonDrift t₂ i)
  have hsub_uIcc : uIcc (t₁ : ℝ) (t₂ : ℝ) ⊆ uIcc 0 (t₂ : ℝ) := by
    rw [uIcc_of_le (NNReal.coe_le_coe.2 ht), uIcc_of_le t₂.coe_nonneg]
    exact Icc_subset_Icc t₁.coe_nonneg le_rfl
  have hf_int (i : Fin n) : IntervalIntegrable (f i) volume t₁ t₂ :=
    (hf_int0 i).mono_set hsub_uIcc
  have hg_val (i : Fin n) (t : ℝ≥0) : g i t = X t i - Y t i := by
    simp only [g, f]
    rw [intervalIntegral.integral_sub (hX.intervalIntegrable_dysonDrift t i)
      (hY.intervalIntegrable_dysonDrift t i)]
    linarith [hX.eq_add_integral t i, hY.eq_add_integral t i]
  -- Apply integration by parts for absolutely continuous functions coordinatewise on `[t₁, t₂]`.
  have hg_ac (i : Fin n) : AbsolutelyContinuousOnInterval (g i) t₁ t₂ := by
    have hac0 : AbsolutelyContinuousOnInterval (g i) 0 t₂ :=
      ((LipschitzWith.const (x i - y i)).lipschitzOnWith.absolutelyContinuousOnInterval).add
        ((hf_int0 i).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
    exact hac0.mono hsub_uIcc
  have hg_deriv (i : Fin n) : ∀ᵐ u, u ∈ uIoc (t₁ : ℝ) (t₂ : ℝ) → HasDerivAt (g i) (f i u) u := by
    filter_upwards [(hf_int0 i).ae_hasDerivAt_integral] with u hu hmem
    have hu_mem : u ∈ uIcc 0 (t₂ : ℝ) := hsub_uIcc (uIoc_subset_uIcc hmem)
    exact (hu hu_mem 0 left_mem_uIcc).const_add (x i - y i)
  have hcoord (i : Fin n) :
      (X t₂ i - Y t₂ i) ^ 2 - (X t₁ i - Y t₁ i) ^ 2 =
        2 * ∫ s in (t₁ : ℝ)..(t₂ : ℝ), f i s * (X s.toNNReal i - Y s.toNNReal i) := by
    have hibp := (hg_ac i).integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt (hg_ac i)
      (hg_deriv i) (hg_deriv i)
    have hcomm : (∫ s in (t₁ : ℝ)..(t₂ : ℝ), g i s * f i s) =
        ∫ s in (t₁ : ℝ)..(t₂ : ℝ), f i s * g i s :=
      intervalIntegral.integral_congr fun s _ ↦ mul_comm _ _
    have hcongr : (∫ s in (t₁ : ℝ)..(t₂ : ℝ), f i s * g i s) =
        ∫ s in (t₁ : ℝ)..(t₂ : ℝ), f i s * (X s.toNNReal i - Y s.toNNReal i) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le (NNReal.coe_le_coe.2 ht)]
      refine Eventually.of_forall fun s hs ↦ ?_
      have hs0 : 0 ≤ s := t₁.coe_nonneg.trans hs.1.le
      have hgs : g i s = X s.toNNReal i - Y s.toNNReal i := by
        simpa [Real.coe_toNNReal s hs0] using hg_val i s.toNNReal
      rw [hgs]
    rw [← hg_val i t₂, ← hg_val i t₁]
    linarith [hibp, hcomm, hcongr]
  have hint_prod (i : Fin n) :
      IntervalIntegrable
        (fun s : ℝ ↦ f i s * (X s.toNNReal i - Y s.toNNReal i)) volume t₁ t₂ := by
    refine (hf_int i).mul_continuousOn ?_
    exact (((hX.continuous_coord i).comp continuous_real_toNNReal).sub
      ((hY.continuous_coord i).comp continuous_real_toNNReal)).continuousOn
  rw [← sum_sub_distrib, sum_congr rfl fun i _ ↦ hcoord i, ← mul_sum,
    ← intervalIntegral.integral_finsetSum fun i _ ↦ hint_prod i]

/-- **Pathwise `ℓ²`-dissipation.** For any two pathwise Dyson solutions `X` and `Y` driven by the
same path `w`, the squared Euclidean distance `t ↦ ∑ i, (X t i - Y t i) ^ 2` is antitone on
`ℝ≥0`. -/
theorem antitone_sum_sq_sub (hX : IsPathwiseDysonSolution x w X)
    (hY : IsPathwiseDysonSolution y w Y) :
    Antitone (fun t ↦ ∑ i, (X t i - Y t i) ^ 2) := by
  intro t₁ t₂ ht
  have hid := hX.sum_sq_sub_eq hY ht
  have hint : IntervalIntegrable
      (fun s : ℝ ↦ ∑ i : Fin n, (dysonDrift (X s.toNNReal) i - dysonDrift (Y s.toNNReal) i) *
        (X s.toNNReal i - Y s.toNNReal i)) volume t₁ t₂ :=
    (IntervalIntegrable.sum (univ : Finset (Fin n)) fun i _ ↦
      ((hX.intervalIntegrable_dysonDrift_Icc ht i).sub
        (hY.intervalIntegrable_dysonDrift_Icc ht i)).mul_continuousOn
        ((((hX.continuous_coord i).comp continuous_real_toNNReal).sub
          ((hY.continuous_coord i).comp continuous_real_toNNReal)).continuousOn)).congr
      fun u _ ↦ Finset.sum_apply u univ _
  have hint_nonpos :
      ∫ s in (t₁ : ℝ)..(t₂ : ℝ),
        ∑ i, (dysonDrift (X s.toNNReal) i - dysonDrift (Y s.toNNReal) i) *
          (X s.toNNReal i - Y s.toNNReal i) ≤ 0 := by
    rw [← intervalIntegral.integral_zero (a := (t₁ : ℝ)) (b := (t₂ : ℝ))]
    refine intervalIntegral.integral_mono_on_of_le_Ioo (NNReal.coe_le_coe.2 ht)
      hint intervalIntegrable_const fun s hs ↦ ?_
    have hs_pos : 0 < s.toNNReal :=
      Real.toNNReal_pos.2 (t₁.coe_nonneg.trans_lt hs.1)
    exact sum_sub_mul_dysonDrift_sub_nonpos (hX.strictAnti hs_pos) (hY.strictAnti hs_pos)
  linarith

/-- **Pathwise `ℓ²`-contraction in initial data (AGZ Proposition 4.3.5).** Two pathwise Dyson
solutions driven by the same path `w` satisfy `∑ i, (X t i - Y t i) ^ 2 ≤ ∑ i, (x i - y i) ^ 2`
at every time `t ≥ 0`. -/
theorem sum_sq_sub_le (hX : IsPathwiseDysonSolution x w X) (hY : IsPathwiseDysonSolution y w Y)
    (t : ℝ≥0) :
    ∑ i, (X t i - Y t i) ^ 2 ≤ ∑ i, (x i - y i) ^ 2 := by
  have h0 : ∑ i, (X 0 i - Y 0 i) ^ 2 = ∑ i, (x i - y i) ^ 2 := by
    refine sum_congr rfl fun i _ ↦ ?_
    rw [hX.apply_zero, hY.apply_zero]
    ring
  exact h0 ▸ hX.antitone_sum_sq_sub hY (zero_le : (0 : ℝ≥0) ≤ t)

/-- **Pathwise uniqueness.** Two pathwise Dyson solutions with the same initial configuration `x`
and driving path `w` are identical. -/
theorem eq_of_init_eq (hX : IsPathwiseDysonSolution x w X) (hY : IsPathwiseDysonSolution x w Y) :
    X = Y := by
  ext t i
  have hle : ∑ j, (X t j - Y t j) ^ 2 ≤ 0 := by
    simpa using hX.sum_sq_sub_le hY t
  have hge : 0 ≤ (X t i - Y t i) ^ 2 := sq_nonneg _
  have hsingle : (X t i - Y t i) ^ 2 ≤ ∑ j, (X t j - Y t j) ^ 2 :=
    single_le_sum (f := fun j ↦ (X t j - Y t j) ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ i)
  have hzero : (X t i - Y t i) ^ 2 = 0 := le_antisymm (hsingle.trans hle) hge
  exact sub_eq_zero.1 (sq_eq_zero_iff.1 hzero)

end IsPathwiseDysonSolution

/-- For `n ≤ 1` (`[Subsingleton (Fin n)]`), the pairwise drift vanishes identically and `x + w`
is the unique pathwise Dyson solution whenever `w` is continuous. -/
theorem isPathwiseDysonSolution_of_subsingleton [Subsingleton (Fin n)] (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    IsPathwiseDysonSolution x w (fun t i ↦ x i + w t i) where
  continuous_path := continuous_const.add hw
  strictAnti _ _ i j hij := False.elim (hij.ne (Subsingleton.elim i j))
  intervalIntegrable_sum_inv_sub _ i := by
    have hempty : univ.erase i = ∅ := by
      ext j
      simp [Subsingleton.elim j i]
    simp [hempty]
  eq_add_integral _ _ := by
    simp [dysonDrift_of_subsingleton]

/-- **Explicit `n = 2` square-root Dyson solution (including coincident start `r₀ = 0`).**
For any center `a : ℝ` and initial gap `r₀ ≥ 0`, the deterministic trajectory
`X t = ![a + 2⁻¹ * √(r₀² + 2t), a - 2⁻¹ * √(r₀² + 2t)]` solves `IsPathwiseDysonSolution` with
zero driving path from `![a + 2⁻¹ * r₀, a - 2⁻¹ * r₀]`. When `r₀ = 0`, both particles start at `a`
and immediately separate at rate `√(2t)` under the singular integrable drift `(2√(2s))⁻¹`. -/
theorem isPathwiseDysonSolution_fin_two_sqrt (a : ℝ) {r₀ : ℝ} (hr₀ : 0 ≤ r₀) :
    IsPathwiseDysonSolution ![a + 2⁻¹ * r₀, a - 2⁻¹ * r₀] 0
      (fun t : ℝ≥0 ↦
        ![a + 2⁻¹ * Real.sqrt (r₀ ^ 2 + 2 * (t : ℝ)),
          a - 2⁻¹ * Real.sqrt (r₀ ^ 2 + 2 * (t : ℝ))]) := by
  -- Precompute regularity and FTC on `[0, t]` for the gap profile `g s = √(r₀² + 2s)`.
  let g : ℝ → ℝ := fun s ↦ Real.sqrt (r₀ ^ 2 + 2 * s)
  have hg_cont : Continuous g :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hg_deriv (s : ℝ) (hs : 0 < s) : HasDerivAt g (g s)⁻¹ s := by
    have hpos : 0 < r₀ ^ 2 + 2 * s := by positivity
    have hinner : HasDerivAt (fun u : ℝ ↦ r₀ ^ 2 + 2 * u) 2 s := by
      simpa only [mul_one] using ((hasDerivAt_id' s).const_mul (2 : ℝ)).const_add (r₀ ^ 2)
    refine ((Real.hasDerivAt_sqrt hpos.ne').comp s hinner).congr_deriv ?_
    simp only [g]
    field_simp [(Real.sqrt_pos.2 hpos).ne']
  have hint_g (t : ℝ≥0) : IntervalIntegrable (fun s : ℝ ↦ (g s)⁻¹) volume 0 t := by
    refine intervalIntegral.intervalIntegrable_deriv_of_nonneg hg_cont.continuousOn ?_
      fun _ _ ↦ inv_nonneg.2 (Real.sqrt_nonneg _)
    intro s hs
    exact hg_deriv s ((min_eq_left t.coe_nonneg) ▸ hs.1)
  have hint_nn (t : ℝ≥0) : IntervalIntegrable (fun s : ℝ ↦ (g s.toNNReal)⁻¹) volume 0 t := by
    refine (hint_g t).congr ?_
    rw [uIoc_of_le t.coe_nonneg]
    intro s hs
    simp [g, Real.coe_toNNReal s hs.1.le]
  have hint_val (t : ℝ≥0) : ∫ s in (0 : ℝ)..t, (g s.toNNReal)⁻¹ = g t - r₀ := by
    have hftc : ∫ s in (0 : ℝ)..t, (g s)⁻¹ = g t - r₀ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.coe_nonneg hg_cont.continuousOn
        (fun s hs ↦ hg_deriv s hs.1) (hint_g t)]
      simp [g, Real.sqrt_sq hr₀]
    rw [← hftc]
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le t.coe_nonneg]
    exact Eventually.of_forall fun s hs ↦ by simp [g, Real.coe_toNNReal s hs.1.le]
  refine
    { continuous_path := ?_
      strictAnti := ?_
      intervalIntegrable_sum_inv_sub := ?_
      eq_add_integral := ?_ }
  · rw [continuous_pi_iff]
    intro i
    have hsqrt : Continuous (fun t : ℝ≥0 ↦ g t) := hg_cont.comp NNReal.continuous_coe
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      exact continuous_const.add (continuous_const.mul hsqrt)
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact continuous_const.sub (continuous_const.mul hsqrt)
  · intro t ht i j hij
    have hpos : 0 < Real.sqrt (r₀ ^ 2 + 2 * (t : ℝ)) := by
      have : (0 : ℝ) < t := ht
      exact Real.sqrt_pos.2 (by positivity)
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    linarith
  · intro t i
    fin_cases i
    · simp only [Fin.zero_eta]
      have herase : (univ : Finset (Fin 2)).erase 0 = {1} := by ext j; fin_cases j <;> simp
      refine (hint_nn t).congr fun s _ ↦ ?_
      simp only [herase, sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, g]
      congr 1; ring
    · simp only [Fin.mk_one]
      have herase : (univ : Finset (Fin 2)).erase 1 = {0} := by ext j; fin_cases j <;> simp
      refine (hint_nn t).neg.congr fun s _ ↦ ?_
      simp only [Pi.neg_apply, herase, sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, g, ← inv_neg]
      congr 1; ring
  · intro t i
    have hcongr_g := hint_val t
    fin_cases i
    · simp only [Fin.zero_eta, dysonDrift_fin_two_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Pi.zero_apply, add_zero]
      have heq : (∫ s in (0 : ℝ)..t,
          2⁻¹ * ((a + 2⁻¹ * g s.toNNReal) - (a - 2⁻¹ * g s.toNNReal))⁻¹) =
          2⁻¹ * ∫ s in (0 : ℝ)..t, (g s.toNNReal)⁻¹ := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun s _ ↦ by congr 2; ring
      simp only [g] at heq hcongr_g
      rw [heq, hcongr_g]; ring
    · simp only [Fin.mk_one, dysonDrift_fin_two_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Pi.zero_apply, add_zero]
      have heq : (∫ s in (0 : ℝ)..t,
          -(2⁻¹ * ((a + 2⁻¹ * g s.toNNReal) - (a - 2⁻¹ * g s.toNNReal))⁻¹)) =
          -(2⁻¹ * ∫ s in (0 : ℝ)..t, (g s.toNNReal)⁻¹) := by
        rw [intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
        exact congrArg Neg.neg (intervalIntegral.integral_congr fun s _ ↦ by congr 2; ring)
      simp only [g] at heq hcongr_g
      rw [heq, hcongr_g]; ring

end Pathwise

section Stochastic

variable {Ω : Type*}

/-- A continuous process `X`, lying in the open decreasing chamber at positive times, solving the
Dyson system of size `n` and parameter `β` from `x` driven by `B` as an almost-sure pathwise
integral identity with locally integrable drift. Adaptedness to a filtration is not part of the
definition. -/
def IsDysonSolution [MeasurableSpace Ω] (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (P : Measure Ω)
    (B : Fin n → ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω) ∧ (∀ t, 0 < t → StrictAnti (X t ω)) ∧
    ∀ (t : ℝ≥0) (i : Fin n),
      IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ Finset.univ.erase i,
        (X s.toNNReal ω i - X s.toNNReal ω j)⁻¹) volume 0 t ∧
      X t ω i = x i + Real.sqrt (2 / (β * n)) * B i t ω +
        ∫ s in (0 : ℝ)..t, (n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
          (X s.toNNReal ω i - X s.toNNReal ω j)⁻¹

/-- Definitional unfolding of `IsDysonSolution`. -/
theorem isDysonSolution_def [MeasurableSpace Ω] (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (P : Measure Ω)
    (B : Fin n → ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) :
    IsDysonSolution β n x P B X ↔
      (∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω) ∧ (∀ t, 0 < t → StrictAnti (X t ω)) ∧
        ∀ (t : ℝ≥0) (i : Fin n),
          IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ Finset.univ.erase i,
            (X s.toNNReal ω i - X s.toNNReal ω j)⁻¹) volume 0 t ∧
          X t ω i = x i + Real.sqrt (2 / (β * n)) * B i t ω +
            ∫ s in (0 : ℝ)..t, (n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
              (X s.toNNReal ω i - X s.toNNReal ω j)⁻¹) :=
  (Iff.rfl)

/-- `IsDysonSolution` is equivalent to `IsPathwiseDysonSolution` holding `P`-almost everywhere
with driving path `t i ↦ √(2 / (β * n)) * B i t ω`. -/
theorem isDysonSolution_iff_ae_isPathwiseDysonSolution [MeasurableSpace Ω] (β : ℝ) (n : ℕ)
    (x : Fin n → ℝ) (P : Measure Ω) (B : Fin n → ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) :
    IsDysonSolution β n x P B X ↔
      ∀ᵐ ω ∂P, IsPathwiseDysonSolution x
        (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) (fun t ↦ X t ω) := by
  rw [isDysonSolution_def]
  refine eventually_congr (Eventually.of_forall fun ω ↦ ?_)
  constructor
  · rintro ⟨hcont, hanti, hint⟩
    refine ⟨hcont, fun t ht ↦ hanti t ht, fun t i ↦ (hint t i).1, fun t i ↦ ?_⟩
    simpa only [dysonDrift_apply] using (hint t i).2
  · intro hX
    refine ⟨hX.continuous_path, fun t ht ↦ hX.strictAnti ht, fun t i ↦ ⟨?_, ?_⟩⟩
    · exact hX.intervalIntegrable_sum_inv_sub t i
    · simpa only [dysonDrift_apply] using hX.eq_add_integral t i

namespace IsDysonSolution

variable [MeasurableSpace Ω] {β : ℝ} {n : ℕ} {x y : Fin n → ℝ} {P : Measure Ω}
  {B : Fin n → ℝ≥0 → Ω → ℝ} {X Y : ℝ≥0 → Ω → Fin n → ℝ}

/-- Almost every sample path of a Dyson solution lies in the closed chamber `Antitone (X t ω)` at
all times `t ≥ 0`. -/
theorem ae_antitone (hX : IsDysonSolution β n x P B X) :
    ∀ᵐ ω ∂P, ∀ t, Antitone (X t ω) := by
  filter_upwards [(isDysonSolution_iff_ae_isPathwiseDysonSolution β n x P B X).1 hX] with ω hω t
  exact hω.antitone t

/-- **Almost-sure `ℓ²`-contraction in initial data.** Any two Dyson solutions driven by the same
process `B` satisfy `∑ i, (X t ω i - Y t ω i) ^ 2 ≤ ∑ i, (x i - y i) ^ 2` simultaneously for all
`t ≥ 0`, `P`-almost surely. -/
theorem ae_sum_sq_sub_le (hX : IsDysonSolution β n x P B X) (hY : IsDysonSolution β n y P B Y) :
    ∀ᵐ ω ∂P, ∀ t, ∑ i, (X t ω i - Y t ω i) ^ 2 ≤ ∑ i, (x i - y i) ^ 2 := by
  filter_upwards [(isDysonSolution_iff_ae_isPathwiseDysonSolution β n x P B X).1 hX,
    (isDysonSolution_iff_ae_isPathwiseDysonSolution β n y P B Y).1 hY] with ω hωX hωY t
  exact hωX.sum_sq_sub_le hωY t

/-- **Almost-sure pathwise uniqueness for the Dyson system** (the uniqueness half of AGZ
Proposition 4.3.5, with no restriction on `β`, `x`, `P`, or the law of `B`). -/
theorem ae_eq (hX : IsDysonSolution β n x P B X) (hY : IsDysonSolution β n x P B Y) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  filter_upwards [(isDysonSolution_iff_ae_isPathwiseDysonSolution β n x P B X).1 hX,
    (isDysonSolution_iff_ae_isPathwiseDysonSolution β n x P B Y).1 hY] with ω hωX hωY t
  exact congrFun (hωX.eq_of_init_eq hωY) t

end IsDysonSolution

/-- For `n ≤ 1` (`[Subsingleton (Fin n)]`), any process `B` with almost surely continuous sample
paths drives a solution `X t ω i = x i + √(2 / (β * n)) * B i t ω` of `IsDysonSolution`. -/
theorem isDysonSolution_of_subsingleton [MeasurableSpace Ω] {n : ℕ} [Subsingleton (Fin n)]
    (β : ℝ) (x : Fin n → ℝ) (P : Measure Ω) {B : Fin n → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t ↦ B i t ω)) :
    IsDysonSolution β n x P B
      (fun t ω i ↦ x i + Real.sqrt (2 / (β * n)) * B i t ω) := by
  rw [isDysonSolution_def]
  have hB_all : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t ↦ B i t ω) := ae_all_iff.2 hB
  filter_upwards [hB_all] with ω hω
  refine ⟨?_, fun _ _ i j hij ↦ False.elim (hij.ne (Subsingleton.elim i j)), fun t i ↦ ?_⟩
  · rw [continuous_pi_iff]
    intro i
    exact continuous_const.add (continuous_const.mul (hω i))
  · have hempty : (univ : Finset (Fin n)).erase i = ∅ := by
      ext j
      simp [Subsingleton.elim j i]
    simp [hempty]

/-- The deterministic `n = 2` square-root trajectory witnesses `IsDysonSolution` for any measure
`P` and parameter `β` under zero noise `B = 0`, including from a coincident start `r₀ = 0`. -/
theorem isDysonSolution_fin_two_sqrt [MeasurableSpace Ω] (β : ℝ) (P : Measure Ω) (a : ℝ)
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) :
    IsDysonSolution β 2 ![a + 2⁻¹ * r₀, a - 2⁻¹ * r₀] P 0
      (fun t _ω ↦
        ![a + 2⁻¹ * Real.sqrt (r₀ ^ 2 + 2 * (t : ℝ)),
          a - 2⁻¹ * Real.sqrt (r₀ ^ 2 + 2 * (t : ℝ))]) := by
  rw [isDysonSolution_iff_ae_isPathwiseDysonSolution]
  refine Eventually.of_forall fun ω ↦ ?_
  have hzero : (fun t (i : Fin 2) ↦
      Real.sqrt (2 / (β * (2 : ℕ))) * (0 : Fin 2 → ℝ≥0 → Ω → ℝ) i t ω) = 0 := by
    ext t i
    simp
  rw [hzero]
  exact isPathwiseDysonSolution_fin_two_sqrt a hr₀

end Stochastic

end TauCeti.Probability
