/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Probability.DysonBrownianMotion.Drift
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Order.BigOperators.Ring.Finset
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

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
* **Interval integrability of individual singular reciprocals:** although `IsPathwiseDysonSolution`
  only assumes integrability of the signed sum `∑_{j ≠ i} (X_i - X_j)⁻¹`, every individual pairwise
  reciprocal `(X_i - X_j)⁻¹` (`i ≠ j`) is interval integrable on `0..t`, with a quantitative `L¹`
  staircase bound on `n⁻¹ ∑_{i < j} ∫₀ᵗ (X_i - X_j)⁻¹`.
* **Pathwise `ℓ²`-dissipation, contraction, and uniqueness (AGZ Proposition 4.3.5):** using the
  general energy identity `TauCeti.intervalIntegral.sum_sq_sub_eq_of_eq_add_integral` and
  dissipation bound `TauCeti.intervalIntegral.sum_sq_sub_le_of_eq_add_integral`, for two solutions
  `X` and `Y` of the Dyson system driven by the same path `w`, the squared Euclidean distance
  `t ↦ ∑ i, (X t i - Y t i) ^ 2` is antitone on `ℝ≥0`, hence bounded by `∑ i, (x i - y i) ^ 2`.
  In particular, `IsPathwiseDysonSolution.eq_of_init_eq` gives pathwise uniqueness and
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
* `TauCeti.Probability.IsPathwiseDysonSolution.sum_sq_sub_eq`: `ℓ²`-energy identity for two
  pathwise Dyson solutions driven by the same path.
* `TauCeti.Probability.IsPathwiseDysonSolution.antitone_sum_sq_sub` and
  `TauCeti.Probability.IsPathwiseDysonSolution.sum_sq_sub_le`: `ℓ²`-contraction in initial data.
* `TauCeti.Probability.IsPathwiseDysonSolution.eq_of_init_eq` and
  `TauCeti.Probability.IsDysonSolution.ae_eq`: pathwise and almost-sure uniqueness.
* `TauCeti.Probability.isPathwiseDysonSolution_fin_two_sqrt`: explicit `n = 2` non-colliding
  solution, including coincident initial position `r₀ = 0`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.1, Lemma 4.3.3 and Proposition 4.3.5 (integral formulation,
  pathwise uniqueness, and `ℓ²`-contraction for the Dyson system).
* L. C. G. Rogers, Z. Shi, *Interacting Brownian particles and the Wigner law*, Probab. Theory
  Related Fields 95 (1993) (monotonicity-based pathwise uniqueness and `ℓ²`-contraction for the
  `n⁻¹`-rescaled Dyson particle system).
* E. Cépa, D. Lépingle, *Diffusing particles with electrostatic repulsion*, Probab. Theory Related
  Fields 107 (1997) (closed-chamber persistence and boundary-start handling including coincident
  initial data `r₀ = 0`, `ℓ²`-contraction across the boundary, and `L¹` integrability of individual
  pairwise gap reciprocals).
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

/-- At `t = 0`, a pathwise Dyson solution satisfies `X 0 = x + w 0`. -/
theorem apply_zero (hX : IsPathwiseDysonSolution x w X) : X 0 = x + w 0 := by
  ext i
  simpa using hX.eq_add_integral 0 i

/-- When the driving path starts at `0`, a pathwise Dyson solution starts at `X 0 = x`. -/
theorem apply_zero_eq_of_driving_zero (hX : IsPathwiseDysonSolution x w X) (hw0 : w 0 = 0) :
    X 0 = x := by
  rw [hX.apply_zero, hw0, add_zero]

/-- The cumulative drift integral `t ↦ ∫ s in 0..t, dysonDrift (X s.toNNReal) i` of a pathwise
Dyson solution is continuous on `ℝ≥0`. -/
theorem continuous_integral_dysonDrift (hX : IsPathwiseDysonSolution x w X) (i : Fin n) :
    Continuous (fun t : ℝ≥0 ↦ ∫ s in (0 : ℝ)..t, dysonDrift (X s.toNNReal) i) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  set T : ℝ≥0 := t₀ + 1
  have hcont : ContinuousOn (fun u : ℝ ↦ ∫ s in (0 : ℝ)..u, dysonDrift (X s.toNNReal) i)
      (uIcc 0 (T : ℝ)) :=
    intervalIntegral.continuousOn_primitive_interval' (hX.intervalIntegrable_dysonDrift T i)
      left_mem_uIcc
  have hcont_nn : ContinuousOn (fun t : ℝ≥0 ↦ ∫ s in (0 : ℝ)..t, dysonDrift (X s.toNNReal) i)
      (Iic T) := by
    refine hcont.comp NNReal.continuous_coe.continuousOn fun t ht ↦ ?_
    rw [uIcc_of_le T.coe_nonneg]
    exact ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩
  exact hcont_nn.continuousAt (Iic_mem_nhds (lt_add_of_pos_right t₀ zero_lt_one))

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
theorem antitone (hX : IsPathwiseDysonSolution x w X) (t : ℝ≥0) : Antitone (X t) :=
  isClosed_antitone.mem_of_tendsto
    (hX.continuous_path.continuousWithinAt (s := Ioi t)).tendsto
    (eventually_nhdsWithin_of_forall fun _ hs ↦ (hX.strictAnti (zero_le.trans_lt hs)).antitone)

/-- If `w 0 = 0`, the initial configuration `x` of any pathwise Dyson solution must be antitone. -/
theorem antitone_init (hX : IsPathwiseDysonSolution x w X) (hw0 : w 0 = 0) : Antitone x := by
  simpa only [hX.apply_zero_eq_of_driving_zero hw0] using hX.antitone 0

/-- **Center-of-mass conservation.** The coordinate sum of `X t` equals `∑ i, x i + ∑ i, w t i` at
every time `t`. -/
theorem sum_eq_sum_add_sum (hX : IsPathwiseDysonSolution x w X) (t : ℝ≥0) :
    ∑ i, X t i = ∑ i, x i + ∑ i, w t i := by
  simp_rw [hX.eq_add_integral t, sum_add_distrib]
  rw [← intervalIntegral.integral_finsetSum fun i _ ↦ hX.intervalIntegrable_dysonDrift t i]
  simp

/-- **Interval integrability of individual pairwise reciprocals.** Every single off-diagonal
gap reciprocal `(X s.toNNReal i - X s.toNNReal j)⁻¹` (`i ≠ j`) is interval integrable on `0..t`. -/
theorem intervalIntegrable_inv_sub (hX : IsPathwiseDysonSolution x w X) (t : ℝ≥0) {i j : Fin n}
    (hij : i ≠ j) :
    IntervalIntegrable (fun s : ℝ ↦ (X s.toNNReal i - X s.toNNReal j)⁻¹) volume 0 t := by
  -- 1. Reduce by antisymmetry to strictly increasing pairs `a < b`.
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
  -- 2. Construct the integrable staircase majorant `n * (-∑ k, k * dysonDrift (X s) k)`.
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
  -- 3. Dominate the positive pair `(X s a - X s b)⁻¹` by the sum of all upper-triangular pairs
  --    and apply `sum_Ioi_inv_sub_le_neg_sum_natCast_mul_dysonDrift` on `(0, t]`.
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

/-- **Quantitative `L¹` staircase estimate on singular pairwise reciprocals.** On `[0, t]`,
`n⁻¹ ∑_{i < j} ∫₀ᵗ (X_i - X_j)⁻¹` is bounded by `∑ i, i * (x i + w t i - X t i)`. -/
theorem sum_Ioi_integral_inv_sub_le (hX : IsPathwiseDysonSolution x w X) (t : ℝ≥0) :
    (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        ∫ s in (0 : ℝ)..t, (X s.toNNReal i - X s.toNNReal j)⁻¹ ≤
      ∑ i : Fin n, (i : ℝ) * (x i + w t i - X t i) := by
  -- 1. Move the interval integral outside the double sum on the LHS.
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
  -- 2. Rewrite the RHS as the integral of `-∑ i, i * dysonDrift (X s) i` via the integral equation.
  have hrhs_eq : ∑ i : Fin n, (i : ℝ) * (x i + w t i - X t i) =
      ∫ s in (0 : ℝ)..t, -∑ i : Fin n, (i : ℝ) * dysonDrift (X s.toNNReal) i := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_finsetSum fun i _ ↦
      (hX.intervalIntegrable_dysonDrift t i).const_mul (i : ℝ), ← sum_neg_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [intervalIntegral.integral_const_mul, hX.eq_add_integral t i]
    ring
  -- 3. Compare the integrands pointwise on `(0, t)` via the algebraic staircase bound.
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

/-- Helper for shifting a nonnegative real timestamp inside `Real.toNNReal`. -/
private theorem toNNReal_coe_add (t₀ : ℝ≥0) {s : ℝ} (hs : 0 ≤ s) :
    ((t₀ : ℝ) + s).toNNReal = t₀ + s.toNNReal := by
  rw [Real.toNNReal_add t₀.coe_nonneg hs, Real.toNNReal_coe]

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
    simp [toNNReal_coe_add t₀ hs.1.le]
  eq_add_integral t i := by
    have h1 := hX.eq_add_integral (t₀ + t) i
    have h2 := hX.eq_add_integral t₀ i
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hX.intervalIntegrable_dysonDrift t₀ i)
      (hX.intervalIntegrable_dysonDrift_Icc (le_self_add : t₀ ≤ t₀ + t) i)
    -- Shift the integral over `[0, t]` to `[t₀, t₀ + t]` using `toNNReal_coe_add`.
    have hchg : (∫ s in (0 : ℝ)..t, dysonDrift (X (t₀ + s.toNNReal)) i) =
        ∫ u in (t₀ : ℝ)..((t₀ + t : ℝ≥0) : ℝ), dysonDrift (X u.toNNReal) i := by
      have hcongr : (∫ s in (0 : ℝ)..t, dysonDrift (X (t₀ + s.toNNReal)) i) =
          ∫ s in (0 : ℝ)..t, dysonDrift (X ((t₀ : ℝ) + s).toNNReal) i := by
        refine intervalIntegral.integral_congr_ae ?_
        rw [uIoc_of_le t.coe_nonneg]
        exact Eventually.of_forall fun s hs ↦ by simp [toNNReal_coe_add t₀ hs.1.le]
      rw [hcongr,
        intervalIntegral.integral_comp_add_left (fun u : ℝ ↦ dysonDrift (X u.toNNReal) i) (t₀ : ℝ),
        add_zero, NNReal.coe_add]
    linarith

/-- The Dyson integral equation evaluated at a nonnegative real time `s ≥ 0`. -/
private theorem eq_add_integral_of_nonneg (hX : IsPathwiseDysonSolution x w X) {s : ℝ}
    (hs : 0 ≤ s) (i : Fin n) :
    X s.toNNReal i = x i + w s.toNNReal i +
      ∫ u in (0 : ℝ)..s, dysonDrift (X u.toNNReal) i := by
  simpa only [Real.coe_toNNReal s hs] using hX.eq_add_integral s.toNNReal i

/-- **Pathwise `ℓ²`-energy identity.** For two pathwise Dyson solutions `X` and `Y` driven by the
same path `w`, the change in `∑ i, (X t i - Y t i) ^ 2` from `t₁` to `t₂` equals twice the
integrated drift-difference pairing. -/
theorem sum_sq_sub_eq (hX : IsPathwiseDysonSolution x w X) (hY : IsPathwiseDysonSolution y w Y)
    (t₁ t₂ : ℝ≥0) :
    ∑ i, (X t₂ i - Y t₂ i) ^ 2 - ∑ i, (X t₁ i - Y t₁ i) ^ 2 =
      2 * ∫ s in (t₁ : ℝ)..(t₂ : ℝ),
        ∑ i, (dysonDrift (X s.toNNReal) i - dysonDrift (Y s.toNNReal) i) *
          (X s.toNNReal i - Y s.toNNReal i) := by
  simpa only [Real.toNNReal_coe] using
    TauCeti.intervalIntegral.sum_sq_sub_eq_of_eq_add_integral (univ : Finset (Fin n))
      (x := x) (y := y) (w := fun s ↦ w s.toNNReal) (X := fun s ↦ X s.toNNReal)
      (Y := fun s ↦ Y s.toNNReal)
      (F := fun s ↦ dysonDrift (X s.toNNReal)) (G := fun s ↦ dysonDrift (Y s.toNNReal))
      (t₀ := 0) (t₁ := (t₁ : ℝ)) (t₂ := (t₂ : ℝ))
      (fun i _ ↦ hX.intervalIntegrable_dysonDrift t₁ i)
      (fun i _ ↦ hX.intervalIntegrable_dysonDrift t₂ i)
      (fun i _ ↦ hY.intervalIntegrable_dysonDrift t₁ i)
      (fun i _ ↦ hY.intervalIntegrable_dysonDrift t₂ i)
      (fun _ ht i _ ↦ hX.eq_add_integral_of_nonneg
        ((le_min t₁.coe_nonneg t₂.coe_nonneg).trans ht.1) i)
      (fun _ ht i _ ↦ hY.eq_add_integral_of_nonneg
        ((le_min t₁.coe_nonneg t₂.coe_nonneg).trans ht.1) i)

/-- **Pathwise `ℓ²`-dissipation.** For any two pathwise Dyson solutions `X` and `Y` driven by the
same path `w`, the squared Euclidean distance `t ↦ ∑ i, (X t i - Y t i) ^ 2` is antitone on
`ℝ≥0`. -/
theorem antitone_sum_sq_sub (hX : IsPathwiseDysonSolution x w X)
    (hY : IsPathwiseDysonSolution y w Y) :
    Antitone (fun t ↦ ∑ i, (X t i - Y t i) ^ 2) := fun t₁ t₂ ht ↦ by
  simpa only [Real.toNNReal_coe] using
    TauCeti.intervalIntegral.sum_sq_sub_le_of_eq_add_integral (univ : Finset (Fin n))
      (x := x) (y := y) (w := fun s ↦ w s.toNNReal) (X := fun s ↦ X s.toNNReal)
      (Y := fun s ↦ Y s.toNNReal)
      (F := fun s ↦ dysonDrift (X s.toNNReal)) (G := fun s ↦ dysonDrift (Y s.toNNReal))
      (t₀ := 0) (NNReal.coe_le_coe.2 ht)
      (fun i _ ↦ hX.intervalIntegrable_dysonDrift t₁ i)
      (fun i _ ↦ hX.intervalIntegrable_dysonDrift t₂ i)
      (fun i _ ↦ hY.intervalIntegrable_dysonDrift t₁ i)
      (fun i _ ↦ hY.intervalIntegrable_dysonDrift t₂ i)
      (fun _ ht_mem i _ ↦ hX.eq_add_integral_of_nonneg
        ((le_min t₁.coe_nonneg t₂.coe_nonneg).trans ht_mem.1) i)
      (fun _ ht_mem i _ ↦ hY.eq_add_integral_of_nonneg
        ((le_min t₁.coe_nonneg t₂.coe_nonneg).trans ht_mem.1) i)
      fun s hs ↦
        have hs_pos : 0 < s.toNNReal := Real.toNNReal_pos.2 (t₁.coe_nonneg.trans_lt hs.1)
        sum_sub_mul_dysonDrift_sub_nonpos (hX.strictAnti hs_pos) (hY.strictAnti hs_pos)

/-- **Pathwise `ℓ²`-contraction in initial data (AGZ Proposition 4.3.5).** Two pathwise Dyson
solutions driven by the same path `w` satisfy `∑ i, (X t i - Y t i) ^ 2 ≤ ∑ i, (x i - y i) ^ 2`
at every time `t ≥ 0`. -/
theorem sum_sq_sub_le (hX : IsPathwiseDysonSolution x w X) (hY : IsPathwiseDysonSolution y w Y)
    (t : ℝ≥0) :
    ∑ i, (X t i - Y t i) ^ 2 ≤ ∑ i, (x i - y i) ^ 2 := by
  simpa only [hX.apply_zero, hY.apply_zero, Pi.add_apply, add_sub_add_right_eq_sub] using
    hX.antitone_sum_sq_sub hY (zero_le : (0 : ℝ≥0) ≤ t)

/-- **Pathwise uniqueness.** Two pathwise Dyson solutions with the same initial configuration `x`
and driving path `w` are identical. -/
theorem eq_of_init_eq (hX : IsPathwiseDysonSolution x w X) (hY : IsPathwiseDysonSolution x w Y) :
    X = Y := by
  ext t i
  have hle : ∑ j, (X t j - Y t j) ^ 2 ≤ 0 := by
    simpa only [sub_self, zero_pow two_ne_zero, sum_const_zero] using hX.sum_sq_sub_le hY t
  exact sub_eq_zero.1 ((sum_sq_le_zero_iff univ fun j ↦ X t j - Y t j).1 hle i (mem_univ i))

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

/-- Derivative of the two-particle gap profile `u ↦ √(r₀² + 2u)` at positive times `s > 0`. -/
private theorem hasDerivAt_sqrt_sq_add_two_mul (r₀ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun u : ℝ ↦ Real.sqrt (r₀ ^ 2 + 2 * u))
      (Real.sqrt (r₀ ^ 2 + 2 * s))⁻¹ s := by
  have hpos : 0 < r₀ ^ 2 + 2 * s := by positivity
  have hinner : HasDerivAt (fun u : ℝ ↦ r₀ ^ 2 + 2 * u) 2 s := by
    simpa only [mul_one] using ((hasDerivAt_id' s).const_mul (2 : ℝ)).const_add (r₀ ^ 2)
  refine ((Real.hasDerivAt_sqrt hpos.ne').comp s hinner).congr_deriv ?_
  field_simp [(Real.sqrt_pos.2 hpos).ne']

/-- Interval integrability of `s ↦ (√(r₀² + 2s))⁻¹` on `0..t`, including the singular `r₀ = 0`
case. -/
private theorem intervalIntegrable_inv_sqrt_sq_add_two_mul_real (r₀ : ℝ) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt (r₀ ^ 2 + 2 * s))⁻¹) volume 0 t := by
  have hg_cont : Continuous (fun s : ℝ ↦ Real.sqrt (r₀ ^ 2 + 2 * s)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_const.mul continuous_id))
  refine intervalIntegral.intervalIntegrable_deriv_of_nonneg hg_cont.continuousOn ?_
    fun _ _ ↦ inv_nonneg.2 (Real.sqrt_nonneg _)
  intro s hs
  exact hasDerivAt_sqrt_sq_add_two_mul r₀ ((min_eq_left t.coe_nonneg) ▸ hs.1)

/-- Interval integrability of the `ℝ≥0`-clamped reciprocal gap profile
`s ↦ (√(r₀² + 2 * s.toNNReal))⁻¹` on `0..t`. -/
private theorem intervalIntegrable_inv_sqrt_sq_add_two_mul (r₀ : ℝ) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt (r₀ ^ 2 + 2 * (s.toNNReal : ℝ)))⁻¹)
      volume 0 t := by
  refine (intervalIntegrable_inv_sqrt_sq_add_two_mul_real r₀ t).congr ?_
  rw [uIoc_of_le t.coe_nonneg]
  intro s hs
  simp [Real.coe_toNNReal s hs.1.le]

/-- Exact improper integral `∫₀ᵗ (√(r₀² + 2s))⁻¹ ds = √(r₀² + 2t) - r₀` for `r₀ ≥ 0`. -/
private theorem integral_inv_sqrt_sq_add_two_mul {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (t : ℝ≥0) :
    ∫ s in (0 : ℝ)..t, (Real.sqrt (r₀ ^ 2 + 2 * (s.toNNReal : ℝ)))⁻¹ =
      Real.sqrt (r₀ ^ 2 + 2 * (t : ℝ)) - r₀ := by
  have hg_cont : Continuous (fun s : ℝ ↦ Real.sqrt (r₀ ^ 2 + 2 * s)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hftc : ∫ s in (0 : ℝ)..t, (Real.sqrt (r₀ ^ 2 + 2 * s))⁻¹ =
      Real.sqrt (r₀ ^ 2 + 2 * (t : ℝ)) - r₀ := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.coe_nonneg hg_cont.continuousOn
      (fun s hs ↦ hasDerivAt_sqrt_sq_add_two_mul r₀ hs.1)
      (intervalIntegrable_inv_sqrt_sq_add_two_mul_real r₀ t)]
    simp [Real.sqrt_sq hr₀]
  rw [← hftc]
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le t.coe_nonneg]
  exact Eventually.of_forall fun s hs ↦ by simp [Real.coe_toNNReal s hs.1.le]

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
  -- Express both coordinates in terms of the shared gap profile `g t = √(r₀² + 2t)`.
  set X : ℝ≥0 → Fin 2 → ℝ := fun t : ℝ≥0 ↦
    ![a + 2⁻¹ * Real.sqrt (r₀ ^ 2 + 2 * (t : ℝ)),
      a - 2⁻¹ * Real.sqrt (r₀ ^ 2 + 2 * (t : ℝ))]
  let g : ℝ≥0 → ℝ := fun t ↦ Real.sqrt (r₀ ^ 2 + 2 * (t : ℝ))
  have hX0 (t : ℝ≥0) : X t 0 = a + 2⁻¹ * g t := by simp only [X, g, Matrix.cons_val_zero]
  have hX1 (t : ℝ≥0) : X t 1 = a - 2⁻¹ * g t := by
    simp only [X, g, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hgap (t : ℝ≥0) : X t 0 - X t 1 = g t := by
    rw [hX0, hX1]
    ring
  have hdrift0 (t : ℝ≥0) : dysonDrift (X t) 0 = 2⁻¹ * (g t)⁻¹ := by
    rw [dysonDrift_fin_two_zero, hgap]
  have hdrift1 (t : ℝ≥0) : dysonDrift (X t) 1 = -(2⁻¹ * (g t)⁻¹) := by
    rw [dysonDrift_fin_two_one, hgap]
  have herase_eq (t : ℝ≥0) (i : Fin 2) :
      ∑ j ∈ univ.erase i, (X t i - X t j)⁻¹ = 2 * dysonDrift (X t) i := by
    simp [dysonDrift_apply]
  have hg_cont : Continuous g :=
    Real.continuous_sqrt.comp
      (continuous_const.add (continuous_const.mul NNReal.continuous_coe))
  refine
    { continuous_path := ?_
      strictAnti := ?_
      intervalIntegrable_sum_inv_sub := ?_
      eq_add_integral := ?_ }
  · -- 1. Continuity of each coordinate from continuity of `g`.
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · simp_rw [Fin.zero_eta, hX0]
      exact continuous_const.add (continuous_const.mul hg_cont)
    · simp_rw [Fin.mk_one, hX1]
      exact continuous_const.sub (continuous_const.mul hg_cont)
  · -- 2. Strict decreasing order at `t > 0`: the unique pair `i < j` in `Fin 2` is `(0, 1)`.
    intro t ht i j hij
    have hi : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    have hj : j = 1 := Fin.ext (by rw [Fin.val_one]; omega)
    subst hi hj
    have hpos : 0 < g t := Real.sqrt_pos.2 (by have : (0 : ℝ) < t := ht; positivity)
    exact sub_pos.1 (hgap t ▸ hpos)
  · -- 3. Integrability of the off-diagonal sum, obtained via `2 * dysonDrift (X s) i`.
    intro t i
    simp_rw [herase_eq]
    fin_cases i
    · simp_rw [Fin.zero_eta, hdrift0, ← mul_assoc, mul_inv_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0),
        one_mul]
      exact intervalIntegrable_inv_sqrt_sq_add_two_mul r₀ t
    · simp_rw [Fin.mk_one, hdrift1, mul_neg, ← mul_assoc,
        mul_inv_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_mul]
      exact (intervalIntegrable_inv_sqrt_sq_add_two_mul r₀ t).neg
  · -- 4. Integral equation via `dysonDrift_fin_two_zero`/`_one` and FTC for `g`.
    intro t i
    have hint : ∫ s in (0 : ℝ)..t, (g s.toNNReal)⁻¹ = g t - r₀ :=
      integral_inv_sqrt_sq_add_two_mul hr₀ t
    fin_cases i
    · simp only [Fin.zero_eta, hX0, hdrift0, Matrix.cons_val_zero, Pi.zero_apply, add_zero,
        intervalIntegral.integral_const_mul, hint]
      ring
    · simp only [Fin.mk_one, hX1, hdrift1, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.zero_apply, add_zero, intervalIntegral.integral_neg,
        intervalIntegral.integral_const_mul, hint]
      ring

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
  rw [isDysonSolution_iff_ae_isPathwiseDysonSolution]
  filter_upwards [ae_all_iff.2 hB] with ω hω
  exact isPathwiseDysonSolution_of_subsingleton x
    (continuous_pi fun i ↦ continuous_const.mul (hω i))

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
