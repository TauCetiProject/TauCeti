/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Topology.Algebra.Module.Matrix
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import TauCeti.Analysis.Calculus.FDeriv.Matrix
import TauCeti.Analysis.ODE.Gronwall.Uniqueness
import TauCeti.Analysis.SpecificLimits.Normed

/-!
# Holomorphic linear differential systems on discs

For a holomorphic family `A : ℂ → B` in a complete complex normed algebra on an open disc around
`z₀`, the linear differential equation `Φ' z = A z * Φ z` with `Φ z₀ = 1` is solved by the power
series `TauCeti.propagatorSeries A z₀`, whose coefficients are determined recursively by
Cauchy convolution with the Taylor coefficients of `A` at `z₀`. Unlike `TauCeti.dysonSeriesLeft`,
which integrates continuous paths along the real line, this series converges and differentiates
termwise on any complex disc `Metric.eball z₀ r` (finite or infinite radius) on which `A` is
complex differentiable: Cauchy's derivative estimate on interior circles together with Bernoulli's
inequality bounds the `n`-th coefficient by `‖1‖ * (n + 1) ^ K / ρ ^ n`.

Combining this series construction with the general Grönwall uniqueness theorems on convex and open
preconnected domains from `TauCeti.Analysis.ODE.Gronwall.Uniqueness` and specializing `B` to
`E →L[ℂ] E` yields existence and uniqueness for linear operator systems on open discs (giving
Cauchy's local initial-value theorem when `0 < r`, and holding vacuously on the empty ball when
`r ≤ 0`), the restricted solution submodule `TauCeti.linearODESolutionSpace`, and its evaluation
linear equivalences `TauCeti.linearODESolutionSpace.evalEquivEball` and
`TauCeti.linearODESolutionSpace.evalEquivBall` with `E` on positive-radius discs. Specializing
further via `Matrix.mulVecCLM` to `E = (ι → ℂ)` gives the matrix disc existence and uniqueness
theorem, `TauCeti.matrixODESolutionSpace`, and its dimension `Fintype.card ι` on positive-radius
discs.

## Main declarations

* `TauCeti.propagatorCoeff`, `TauCeti.propagatorSeries`: recursive Taylor coefficients and
  power-series sum solving `Φ' z = A z * Φ z` with `Φ z₀ = 1` when `A` is holomorphic on a disc.
* `TauCeti.norm_propagatorCoeff_le_of_forall_mem_sphere_norm_le`: Cauchy--Bernoulli majorant bound
  on the propagator coefficients.
* `TauCeti.hasDerivAt_propagatorSeries_of_mem_eball`: `propagatorSeries` solves `Φ' = A * Φ` on
  `Metric.eball z₀ r`.
* `TauCeti.linearODESolutionSpace`, `TauCeti.linearODESolutionSpace.evalEquivEball`,
  `TauCeti.linearODESolutionSpace.evalEquivBall`: the restricted solution submodule of
  `v' = A(z) v` and its evaluation linear isomorphisms with `E` on discs of positive radius.
* `TauCeti.exists_analyticOnNhd_ball_hasDerivAt_mulVec`, `TauCeti.matrixODESolutionSpace`,
  `TauCeti.finrank_matrixODESolutionSpace_ball`: existence, uniqueness, evaluation isomorphism, and
  dimension for holomorphic matrix systems `y' = M(z) *ᵥ y`.

## References

* Frits Beukers, *E-functions and G-functions* (Arizona Winter School 2008 lecture notes),
  §2.2, Theorem 2.2.1.
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §4.2--4.3, Theorem 4.7.
-/

public noncomputable section

open Filter Function Metric Set Topology
open scoped ENNReal NNReal Matrix

namespace TauCeti

section Propagator

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

/-- Recursive Taylor coefficients around `z₀` associated with a family `A : ℂ → B`, which give the
Taylor coefficients of the propagator solving `Φ' z = A z * Φ z` with `Φ z₀ = 1` when `B` is
complete and `A` is complex differentiable on an open disc around `z₀`. -/
def propagatorCoeff (A : ℂ → B) (z₀ : ℂ) : ℕ → B
  | 0 => 1
  | n + 1 => ((n + 1 : ℂ))⁻¹ •
      ∑ k ∈ Finset.range (n + 1),
        ((k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀) * propagatorCoeff A z₀ (n - k)

/-- The zeroth propagator coefficient is `1`. -/
@[simp]
theorem propagatorCoeff_zero (A : ℂ → B) (z₀ : ℂ) : propagatorCoeff A z₀ 0 = 1 := by
  simp [propagatorCoeff]

/-- Recursion for the `(n + 1)`-st propagator coefficient. -/
theorem propagatorCoeff_succ (A : ℂ → B) (z₀ : ℂ) (n : ℕ) :
    propagatorCoeff A z₀ (n + 1) = ((n + 1 : ℂ))⁻¹ •
      ∑ k ∈ Finset.range (n + 1),
        ((k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀) * propagatorCoeff A z₀ (n - k) := by
  simp [propagatorCoeff]

/-- The first propagator coefficient is `A z₀ * 1`. -/
@[simp]
theorem propagatorCoeff_one (A : ℂ → B) (z₀ : ℂ) : propagatorCoeff A z₀ 1 = A z₀ := by
  simp [propagatorCoeff]

/-- The `tsum` power series around `z₀` with coefficients `propagatorCoeff A z₀` associated with a
family `A : ℂ → B`. When `B` is complete and `A` is complex differentiable on an open disc around
`z₀`, this series converges and solves `Φ' z = A z * Φ z` with `Φ z₀ = 1`. -/
def propagatorSeries (A : ℂ → B) (z₀ z : ℂ) : B :=
  ∑' n : ℕ, (z - z₀) ^ n • propagatorCoeff A z₀ n

/-- Defining series for `propagatorSeries`. -/
theorem propagatorSeries_def (A : ℂ → B) (z₀ z : ℂ) :
    propagatorSeries A z₀ z = ∑' n : ℕ, (z - z₀) ^ n • propagatorCoeff A z₀ n := by rfl

/-- At the center `z₀`, `propagatorSeries` evaluates to `1`. -/
@[simp]
theorem propagatorSeries_self (A : ℂ → B) (z₀ : ℂ) :
    propagatorSeries A z₀ z₀ = 1 := by
  rw [propagatorSeries_def, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

private theorem natCast_succ_smul_pow_smul_propagatorCoeff_succ
    (A : ℂ → B) (z₀ z : ℂ) (n : ℕ) :
    ((n + 1 : ℂ) * (z - z₀) ^ n) • propagatorCoeff A z₀ (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        ((k.factorial : ℂ)⁻¹ • (z - z₀) ^ k • iteratedDeriv k A z₀) *
          ((z - z₀) ^ (n - k) • propagatorCoeff A z₀ (n - k)) := by
  have hn : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [mul_comm, ← smul_smul, propagatorCoeff_succ, smul_inv_smul₀ hn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (z - z₀) ^ n = (z - z₀) ^ k * (z - z₀) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [hpow, ← smul_mul_smul_comm, smul_comm ((z - z₀) ^ k)]

private theorem norm_propagatorCoeff_succ_step
    {A : ℂ → B} {z₀ : ℂ} {ρ C : ℝ} (hρ : 0 < ρ)
    (hA_coeff : ∀ k, ‖(k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀‖ ≤ C / ρ ^ k) (m : ℕ) :
    ρ ^ (m + 1) * ‖propagatorCoeff A z₀ (m + 1)‖ ≤
      ((m + 1 : ℝ))⁻¹ * ((Nat.ceil (C * ρ) : ℝ) *
        ∑ j ∈ Finset.range (m + 1), ρ ^ j * ‖propagatorCoeff A z₀ j‖) := by
  set S := ∑ j ∈ Finset.range (m + 1), ρ ^ j * ‖propagatorCoeff A z₀ j‖
  have hS0 : 0 ≤ S :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (pow_nonneg hρ.le j) (norm_nonneg _)
  rw [propagatorCoeff_succ, norm_smul, norm_inv, ← Nat.cast_add_one, Complex.norm_natCast,
    Nat.cast_add_one, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc
    ρ ^ (m + 1) * ‖∑ k ∈ Finset.range (m + 1),
        ((k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀) * propagatorCoeff A z₀ (m - k)‖
        ≤ ∑ k ∈ Finset.range (m + 1), ρ ^ (m + 1) *
            (‖(k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀‖ *
              ‖propagatorCoeff A z₀ (m - k)‖) := by
          rw [← Finset.mul_sum]
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ norm_mul_le _ _)
    _ ≤ ∑ k ∈ Finset.range (m + 1),
          C * ρ * (ρ ^ (m - k) * ‖propagatorCoeff A z₀ (m - k)‖) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hpow : ρ ^ (m + 1) * (C / ρ ^ k) = C * ρ * ρ ^ (m - k) := by
          have hkpow : ρ ^ k ≠ 0 := pow_ne_zero k hρ.ne'
          have hsplit : ρ ^ (m + 1) = ρ * ρ ^ k * ρ ^ (m - k) := by
            rw [← pow_succ', ← pow_add, Nat.succ_add, Nat.add_sub_of_le hkm, Nat.succ_eq_add_one]
          rw [hsplit]
          field_simp [hkpow]
        calc
          ρ ^ (m + 1) * (‖(k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀‖ *
              ‖propagatorCoeff A z₀ (m - k)‖)
              ≤ ρ ^ (m + 1) * ((C / ρ ^ k) * ‖propagatorCoeff A z₀ (m - k)‖) := by
                gcongr; exact hA_coeff k
          _ = C * ρ * (ρ ^ (m - k) * ‖propagatorCoeff A z₀ (m - k)‖) := by
                rw [← mul_assoc, hpow, mul_assoc]
    _ = C * ρ * S := by
        rw [← Finset.mul_sum]
        congr 1
        simpa [S, Nat.add_sub_cancel] using
          (Finset.sum_range_reflect (fun j ↦ ρ ^ j * ‖propagatorCoeff A z₀ j‖) (m + 1))
    _ ≤ (Nat.ceil (C * ρ) : ℝ) * S :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil (C * ρ)) hS0

section Complete

variable [CompleteSpace B]

/-- **Cauchy--Bernoulli majorant bound** on the recursive propagator coefficients: if `A` is
complex differentiable on `ball z₀ ρ`, continuous on its closure, and bounded in norm by `C` on
`sphere z₀ ρ`, then `‖propagatorCoeff A z₀ n‖ ≤ ‖(1 : B)‖ * (n + 1) ^ ⌈C * ρ⌉₊ / ρ ^ n`. -/
theorem norm_propagatorCoeff_le_of_forall_mem_sphere_norm_le
    {A : ℂ → B} {z₀ : ℂ} {ρ C : ℝ} (hρ : 0 < ρ)
    (hA : DiffContOnCl ℂ A (ball z₀ ρ)) (hC : ∀ w ∈ sphere z₀ ρ, ‖A w‖ ≤ C) (n : ℕ) :
    ‖propagatorCoeff A z₀ n‖ ≤ ‖(1 : B)‖ * (n + 1 : ℝ) ^ Nat.ceil (C * ρ) / ρ ^ n := by
  set K := Nat.ceil (C * ρ)
  have hA_coeff (k : ℕ) : ‖(k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀‖ ≤ C / ρ ^ k := by
    have hk := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρ hA hC
    have hfac : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr k.factorial_pos
    rw [norm_smul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hfac, ← mul_div_assoc]
    exact hk
  let S : ℕ → ℝ := fun m ↦ ∑ j ∈ Finset.range (m + 1), ρ ^ j * ‖propagatorCoeff A z₀ j‖
  have hS (m : ℕ) : S m ≤ ‖(1 : B)‖ * (m + 1 : ℝ) ^ K := by
    induction m with
    | zero => simp [S]
    | succ m ih =>
      have hterm := norm_propagatorCoeff_succ_step hρ hA_coeff m
      have hm1 : (0 : ℝ) < m + 1 := by positivity
      have hbern : (m + 1 : ℝ) ^ K * (1 + (K : ℝ) * ((m + 1 : ℝ))⁻¹) ≤ (m + 2 : ℝ) ^ K := by
        calc
          (m + 1 : ℝ) ^ K * (1 + (K : ℝ) * ((m + 1 : ℝ))⁻¹)
              ≤ (m + 1 : ℝ) ^ K * (1 + ((m + 1 : ℝ))⁻¹) ^ K := by
                gcongr
                exact one_add_mul_le_pow (by linarith [inv_nonneg.mpr hm1.le]) K
          _ = ((m + 1 : ℝ) * (1 + ((m + 1 : ℝ))⁻¹)) ^ K := (mul_pow _ _ K).symm
          _ = (m + 2 : ℝ) ^ K := by congr 1; field_simp [hm1.ne']; ring
      calc
        S (m + 1) = S m + ρ ^ (m + 1) * ‖propagatorCoeff A z₀ (m + 1)‖ :=
          Finset.sum_range_succ _ (m + 1)
        _ ≤ S m * (1 + (K : ℝ) * ((m + 1 : ℝ))⁻¹) := by linarith [hterm]
        _ ≤ ‖(1 : B)‖ * (m + 1 : ℝ) ^ K * (1 + (K : ℝ) * ((m + 1 : ℝ))⁻¹) := by gcongr
        _ ≤ ‖(1 : B)‖ * (m + 2 : ℝ) ^ K := by rw [mul_assoc]; gcongr
        _ = ‖(1 : B)‖ * ((m + 1 : ℕ) + 1 : ℝ) ^ K := by push_cast; ring
  have hsingle : ρ ^ n * ‖propagatorCoeff A z₀ n‖ ≤ S n :=
    Finset.single_le_sum (fun j _ ↦ mul_nonneg (pow_nonneg hρ.le j) (norm_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  rw [le_div_iff₀ (pow_pos hρ n), mul_comm]
  exact hsingle.trans (hS n)

private theorem exists_subdisc_bound_of_mem_eball
    {A : ℂ → B} {z₀ z : ℂ} {r : ℝ≥0∞} (hA : DifferentiableOn ℂ A (eball z₀ r))
    (hz : z ∈ eball z₀ r) :
    ∃ (r₁ ρ C : ℝ) (K : ℕ), 0 < r₁ ∧ r₁ < ρ ∧ 0 ≤ C ∧ z ∈ ball z₀ r₁ ∧
      (∀ k, ‖(k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀‖ ≤ C / ρ ^ k) ∧
      ∀ n, ‖propagatorCoeff A z₀ n‖ ≤ ‖(1 : B)‖ * (n + 1 : ℝ) ^ K / ρ ^ n := by
  obtain ⟨ρ', hzρ', hρ'r⟩ := exists_between (mem_eball.mp hz)
  lift ρ' to ℝ≥0 using ne_top_of_lt hρ'r
  have hρ_pos : 0 < (ρ' : ℝ) := by
    exact_mod_cast pos_of_gt hzρ'
  have hz_ball : z ∈ ball z₀ ρ' := by
    rwa [← eball_coe, mem_eball]
  obtain ⟨r₁, hzr₁, hr₁ρ⟩ := exists_between (mem_ball_iff_norm.mp hz_ball)
  have hr₁_pos : 0 < r₁ := (norm_nonneg _).trans_lt hzr₁
  have hclosed : closedBall z₀ ρ' ⊆ eball z₀ r := fun w hw ↦ by
    rw [mem_eball, edist_dist]
    exact (ENNReal.ofReal_le_ofReal (mem_closedBall.mp hw)).trans_lt
      (by simpa [ENNReal.ofReal_coe_nnreal] using hρ'r)
  have hDiffCl : DiffContOnCl ℂ A (ball z₀ ρ') :=
    (hA.mono (closure_ball_subset_closedBall.trans hclosed)).diffContOnCl
  obtain ⟨C₀, hC₀⟩ := (isCompact_sphere z₀ ρ').exists_bound_of_continuousOn
    (hDiffCl.continuousOn.mono
      (by rw [closure_ball z₀ hρ_pos.ne']; exact sphere_subset_closedBall))
  set C := max C₀ 0
  have hC : ∀ w ∈ sphere z₀ ρ', ‖A w‖ ≤ C :=
    fun w hw ↦ (hC₀ w hw).trans (le_max_left C₀ 0)
  refine ⟨r₁, ρ', C, Nat.ceil (C * ρ'), hr₁_pos, hr₁ρ, le_max_right C₀ 0,
    mem_ball_iff_norm.mpr hzr₁, fun k ↦ ?_,
    norm_propagatorCoeff_le_of_forall_mem_sphere_norm_le hρ_pos hDiffCl hC⟩
  have hk := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρ_pos hDiffCl hC
  have hfac : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr k.factorial_pos
  rw [norm_smul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hfac, ← mul_div_assoc]
  exact hk

/-- The power series defining `propagatorSeries A z₀ z` is norm-summable at every point of an
extended open ball on which `A` is complex differentiable. -/
theorem summable_norm_pow_smul_propagatorCoeff_of_mem_eball
    {A : ℂ → B} {z₀ z : ℂ} {r : ℝ≥0∞} (hA : DifferentiableOn ℂ A (eball z₀ r))
    (hz : z ∈ eball z₀ r) :
    Summable (fun n : ℕ ↦ ‖(z - z₀) ^ n • propagatorCoeff A z₀ n‖) := by
  obtain ⟨r₁, ρ, -, K, hr₁, hr₁ρ, -, hzr₁, -, hbound⟩ := exists_subdisc_bound_of_mem_eball hA hz
  have hρ : 0 < ρ := hr₁.trans hr₁ρ
  have hq : ‖r₁ / ρ‖ < 1 := by
    rw [Real.norm_of_nonneg (div_nonneg hr₁.le hρ.le)]
    exact (div_lt_one hρ).mpr hr₁ρ
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    ((summable_add_pow_mul_geometric_of_norm_lt_one (1 : ℝ) K hq).mul_left ‖(1 : B)‖)
  calc
    ‖(z - z₀) ^ n • propagatorCoeff A z₀ n‖
        = ‖z - z₀‖ ^ n * ‖propagatorCoeff A z₀ n‖ := by rw [norm_smul, norm_pow]
    _ ≤ r₁ ^ n * (‖(1 : B)‖ * (n + 1 : ℝ) ^ K / ρ ^ n) := by
        gcongr
        · exact (mem_ball_iff_norm.mp hzr₁).le
        · exact hbound n
    _ = ‖(1 : B)‖ * ((n + 1 : ℝ) ^ K * (r₁ / ρ) ^ n) := by rw [div_pow]; ring

private theorem tsum_deriv_propagator_eq_mul
    {A : ℂ → B} {z₀ z : ℂ} {r : ℝ≥0∞} (hA : DifferentiableOn ℂ A (eball z₀ r))
    (hz : z ∈ eball z₀ r) {ρ C : ℝ} (hρ : 0 < ρ) (hzρ : ‖z - z₀‖ < ρ)
    (hA_coeff : ∀ k, ‖(k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀‖ ≤ C / ρ ^ k)
    (hg'_sum : Summable (fun n : ℕ ↦ ((n : ℂ) * (z - z₀) ^ (n - 1)) • propagatorCoeff A z₀ n)) :
    (∑' n : ℕ, ((n : ℂ) * (z - z₀) ^ (n - 1)) • propagatorCoeff A z₀ n) =
      A z * propagatorSeries A z₀ z := by
  have hf_sum :
      Summable (fun k : ℕ ↦ ‖(k.factorial : ℂ)⁻¹ • (z - z₀) ^ k • iteratedDeriv k A z₀‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ by
      rw [smul_comm, norm_smul, norm_pow]
      calc
        ‖z - z₀‖ ^ k * ‖(k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀‖
            ≤ ‖z - z₀‖ ^ k * (C / ρ ^ k) := by gcongr; exact hA_coeff k
        _ = C * (‖z - z₀‖ / ρ) ^ k := by rw [div_pow]; ring)
      ((summable_geometric_of_lt_one (div_nonneg (norm_nonneg _) hρ.le)
        ((div_lt_one hρ).mpr hzρ)).mul_left C)
  rw [hg'_sum.tsum_eq_zero_add]
  simp only [CharP.cast_eq_zero, zero_mul, zero_smul, zero_add, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one]
  simp_rw [natCast_succ_smul_pow_smul_propagatorCoeff_succ]
  rw [← tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf_sum
    (summable_norm_pow_smul_propagatorCoeff_of_mem_eball hA hz),
    Complex.taylorSeries_eq_on_eball hA hz, propagatorSeries_def]

/-- On any extended open ball where `A` is complex differentiable, `propagatorSeries A z₀`
satisfies the differential equation `Φ' z = A z * Φ z`. -/
theorem hasDerivAt_propagatorSeries_of_mem_eball
    {A : ℂ → B} {z₀ z : ℂ} {r : ℝ≥0∞} (hA : DifferentiableOn ℂ A (eball z₀ r))
    (hz : z ∈ eball z₀ r) :
    HasDerivAt (propagatorSeries A z₀) (A z * propagatorSeries A z₀ z) z := by
  obtain ⟨r₁, ρ, C, K, hr₁, hr₁ρ, -, hzr₁, hA_coeff, hbound⟩ :=
    exists_subdisc_bound_of_mem_eball hA hz
  have hρ : 0 < ρ := hr₁.trans hr₁ρ
  let g : ℕ → ℂ → B := fun n w ↦ (w - z₀) ^ n • propagatorCoeff A z₀ n
  let g' : ℕ → ℂ → B := fun n w ↦ ((n : ℂ) * (w - z₀) ^ (n - 1)) • propagatorCoeff A z₀ n
  let u : ℕ → ℝ := fun n ↦ (‖(1 : B)‖ / ρ) * ((n + 1 : ℝ) ^ (K + 1) * (r₁ / ρ) ^ (n - 1))
  have hg : ∀ n w, w ∈ ball z₀ r₁ → HasDerivAt (g n) (g' n w) w := fun n w _ ↦ by
    simpa [g, g'] using (((hasDerivAt_id w).sub_const z₀).pow n).smul_const
      (propagatorCoeff A z₀ n)
  have hg' : ∀ n w, w ∈ ball z₀ r₁ → ‖g' n w‖ ≤ u n := fun n w hw ↦ by
    cases n with
    | zero => simp only [g', u, CharP.cast_eq_zero, zero_mul, zero_smul, norm_zero]; positivity
    | succ m =>
      have hb : ‖propagatorCoeff A z₀ (m + 1)‖ ≤ ‖(1 : B)‖ * (m + 2 : ℝ) ^ K / ρ ^ (m + 1) := by
        convert hbound (m + 1) using 3; push_cast; ring
      calc
        ‖g' (m + 1) w‖ = (m + 1 : ℝ) * ‖w - z₀‖ ^ m * ‖propagatorCoeff A z₀ (m + 1)‖ := by
          dsimp only [g']
          rw [Nat.add_sub_cancel, norm_smul, norm_mul, norm_pow, Complex.norm_natCast,
            Nat.cast_add, Nat.cast_one]
        _ ≤ (m + 2 : ℝ) * r₁ ^ m * (‖(1 : B)‖ * (m + 2 : ℝ) ^ K / ρ ^ (m + 1)) := by
          gcongr
          · linarith
          · exact (mem_ball_iff_norm.mp hw).le
        _ = u (m + 1) := by
          simp only [u, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_assoc,
            one_add_one_eq_two, pow_succ', div_pow]
          field_simp [hρ.ne']
  have hu : Summable u := (summable_nat_add_iff 1).mp <|
    ((summable_add_pow_mul_geometric_of_norm_lt_one (2 : ℝ) (K + 1)
      (by rw [Real.norm_of_nonneg (div_nonneg hr₁.le hρ.le)]; exact (div_lt_one hρ).mpr hr₁ρ))
        |>.mul_left (‖(1 : B)‖ / ρ)).congr
        fun m ↦ by simp only [u, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]; ring
  have hg0 : Summable (fun n ↦ g n z₀) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn ↦ by
      simp [g, zero_pow (Finset.notMem_singleton.mp hn)]
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball z₀ r₁).isPreconnected
    hg hg' (mem_ball_self hr₁) hg0 hzr₁
  have hg'_sum : Summable (fun n ↦ g' n z) := .of_norm_bounded hu fun n ↦ hg' n z hzr₁
  have hprod := tsum_deriv_propagator_eq_mul hA hz hρ ((mem_ball_iff_norm.mp hzr₁).trans hr₁ρ)
    hA_coeff hg'_sum
  rwa [← funext (propagatorSeries_def A z₀), hprod] at hderiv

/-- On any extended open ball where `A` is complex differentiable, `propagatorSeries A z₀` is
analytic. -/
theorem analyticOnNhd_propagatorSeries_eball
    {A : ℂ → B} {z₀ : ℂ} {r : ℝ≥0∞} (hA : DifferentiableOn ℂ A (eball z₀ r)) :
    AnalyticOnNhd ℂ (propagatorSeries A z₀) (eball z₀ r) := by
  have hdiff : DifferentiableOn ℂ (propagatorSeries A z₀) (eball z₀ r) := fun z hz ↦
    (hasDerivAt_propagatorSeries_of_mem_eball hA hz).differentiableAt.differentiableWithinAt
  exact hdiff.analyticOnNhd isOpen_eball

/-- On any open disc `ball z₀ r` where `A` is complex differentiable, `propagatorSeries A z₀`
satisfies `Φ' z = A z * Φ z`. -/
theorem hasDerivAt_propagatorSeries_of_mem_ball
    {A : ℂ → B} {z₀ z : ℂ} {r : ℝ} (hA : DifferentiableOn ℂ A (ball z₀ r))
    (hz : z ∈ ball z₀ r) :
    HasDerivAt (propagatorSeries A z₀) (A z * propagatorSeries A z₀ z) z := by
  rw [← eball_ofReal] at hA hz
  exact hasDerivAt_propagatorSeries_of_mem_eball hA hz

/-- On any open disc `ball z₀ r` where `A` is complex differentiable, `propagatorSeries A z₀`
is analytic. -/
theorem analyticOnNhd_propagatorSeries_ball
    {A : ℂ → B} {z₀ : ℂ} {r : ℝ} (hA : DifferentiableOn ℂ A (ball z₀ r)) :
    AnalyticOnNhd ℂ (propagatorSeries A z₀) (ball z₀ r) := by
  rw [← eball_ofReal] at hA ⊢
  exact analyticOnNhd_propagatorSeries_eball hA

/-- For an entire coefficient family `A : ℂ → B`, `propagatorSeries A z₀` solves
`Φ' z = A z * Φ z` on all of `ℂ`. -/
theorem hasDerivAt_propagatorSeries_of_differentiable
    {A : ℂ → B} (hA : Differentiable ℂ A) (z₀ z : ℂ) :
    HasDerivAt (propagatorSeries A z₀) (A z * propagatorSeries A z₀ z) z :=
  hasDerivAt_propagatorSeries_of_mem_eball
    (r := ⊤) (by simpa [eball_top] using hA.differentiableOn) (by simp [eball_top])

end Complete

end Propagator

section LinearSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex subspace of functions `U → E` admitting an ambient representative that solves the
linear differential system `Y' z = A z (Y z)` at every point of `U`. -/
def linearODESolutionSpace (A : ℂ → E →L[ℂ] E) (U : Set ℂ) : Submodule ℂ (U → E) where
  carrier := {y | ∃ Y : ℂ → E, (∀ z : U, Y z = y z) ∧ ∀ z ∈ U, HasDerivAt Y (A z (Y z)) z}
  zero_mem' := ⟨0, fun _ ↦ rfl, fun z _ ↦ by simp⟩
  add_mem' := by
    rintro y₁ y₂ ⟨Y₁, hY₁, hd₁⟩ ⟨Y₂, hY₂, hd₂⟩
    refine ⟨Y₁ + Y₂, fun z ↦ by simp [hY₁ z, hY₂ z], fun z hz ↦ ?_⟩
    simpa [map_add] using (hd₁ z hz).add (hd₂ z hz)
  smul_mem' := by
    rintro c y ⟨Y, hY, hd⟩
    refine ⟨c • Y, fun z ↦ by simp [hY z], fun z hz ↦ ?_⟩
    simpa [map_smul] using (hd z hz).const_smul c

/-- Membership in `linearODESolutionSpace` means having an ambient solution extending `y`. -/
theorem mem_linearODESolutionSpace_iff {A : ℂ → E →L[ℂ] E} {U : Set ℂ} {y : U → E} :
    y ∈ linearODESolutionSpace A U ↔
      ∃ Y : ℂ → E, (∀ z : U, Y z = y z) ∧ ∀ z ∈ U, HasDerivAt Y (A z (Y z)) z := by rfl

/-- On an open domain `U`, membership in `linearODESolutionSpace A U` is equivalent to the zero
extension solving `Y' z = A z (Y z)` at every point of `U`. -/
theorem mem_linearODESolutionSpace_iff_of_isOpen {A : ℂ → E →L[ℂ] E} {U : Set ℂ}
    (hU : IsOpen U) {y : U → E} :
    y ∈ linearODESolutionSpace A U ↔
      ∀ z : U, HasDerivAt (Function.extend Subtype.val y 0) (A z (y z)) z := by
  constructor
  · rintro ⟨Y, hY, hd⟩ ⟨z, hz⟩
    have heq : Function.extend Subtype.val y 0 =ᶠ[𝓝 z] Y := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact (Subtype.val_injective.extend_apply y 0 ⟨w, hw⟩).trans (hY ⟨w, hw⟩).symm
    simpa [hY ⟨z, hz⟩] using (hd z hz).congr_of_eventuallyEq heq
  · intro hd
    refine ⟨Function.extend Subtype.val y 0,
      fun z ↦ Subtype.val_injective.extend_apply y 0 z, fun z hz ↦ ?_⟩
    simpa [Subtype.val_injective.extend_apply y 0 ⟨z, hz⟩] using hd ⟨z, hz⟩

namespace linearODESolutionSpace

/-- Restrict an ambient solution of `Y' z = A z (Y z)` on `U` to `linearODESolutionSpace A U`. -/
def of (A : ℂ → E →L[ℂ] E) (U : Set ℂ) (Y : ℂ → E)
    (hY : ∀ z ∈ U, HasDerivAt Y (A z (Y z)) z) : linearODESolutionSpace A U :=
  ⟨U.domRestrict Y, Y, fun _ ↦ rfl, hY⟩

/-- Restricting an ambient solution evaluates pointwise on `U`. -/
@[simp]
theorem of_apply (A : ℂ → E →L[ℂ] E) (U : Set ℂ) (Y : ℂ → E)
    (hY : ∀ z ∈ U, HasDerivAt Y (A z (Y z)) z) (z : U) :
    (of A U Y hY).val z = Y z := by rfl

/-- Evaluation at a point `z₀ ∈ U` as a `ℂ`-linear map on `linearODESolutionSpace A U`. -/
def eval (A : ℂ → E →L[ℂ] E) {U : Set ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    linearODESolutionSpace A U →ₗ[ℂ] E :=
  (LinearMap.proj ⟨z₀, hz₀⟩).comp (linearODESolutionSpace A U).subtype

/-- Evaluation at `z₀` reads the value of the restricted solution at `⟨z₀, hz₀⟩`. -/
@[simp]
theorem eval_apply (A : ℂ → E →L[ℂ] E) {U : Set ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (y : linearODESolutionSpace A U) :
    eval A hz₀ y = y.val ⟨z₀, hz₀⟩ := by rfl

/-- On an open preconnected domain `U` where `A` is continuous, evaluation at any `z₀ ∈ U` is
injective on `linearODESolutionSpace A U`. -/
theorem eval_injective_of_isPreconnected {A : ℂ → E →L[ℂ] E} {U : Set ℂ}
    (hU : IsOpen U) (hU' : IsPreconnected U) (hA : ContinuousOn A U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    Injective (eval A hz₀) := by
  intro y₁ y₂ heq
  obtain ⟨Y₁, hY₁, hd₁⟩ := y₁.property
  obtain ⟨Y₂, hY₂, hd₂⟩ := y₂.property
  apply Subtype.ext
  ext ⟨z, hz⟩
  have h0 : Y₁ z₀ = Y₂ z₀ := by
    rw [hY₁ ⟨z₀, hz₀⟩, hY₂ ⟨z₀, hz₀⟩]
    exact heq
  rw [← hY₁ ⟨z, hz⟩, ← hY₂ ⟨z, hz⟩]
  exact hU.eqOn_of_hasDerivAt_clm_apply hU' hA hd₁ hd₂ hz₀ h0 hz

section Complete

variable [CompleteSpace E]

/-- On an open domain `U`, the zero extension of any element of `linearODESolutionSpace A U` is
analytic on `U`. -/
theorem analyticOnNhd_extend {A : ℂ → E →L[ℂ] E} {U : Set ℂ} (hU : IsOpen U)
    (y : linearODESolutionSpace A U) :
    AnalyticOnNhd ℂ (Function.extend Subtype.val y.val 0) U := by
  have hd := (mem_linearODESolutionSpace_iff_of_isOpen hU).mp y.property
  have hdiff : DifferentiableOn ℂ (Function.extend Subtype.val y.val 0) U :=
    fun z hz ↦ (hd ⟨z, hz⟩).differentiableAt.differentiableWithinAt
  exact hdiff.analyticOnNhd hU

end Complete

end linearODESolutionSpace

section CompleteSystem

variable [CompleteSpace E]

/-- Applying `propagatorSeries A z₀` to an initial vector `y₀ : E` solves the linear system
`y' z = A z (y z)` on `eball z₀ r`. -/
theorem hasDerivAt_propagatorSeries_apply_of_mem_eball
    {A : ℂ → E →L[ℂ] E} {z₀ z : ℂ} {r : ℝ≥0∞}
    (hA : DifferentiableOn ℂ A (eball z₀ r)) (hz : z ∈ eball z₀ r) (y₀ : E) :
    HasDerivAt (fun w ↦ propagatorSeries A z₀ w y₀)
      (A z (propagatorSeries A z₀ z y₀)) z := by
  simpa [Function.comp_def] using (ContinuousLinearMap.apply ℂ E y₀).hasFDerivAt.comp_hasDerivAt z
    (hasDerivAt_propagatorSeries_of_mem_eball hA hz)

/-- Applying `propagatorSeries A z₀` to an initial vector `y₀ : E` solves the linear system
`y' z = A z (y z)` on `ball z₀ r`. -/
theorem hasDerivAt_propagatorSeries_apply_of_mem_ball
    {A : ℂ → E →L[ℂ] E} {z₀ z : ℂ} {r : ℝ}
    (hA : DifferentiableOn ℂ A (ball z₀ r)) (hz : z ∈ ball z₀ r) (y₀ : E) :
    HasDerivAt (fun w ↦ propagatorSeries A z₀ w y₀)
      (A z (propagatorSeries A z₀ z y₀)) z := by
  rw [← eball_ofReal] at hA hz
  exact hasDerivAt_propagatorSeries_apply_of_mem_eball hA hz y₀

/-- **Existence and uniqueness for holomorphic linear operator systems on open discs.**
For any `A : ℂ → E →L[ℂ] E` complex differentiable on `ball z₀ r` and any `y₀ : E`, there exists a
function `y : ℂ → E` analytic on `ball z₀ r` solving `y' z = A z (y z)` on `ball z₀ r` with
`y z₀ = y₀`, and any solution on `ball z₀ r` with `w z₀ = y₀` agrees with `y` on `ball z₀ r`.
When `0 < r`, `z₀ ∈ ball z₀ r` and this is Cauchy's local initial-value theorem on `ball z₀ r`;
when `r ≤ 0`, `ball z₀ r` is empty so the domain conditions and `EqOn` uniqueness hold vacuously
while `y z₀ = y₀` still holds at `z₀`. -/
theorem exists_analyticOnNhd_ball_hasDerivAt_clm_apply
    {A : ℂ → E →L[ℂ] E} {z₀ : ℂ} {r : ℝ}
    (hA : DifferentiableOn ℂ A (ball z₀ r)) (y₀ : E) :
    ∃ y : ℂ → E, AnalyticOnNhd ℂ y (ball z₀ r) ∧
      (∀ z ∈ ball z₀ r, HasDerivAt y (A z (y z)) z) ∧
      y z₀ = y₀ ∧
      ∀ w : ℂ → E, (∀ z ∈ ball z₀ r, HasDerivAt w (A z (w z)) z) →
        w z₀ = y₀ → EqOn w y (ball z₀ r) := by
  refine ⟨fun z ↦ propagatorSeries A z₀ z y₀, ?_, ?_, by simp, ?_⟩
  · intro z hz
    exact ((ContinuousLinearMap.apply ℂ E y₀).analyticAt _).comp
      (analyticOnNhd_propagatorSeries_ball hA z hz)
  · exact fun z hz ↦ hasDerivAt_propagatorSeries_apply_of_mem_ball hA hz y₀
  · intro w hw hw0 z hz
    have hr : 0 < r := pos_of_mem_ball hz
    exact isOpen_ball.eqOn_of_hasDerivAt_clm_apply (convex_ball z₀ r).isPreconnected
      hA.continuousOn hw
      (fun p hp ↦ hasDerivAt_propagatorSeries_apply_of_mem_ball hA hp y₀)
      (mem_ball_self hr) (by simp [hw0]) hz

namespace linearODESolutionSpace

/-- On an extended open disc `eball z₀ r` of positive radius where `A` is complex differentiable,
evaluation at `z₀` is a `ℂ`-linear isomorphism `linearODESolutionSpace A (eball z₀ r) ≃ₗ[ℂ] E`. -/
def evalEquivEball {A : ℂ → E →L[ℂ] E} {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hA : DifferentiableOn ℂ A (eball z₀ r)) :
    linearODESolutionSpace A (eball z₀ r) ≃ₗ[ℂ] E :=
  LinearEquiv.ofBijective (eval A (mem_eball_self hr))
    ⟨eval_injective_of_isPreconnected isOpen_eball
        (by
          rcases eq_or_ne r ⊤ with rfl | hr_ne
          · simpa [eball_top] using isPreconnected_univ
          · lift r to ℝ≥0 using hr_ne
            simpa [eball_coe] using (convex_ball z₀ r).isPreconnected)
        hA.continuousOn (mem_eball_self hr),
      fun y₀ ↦ ⟨of A (eball z₀ r) (fun z ↦ propagatorSeries A z₀ z y₀)
        (fun z hz ↦ hasDerivAt_propagatorSeries_apply_of_mem_eball hA hz y₀), by simp⟩⟩

/-- Forward evaluation of `evalEquivEball` reads the value at `z₀`. -/
@[simp]
theorem evalEquivEball_apply {A : ℂ → E →L[ℂ] E} {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hA : DifferentiableOn ℂ A (eball z₀ r)) (y : linearODESolutionSpace A (eball z₀ r)) :
    evalEquivEball hr hA y = y.val ⟨z₀, mem_eball_self hr⟩ := by rfl

/-- The inverse of `evalEquivEball` sends `y₀` to the propagator solution
`z ↦ propagatorSeries A z₀ z y₀`. -/
@[simp]
theorem evalEquivEball_symm_apply {A : ℂ → E →L[ℂ] E} {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hA : DifferentiableOn ℂ A (eball z₀ r)) (y₀ : E) (z : eball z₀ r) :
    ((evalEquivEball hr hA).symm y₀).val z = propagatorSeries A z₀ z y₀ := by
  let sol := of A (eball z₀ r) (fun w ↦ propagatorSeries A z₀ w y₀)
    (fun w hw ↦ hasDerivAt_propagatorSeries_apply_of_mem_eball hA hw y₀)
  have hsol : evalEquivEball hr hA sol = y₀ := by simp [sol]
  conv_lhs => rw [← hsol, LinearEquiv.symm_apply_apply]
  exact of_apply A (eball z₀ r) _ _ z

/-- On an open disc `ball z₀ r` of positive radius where `A` is complex differentiable, evaluation
at the center `z₀` is a `ℂ`-linear isomorphism `linearODESolutionSpace A (ball z₀ r) ≃ₗ[ℂ] E`. -/
def evalEquivBall {A : ℂ → E →L[ℂ] E} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hA : DifferentiableOn ℂ A (ball z₀ r)) :
    linearODESolutionSpace A (ball z₀ r) ≃ₗ[ℂ] E :=
  eball_ofReal (x := z₀) (ε := r) ▸
    evalEquivEball (ENNReal.ofReal_pos.mpr hr) (by rwa [eball_ofReal])

/-- Forward evaluation of `evalEquivBall` reads the value at `z₀`. -/
@[simp]
theorem evalEquivBall_apply {A : ℂ → E →L[ℂ] E} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hA : DifferentiableOn ℂ A (ball z₀ r)) (y : linearODESolutionSpace A (ball z₀ r)) :
    evalEquivBall hr hA y = y.val ⟨z₀, mem_ball_self hr⟩ := by
  have hAe : DifferentiableOn ℂ A (eball z₀ (ENNReal.ofReal r)) := by rwa [eball_ofReal]
  have key : ∀ (U : Set ℂ) (hU : eball z₀ (ENNReal.ofReal r) = U) (hz₀ : z₀ ∈ U)
      (y : linearODESolutionSpace A U),
      (hU ▸ evalEquivEball (ENNReal.ofReal_pos.mpr hr) hAe) y = y.val ⟨z₀, hz₀⟩ := by
    rintro _ rfl _ y
    exact evalEquivEball_apply (ENNReal.ofReal_pos.mpr hr) hAe y
  exact key (ball z₀ r) eball_ofReal (mem_ball_self hr) y

/-- The inverse of `evalEquivBall` sends `y₀` to the propagator solution
`z ↦ propagatorSeries A z₀ z y₀`. -/
@[simp]
theorem evalEquivBall_symm_apply {A : ℂ → E →L[ℂ] E} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hA : DifferentiableOn ℂ A (ball z₀ r)) (y₀ : E) (z : ball z₀ r) :
    ((evalEquivBall hr hA).symm y₀).val z = propagatorSeries A z₀ z y₀ := by
  have hAe : DifferentiableOn ℂ A (eball z₀ (ENNReal.ofReal r)) := by rwa [eball_ofReal]
  have key : ∀ (U : Set ℂ) (hU : eball z₀ (ENNReal.ofReal r) = U) (z : U),
      ((hU ▸ evalEquivEball (ENNReal.ofReal_pos.mpr hr) hAe).symm y₀).val z =
        propagatorSeries A z₀ z y₀ := by
    rintro _ rfl z
    exact evalEquivEball_symm_apply (ENNReal.ofReal_pos.mpr hr) hAe y₀ z
  exact key (ball z₀ r) eball_ofReal z

end linearODESolutionSpace

/-- On an open disc `ball z₀ r` of positive radius where `A` is complex differentiable, the
dimension of `linearODESolutionSpace A (ball z₀ r)` equals `Module.finrank ℂ E`. -/
theorem finrank_linearODESolutionSpace_ball
    {A : ℂ → E →L[ℂ] E} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hA : DifferentiableOn ℂ A (ball z₀ r)) :
    Module.finrank ℂ (linearODESolutionSpace A (ball z₀ r)) = Module.finrank ℂ E :=
  (linearODESolutionSpace.evalEquivBall hr hA).finrank_eq

end CompleteSystem

end LinearSystem

section MatrixSystem

variable {ι : Type*} [Fintype ι]

/-- **Existence and uniqueness for holomorphic matrix differential systems on open discs.**
For a matrix family `M : ℂ → Matrix ι ι ℂ` with holomorphic entries on `ball z₀ r` and any vector
`y₀ : ι → ℂ`, there exists a function `y : ℂ → ι → ℂ` analytic on `ball z₀ r` solving
`y' z = M z *ᵥ y z` on `ball z₀ r` with `y z₀ = y₀`, unique on `ball z₀ r` among solutions taking
value `y₀` at `z₀`. When `0 < r`, `z₀ ∈ ball z₀ r` and this is Cauchy's disc initial-value theorem;
when `r ≤ 0`, `ball z₀ r` is empty so the differential equation and `EqOn` uniqueness on
`ball z₀ r` hold vacuously while `y z₀ = y₀` still holds. -/
theorem exists_analyticOnNhd_ball_hasDerivAt_mulVec
    {M : ℂ → Matrix ι ι ℂ} {z₀ : ℂ} {r : ℝ}
    (hM : ∀ i j, DifferentiableOn ℂ (fun z ↦ M z i j) (ball z₀ r)) (y₀ : ι → ℂ) :
    ∃ y : ℂ → ι → ℂ, AnalyticOnNhd ℂ y (ball z₀ r) ∧
      (∀ z ∈ ball z₀ r, HasDerivAt y (M z *ᵥ y z) z) ∧
      y z₀ = y₀ ∧
      ∀ w : ℂ → ι → ℂ, (∀ z ∈ ball z₀ r, HasDerivAt w (M z *ᵥ w z) z) →
        w z₀ = y₀ → EqOn w y (ball z₀ r) := by
  simpa only [Matrix.mulVecCLM_apply] using
    exists_analyticOnNhd_ball_hasDerivAt_clm_apply (Matrix.differentiableOn_mulVecCLM hM) y₀

/-- The complex subspace of functions `U → ι → ℂ` extending to ambient solutions of the matrix
differential system `Y' z = M z *ᵥ Y z` on `U`. -/
def matrixODESolutionSpace (M : ℂ → Matrix ι ι ℂ) (U : Set ℂ) : Submodule ℂ (U → ι → ℂ) :=
  linearODESolutionSpace (fun z ↦ (M z).mulVecCLM) U

/-- Membership in `matrixODESolutionSpace M U` means having an ambient solution of
`Y' z = M z *ᵥ Y z` on `U` extending `y`. -/
theorem mem_matrixODESolutionSpace_iff {M : ℂ → Matrix ι ι ℂ} {U : Set ℂ} {y : U → ι → ℂ} :
    y ∈ matrixODESolutionSpace M U ↔
      ∃ Y : ℂ → ι → ℂ, (∀ z : U, Y z = y z) ∧ ∀ z ∈ U, HasDerivAt Y (M z *ᵥ Y z) z := by
  simp [matrixODESolutionSpace, mem_linearODESolutionSpace_iff]

namespace matrixODESolutionSpace

/-- Restrict an ambient solution of `Y' z = M z *ᵥ Y z` on `U` to `matrixODESolutionSpace M U`. -/
def of (M : ℂ → Matrix ι ι ℂ) (U : Set ℂ) (Y : ℂ → ι → ℂ)
    (hY : ∀ z ∈ U, HasDerivAt Y (M z *ᵥ Y z) z) : matrixODESolutionSpace M U :=
  linearODESolutionSpace.of (fun z ↦ (M z).mulVecCLM) U Y fun z hz ↦ by simpa using hY z hz

/-- Restricting an ambient matrix-system solution evaluates pointwise on `U`. -/
@[simp]
theorem of_apply (M : ℂ → Matrix ι ι ℂ) (U : Set ℂ) (Y : ℂ → ι → ℂ)
    (hY : ∀ z ∈ U, HasDerivAt Y (M z *ᵥ Y z) z) (z : U) :
    (of M U Y hY).val z = Y z := by rfl

/-- Evaluation at `z₀ ∈ U` as a `ℂ`-linear map on `matrixODESolutionSpace M U`. -/
def eval (M : ℂ → Matrix ι ι ℂ) {U : Set ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    matrixODESolutionSpace M U →ₗ[ℂ] (ι → ℂ) :=
  linearODESolutionSpace.eval (fun z ↦ (M z).mulVecCLM) hz₀

/-- Evaluation at `z₀` reads the value of the restricted solution at `⟨z₀, hz₀⟩`. -/
@[simp]
theorem eval_apply (M : ℂ → Matrix ι ι ℂ) {U : Set ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (y : matrixODESolutionSpace M U) :
    eval M hz₀ y = y.val ⟨z₀, hz₀⟩ := by rfl

/-- On an open preconnected domain `U` where `M` has continuous entries, evaluation at any
`z₀ ∈ U` is injective on `matrixODESolutionSpace M U`. -/
theorem eval_injective_of_isPreconnected {M : ℂ → Matrix ι ι ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hU' : IsPreconnected U)
    (hM : ∀ i j, ContinuousOn (fun z ↦ M z i j) U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    Injective (eval M hz₀) :=
  linearODESolutionSpace.eval_injective_of_isPreconnected hU hU'
    (Matrix.continuousOn_mulVecCLM hM) hz₀

/-- On an open disc `ball z₀ r` of positive radius where `M` has holomorphic entries, evaluation at
`z₀` is a `ℂ`-linear isomorphism `matrixODESolutionSpace M (ball z₀ r) ≃ₗ[ℂ] (ι → ℂ)`. -/
def evalEquivBall {M : ℂ → Matrix ι ι ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hM : ∀ i j, DifferentiableOn ℂ (fun z ↦ M z i j) (ball z₀ r)) :
    matrixODESolutionSpace M (ball z₀ r) ≃ₗ[ℂ] (ι → ℂ) :=
  linearODESolutionSpace.evalEquivBall hr (Matrix.differentiableOn_mulVecCLM hM)

/-- Forward evaluation of `matrixODESolutionSpace.evalEquivBall` reads the value at `z₀`. -/
@[simp]
theorem evalEquivBall_apply {M : ℂ → Matrix ι ι ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hM : ∀ i j, DifferentiableOn ℂ (fun z ↦ M z i j) (ball z₀ r))
    (y : matrixODESolutionSpace M (ball z₀ r)) :
    evalEquivBall hr hM y = y.val ⟨z₀, mem_ball_self hr⟩ :=
  linearODESolutionSpace.evalEquivBall_apply hr (Matrix.differentiableOn_mulVecCLM hM) y

/-- The inverse of `matrixODESolutionSpace.evalEquivBall` sends `y₀` to the propagator solution
`z ↦ propagatorSeries (fun w ↦ (M w).mulVecCLM) z₀ z y₀`. -/
@[simp]
theorem evalEquivBall_symm_apply {M : ℂ → Matrix ι ι ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hM : ∀ i j, DifferentiableOn ℂ (fun z ↦ M z i j) (ball z₀ r))
    (y₀ : ι → ℂ) (z : ball z₀ r) :
    ((evalEquivBall hr hM).symm y₀).val z =
      propagatorSeries (fun w ↦ (M w).mulVecCLM) z₀ z y₀ :=
  linearODESolutionSpace.evalEquivBall_symm_apply hr (Matrix.differentiableOn_mulVecCLM hM) y₀ z

end matrixODESolutionSpace

/-- On an open disc `ball z₀ r` of positive radius where `M` has holomorphic entries, the dimension
of `matrixODESolutionSpace M (ball z₀ r)` is `Fintype.card ι`. -/
theorem finrank_matrixODESolutionSpace_ball
    {M : ℂ → Matrix ι ι ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hM : ∀ i j, DifferentiableOn ℂ (fun z ↦ M z i j) (ball z₀ r)) :
    Module.finrank ℂ (matrixODESolutionSpace M (ball z₀ r)) = Fintype.card ι := by
  rw [matrixODESolutionSpace,
    finrank_linearODESolutionSpace_ball hr (Matrix.differentiableOn_mulVecCLM hM),
    Module.finrank_pi]

end MatrixSystem

/-! Checks on zero-dimensional, constant, and nonconstant holomorphic matrix systems. -/

example (z₀ : ℂ) :
    Module.finrank ℂ
      (matrixODESolutionSpace (fun _ : ℂ ↦ (0 : Matrix (Fin 0) (Fin 0) ℂ)) (ball z₀ 1)) = 0 := by
  simpa using finrank_matrixODESolutionSpace_ball zero_lt_one (fun i _ ↦ Fin.elim0 i)

example (z₀ : ℂ) :
    Module.finrank ℂ
      (matrixODESolutionSpace (fun z : ℂ ↦ !![z, (1 : ℂ); 0, -z]) (ball z₀ 1)) = 2 := by
  have hM : ∀ i j : Fin 2,
      DifferentiableOn ℂ (fun z : ℂ ↦ (!![z, (1 : ℂ); 0, -z] : Matrix (Fin 2) (Fin 2) ℂ) i j)
        (ball z₀ 1) := by
    intro i j
    fin_cases i <;> fin_cases j <;> dsimp <;> fun_prop
  simpa using finrank_matrixODESolutionSpace_ball zero_lt_one hM

end TauCeti
