/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.LinearEquation
public import Mathlib.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Nat.Choose.Sum

/-!
# Linear differential equations in the complex domain at an ordinary point

At an ordinary point `z₀ ∈ ℂ`, a linear differential equation whose coefficients are holomorphic
on an open disc `Metric.eball z₀ r` (`0 < r ≤ ∞`) admits a unique holomorphic solution on the
entire disc for any prescribed initial data at `z₀`, and the Taylor series of that solution
around `z₀` converges on the whole disc `Metric.eball z₀ r`.

This file develops the theory at three levels of generality:

1. **First-order linear equations in a complex Banach space.** For `A : ℂ → E →L[ℂ] E` and
   `b : ℂ → E` holomorphic on `Metric.eball z₀ r`, the initial-value problem
   `y'(z) = A(z) y(z) + b(z)`, `y(z₀) = y₀` has a unique holomorphic solution on
   `Metric.eball z₀ r`, represented there by `TauCeti.linearODESeries` whose coefficients
   `TauCeti.linearODESeriesCoeff` satisfy the Cauchy-product recursion
   `(n + 1) • v_{n + 1} = ∑_{j ≤ n} A_{n - j}(v_j) + b_n`. On any preconnected open domain `U`,
   two holomorphic solutions agreeing at a point of `U` agree throughout `U`.

2. **Monic scalar equations of arbitrary positive order (`TauCeti.LinearEquation`).** Using the
   companion-system reduction of `TauCeti.LinearEquation`, the initial-jet evaluation map
   `LinearEquation.initialJet` is injective on every preconnected open domain, and is a linear
   isomorphism `E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ)` on every nonempty open disc (including `ℂ`),
   giving `Module.finrank ℂ E.solutionSpace = n`.

3. **Scalar second-order equations `w'' + f(z) w' + g(z) w = h(z)` (DLMF 2.7.1).** Specializing
   to second-order scalar equations gives the explicit two-step Taylor recursion
   `TauCeti.secondOrderODESeriesCoeff`, convergence of the scalar power series on the full open
   disc (`Metric.eball z₀ r`, `Metric.ball z₀ R`, and `ℂ` for entire coefficients), global
   uniqueness on preconnected open sets and for entire solutions, and the explicit expansion of
   every solution in terms of two homogeneous solutions with nonvanishing Wronskian at `z₀`.

## Main definitions

* `TauCeti.linearODESeriesCoeff`: recursive Taylor coefficients for `y' = A y + b` in a complex
  normed space.
* `TauCeti.linearODESeries`: the one-variable formal multilinear series associated with
  `linearODESeriesCoeff`.
* `TauCeti.LinearEquation.initialJetEquivEball`, `TauCeti.LinearEquation.initialJetEquivTop`:
  the initial-jet linear equivalences `E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ)` on open discs and `ℂ`.
* `TauCeti.secondOrderODESeriesCoeff`: recursive Taylor coefficients for `w'' + f w' + g w = h`.

## Main results

* `TauCeti.exists_hasFPowerSeriesOnBall_linearODE`,
  `TauCeti.existsUnique_differentiable_linearODE`: disc and global existence, uniqueness, and
  Taylor-series convergence for Banach-space linear differential equations.
* `TauCeti.LinearEquation.initialJet_injective`,
  `TauCeti.LinearEquation.finrank_solutionSpace_eball`,
  `TauCeti.LinearEquation.finrank_solutionSpace_top`: uniqueness on preconnected domains and
  dimension of the holomorphic solution space on discs and `ℂ`.
* `TauCeti.exists_hasFPowerSeriesOnBall_secondOrderODE`,
  `TauCeti.exists_hasFPowerSeriesOnBall_secondOrderODE_of_coeff`,
  `TauCeti.exists_differentiableOn_ball_secondOrderODE`,
  `TauCeti.existsUnique_differentiable_secondOrderODE`: existence, uniqueness, and whole-disc
  Taylor convergence for `w'' + f w' + g w = h` and `w'' + f w' + g w = 0`.
* `TauCeti.eqOn_linear_combination_of_secondOrderODE`,
  `TauCeti.eq_linear_combination_of_secondOrderODE`: representation of any solution as a linear
  combination of two homogeneous solutions with nonvanishing Wronskian at `z₀`.

## References

* [NIST Digital Library of Mathematical Functions](https://dlmf.nist.gov/2.7), §2.7(i),
  equation (2.7.1).
* Frank W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §1.
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, American Mathematical
  Society, 2012, §1.2 and §4.1.
-/

public noncomputable section

open Filter Metric Set TopologicalSpace
open scoped BigOperators ENNReal Matrix NNReal Nat Topology

namespace TauCeti

/-! ### First-order linear equations in a complex Banach space -/

section FirstOrderCoeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Recursive Taylor coefficients of the solution to `y'(z) = A(z) y(z) + b(z)` with `y(z₀) = y₀`,
expressed in terms of the Taylor coefficient sequences `Ac` of `A` and `bc` of `b` at `z₀`. -/
def linearODESeriesCoeff (Ac : ℕ → E →L[ℂ] E) (bc : ℕ → E) (y₀ : E) : ℕ → E
  | 0 => y₀
  | n + 1 => ((n : ℂ) + 1)⁻¹ •
      (∑ j : Fin (n + 1), Ac (n - j.1) (linearODESeriesCoeff Ac bc y₀ j.1) + bc n)

/-- The zeroth Taylor coefficient is the prescribed initial value. -/
@[simp]
theorem linearODESeriesCoeff_zero (Ac : ℕ → E →L[ℂ] E) (bc : ℕ → E) (y₀ : E) :
    linearODESeriesCoeff Ac bc y₀ 0 = y₀ := by
  rw [linearODESeriesCoeff]

/-- Each higher Taylor coefficient is determined by the Cauchy product of `Ac` with the preceding
coefficients plus the inhomogeneous coefficient `bc n`, divided by `n + 1`. -/
@[simp]
theorem linearODESeriesCoeff_succ (Ac : ℕ → E →L[ℂ] E) (bc : ℕ → E) (y₀ : E) (n : ℕ) :
    linearODESeriesCoeff Ac bc y₀ (n + 1) = ((n : ℂ) + 1)⁻¹ •
      (∑ j ∈ Finset.range (n + 1), Ac (n - j) (linearODESeriesCoeff Ac bc y₀ j) + bc n) := by
  rw [linearODESeriesCoeff, ← Fin.sum_univ_eq_sum_range]

/-- Undivided form of the Taylor recursion for `linearODESeriesCoeff`. -/
theorem smul_linearODESeriesCoeff_succ (Ac : ℕ → E →L[ℂ] E) (bc : ℕ → E) (y₀ : E) (n : ℕ) :
    ((n : ℂ) + 1) • linearODESeriesCoeff Ac bc y₀ (n + 1) =
      ∑ j ∈ Finset.range (n + 1), Ac (n - j) (linearODESeriesCoeff Ac bc y₀ j) + bc n := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [linearODESeriesCoeff_succ, smul_inv_smul₀ hn]

/-- A sequence equals `linearODESeriesCoeff Ac bc y₀` if and only if it has initial value `y₀`
and satisfies the undivided first-order Cauchy-product recursion. -/
theorem eq_linearODESeriesCoeff_iff {Ac : ℕ → E →L[ℂ] E} {bc v : ℕ → E} {y₀ : E} :
    v = linearODESeriesCoeff Ac bc y₀ ↔
      v 0 = y₀ ∧ ∀ n : ℕ, ((n : ℂ) + 1) • v (n + 1) =
        ∑ j ∈ Finset.range (n + 1), Ac (n - j) (v j) + bc n := by
  refine ⟨fun h ↦ ?_, fun ⟨h0, hrec⟩ ↦ funext fun n ↦ ?_⟩
  · subst h
    exact ⟨linearODESeriesCoeff_zero Ac bc y₀, smul_linearODESeriesCoeff_succ Ac bc y₀⟩
  · induction n using Nat.strong_induction_on with
    | ind n ih =>
      rcases n with _ | n
      · exact h0.trans (linearODESeriesCoeff_zero Ac bc y₀).symm
      · have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        rw [linearODESeriesCoeff_succ, ← inv_smul_smul₀ hn (v (n + 1)), hrec n]
        congr 2
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [ih j (Finset.mem_range.mp hj)]

/-- Zero initial value and zero forcing produce identically zero Taylor coefficients. -/
@[simp]
theorem linearODESeriesCoeff_zero_zero (Ac : ℕ → E →L[ℂ] E) :
    linearODESeriesCoeff Ac 0 0 = 0 := by
  symm
  rw [eq_linearODESeriesCoeff_iff]
  simp

/-- The recursive Taylor coefficients depend additively on the forcing sequence and initial
value. -/
theorem linearODESeriesCoeff_add (Ac : ℕ → E →L[ℂ] E) (bc₁ bc₂ : ℕ → E) (y₁ y₂ : E) :
    linearODESeriesCoeff Ac (bc₁ + bc₂) (y₁ + y₂) =
      linearODESeriesCoeff Ac bc₁ y₁ + linearODESeriesCoeff Ac bc₂ y₂ := by
  symm
  rw [eq_linearODESeriesCoeff_iff]
  refine ⟨by simp, fun n ↦ ?_⟩
  simp only [Pi.add_apply, smul_add, smul_linearODESeriesCoeff_succ, map_add,
    Finset.sum_add_distrib]
  abel

/-- The recursive Taylor coefficients commute with complex scalar multiplication of the forcing
sequence and initial value. -/
theorem linearODESeriesCoeff_smul (Ac : ℕ → E →L[ℂ] E) (c : ℂ) (bc : ℕ → E) (y₀ : E) :
    linearODESeriesCoeff Ac (c • bc) (c • y₀) = c • linearODESeriesCoeff Ac bc y₀ := by
  symm
  rw [eq_linearODESeriesCoeff_iff]
  refine ⟨by simp, fun n ↦ ?_⟩
  simp only [Pi.smul_apply, smul_comm ((n : ℂ) + 1) c, smul_linearODESeriesCoeff_succ, map_smul,
    ← Finset.smul_sum, smul_add]

/-- The one-variable formal multilinear series with coefficients `linearODESeriesCoeff Ac bc y₀`. -/
def linearODESeries (Ac : ℕ → E →L[ℂ] E) (bc : ℕ → E) (y₀ : E) :
    FormalMultilinearSeries ℂ ℂ E :=
  fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (linearODESeriesCoeff Ac bc y₀ n)

/-- The `n`-th coefficient of `linearODESeries` is `linearODESeriesCoeff Ac bc y₀ n`. -/
@[simp]
theorem coeff_linearODESeries (Ac : ℕ → E →L[ℂ] E) (bc : ℕ → E) (y₀ : E) (n : ℕ) :
    (linearODESeries Ac bc y₀).coeff n = linearODESeriesCoeff Ac bc y₀ n := by
  simp [linearODESeries, FormalMultilinearSeries.coeff]

/-- Evaluating the `n`-th homogeneous term of `linearODESeries` on a constant tuple `(w, …, w)`
yields `w ^ n • linearODESeriesCoeff Ac bc y₀ n`. -/
theorem linearODESeries_apply (Ac : ℕ → E →L[ℂ] E) (bc : ℕ → E) (y₀ : E) (n : ℕ) (w : ℂ) :
    linearODESeries Ac bc y₀ n (fun _ ↦ w) = w ^ n • linearODESeriesCoeff Ac bc y₀ n := by
  simp

/-- The operator norm of the `n`-th term of `linearODESeries` equals the norm of its `n`-th
vector coefficient. -/
theorem norm_linearODESeries (Ac : ℕ → E →L[ℂ] E) (bc : ℕ → E) (y₀ : E) (n : ℕ) :
    ‖linearODESeries Ac bc y₀ n‖ = ‖linearODESeriesCoeff Ac bc y₀ n‖ :=
  ContinuousMultilinearMap.norm_mkPiRing _

/-- Inductive step for the Cauchy majorant estimate on `linearODESeriesCoeff`. -/
private theorem norm_linearODESeriesCoeff_succ_mul_pow_le {Ac : ℕ → E →L[ℂ] E} {bc : ℕ → E}
    {y₀ : E} {R M B : ℝ} (hR : 0 < R)
    (hAc : ∀ m, ‖Ac m‖ * R ^ m ≤ M) (hbc : ∀ m, ‖bc m‖ * R ^ m ≤ B) {n : ℕ}
    (ih : ∀ j < n + 1, ‖linearODESeriesCoeff Ac bc y₀ j‖ * R ^ j ≤
      max ‖y₀‖ (B * R) * ((j + ⌈M * R⌉₊).choose ⌈M * R⌉₊ : ℝ)) :
    ‖linearODESeriesCoeff Ac bc y₀ (n + 1)‖ * R ^ (n + 1) ≤
      max ‖y₀‖ (B * R) * ((n + 1 + ⌈M * R⌉₊).choose ⌈M * R⌉₊ : ℝ) := by
  have hM : 0 ≤ M := (norm_nonneg (Ac 0)).trans (by simpa using hAc 0)
  set k : ℕ := ⌈M * R⌉₊
  set C : ℝ := max ‖y₀‖ (B * R)
  have hC0 : 0 ≤ C := (norm_nonneg y₀).trans (le_max_left _ _)
  have hk : M * R ≤ k := Nat.le_ceil (M * R)
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [← mul_le_mul_iff_right₀ hn_pos]
  have hrec := congrArg (fun x ↦ ‖x‖ * R ^ (n + 1)) (smul_linearODESeriesCoeff_succ Ac bc y₀ n)
  have hnorm_n : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
  rw [norm_smul, hnorm_n] at hrec
  have hstep : ((n : ℝ) + 1) * (‖linearODESeriesCoeff Ac bc y₀ (n + 1)‖ * R ^ (n + 1)) ≤
      (∑ j ∈ Finset.range (n + 1), ‖Ac (n - j)‖ * ‖linearODESeriesCoeff Ac bc y₀ j‖) *
          R ^ (n + 1) + ‖bc n‖ * R ^ (n + 1) := by
    rw [← add_mul, ← mul_assoc, hrec]
    gcongr
    exact (norm_add_le _ _).trans (add_le_add_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ContinuousLinearMap.le_opNorm _ _)) _)
  have hconv : (∑ j ∈ Finset.range (n + 1), ‖Ac (n - j)‖ * ‖linearODESeriesCoeff Ac bc y₀ j‖) *
        R ^ (n + 1) ≤ M * R * C * ∑ j ∈ Finset.range (n + 1), ((j + k).choose k : ℝ) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj ↦ ?_
    have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hexp : n + 1 = n - j + 1 + j := by omega
    have hpow : R ^ (n + 1) = R ^ (n - j) * R * R ^ j := by
      rw [hexp, pow_add, pow_succ]
    calc
      ‖Ac (n - j)‖ * ‖linearODESeriesCoeff Ac bc y₀ j‖ * R ^ (n + 1) =
          (‖Ac (n - j)‖ * R ^ (n - j)) * R * (‖linearODESeriesCoeff Ac bc y₀ j‖ * R ^ j) := by
        rw [hpow]; ring
      _ ≤ M * R * (C * ((j + k).choose k : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hAc (n - j)) hR.le)
          (ih j (Finset.mem_range.mp hj)) (by positivity) (by positivity)
      _ = M * R * C * ((j + k).choose k : ℝ) := by ring
  have hforc : ‖bc n‖ * R ^ (n + 1) ≤ C * ∑ j ∈ Finset.range (n + 1), ((j + k).choose k : ℝ) := by
    have h1 : (1 : ℝ) ≤ ∑ j ∈ Finset.range (n + 1), ((j + k).choose k : ℝ) := by
      have hmem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.succ_pos n)
      simpa using Finset.single_le_sum (f := fun j ↦ ((j + k).choose k : ℝ))
        (fun j _ ↦ Nat.cast_nonneg _) hmem
    calc
      ‖bc n‖ * R ^ (n + 1) = (‖bc n‖ * R ^ n) * R := by rw [pow_succ]; ring
      _ ≤ B * R := mul_le_mul_of_nonneg_right (hbc n) hR.le
      _ ≤ C * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ C * ∑ j ∈ Finset.range (n + 1), ((j + k).choose k : ℝ) := mul_le_mul_of_nonneg_left h1 hC0
  -- The hockey-stick identity turns the majorant sum into the next binomial coefficient.
  have hchoose_nat : (∑ j ∈ Finset.range (n + 1), (j + k).choose k) * (k + 1) =
      (n + 1 + k).choose k * (n + 1) := by
    rw [Nat.sum_range_add_choose, Nat.choose_succ_right_eq, add_right_comm n k 1]
    simp
  have hchoose : ((k : ℝ) + 1) * ∑ j ∈ Finset.range (n + 1), ((j + k).choose k : ℝ) =
      ((n : ℝ) + 1) * ((n + 1 + k).choose k : ℝ) := by
    have := congrArg (Nat.cast (R := ℝ)) hchoose_nat
    push_cast at this
    linarith
  calc
    ((n : ℝ) + 1) * (‖linearODESeriesCoeff Ac bc y₀ (n + 1)‖ * R ^ (n + 1))
        ≤ M * R * C * (∑ j ∈ Finset.range (n + 1), ((j + k).choose k : ℝ)) +
            C * ∑ j ∈ Finset.range (n + 1), ((j + k).choose k : ℝ) :=
      hstep.trans (add_le_add hconv hforc)
    _ = C * ((M * R + 1) * ∑ j ∈ Finset.range (n + 1), ((j + k).choose k : ℝ)) := by ring
    _ ≤ C * (((k : ℝ) + 1) * ∑ j ∈ Finset.range (n + 1), ((j + k).choose k : ℝ)) := by gcongr
    _ = ((n : ℝ) + 1) * (C * ((n + 1 + k).choose k : ℝ)) := by rw [hchoose]; ring

/-- **Cauchy majorant bound for first-order linear ODE coefficients.** If `‖Ac m‖ * R ^ m ≤ M` and
`‖bc m‖ * R ^ m ≤ B` for every `m`, with `0 < R`, then the rescaled coefficients
`‖linearODESeriesCoeff Ac bc y₀ n‖ * R ^ n` are bounded by the binomial majorant sequence
`max ‖y₀‖ (B * R) * (n + ⌈M * R⌉₊).choose ⌈M * R⌉₊`. -/
theorem norm_linearODESeriesCoeff_mul_pow_le {Ac : ℕ → E →L[ℂ] E} {bc : ℕ → E} {y₀ : E}
    {R M B : ℝ} (hR : 0 < R)
    (hAc : ∀ m, ‖Ac m‖ * R ^ m ≤ M) (hbc : ∀ m, ‖bc m‖ * R ^ m ≤ B) (n : ℕ) :
    ‖linearODESeriesCoeff Ac bc y₀ n‖ * R ^ n ≤
      max ‖y₀‖ (B * R) * ((n + ⌈M * R⌉₊).choose ⌈M * R⌉₊ : ℝ) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | n
    · simp
    · exact norm_linearODESeriesCoeff_succ_mul_pow_le hR hAc hbc ih

/-- If the coefficient sequences `Ac` and `bc` satisfy Cauchy geometric bounds on every positive
radius strictly below `r`, then `linearODESeries Ac bc y₀` has convergence radius at least `r`. -/
theorem le_radius_linearODESeries {Ac : ℕ → E →L[ℂ] E} {bc : ℕ → E} {y₀ : E} {r : ℝ≥0∞}
    (hbound : ∀ R : ℝ≥0, 0 < R → (R : ℝ≥0∞) < r →
      (∃ M, ∀ m, ‖Ac m‖ * (R : ℝ) ^ m ≤ M) ∧ ∃ B, ∀ m, ‖bc m‖ * (R : ℝ) ^ m ≤ B) :
    r ≤ (linearODESeries Ac bc y₀).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun ρ hρ ↦ ?_
  obtain ⟨R, hρR, hRr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hρ
  have hR_pos : 0 < R := zero_le.trans_lt (ENNReal.coe_lt_coe.mp hρR)
  have hR_real : (0 : ℝ) < R := NNReal.coe_pos.mpr hR_pos
  obtain ⟨⟨M, hAc⟩, ⟨B, hbc⟩⟩ := hbound R hR_pos hRr
  set k : ℕ := ⌈M * (R : ℝ)⌉₊
  set C : ℝ := max ‖y₀‖ (B * R)
  have hC0 : 0 ≤ C := (norm_nonneg y₀).trans (le_max_left _ _)
  set p := FormalMultilinearSeries.ofScalars ℝ fun n : ℕ ↦ ((n + k).choose k : ℝ)
  have hlt : ((R⁻¹ * ρ : ℝ≥0) : ℝ≥0∞) < p.radius := by
    have hlt1 : (R⁻¹ * ρ : ℝ≥0) < 1 := by
      rw [inv_mul_lt_iff₀ hR_pos, mul_one]
      exact ENNReal.coe_lt_coe.mp hρR
    exact (ENNReal.coe_lt_one_iff.mpr hlt1).trans_le (one_le_ofScalars_choose_radius ℝ ℝ k)
  obtain ⟨D, -, hD⟩ := p.norm_mul_pow_le_of_lt_radius hlt
  refine (linearODESeries Ac bc y₀).le_radius_of_bound (C * D) fun n ↦ ?_
  calc
    ‖linearODESeries Ac bc y₀ n‖ * (ρ : ℝ) ^ n
        = (‖linearODESeriesCoeff Ac bc y₀ n‖ * (R : ℝ) ^ n) *
            ((R⁻¹ * ρ : ℝ≥0) : ℝ) ^ n := by
      rw [norm_linearODESeries, NNReal.coe_mul, NNReal.coe_inv, mul_pow, inv_pow]
      have hRn : (R : ℝ) ^ n ≠ 0 := (pow_pos hR_real n).ne'
      field_simp [hRn]
    _ ≤ (C * ((n + k).choose k : ℝ)) * ((R⁻¹ * ρ : ℝ≥0) : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right
        (norm_linearODESeriesCoeff_mul_pow_le hR_real hAc hbc n) (by positivity)
    _ = C * (‖p n‖ * ((R⁻¹ * ρ : ℝ≥0) : ℝ) ^ n) := by
      rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_of_nonneg (Nat.cast_nonneg _),
        mul_assoc]
    _ ≤ C * D := mul_le_mul_of_nonneg_left (hD n) hC0

end FirstOrderCoeff

section FirstOrderAnalytic

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance : IsBoundedSMul (E →L[ℂ] E) E :=
  .of_norm_smul_le ContinuousLinearMap.le_opNorm

local instance : IsScalarTower ℂ (E →L[ℂ] E) E :=
  ⟨fun _ _ _ ↦ rfl⟩

/-- **Taylor-coefficient residual of a first-order linear ODE.** At a point `z₀` where `A`, `b`,
and `y` are analytic, the `n`-th Taylor coefficient of `y' - A y - b` is the discrepancy in the
`n`-th step of `linearODESeriesCoeff`. -/
theorem inv_factorial_smul_iteratedDeriv_linearODE {A : ℂ → E →L[ℂ] E} {b y : ℂ → E} {z₀ : ℂ}
    (hA : AnalyticAt ℂ A z₀) (hb : AnalyticAt ℂ b z₀) (hy : AnalyticAt ℂ y z₀) (n : ℕ) :
    (n.factorial : ℂ)⁻¹ • iteratedDeriv n (fun z ↦ deriv y z - A z (y z) - b z) z₀ =
      ((n : ℂ) + 1) • ((n + 1).factorial : ℂ)⁻¹ • iteratedDeriv (n + 1) y z₀ -
        ∑ j ∈ Finset.range (n + 1),
          (((n - j).factorial : ℂ)⁻¹ • iteratedDeriv (n - j) A z₀)
            ((j.factorial : ℂ)⁻¹ • iteratedDeriv j y z₀) -
        (n.factorial : ℂ)⁻¹ • iteratedDeriv n b z₀ := by
  have hAy_an : AnalyticAt ℂ (fun z ↦ A z (y z)) z₀ := hA.smul hy
  have hy'_an : AnalyticAt ℂ (deriv y) z₀ := hy.deriv
  have hsub₁ : iteratedDeriv n (fun z ↦ deriv y z - A z (y z) - b z) z₀ =
      iteratedDeriv n (fun z ↦ deriv y z - A z (y z)) z₀ - iteratedDeriv n b z₀ :=
    iteratedDeriv_fun_sub (hy'_an.sub hAy_an).contDiffAt hb.contDiffAt
  have hsub₂ : iteratedDeriv n (fun z ↦ deriv y z - A z (y z)) z₀ =
      iteratedDeriv n (deriv y) z₀ - iteratedDeriv n (fun z ↦ A z (y z)) z₀ :=
    iteratedDeriv_fun_sub hy'_an.contDiffAt hAy_an.contDiffAt
  -- Express `z ↦ A z (y z)` as `A • y` so the 1D module Leibniz rule applies directly.
  have hleib := iteratedDerivWithin_smul (𝕜 := ℂ) (𝔸 := E →L[ℂ] E) (F := E) (n := n)
    (mem_univ z₀) uniqueDiffOn_univ hA.contDiffAt.contDiffWithinAt hy.contDiffAt.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at hleib
  have hsmul_eq : (fun z ↦ A z (y z)) = A • y := rfl
  rw [hsub₁, hsub₂, ← iteratedDeriv_succ', hsmul_eq, hleib, smul_sub, smul_sub]
  congr 1
  congr 1
  · rw [smul_comm ((n : ℂ) + 1), smul_smul]
    have hfac : ((n + 1).factorial : ℂ) = ((n : ℂ) + 1) * n.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hnf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    congr 1
    rw [hfac]
    field_simp
  · rw [Finset.smul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.add_sub_cancel, Nat.sub_sub_self hjle, ContinuousLinearMap.smul_def, smul_apply,
      ContinuousLinearMap.map_smul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    have hchoose := Nat.choose_mul_factorial_mul_factorial (n.sub_le j)
    rw [Nat.sub_sub_self hjle] at hchoose
    have hnf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hnjf : ((n - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - j).factorial_ne_zero
    have hjf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    have hcast : ((n.choose (n - j) : ℂ) * ((n - j).factorial : ℂ) * (j.factorial : ℂ)) =
        (n.factorial : ℂ) := by exact_mod_cast hchoose
    calc
      (n.factorial : ℂ)⁻¹ * (n.choose (n - j) : ℂ) =
          (n.factorial : ℂ)⁻¹ * ((n.factorial : ℂ) *
            (((n - j).factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹)) := by
        rw [← hcast]; field_simp
      _ = ((n - j).factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹ := by field_simp

/-- Any holomorphic solution of `y'(z) = A(z) y(z) + b(z)` on an open neighbourhood of `z₀` has
Taylor coefficients given by `linearODESeriesCoeff`. -/
theorem inv_factorial_smul_iteratedDeriv_eq_linearODESeriesCoeff {U : Set ℂ} (hUo : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {A : ℂ → E →L[ℂ] E} {b y : ℂ → E}
    (hA : DifferentiableOn ℂ A U) (hb : DifferentiableOn ℂ b U) (hy : DifferentiableOn ℂ y U)
    (hode : ∀ z ∈ U, deriv y z = A z (y z) + b z) :
    (fun n ↦ (n.factorial : ℂ)⁻¹ • iteratedDeriv n y z₀) =
      linearODESeriesCoeff
        (fun k ↦ (k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀)
        (fun k ↦ (k.factorial : ℂ)⁻¹ • iteratedDeriv k b z₀)
        (y z₀) := by
  rw [eq_linearODESeriesCoeff_iff]
  refine ⟨by simp, fun n ↦ ?_⟩
  have hzero : (fun z ↦ deriv y z - A z (y z) - b z) =ᶠ[𝓝 z₀] fun _ ↦ (0 : E) := by
    filter_upwards [hUo.mem_nhds hz₀] with z hz
    rw [hode z hz]
    abel
  have hid := inv_factorial_smul_iteratedDeriv_linearODE
    (hA.analyticAt (hUo.mem_nhds hz₀)) (hb.analyticAt (hUo.mem_nhds hz₀))
    (hy.analyticAt (hUo.mem_nhds hz₀)) n
  rw [hzero.iteratedDeriv_eq, iteratedDeriv_const] at hid
  simp only [ite_self, smul_zero] at hid
  rw [← sub_eq_zero, ← sub_sub]
  exact hid.symm

/-- **Uniqueness on preconnected open domains.** Two holomorphic solutions of
`y'(z) = A(z) y(z) + b(z)` on a preconnected open set `U` that agree at a point `z₀ ∈ U` agree
throughout `U`. No regularity hypothesis on `b` is needed. -/
theorem eqOn_of_deriv_eq_linearODE {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {A : ℂ → E →L[ℂ] E} {b y₁ y₂ : ℂ → E}
    (hA : DifferentiableOn ℂ A U) (hy₁ : DifferentiableOn ℂ y₁ U)
    (hy₂ : DifferentiableOn ℂ y₂ U)
    (hode₁ : ∀ z ∈ U, deriv y₁ z = A z (y₁ z) + b z)
    (hode₂ : ∀ z ∈ U, deriv y₂ z = A z (y₂ z) + b z)
    (hinit : y₁ z₀ = y₂ z₀) :
    EqOn y₁ y₂ U := by
  set d : ℂ → E := y₁ - y₂
  have hd_diff : DifferentiableOn ℂ d U := hy₁.sub hy₂
  have hd_an : AnalyticOnNhd ℂ d U := hd_diff.analyticOnNhd hUo
  have hd_ode : ∀ z ∈ U, deriv d z = A z (d z) + (fun _ : ℂ ↦ (0 : E)) z := by
    intro z hz
    have hy₁z := (hy₁.differentiableAt (hUo.mem_nhds hz)).hasDerivAt
    have hy₂z := (hy₂.differentiableAt (hUo.mem_nhds hz)).hasDerivAt
    rw [(hy₁z.sub hy₂z).deriv, hy₁z.deriv, hy₂z.deriv, hode₁ z hz, hode₂ z hz]
    simp [d, map_sub, add_sub_add_right_eq_sub]
  have hcoeff := inv_factorial_smul_iteratedDeriv_eq_linearODESeriesCoeff hUo hz₀ hA
    (differentiableOn_const (0 : E)) hd_diff hd_ode
  have hd0 : d z₀ = 0 := sub_eq_zero.mpr hinit
  have hiter (n : ℕ) : iteratedDeriv n d z₀ = 0 := by
    have hn := congrFun hcoeff n
    have hpi0 : (fun k ↦ (k.factorial : ℂ)⁻¹ • iteratedDeriv k (fun _ : ℂ ↦ (0 : E)) z₀) = 0 := by
      ext k; simp
    rw [hd0, hpi0, linearODESeriesCoeff_zero_zero, Pi.zero_apply, smul_eq_zero] at hn
    exact hn.resolve_left (inv_ne_zero (Nat.cast_ne_zero.mpr n.factorial_ne_zero))
  have hord : analyticOrderAt d z₀ = ⊤ :=
    ENat.eq_top_iff_forall_ne.mpr fun n hn ↦
      ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hd_an z₀ hz₀)).mp hn.symm).2 (hiter n)
  have hzero := hd_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₀
    (analyticOrderAt_eq_top.mp hord)
  exact fun z hz ↦ sub_eq_zero.mp (hzero hz)

/-- **Global uniqueness for entire first-order linear ODEs.** Two entire solutions of
`y'(z) = A(z) y(z) + b(z)` that agree at a single point `z₀` are equal everywhere on `ℂ`. -/
theorem eq_of_deriv_eq_linearODE {A : ℂ → E →L[ℂ] E} {b y₁ y₂ : ℂ → E} (z₀ : ℂ)
    (hA : Differentiable ℂ A) (hy₁ : Differentiable ℂ y₁) (hy₂ : Differentiable ℂ y₂)
    (hode₁ : ∀ z, deriv y₁ z = A z (y₁ z) + b z)
    (hode₂ : ∀ z, deriv y₂ z = A z (y₂ z) + b z)
    (hinit : y₁ z₀ = y₂ z₀) :
    y₁ = y₂ := by
  funext z
  exact eqOn_of_deriv_eq_linearODE isOpen_univ isPreconnected_univ (mem_univ z₀)
    hA.differentiableOn hy₁.differentiableOn hy₂.differentiableOn
    (fun w _ ↦ hode₁ w) (fun w _ ↦ hode₂ w) hinit (mem_univ z)

/-- If `A` and `b` are holomorphic on `Metric.eball z₀ r`, then `linearODESeries` formed from their
Taylor coefficients at `z₀` has convergence radius at least `r`. -/
theorem le_radius_linearODESeries_of_differentiableOn {A : ℂ → E →L[ℂ] E} {b : ℂ → E}
    {z₀ : ℂ} {r : ℝ≥0∞} (hA : DifferentiableOn ℂ A (Metric.eball z₀ r))
    (hb : DifferentiableOn ℂ b (Metric.eball z₀ r)) (y₀ : E) :
    r ≤ (linearODESeries
      (fun k ↦ (k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀)
      (fun k ↦ (k.factorial : ℂ)⁻¹ • iteratedDeriv k b z₀) y₀).radius := by
  have hcauchy {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
      {f : ℂ → F} (hf : DifferentiableOn ℂ f (Metric.eball z₀ r)) {R : ℝ≥0} (hR : 0 < R)
      (hRr : (R : ℝ≥0∞) < r) :
      ∃ M, ∀ m : ℕ, ‖(m.factorial : ℂ)⁻¹ • iteratedDeriv m f z₀‖ * (R : ℝ) ^ m ≤ M := by
    have hR_real : (0 : ℝ) < R := NNReal.coe_pos.mpr hR
    have hsub : closedBall z₀ (R : ℝ) ⊆ Metric.eball z₀ r := fun w hw ↦ by
      rw [mem_eball, edist_dist]
      exact (ENNReal.ofReal_le_ofReal (mem_closedBall.mp hw)).trans_lt (by simpa using hRr)
    obtain ⟨C, hC⟩ := (isCompact_sphere z₀ (R : ℝ)).exists_bound_of_continuousOn
      (hf.continuousOn.mono (sphere_subset_closedBall.trans hsub))
    refine ⟨max C 0, fun m ↦ ?_⟩
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hR_real
      (hf.diffContOnCl_ball hsub) fun w hw ↦ (hC w hw).trans (le_max_left C 0)
    have hfac_pos : (0 : ℝ) < m.factorial := Nat.cast_pos.mpr m.factorial_pos
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    calc
      (m.factorial : ℝ)⁻¹ * ‖iteratedDeriv m f z₀‖ * (R : ℝ) ^ m
          ≤ (m.factorial : ℝ)⁻¹ * ((m.factorial : ℝ) * max C 0 / (R : ℝ) ^ m) * (R : ℝ) ^ m := by
        gcongr
      _ = max C 0 := by
        have hpow_ne : (R : ℝ) ^ m ≠ 0 := (pow_pos hR_real m).ne'
        field_simp [hfac_pos.ne', hpow_ne]
  exact le_radius_linearODESeries fun _ hR hRr ↦ ⟨hcauchy hA hR hRr, hcauchy hb hR hRr⟩

/-- **Existence, uniqueness, and Taylor-series convergence for Banach-space linear ODEs on an open
disc.** Let `A : ℂ → E →L[ℂ] E` and `b : ℂ → E` be holomorphic on `Metric.eball z₀ r` (`0 < r ≤ ∞`).
For every `y₀ : E`, the series `linearODESeries` around `z₀` converges on the whole disc
`Metric.eball z₀ r` to a holomorphic solution `y` of `y'(z) = A(z) y(z) + b(z)` with `y(z₀) = y₀`,
and every holomorphic solution on `Metric.eball z₀ r` with `u(z₀) = y₀` agrees with `y` on the
disc. -/
theorem exists_hasFPowerSeriesOnBall_linearODE {A : ℂ → E →L[ℂ] E} {b : ℂ → E} {z₀ : ℂ}
    {r : ℝ≥0∞} (hr : 0 < r) (hA : DifferentiableOn ℂ A (Metric.eball z₀ r))
    (hb : DifferentiableOn ℂ b (Metric.eball z₀ r)) (y₀ : E) :
    let Ac := fun k ↦ (k.factorial : ℂ)⁻¹ • iteratedDeriv k A z₀
    let bc := fun k ↦ (k.factorial : ℂ)⁻¹ • iteratedDeriv k b z₀
    ∃ y : ℂ → E,
      HasFPowerSeriesOnBall y (linearODESeries Ac bc y₀) z₀ r ∧
      DifferentiableOn ℂ y (Metric.eball z₀ r) ∧
      (∀ z ∈ Metric.eball z₀ r, HasDerivAt y (A z (y z) + b z) z) ∧
      y z₀ = y₀ ∧
      ∀ u : ℂ → E, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        (∀ z ∈ Metric.eball z₀ r, deriv u z = A z (u z) + b z) →
        u z₀ = y₀ → EqOn u y (Metric.eball z₀ r) := by
  intro Ac bc
  set p := linearODESeries Ac bc y₀
  have hrad : r ≤ p.radius := le_radius_linearODESeries_of_differentiableOn hA hb y₀
  set y : ℂ → E := fun z ↦ p.sum (z - z₀)
  have hy_ps : HasFPowerSeriesOnBall y p z₀ r := by
    simpa only [zero_add, y] using
      ((p.hasFPowerSeriesOnBall (hr.trans_le hrad)).mono hr hrad).comp_sub z₀
  have hy_an : AnalyticOnNhd ℂ y (Metric.eball z₀ r) := hy_ps.analyticOnNhd
  have hy_diff : DifferentiableOn ℂ y (Metric.eball z₀ r) := hy_an.differentiableOn
  -- Identify the iterated derivatives of `y` at `z₀` with the recursive coefficients.
  have hy_coeff (n : ℕ) :
      (n.factorial : ℂ)⁻¹ • iteratedDeriv n y z₀ = linearODESeriesCoeff Ac bc y₀ n := by
    have hfac := hy_ps.factorial_smul 1 n
    rw [← iteratedDeriv_eq_iteratedFDeriv] at hfac
    have hp1 : p n (fun _ ↦ 1) = linearODESeriesCoeff Ac bc y₀ n := by simp [p]
    rw [hp1, ← Nat.cast_smul_eq_nsmul ℂ] at hfac
    have hnf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    rw [← hfac, inv_smul_smul₀ hnf]
  have hy0 : y z₀ = y₀ := by simpa using hy_coeff 0
  -- Show the ODE residual `y' - A y - b` vanishes on the whole disc via the identity principle.
  have hA_an : AnalyticOnNhd ℂ A (Metric.eball z₀ r) := hA.analyticOnNhd isOpen_eball
  have hb_an : AnalyticOnNhd ℂ b (Metric.eball z₀ r) := hb.analyticOnNhd isOpen_eball
  set res : ℂ → E := fun z ↦ deriv y z - A z (y z) - b z
  have hres_an : AnalyticOnNhd ℂ res (Metric.eball z₀ r) := fun z hz ↦
    ((hy_an.deriv z hz).sub ((hA_an z hz).smul (hy_an z hz))).sub (hb_an z hz)
  have hz₀_mem : z₀ ∈ Metric.eball z₀ r := mem_eball_self hr
  have hres_iter (n : ℕ) : iteratedDeriv n res z₀ = 0 := by
    have hid := inv_factorial_smul_iteratedDeriv_linearODE
      (hA_an z₀ hz₀_mem) (hb_an z₀ hz₀_mem) (hy_an z₀ hz₀_mem) n
    dsimp only [res]
    simp only [hy_coeff] at hid
    have hrhs : ((n : ℂ) + 1) • linearODESeriesCoeff Ac bc y₀ (n + 1) -
        ∑ j ∈ Finset.range (n + 1), Ac (n - j) (linearODESeriesCoeff Ac bc y₀ j) - bc n = 0 := by
      rw [smul_linearODESeriesCoeff_succ]
      abel
    rw [hrhs, smul_eq_zero] at hid
    exact hid.resolve_left (inv_ne_zero (Nat.cast_ne_zero.mpr n.factorial_ne_zero))
  have hres_ord : analyticOrderAt res z₀ = ⊤ :=
    ENat.eq_top_iff_forall_ne.mpr fun n hn ↦
      ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hres_an z₀ hz₀_mem)).mp hn.symm).2
        (hres_iter n)
  have hres_zero : EqOn res 0 (Metric.eball z₀ r) :=
    hres_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_eball hz₀_mem
      (analyticOrderAt_eq_top.mp hres_ord)
  have hderiv_eq : ∀ z ∈ Metric.eball z₀ r, deriv y z = A z (y z) + b z := fun z hz ↦ by
    have hz0 : deriv y z - (A z (y z) + b z) = 0 := by simpa [res, sub_sub] using hres_zero hz
    exact sub_eq_zero.mp hz0
  refine ⟨y, hy_ps, hy_diff, fun z hz ↦ ?_, hy0, fun u hu hu_ode hu0 ↦ ?_⟩
  · rw [← hderiv_eq z hz]
    exact (hy_an z hz).differentiableAt.hasDerivAt
  · exact eqOn_of_deriv_eq_linearODE isOpen_eball isPreconnected_eball hz₀_mem hA hu hy_diff
      hu_ode hderiv_eq (hu0.trans hy0.symm)

/-- **Global existence and uniqueness for entire Banach-space linear ODEs.** If `A : ℂ → E →L[ℂ] E`
and `b : ℂ → E` are entire, then for every `z₀ : ℂ` and `y₀ : E` there exists a unique entire
function `y : ℂ → E` solving `y'(z) = A(z) y(z) + b(z)` with `y(z₀) = y₀`. -/
theorem existsUnique_differentiable_linearODE {A : ℂ → E →L[ℂ] E} {b : ℂ → E}
    (hA : Differentiable ℂ A) (hb : Differentiable ℂ b) (z₀ : ℂ) (y₀ : E) :
    ∃! y : ℂ → E, Differentiable ℂ y ∧ (∀ z, deriv y z = A z (y z) + b z) ∧ y z₀ = y₀ := by
  obtain ⟨y, -, hy_diff, hy_ode, hy0, -⟩ :=
    exists_hasFPowerSeriesOnBall_linearODE (r := ⊤) ENNReal.zero_lt_top
      hA.differentiableOn hb.differentiableOn y₀
  rw [eball_top, differentiableOn_univ] at hy_diff
  refine ⟨y, ⟨hy_diff, fun z ↦ (hy_ode z (by simp)).deriv, hy0⟩, ?_⟩
  rintro u ⟨hu_diff, hu_ode, hu0⟩
  exact eq_of_deriv_eq_linearODE z₀ hA hu_diff hy_diff hu_ode
    (fun z ↦ (hy_ode z (by simp)).deriv) (hu0.trans hy0.symm)

end FirstOrderAnalytic

/-! ### Monic scalar equations of order `n` (`TauCeti.LinearEquation`) -/

namespace LinearEquation

variable {U : Opens ℂ} {n : ℕ} (E : LinearEquation U n)

/-- Continuous linear endomorphism on `Fin n → ℂ` representing multiplication by `E.companion z`. -/
private def companionCLM (z : ℂ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ∑ i : Fin n, ∑ j : Fin n, E.companion z i j •
    (ContinuousLinearMap.single ℂ (fun _ : Fin n ↦ ℂ) i).comp (ContinuousLinearMap.proj j)

private theorem companionCLM_apply (z : ℂ) (v : Fin n → ℂ) :
    companionCLM E z v = E.companion z *ᵥ v := by
  ext k
  simp only [companionCLM, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.single_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    simp [Pi.single_eq_of_ne' hik]
  · simp

private theorem differentiableOn_companionCLM :
    DifferentiableOn ℂ (companionCLM E) U := by
  have han : AnalyticOnNhd ℂ (companionCLM E) U := fun z hz ↦
    Finset.analyticAt_fun_sum _ fun i _ ↦ Finset.analyticAt_fun_sum _ fun j _ ↦
      (E.analyticOnNhd_companion i j z hz).smul analyticAt_const
  exact han.differentiableOn

/-- Two companion-system solutions on a preconnected open domain that agree at one point agree
throughout the domain. -/
theorem IsCompanionSolution.eqOn {v₁ v₂ : ℂ → Fin n → ℂ} (hUc : IsPreconnected (U : Set ℂ))
    {a : ℂ} (ha : a ∈ U) (hv₁ : E.IsCompanionSolution v₁) (hv₂ : E.IsCompanionSolution v₂)
    (hinit : v₁ a = v₂ a) :
    EqOn v₁ v₂ U := by
  refine eqOn_of_deriv_eq_linearODE (b := 0) U.isOpen hUc ha (differentiableOn_companionCLM E)
    hv₁.analyticOnNhd.differentiableOn hv₂.analyticOnNhd.differentiableOn ?_ ?_ hinit
  · intro z hz
    rw [companionCLM_apply E, Pi.zero_apply, add_zero]
    exact (hv₁.hasDerivAt z hz).deriv
  · intro z hz
    rw [companionCLM_apply E, Pi.zero_apply, add_zero]
    exact (hv₂.hasDerivAt z hz).deriv

/-- **Uniqueness for `LinearEquation` on preconnected domains.** Two solutions of `E` on a
preconnected open domain whose first `n` derivatives agree at `a ∈ U` agree on `U`. -/
theorem IsSolution.eqOn_of_iteratedDeriv_eq {y₁ y₂ : ℂ → ℂ} (hUc : IsPreconnected (U : Set ℂ))
    {a : ℂ} (ha : a ∈ U) (hy₁ : E.IsSolution y₁) (hy₂ : E.IsSolution y₂)
    (hjet : ∀ j < n, iteratedDeriv j y₁ a = iteratedDeriv j y₂ a) :
    EqOn y₁ y₂ U := by
  have hv := IsCompanionSolution.eqOn E hUc ha hy₁.isCompanionSolution hy₂.isCompanionSolution
    (funext fun j ↦ hjet j j.isLt)
  intro z hz
  simpa only [iteratedDeriv_zero] using congrFun (hv hz) ⟨0, E.order_pos⟩

/-- **Injectivity of the initial jet.** On a preconnected open domain, a holomorphic solution in
`E.solutionSpace` is uniquely determined by its initial `n`-jet at any point `a ∈ U`. -/
theorem initialJet_injective (hUc : IsPreconnected (U : Set ℂ)) {a : ℂ} (ha : a ∈ U) :
    Function.Injective (E.initialJet ha) := by
  intro f₁ f₂ hjet
  have heq := IsSolution.eqOn_of_iteratedDeriv_eq E hUc ha
    ((E.mem_solutionSpace f₁.1).mp f₁.2) ((E.mem_solutionSpace f₂.1).mp f₂.2) fun j hj ↦ by
      simpa [initialJet_apply] using congrFun hjet ⟨j, hj⟩
  apply Subtype.ext
  apply Subtype.ext
  ext z
  simpa only [HolomorphicFunctions.extend_apply] using heq z.2

/-- On a preconnected open domain containing `a`, the solution space `E.solutionSpace` has complex
dimension at most `n`. -/
theorem finrank_solutionSpace_le (hUc : IsPreconnected (U : Set ℂ)) {a : ℂ} (ha : a ∈ U) :
    Module.finrank ℂ E.solutionSpace ≤ n := by
  simpa using LinearMap.finrank_le_finrank_of_injective (E.initialJet_injective hUc ha)

/-- **Existence of companion-system solutions on an open disc.** Every initial vector
`c : Fin n → ℂ` at the center `z₀` of `Metric.eball z₀ r` (`0 < r`) extends to a companion-system
solution on the whole disc. -/
theorem exists_isCompanionSolution_eball {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.eball z₀ r, isOpen_eball⟩ n) (c : Fin n → ℂ) :
    ∃ v : ℂ → Fin n → ℂ, E.IsCompanionSolution v ∧ v z₀ = c := by
  obtain ⟨v, -, hv_diff, hv_ode, hv0, -⟩ :=
    exists_hasFPowerSeriesOnBall_linearODE (b := 0) hr (differentiableOn_companionCLM E)
      (differentiableOn_const 0) c
  refine ⟨v, (E.isCompanionSolution_iff v).mpr ⟨hv_diff.analyticOnNhd isOpen_eball, fun z hz ↦ ?_⟩,
    hv0⟩
  have hd := hv_ode z hz
  rwa [companionCLM_apply E, Pi.zero_apply, add_zero] at hd

/-- **Existence of scalar solutions on an open disc.** For any prescribed `n`-jet `c : Fin n → ℂ`
at `z₀`, a monic linear equation on `Metric.eball z₀ r` (`0 < r`) admits a holomorphic solution on
the disc matching `c` at `z₀`. -/
theorem exists_isSolution_eball {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.eball z₀ r, isOpen_eball⟩ n) (c : Fin n → ℂ) :
    ∃ y : ℂ → ℂ, E.IsSolution y ∧ ∀ j : Fin n, iteratedDeriv j y z₀ = c j := by
  obtain ⟨v, hv, hv0⟩ := exists_isCompanionSolution_eball hr E c
  refine ⟨fun z ↦ v z ⟨0, E.order_pos⟩, hv.isSolution, fun j ↦ ?_⟩
  rw [← hv.eq_iteratedDeriv z₀ (mem_eball_self hr) j, hv0]

/-- On an open disc `Metric.eball z₀ r` (`0 < r`), the initial-jet map at `z₀` is bijective. -/
theorem initialJet_bijective_eball {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.eball z₀ r, isOpen_eball⟩ n) :
    Function.Bijective (E.initialJet (mem_eball_self hr)) := by
  refine ⟨E.initialJet_injective isPreconnected_eball (mem_eball_self hr), fun c ↦ ?_⟩
  obtain ⟨v, hv, hv0⟩ := exists_isCompanionSolution_eball hr E c
  exact ⟨hv.toSolutionSpace, (hv.initialJet_toSolutionSpace (mem_eball_self hr)).trans hv0⟩

/-- **Initial-jet isomorphism on an open disc.** Evaluating the first `n` derivatives at the center
`z₀` identifies the holomorphic solution space on `Metric.eball z₀ r` linearly with `Fin n → ℂ`. -/
def initialJetEquivEball {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.eball z₀ r, isOpen_eball⟩ n) :
    E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (E.initialJet (mem_eball_self hr)) (initialJet_bijective_eball hr E)

/-- `initialJetEquivEball` acts on solutions by `initialJet` at the disc center. -/
@[simp]
theorem initialJetEquivEball_apply {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.eball z₀ r, isOpen_eball⟩ n) (f : E.solutionSpace) :
    E.initialJetEquivEball hr f = E.initialJet (mem_eball_self hr) f := by
  rfl

/-- On an open disc of positive radius, the holomorphic solution space is finitely generated. -/
theorem moduleFinite_solutionSpace_eball {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.eball z₀ r, isOpen_eball⟩ n) :
    Module.Finite ℂ E.solutionSpace :=
  .equiv (E.initialJetEquivEball hr).symm

/-- The holomorphic solution space of an order-`n` monic linear equation on `Metric.eball z₀ r`
(`0 < r`) has complex dimension `n`. -/
theorem finrank_solutionSpace_eball {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.eball z₀ r, isOpen_eball⟩ n) :
    Module.finrank ℂ E.solutionSpace = n := by
  simpa using (E.initialJetEquivEball hr).finrank_eq

/-- **Initial-jet isomorphism for entire equations.** On `(⊤ : Opens ℂ)`, evaluating the first `n`
derivatives at any point `z₀ ∈ ℂ` gives a linear isomorphism `E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ)`. -/
def initialJetEquivTop (E : LinearEquation (⊤ : Opens ℂ) n) (z₀ : ℂ) :
    E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) := by
  refine LinearEquiv.ofBijective (E.initialJet (mem_univ z₀))
    ⟨E.initialJet_injective isPreconnected_univ (mem_univ z₀), fun c ↦ ?_⟩
  let E' : LinearEquation ⟨Metric.eball z₀ ⊤, isOpen_eball⟩ n :=
    { order_pos := E.order_pos
      coeff := fun j ↦ HolomorphicFunctions.restrict (fun _ _ ↦ trivial) (E.coeff j) }
  obtain ⟨v, hv, hv0⟩ := exists_isCompanionSolution_eball ENNReal.zero_lt_top E' c
  have hv_top : E.IsCompanionSolution v := by
    rw [E.isCompanionSolution_iff]
    refine ⟨fun z _ ↦ hv.analyticOnNhd z (by simp), fun z _ ↦ ?_⟩
    have hd := hv.hasDerivAt z (by simp)
    have hcomp : E'.companion z = E.companion z := by
      ext i j
      have hz_eball : z ∈ (⟨Metric.eball z₀ ⊤, isOpen_eball⟩ : Opens ℂ) := by simp
      have hz_top : z ∈ (⊤ : Opens ℂ) := trivial
      have hext : HolomorphicFunctions.extend (E'.coeff j) z =
          HolomorphicFunctions.extend (E.coeff j) z := by
        rw [HolomorphicFunctions.extend_apply _ ⟨z, hz_eball⟩,
          HolomorphicFunctions.extend_apply _ ⟨z, hz_top⟩]
        exact HolomorphicFunctions.restrict_apply _ (E.coeff j) ⟨z, hz_eball⟩
      simp [companion_apply, hext]
    rwa [hcomp] at hd
  exact ⟨hv_top.toSolutionSpace, (hv_top.initialJet_toSolutionSpace (mem_univ z₀)).trans hv0⟩

/-- `initialJetEquivTop` acts on entire solutions by `initialJet` at `z₀`. -/
@[simp]
theorem initialJetEquivTop_apply (E : LinearEquation (⊤ : Opens ℂ) n) (z₀ : ℂ)
    (f : E.solutionSpace) :
    E.initialJetEquivTop z₀ f = E.initialJet (mem_univ z₀) f := by
  rfl

/-- The space of entire solutions of an entire monic linear equation is finitely generated over
`ℂ`. -/
instance moduleFinite_solutionSpace_top (E : LinearEquation (⊤ : Opens ℂ) n) :
    Module.Finite ℂ E.solutionSpace :=
  .equiv (E.initialJetEquivTop 0).symm

/-- The space of entire solutions of an entire monic linear equation of order `n` has complex
dimension `n`. -/
@[simp]
theorem finrank_solutionSpace_top (E : LinearEquation (⊤ : Opens ℂ) n) :
    Module.finrank ℂ E.solutionSpace = n := by
  simpa using (E.initialJetEquivTop 0).finrank_eq

end LinearEquation

/-! ### Scalar second-order equations `w'' + f(z) w' + g(z) w = h(z)` at an ordinary point -/

section SecondOrder

/-- Recursive Taylor coefficients of the solution to `w''(z) + f(z) w'(z) + g(z) w(z) = h(z)` with
initial data `w(z₀) = w₀`, `w'(z₀) = w₁`, written in terms of the Taylor coefficient sequences
`fc`, `gc`, `hc` of `f`, `g`, `h` around `z₀` (DLMF 2.7.1). -/
def secondOrderODESeriesCoeff (fc gc hc : ℕ → ℂ) (w₀ w₁ : ℂ) : ℕ → ℂ
  | 0 => w₀
  | 1 => w₁
  | n + 2 => (((n : ℂ) + 1) * ((n : ℂ) + 2))⁻¹ *
      (hc n - ∑ j : Fin (n + 1),
        (((j.1 : ℂ) + 1) * fc (n - j.1) * secondOrderODESeriesCoeff fc gc hc w₀ w₁ (j.1 + 1) +
          gc (n - j.1) * secondOrderODESeriesCoeff fc gc hc w₀ w₁ j.1))

/-- The zeroth Taylor coefficient is `w₀`. -/
@[simp]
theorem secondOrderODESeriesCoeff_zero (fc gc hc : ℕ → ℂ) (w₀ w₁ : ℂ) :
    secondOrderODESeriesCoeff fc gc hc w₀ w₁ 0 = w₀ := by
  rw [secondOrderODESeriesCoeff]

/-- The first Taylor coefficient is `w₁`. -/
@[simp]
theorem secondOrderODESeriesCoeff_one (fc gc hc : ℕ → ℂ) (w₀ w₁ : ℂ) :
    secondOrderODESeriesCoeff fc gc hc w₀ w₁ 1 = w₁ := by
  rw [secondOrderODESeriesCoeff]

/-- Explicit two-step Cauchy-product recursion for `secondOrderODESeriesCoeff` at index `n + 2`. -/
@[simp]
theorem secondOrderODESeriesCoeff_add_two (fc gc hc : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) :
    secondOrderODESeriesCoeff fc gc hc w₀ w₁ (n + 2) =
      (((n : ℂ) + 1) * ((n : ℂ) + 2))⁻¹ *
        (hc n - ∑ j ∈ Finset.range (n + 1),
          (((j : ℂ) + 1) * fc (n - j) * secondOrderODESeriesCoeff fc gc hc w₀ w₁ (j + 1) +
            gc (n - j) * secondOrderODESeriesCoeff fc gc hc w₀ w₁ j)) := by
  rw [secondOrderODESeriesCoeff, ← Fin.sum_univ_eq_sum_range]

/-- Undivided form of the recursion for `secondOrderODESeriesCoeff`. -/
theorem mul_secondOrderODESeriesCoeff_add_two (fc gc hc : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * ((n : ℂ) + 2) * secondOrderODESeriesCoeff fc gc hc w₀ w₁ (n + 2) =
      hc n - ∑ j ∈ Finset.range (n + 1),
        (((j : ℂ) + 1) * fc (n - j) * secondOrderODESeriesCoeff fc gc hc w₀ w₁ (j + 1) +
          gc (n - j) * secondOrderODESeriesCoeff fc gc hc w₀ w₁ j) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn2 : ((n : ℂ) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  rw [secondOrderODESeriesCoeff_add_two, mul_inv_cancel_left₀ (mul_ne_zero hn1 hn2)]

/-- Characterization of `secondOrderODESeriesCoeff` by its two initial values and undivided
coefficient recursion. -/
theorem eq_secondOrderODESeriesCoeff_iff {fc gc hc a : ℕ → ℂ} {w₀ w₁ : ℂ} :
    a = secondOrderODESeriesCoeff fc gc hc w₀ w₁ ↔
      a 0 = w₀ ∧ a 1 = w₁ ∧ ∀ n : ℕ,
        ((n : ℂ) + 1) * ((n : ℂ) + 2) * a (n + 2) =
          hc n - ∑ j ∈ Finset.range (n + 1),
            (((j : ℂ) + 1) * fc (n - j) * a (j + 1) + gc (n - j) * a j) := by
  refine ⟨fun h ↦ ?_, fun ⟨h0, h1, hrec⟩ ↦ funext fun n ↦ ?_⟩
  · subst h
    exact ⟨secondOrderODESeriesCoeff_zero fc gc hc w₀ w₁,
      secondOrderODESeriesCoeff_one fc gc hc w₀ w₁,
      mul_secondOrderODESeriesCoeff_add_two fc gc hc w₀ w₁⟩
  · induction n using Nat.strong_induction_on with
    | ind n ih =>
      rcases n with _ | _ | n
      · exact h0.trans (secondOrderODESeriesCoeff_zero fc gc hc w₀ w₁).symm
      · exact h1.trans (secondOrderODESeriesCoeff_one fc gc hc w₀ w₁).symm
      · have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        have hn2 : ((n : ℂ) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
        have hne : ((n : ℂ) + 1) * ((n : ℂ) + 2) ≠ 0 := mul_ne_zero hn1 hn2
        rw [secondOrderODESeriesCoeff_add_two, ← inv_mul_cancel_left₀ hne (a (n + 2)), hrec n]
        congr 2
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have hjlt : j < n + 1 := Finset.mem_range.mp hj
        rw [ih (j + 1) (Nat.add_lt_add_right hjlt 1), ih j (Nat.lt_succ_of_lt hjlt)]

/-- Zero initial data and zero forcing produce identically zero second-order Taylor coefficients. -/
@[simp]
theorem secondOrderODESeriesCoeff_zero_zero_zero (fc gc : ℕ → ℂ) :
    secondOrderODESeriesCoeff fc gc 0 0 0 = 0 := by
  symm
  rw [eq_secondOrderODESeriesCoeff_iff]
  simp

/-- `secondOrderODESeriesCoeff` is additive in the forcing sequence and initial data. -/
theorem secondOrderODESeriesCoeff_add (fc gc hc₁ hc₂ : ℕ → ℂ) (w₀ w₁ u₀ u₁ : ℂ) :
    secondOrderODESeriesCoeff fc gc (hc₁ + hc₂) (w₀ + u₀) (w₁ + u₁) =
      secondOrderODESeriesCoeff fc gc hc₁ w₀ w₁ + secondOrderODESeriesCoeff fc gc hc₂ u₀ u₁ := by
  symm
  rw [eq_secondOrderODESeriesCoeff_iff]
  refine ⟨by simp, by simp, fun n ↦ ?_⟩
  rw [Pi.add_apply, mul_add, mul_secondOrderODESeriesCoeff_add_two,
    mul_secondOrderODESeriesCoeff_add_two, Pi.add_apply]
  have hsum : ∑ j ∈ Finset.range (n + 1),
        (((j : ℂ) + 1) * fc (n - j) *
            (secondOrderODESeriesCoeff fc gc hc₁ w₀ w₁ +
              secondOrderODESeriesCoeff fc gc hc₂ u₀ u₁) (j + 1) +
          gc (n - j) *
            (secondOrderODESeriesCoeff fc gc hc₁ w₀ w₁ +
              secondOrderODESeriesCoeff fc gc hc₂ u₀ u₁) j) =
      ∑ j ∈ Finset.range (n + 1),
        (((j : ℂ) + 1) * fc (n - j) * secondOrderODESeriesCoeff fc gc hc₁ w₀ w₁ (j + 1) +
          gc (n - j) * secondOrderODESeriesCoeff fc gc hc₁ w₀ w₁ j) +
      ∑ j ∈ Finset.range (n + 1),
        (((j : ℂ) + 1) * fc (n - j) * secondOrderODESeriesCoeff fc gc hc₂ u₀ u₁ (j + 1) +
          gc (n - j) * secondOrderODESeriesCoeff fc gc hc₂ u₀ u₁ j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Pi.add_apply]
    ring
  rw [hsum]
  ring

/-- `secondOrderODESeriesCoeff` commutes with complex scalar multiplication of the forcing sequence
and initial data. -/
theorem secondOrderODESeriesCoeff_smul (fc gc : ℕ → ℂ) (c : ℂ) (hc : ℕ → ℂ) (w₀ w₁ : ℂ) :
    secondOrderODESeriesCoeff fc gc (c • hc) (c * w₀) (c * w₁) =
      c • secondOrderODESeriesCoeff fc gc hc w₀ w₁ := by
  symm
  rw [eq_secondOrderODESeriesCoeff_iff]
  refine ⟨by simp, by simp, fun n ↦ ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, mul_secondOrderODESeriesCoeff_add_two,
    Pi.smul_apply, smul_eq_mul, mul_sub]
  have hsum : c * ∑ j ∈ Finset.range (n + 1),
        (((j : ℂ) + 1) * fc (n - j) * secondOrderODESeriesCoeff fc gc hc w₀ w₁ (j + 1) +
          gc (n - j) * secondOrderODESeriesCoeff fc gc hc w₀ w₁ j) =
      ∑ j ∈ Finset.range (n + 1),
        (((j : ℂ) + 1) * fc (n - j) * (c • secondOrderODESeriesCoeff fc gc hc w₀ w₁) (j + 1) +
          gc (n - j) * (c • secondOrderODESeriesCoeff fc gc hc w₀ w₁) j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum]

/-- **Taylor coefficients of any holomorphic second-order ODE solution.** If `f`, `g`, and `w`
are holomorphic on an open set `U` containing `z₀` and `w'' + f w' + g w = h` on `U`, then the
Taylor coefficients `iteratedDeriv n w z₀ / n!` satisfy `secondOrderODESeriesCoeff`. -/
theorem iteratedDeriv_div_factorial_eq_secondOrderODESeriesCoeff {U : Set ℂ} (hUo : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f g h w : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hw : DifferentiableOn ℂ w U)
    (hode : ∀ z ∈ U, deriv (deriv w) z + f z * deriv w z + g z * w z = h z) :
    (fun n ↦ iteratedDeriv n w z₀ / n.factorial) =
      secondOrderODESeriesCoeff
        (fun k ↦ iteratedDeriv k f z₀ / k.factorial)
        (fun k ↦ iteratedDeriv k g z₀ / k.factorial)
        (fun k ↦ iteratedDeriv k h z₀ / k.factorial)
        (w z₀) (deriv w z₀) := by
  rw [eq_secondOrderODESeriesCoeff_iff]
  refine ⟨by simp, by simp [iteratedDeriv_one], fun n ↦ ?_⟩
  have hf_an : AnalyticAt ℂ f z₀ := hf.analyticAt (hUo.mem_nhds hz₀)
  have hg_an : AnalyticAt ℂ g z₀ := hg.analyticAt (hUo.mem_nhds hz₀)
  have hw_an : AnalyticAt ℂ w z₀ := hw.analyticAt (hUo.mem_nhds hz₀)
  have hconv {p q : ℂ → ℂ} (hp : AnalyticAt ℂ p z₀) (hq : AnalyticAt ℂ q z₀) :
      iteratedDeriv n (fun z ↦ p z * q z) z₀ / (n.factorial : ℂ) =
        ∑ j ∈ Finset.range (n + 1),
          (iteratedDeriv (n - j) p z₀ / (n - j).factorial) *
            (iteratedDeriv j q z₀ / j.factorial) := by
    rw [iteratedDeriv_fun_mul hp.contDiffAt hq.contDiffAt, Finset.sum_div,
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.add_sub_cancel, Nat.sub_sub_self hjle]
    have hchoose : (n.choose (n - j) : ℂ) * (n - j).factorial * j.factorial = n.factorial := by
      exact_mod_cast (by simpa [Nat.sub_sub_self hjle] using
        Nat.choose_mul_factorial_mul_factorial (n.sub_le j))
    have hc_ne : (n.choose (n - j) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (n.sub_le j)).ne'
    have hnjf : ((n - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - j).factorial_ne_zero
    have hjf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    rw [← hchoose]
    field_simp
  have heq : (fun z ↦ deriv (deriv w) z + f z * deriv w z + g z * w z) =ᶠ[𝓝 z₀] h := by
    filter_upwards [hUo.mem_nhds hz₀] with z hz
    exact hode z hz
  have hdiv := congrArg (fun x : ℂ ↦ x / n.factorial) (heq.iteratedDeriv_eq n)
  have hadd₁ : iteratedDeriv n (fun z ↦ deriv (deriv w) z + f z * deriv w z + g z * w z) z₀ =
      iteratedDeriv n (fun z ↦ deriv (deriv w) z + f z * deriv w z) z₀ +
        iteratedDeriv n (fun z ↦ g z * w z) z₀ :=
    iteratedDeriv_fun_add (hw_an.deriv.deriv.add (hf_an.mul hw_an.deriv)).contDiffAt
      (hg_an.mul hw_an).contDiffAt
  have hadd₂ : iteratedDeriv n (fun z ↦ deriv (deriv w) z + f z * deriv w z) z₀ =
      iteratedDeriv n (deriv (deriv w)) z₀ + iteratedDeriv n (fun z ↦ f z * deriv w z) z₀ :=
    iteratedDeriv_fun_add hw_an.deriv.deriv.contDiffAt (hf_an.mul hw_an.deriv).contDiffAt
  rw [hadd₁, hadd₂, ← iteratedDeriv_succ', ← iteratedDeriv_succ', add_div, add_div,
    hconv hf_an hw_an.deriv, hconv hg_an hw_an] at hdiv
  have hlead : iteratedDeriv (n + 2) w z₀ / (n.factorial : ℂ) =
      ((n : ℂ) + 1) * ((n : ℂ) + 2) * (iteratedDeriv (n + 2) w z₀ / (n + 2).factorial) := by
    have hfac : ((n + 2).factorial : ℂ) = ((n : ℂ) + 2) * ((n : ℂ) + 1) * n.factorial := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hn2 : ((n : ℂ) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    rw [hfac]; field_simp
  have hshift (j : ℕ) : (iteratedDeriv (n - j) f z₀ / (n - j).factorial) *
        (iteratedDeriv j (deriv w) z₀ / j.factorial) =
      ((j : ℂ) + 1) * (iteratedDeriv (n - j) f z₀ / (n - j).factorial) *
        (iteratedDeriv (j + 1) w z₀ / (j + 1).factorial) := by
    have hjfac : ((j + 1).factorial : ℂ) = ((j : ℂ) + 1) * j.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hj1 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hjf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    rw [← iteratedDeriv_succ', hjfac]; field_simp
  simp only [hlead, hshift] at hdiv
  rw [add_assoc, ← Finset.sum_add_distrib] at hdiv
  linear_combination hdiv

/-- Companion continuous linear operator on `ℂ × ℂ` associated with `w'' + f(z) w' + g(z) w`. -/
private def secondOrderCompanionCLM (f g : ℂ → ℂ) (z : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ ℂ) -
    g z • (ContinuousLinearMap.inr ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ ℂ ℂ) -
    f z • (ContinuousLinearMap.inr ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ ℂ)

private theorem secondOrderCompanionCLM_apply (f g : ℂ → ℂ) (z : ℂ) (p : ℂ × ℂ) :
    secondOrderCompanionCLM f g z p = (p.2, -(g z * p.1 + f z * p.2)) := by
  ext <;> simp [secondOrderCompanionCLM]
  ring

private theorem differentiableOn_secondOrderCompanionCLM {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ (secondOrderCompanionCLM f g) U :=
  ((differentiableOn_const _).sub (hg.smul (differentiableOn_const _))).sub
    (hf.smul (differentiableOn_const _))

/-- **Uniqueness for second-order linear ODEs on preconnected open sets.** Two holomorphic
solutions of `w''(z) + f(z) w'(z) + g(z) w(z) = h(z)` on a preconnected open set `U` that have
equal value and first derivative at `z₀ ∈ U` agree everywhere on `U`. No regularity hypothesis on
`h` is required. -/
theorem eqOn_of_secondOrderODE {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f g h w₁ w₂ : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hw₁ : DifferentiableOn ℂ w₁ U) (hw₂ : DifferentiableOn ℂ w₂ U)
    (hode₁ : ∀ z ∈ U, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = h z)
    (hode₂ : ∀ z ∈ U, deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = h z)
    (h0 : w₁ z₀ = w₂ z₀) (h1 : deriv w₁ z₀ = deriv w₂ z₀) :
    EqOn w₁ w₂ U := by
  have hY₁ : DifferentiableOn ℂ (fun z ↦ (w₁ z, deriv w₁ z)) U := hw₁.prodMk (hw₁.deriv hUo)
  have hY₂ : DifferentiableOn ℂ (fun z ↦ (w₂ z, deriv w₂ z)) U := hw₂.prodMk (hw₂.deriv hUo)
  have heq := eqOn_of_deriv_eq_linearODE (A := secondOrderCompanionCLM f g)
    (b := fun z ↦ (0, h z)) hUo hUc hz₀
    (differentiableOn_secondOrderCompanionCLM hf hg) hY₁ hY₂ ?_ ?_ (Prod.ext h0 h1)
  · exact fun z hz ↦ congrArg Prod.fst (heq hz)
  · intro z hz
    have hd₁ := (hw₁.differentiableAt (hUo.mem_nhds hz)).hasDerivAt
    have hd₁' := ((hw₁.deriv hUo).differentiableAt (hUo.mem_nhds hz)).hasDerivAt
    rw [(hd₁.prodMk hd₁').deriv, secondOrderCompanionCLM_apply]
    ext <;> simp
    linear_combination hode₁ z hz
  · intro z hz
    have hd₂ := (hw₂.differentiableAt (hUo.mem_nhds hz)).hasDerivAt
    have hd₂' := ((hw₂.deriv hUo).differentiableAt (hUo.mem_nhds hz)).hasDerivAt
    rw [(hd₂.prodMk hd₂').deriv, secondOrderCompanionCLM_apply]
    ext <;> simp
    linear_combination hode₂ z hz

/-- **Global uniqueness for entire second-order linear ODEs.** Two entire solutions of
`w''(z) + f(z) w'(z) + g(z) w(z) = h(z)` with the same value and first derivative at `z₀` are equal
everywhere on `ℂ`. -/
theorem eq_of_secondOrderODE {f g h w₁ w₂ : ℂ → ℂ} (z₀ : ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hw₁ : Differentiable ℂ w₁) (hw₂ : Differentiable ℂ w₂)
    (hode₁ : ∀ z, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = h z)
    (hode₂ : ∀ z, deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = h z)
    (h0 : w₁ z₀ = w₂ z₀) (h1 : deriv w₁ z₀ = deriv w₂ z₀) :
    w₁ = w₂ := by
  funext z
  exact eqOn_of_secondOrderODE isOpen_univ isPreconnected_univ (mem_univ z₀)
    hf.differentiableOn hg.differentiableOn hw₁.differentiableOn hw₂.differentiableOn
    (fun w _ ↦ hode₁ w) (fun w _ ↦ hode₂ w) h0 h1 (mem_univ z)

/-- **Existence, uniqueness, and whole-disc Taylor convergence at an ordinary point (DLMF 2.7.1).**
If `f`, `g`, and `h` are holomorphic on `Metric.eball z₀ r` (`0 < r ≤ ∞`), then for all `w₀, w₁ ∈ ℂ`
there exists a holomorphic solution `w` on `Metric.eball z₀ r` of
`w''(z) + f(z) w'(z) + g(z) w(z) = h(z)` with `w(z₀) = w₀` and `w'(z₀) = w₁`; its Taylor series
around `z₀` has coefficients `secondOrderODESeriesCoeff` and converges on the whole disc, and every
holomorphic solution on the disc with the same initial data agrees with `w`. -/
theorem exists_hasFPowerSeriesOnBall_secondOrderODE {f g h : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r))
    (hh : DifferentiableOn ℂ h (Metric.eball z₀ r)) (w₀ w₁ : ℂ) :
    let a := secondOrderODESeriesCoeff
      (fun k ↦ iteratedDeriv k f z₀ / k.factorial)
      (fun k ↦ iteratedDeriv k g z₀ / k.factorial)
      (fun k ↦ iteratedDeriv k h z₀ / k.factorial) w₀ w₁
    ∃ w : ℂ → ℂ,
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r ∧
      DifferentiableOn ℂ w (Metric.eball z₀ r) ∧
      (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = h z) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        (∀ z ∈ Metric.eball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = h z) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.eball z₀ r) := by
  intro a
  have hcomp := differentiableOn_secondOrderCompanionCLM hf hg
  have hb : DifferentiableOn ℂ (fun z : ℂ ↦ ((0 : ℂ), h z)) (Metric.eball z₀ r) :=
    (differentiableOn_const 0).prodMk hh
  obtain ⟨Y, hY_ps, -, hY_ode, hY0, -⟩ :=
    exists_hasFPowerSeriesOnBall_linearODE hr hcomp hb (w₀, w₁)
  set w : ℂ → ℂ := fun z ↦ (Y z).1
  set q := (ContinuousLinearMap.fst ℂ ℂ ℂ).compFormalMultilinearSeries
    (linearODESeries (fun k ↦ (k.factorial : ℂ)⁻¹ • iteratedDeriv k
      (secondOrderCompanionCLM f g) z₀)
      (fun k ↦ (k.factorial : ℂ)⁻¹ • iteratedDeriv k (fun z : ℂ ↦ ((0 : ℂ), h z)) z₀) (w₀, w₁))
  have hw_ps₀ : HasFPowerSeriesOnBall w q z₀ r :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).comp_hasFPowerSeriesOnBall hY_ps
  have hw_diff : DifferentiableOn ℂ w (Metric.eball z₀ r) := hw_ps₀.analyticOnNhd.differentiableOn
  -- First coordinate's derivative on the open disc is the second coordinate of `Y`.
  have hderiv_w : EqOn (deriv w) (fun z ↦ (Y z).2) (Metric.eball z₀ r) := fun z hz ↦ by
    have hd := ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt z (hY_ode z hz)).deriv
    simpa [Function.comp_def, w, secondOrderCompanionCLM_apply] using hd
  have hw0 : w z₀ = w₀ := congrArg Prod.fst hY0
  have hw1 : deriv w z₀ = w₁ :=
    (hderiv_w (mem_eball_self hr)).trans (congrArg Prod.snd hY0)
  have hw_ode : ∀ z ∈ Metric.eball z₀ r,
      deriv (deriv w) z + f z * deriv w z + g z * w z = h z := by
    intro z hz
    have heq_nhds : deriv w =ᶠ[𝓝 z] fun ζ ↦ (Y ζ).2 :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.eball z₀ r, isOpen_eball.mem_nhds hz, hderiv_w⟩
    have hd2 := ((ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt z (hY_ode z hz)).deriv
    simp only [Function.comp_def, ContinuousLinearMap.coe_snd', secondOrderCompanionCLM_apply,
      Prod.snd_add] at hd2
    rw [heq_nhds.deriv_eq, hd2, hderiv_w hz]
    ring
  -- Identify the scalar power series of `w` with `ofScalars ℂ a`.
  have hcoeff := iteratedDeriv_div_factorial_eq_secondOrderODESeriesCoeff
    isOpen_eball (mem_eball_self hr) hf hg hw_diff hw_ode
  have hseries_eq : q = FormalMultilinearSeries.ofScalars ℂ a := by
    refine funext fun n ↦ ContinuousMultilinearMap.ext fun v ↦ ?_
    rw [q.apply_eq_prod_smul_coeff, FormalMultilinearSeries.ofScalars,
      smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      List.prod_ofFn, smul_eq_mul, smul_eq_mul, mul_comm]
    congr 1
    have hfac := hw_ps₀.factorial_smul 1 n
    rw [← iteratedDeriv_eq_iteratedFDeriv, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul] at hfac
    have hq_coeff : (n.factorial : ℂ) * q.coeff n = iteratedDeriv n w z₀ := hfac
    have hnf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hqn : q.coeff n = iteratedDeriv n w z₀ / n.factorial := by
      rw [← hq_coeff, mul_div_cancel_left₀ _ hnf]
    rw [hqn, congrFun hcoeff n, hw0, hw1]
  rw [hseries_eq] at hw_ps₀
  refine ⟨w, hw_ps₀, hw_diff, hw_ode, hw0, hw1, fun u hu hu_ode hu0 hu1 ↦ ?_⟩
  exact eqOn_of_secondOrderODE isOpen_eball isPreconnected_eball (mem_eball_self hr)
    hf hg hu hw_diff hu_ode hw_ode (hu0.trans hw0.symm) (hu1.trans hw1.symm)

/-- **Power-series form of the ordinary-point theorem (DLMF 2.7.1).** If `f` and `g` have power
series `fc` and `gc` on `Metric.eball z₀ r`, and `a : ℕ → ℂ` satisfies `a 0 = w₀`, `a 1 = w₁`, and
the homogeneous two-step recursion, then `z ↦ ∑' n, a n * (z - z₀) ^ n` converges on the whole disc
`Metric.eball z₀ r` and is the unique holomorphic solution on the disc with `w(z₀) = w₀` and
`w'(z₀) = w₁`. -/
theorem exists_hasFPowerSeriesOnBall_secondOrderODE_of_coeff {f g : ℂ → ℂ} {fc gc a : ℕ → ℂ}
    {z₀ : ℂ} {r : ℝ≥0∞} {w₀ w₁ : ℂ}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ fc) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ gc) z₀ r)
    (ha0 : a 0 = w₀) (ha1 : a 1 = w₁)
    (ha : ∀ n : ℕ, ((n : ℂ) + 1) * ((n : ℂ) + 2) * a (n + 2) =
      -∑ j ∈ Finset.range (n + 1), (((j : ℂ) + 1) * fc (n - j) * a (j + 1) + gc (n - j) * a j)) :
    ∃ w : ℂ → ℂ,
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r ∧
      (∀ z ∈ Metric.eball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      DifferentiableOn ℂ w (Metric.eball z₀ r) ∧
      (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        (∀ z ∈ Metric.eball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.eball z₀ r) := by
  have hfc : (fun k ↦ iteratedDeriv k f z₀ / k.factorial) = fc := by
    funext k
    have hfac := hf.factorial_smul 1 k
    rw [← iteratedDeriv_eq_iteratedFDeriv, FormalMultilinearSeries.ofScalars_apply_eq,
      one_pow, smul_eq_mul, mul_one, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul] at hfac
    have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    rw [← hfac, mul_div_cancel_left₀ _ hkf]
  have hgc : (fun k ↦ iteratedDeriv k g z₀ / k.factorial) = gc := by
    funext k
    have hfac := hg.factorial_smul 1 k
    rw [← iteratedDeriv_eq_iteratedFDeriv, FormalMultilinearSeries.ofScalars_apply_eq,
      one_pow, smul_eq_mul, mul_one, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul] at hfac
    have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    rw [← hfac, mul_div_cancel_left₀ _ hkf]
  have h0c : (fun k ↦ iteratedDeriv k (fun _ : ℂ ↦ (0 : ℂ)) z₀ / k.factorial) = 0 := by
    funext k; simp
  have ha_eq : a = secondOrderODESeriesCoeff fc gc 0 w₀ w₁ := by
    rw [eq_secondOrderODESeriesCoeff_iff]
    refine ⟨ha0, ha1, fun n ↦ ?_⟩
    rw [Pi.zero_apply, zero_sub, ha n]
  obtain ⟨w, hw_ps, hw_diff, hw_ode, hw0, hw1, huniq⟩ :=
    exists_hasFPowerSeriesOnBall_secondOrderODE hf.r_pos hf.analyticOnNhd.differentiableOn
      hg.analyticOnNhd.differentiableOn (differentiableOn_const (0 : ℂ)) w₀ w₁
  rw [hfc, hgc, h0c, ← ha_eq] at hw_ps
  refine ⟨w, hw_ps, fun z hz ↦ ?_, hw_diff, hw_ode, hw0, hw1, huniq⟩
  have hsub : z - z₀ ∈ Metric.eball (0 : ℂ) r := by
    simpa [mem_eball, edist_dist, dist_eq_norm] using hz
  have hsum := hw_ps.hasSum hsub
  rw [add_sub_cancel] at hsum
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hsum

/-- **Ordinary-point theorem on a finite Euclidean disc `Metric.ball z₀ R`.** If `f` and `g` are
holomorphic on `Metric.ball z₀ R` (`0 < R`), then for all `w₀, w₁ ∈ ℂ` there exists a unique
holomorphic solution `w` on `Metric.ball z₀ R` of `w'' + f w' + g w = 0` with `w(z₀) = w₀` and
`w'(z₀) = w₁`, whose Taylor series around `z₀` converges at every point of `Metric.ball z₀ R`. -/
theorem exists_differentiableOn_ball_secondOrderODE {f g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hg : DifferentiableOn ℂ g (Metric.ball z₀ R)) (w₀ w₁ : ℂ) :
    let a := secondOrderODESeriesCoeff
      (fun k ↦ iteratedDeriv k f z₀ / k.factorial)
      (fun k ↦ iteratedDeriv k g z₀ / k.factorial) 0 w₀ w₁
    ∃ w : ℂ → ℂ,
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ (ENNReal.ofReal R) ∧
      (∀ z ∈ Metric.ball z₀ R, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      DifferentiableOn ℂ w (Metric.ball z₀ R) ∧
      (∀ z ∈ Metric.ball z₀ R, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.ball z₀ R) →
        (∀ z ∈ Metric.ball z₀ R, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.ball z₀ R) := by
  intro a
  have hr : 0 < ENNReal.ofReal R := ENNReal.ofReal_pos.mpr hR
  rw [← Metric.eball_ofReal] at hf hg
  have h0c : (fun k ↦ iteratedDeriv k (fun _ : ℂ ↦ (0 : ℂ)) z₀ / k.factorial) = 0 := by
    funext k; simp
  obtain ⟨w, hw_ps, hw_diff, hw_ode, hw0, hw1, huniq⟩ :=
    exists_hasFPowerSeriesOnBall_secondOrderODE hr hf hg (differentiableOn_const (0 : ℂ)) w₀ w₁
  rw [h0c] at hw_ps
  rw [Metric.eball_ofReal] at hw_diff hw_ode huniq
  refine ⟨w, hw_ps, fun z hz ↦ ?_, hw_diff, hw_ode, hw0, hw1, huniq⟩
  have hsub : z - z₀ ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal R) := by
    rw [Metric.eball_ofReal, mem_ball_zero_iff, ← dist_eq_norm]
    exact mem_ball.mp hz
  have hsum := hw_ps.hasSum hsub
  rw [add_sub_cancel] at hsum
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hsum

/-- **Global existence and uniqueness for entire second-order linear ODEs.** If `f`, `g`, and `h`
are entire, then for every `z₀, w₀, w₁ ∈ ℂ` there exists a unique entire function `w : ℂ → ℂ`
solving `w''(z) + f(z) w'(z) + g(z) w(z) = h(z)` with `w(z₀) = w₀` and `w'(z₀) = w₁`. -/
theorem existsUnique_differentiable_secondOrderODE {f g h : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hh : Differentiable ℂ h)
    (z₀ w₀ w₁ : ℂ) :
    ∃! w : ℂ → ℂ, Differentiable ℂ w ∧
      (∀ z, deriv (deriv w) z + f z * deriv w z + g z * w z = h z) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  obtain ⟨w, -, hw_diff, hw_ode, hw0, hw1, -⟩ :=
    exists_hasFPowerSeriesOnBall_secondOrderODE (r := ⊤) ENNReal.zero_lt_top
      hf.differentiableOn hg.differentiableOn hh.differentiableOn w₀ w₁
  rw [eball_top, differentiableOn_univ] at hw_diff
  refine ⟨w, ⟨hw_diff, fun z ↦ hw_ode z (by simp), hw0, hw1⟩, ?_⟩
  rintro u ⟨hu_diff, hu_ode, hu0, hu1⟩
  exact eq_of_secondOrderODE z₀ hf hg hu_diff hw_diff hu_ode
    (fun z ↦ hw_ode z (by simp)) (hu0.trans hw0.symm) (hu1.trans hw1.symm)

/-- **Decomposition in a fundamental solution pair on a preconnected open domain.** If `u₁` and
`u₂` are holomorphic solutions of `w'' + f w' + g w = 0` on a preconnected open set `U` whose
Wronskian `W₀ = u₁(z₀) u₂'(z₀) - u₁'(z₀) u₂(z₀)` at `z₀ ∈ U` is nonzero, then every holomorphic
solution `w` on `U` is given on `U` by Cramer's linear combination of `u₁` and `u₂`. -/
theorem eqOn_linear_combination_of_secondOrderODE {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f g u₁ u₂ w : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hu₁ : DifferentiableOn ℂ u₁ U) (hu₂ : DifferentiableOn ℂ u₂ U)
    (hw : DifferentiableOn ℂ w U)
    (hode₁ : ∀ z ∈ U, deriv (deriv u₁) z + f z * deriv u₁ z + g z * u₁ z = 0)
    (hode₂ : ∀ z ∈ U, deriv (deriv u₂) z + f z * deriv u₂ z + g z * u₂ z = 0)
    (hodew : ∀ z ∈ U, deriv (deriv w) z + f z * deriv w z + g z * w z = 0)
    (hW : u₁ z₀ * deriv u₂ z₀ - deriv u₁ z₀ * u₂ z₀ ≠ 0) :
    EqOn w (fun z ↦
      (u₁ z₀ * deriv u₂ z₀ - deriv u₁ z₀ * u₂ z₀)⁻¹ *
          (w z₀ * deriv u₂ z₀ - deriv w z₀ * u₂ z₀) * u₁ z +
        (u₁ z₀ * deriv u₂ z₀ - deriv u₁ z₀ * u₂ z₀)⁻¹ *
          (deriv w z₀ * u₁ z₀ - w z₀ * deriv u₁ z₀) * u₂ z) U := by
  set W₀ := u₁ z₀ * deriv u₂ z₀ - deriv u₁ z₀ * u₂ z₀
  set c₁ := W₀⁻¹ * (w z₀ * deriv u₂ z₀ - deriv w z₀ * u₂ z₀)
  set c₂ := W₀⁻¹ * (deriv w z₀ * u₁ z₀ - w z₀ * deriv u₁ z₀)
  set L : ℂ → ℂ := fun z ↦ c₁ * u₁ z + c₂ * u₂ z
  have hL_diff : DifferentiableOn ℂ L U := (hu₁.const_mul c₁).add (hu₂.const_mul c₂)
  have hL_deriv : EqOn (deriv L) (fun z ↦ c₁ * deriv u₁ z + c₂ * deriv u₂ z) U := fun z hz ↦ by
    have hd₁ := (hu₁.differentiableAt (hUo.mem_nhds hz)).hasDerivAt.const_mul c₁
    have hd₂ := (hu₂.differentiableAt (hUo.mem_nhds hz)).hasDerivAt.const_mul c₂
    exact (hd₁.add hd₂).deriv
  have hL_ode : ∀ z ∈ U, deriv (deriv L) z + f z * deriv L z + g z * L z = 0 := by
    intro z hz
    have heq_nhds : deriv L =ᶠ[𝓝 z] fun ζ ↦ c₁ * deriv u₁ ζ + c₂ * deriv u₂ ζ :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hUo.mem_nhds hz, hL_deriv⟩
    have hd₁' := ((hu₁.deriv hUo).differentiableAt (hUo.mem_nhds hz)).hasDerivAt.const_mul c₁
    have hd₂' := ((hu₂.deriv hUo).differentiableAt (hUo.mem_nhds hz)).hasDerivAt.const_mul c₂
    have hd' : deriv (fun ζ ↦ c₁ * deriv u₁ ζ + c₂ * deriv u₂ ζ) z =
        c₁ * deriv (deriv u₁) z + c₂ * deriv (deriv u₂) z := (hd₁'.add hd₂').deriv
    rw [heq_nhds.deriv_eq, hd', hL_deriv hz]
    dsimp only [L]
    linear_combination c₁ * hode₁ z hz + c₂ * hode₂ z hz
  have hL0 : w z₀ = L z₀ := by
    dsimp only [L, c₁, c₂]
    have hmul : W₀ * (W₀⁻¹ * (w z₀ * deriv u₂ z₀ - deriv w z₀ * u₂ z₀) * u₁ z₀ +
        W₀⁻¹ * (deriv w z₀ * u₁ z₀ - w z₀ * deriv u₁ z₀) * u₂ z₀) = W₀ * w z₀ := by
      calc
        W₀ * (W₀⁻¹ * (w z₀ * deriv u₂ z₀ - deriv w z₀ * u₂ z₀) * u₁ z₀ +
            W₀⁻¹ * (deriv w z₀ * u₁ z₀ - w z₀ * deriv u₁ z₀) * u₂ z₀) =
            (W₀ * W₀⁻¹) * ((w z₀ * deriv u₂ z₀ - deriv w z₀ * u₂ z₀) * u₁ z₀ +
              (deriv w z₀ * u₁ z₀ - w z₀ * deriv u₁ z₀) * u₂ z₀) := by ring
        _ = W₀ * w z₀ := by rw [mul_inv_cancel₀ hW, one_mul]; dsimp only [W₀]; ring
    exact (mul_right_inj' hW).mp hmul.symm
  have hL1 : deriv w z₀ = deriv L z₀ := by
    rw [hL_deriv hz₀]
    dsimp only [c₁, c₂]
    have hmul : W₀ * (W₀⁻¹ * (w z₀ * deriv u₂ z₀ - deriv w z₀ * u₂ z₀) * deriv u₁ z₀ +
        W₀⁻¹ * (deriv w z₀ * u₁ z₀ - w z₀ * deriv u₁ z₀) * deriv u₂ z₀) = W₀ * deriv w z₀ := by
      calc
        W₀ * (W₀⁻¹ * (w z₀ * deriv u₂ z₀ - deriv w z₀ * u₂ z₀) * deriv u₁ z₀ +
            W₀⁻¹ * (deriv w z₀ * u₁ z₀ - w z₀ * deriv u₁ z₀) * deriv u₂ z₀) =
            (W₀ * W₀⁻¹) * ((w z₀ * deriv u₂ z₀ - deriv w z₀ * u₂ z₀) * deriv u₁ z₀ +
              (deriv w z₀ * u₁ z₀ - w z₀ * deriv u₁ z₀) * deriv u₂ z₀) := by ring
        _ = W₀ * deriv w z₀ := by rw [mul_inv_cancel₀ hW, one_mul]; dsimp only [W₀]; ring
    exact (mul_right_inj' hW).mp hmul.symm
  exact eqOn_of_secondOrderODE hUo hUc hz₀ hf hg hw hL_diff hodew hL_ode hL0 hL1

/-- **Decomposition in an entire fundamental solution pair.** If `u₁` and `u₂` are entire solutions
of `w'' + f w' + g w = 0` with nonvanishing Wronskian at `z₀`, then every entire solution `w` is
the explicit Cramer linear combination of `u₁` and `u₂`. -/
theorem eq_linear_combination_of_secondOrderODE {f g u₁ u₂ w : ℂ → ℂ} (z₀ : ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hu₁ : Differentiable ℂ u₁) (hu₂ : Differentiable ℂ u₂) (hw : Differentiable ℂ w)
    (hode₁ : ∀ z, deriv (deriv u₁) z + f z * deriv u₁ z + g z * u₁ z = 0)
    (hode₂ : ∀ z, deriv (deriv u₂) z + f z * deriv u₂ z + g z * u₂ z = 0)
    (hodew : ∀ z, deriv (deriv w) z + f z * deriv w z + g z * w z = 0)
    (hW : u₁ z₀ * deriv u₂ z₀ - deriv u₁ z₀ * u₂ z₀ ≠ 0) :
    w = fun z ↦
      (u₁ z₀ * deriv u₂ z₀ - deriv u₁ z₀ * u₂ z₀)⁻¹ *
          (w z₀ * deriv u₂ z₀ - deriv w z₀ * u₂ z₀) * u₁ z +
        (u₁ z₀ * deriv u₂ z₀ - deriv u₁ z₀ * u₂ z₀)⁻¹ *
          (deriv w z₀ * u₁ z₀ - w z₀ * deriv u₁ z₀) * u₂ z := by
  funext z
  exact eqOn_linear_combination_of_secondOrderODE isOpen_univ isPreconnected_univ (mem_univ z₀)
    hf.differentiableOn hg.differentiableOn hu₁.differentiableOn hu₂.differentiableOn
    hw.differentiableOn (fun ζ _ ↦ hode₁ ζ) (fun ζ _ ↦ hode₂ ζ) (fun ζ _ ↦ hodew ζ) hW (mem_univ z)

/-! The following checks verify the Taylor recursion on Airy's equation and global uniqueness on
elementary equations. -/

example (w₀ w₁ : ℂ) :
    secondOrderODESeriesCoeff 0 (Pi.single 1 (-1)) 0 w₀ w₁ 2 = 0 := by
  simp

example (w₀ w₁ : ℂ) (n : ℕ) :
    ((n : ℂ) + 2) * ((n : ℂ) + 3) *
        secondOrderODESeriesCoeff 0 (Pi.single 1 (-1)) 0 w₀ w₁ (n + 3) =
      secondOrderODESeriesCoeff 0 (Pi.single 1 (-1)) 0 w₀ w₁ n := by
  have h := mul_secondOrderODESeriesCoeff_add_two (0 : ℕ → ℂ) (Pi.single 1 (-1)) 0 w₀ w₁ (n + 1)
  push_cast at h
  have hcast : ((n : ℂ) + 1 + 1) * ((n : ℂ) + 1 + 2) = ((n : ℂ) + 2) * ((n : ℂ) + 3) := by ring
  rw [hcast] at h
  rw [h, Pi.zero_apply, zero_sub, Finset.sum_eq_single n]
  · simp
  · intro j hj hjn
    have hjle : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hne : n + 1 - j ≠ 1 := by omega
    simp [Pi.single_eq_of_ne hne]
  · simp

example {w : ℂ → ℂ} (z₀ w₀ w₁ : ℂ) (hw : Differentiable ℂ w)
    (hode : ∀ z, deriv (deriv w) z = 0) (h0 : w z₀ = w₀) (h1 : deriv w z₀ = w₁) :
    w = fun z ↦ w₀ + w₁ * (z - z₀) := by
  have hd_lin : ∀ ζ, HasDerivAt (fun z : ℂ ↦ w₀ + w₁ * (z - z₀)) w₁ ζ := fun ζ ↦ by
    have h := (((hasDerivAt_id ζ).sub_const z₀).const_mul w₁).const_add w₀
    rwa [mul_one] at h
  have hd1 : deriv (fun ζ : ℂ ↦ w₀ + w₁ * (ζ - z₀)) = fun _ ↦ w₁ :=
    funext fun ζ ↦ (hd_lin ζ).deriv
  refine eq_of_secondOrderODE (f := 0) (g := 0) (h := 0) z₀
    (differentiable_const 0) (differentiable_const 0) hw (by fun_prop)
    (fun z ↦ by simp [hode z]) (fun z ↦ by simp [hd1]) (by simp [h0]) ?_
  rw [h1, hd1]

end SecondOrder

end TauCeti
