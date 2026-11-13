/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.LinearEquation
public import TauCeti.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Analysis.Analytic.TaylorSeries
import TauCeti.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Calculus.FDeriv.Matrix
import TauCeti.Analysis.Complex.TaylorSeries

/-!
# Linear differential equations at ordinary points in the complex domain

This module develops existence, uniqueness, and Taylor-series representation for complex linear
ordinary differential equations around an ordinary point `z₀ ∈ ℂ`, in three layers:

* **Banach-space first-order linear systems** `v'(z) = A(z) (v(z)) + b(z)`:
  - On any open preconnected set `U ⊆ ℂ`, two solutions that agree at a point `z₀ ∈ U` where `A` is
    analytic coincide throughout `U`, with no regularity hypothesis on `b`
    (`TauCeti.eqOn_of_hasDerivAt_clm_apply_add`).
  - On an open extended disc `Metric.eball z₀ r` (`0 < r ≤ ∞`) where `A` and `b` are holomorphic (or
    admit formal power series), every initial value `v₀` determines a unique holomorphic solution
    whose Taylor series `TauCeti.mkPiRingSeries ℂ (TauCeti.linearSystemCoeff ...)` converges on the
    entire disc (`TauCeti.exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add`,
    `TauCeti.exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add_of_hasFPowerSeriesOnBall`, and
    `TauCeti.existsUnique_hasDerivAt_clm_apply_add` for entire systems).

* **Monic scalar equations** `TauCeti.LinearEquation U n`:
  - On any preconnected open domain `U`, solutions are uniquely determined by their initial `n`-jet
    (`LinearEquation.IsSolution.eqOn_of_isPreconnected`, `LinearEquation.initialJet_injective`), so
    `E.solutionSpace` has dimension at most `n`
    (`LinearEquation.finrank_solutionSpace_le_of_isPreconnected`).
  - On any open disc `(U : Set ℂ) = Metric.eball c r`, the initial-jet map at any point `a ∈ U`
    (not necessarily the disc center `c`) is a `ℂ`-linear equivalence
    `E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ)` (`LinearEquation.initialJetEquivOfEqEBall`, and
    `LinearEquation.initialJetEquivTop` on `⊤`), giving `Module.finrank ℂ E.solutionSpace = n`
    whenever `0 < r` (`LinearEquation.finrank_solutionSpace_of_eq_eball`,
    `LinearEquation.finrank_solutionSpace_top`).

* **Second-order scalar equations** `w'' + f(z) w' + g(z) w = h(z)`:
  - On preconnected open sets `U` (and on `ℂ`), solutions are uniquely determined by `(w z₀, w' z₀)`
    at any ordinary point `z₀ ∈ U` where `f` and `g` are analytic and the equation holds near `z₀`
    (`TauCeti.eqOn_of_secondOrder_linear_ode`, `TauCeti.eq_of_entire_secondOrder_linear_ode`).
  - On open discs `Metric.eball z₀ r` (`0 < r ≤ ∞`), `Metric.ball z₀ r`, and `ℂ`, inhomogeneous
    initial-value problems admit unique holomorphic solutions
    (`TauCeti.exists_secondOrder_linear_ode_eball`,
    `TauCeti.existsUnique_entire_secondOrder_linear_ode`), and homogeneous solutions (`h = 0`) are
    represented across the full disc by the Cauchy-product recurrence `TauCeti.ordinaryPointCoeff`
    (`TauCeti.hasFPowerSeriesOnBall_of_ordinaryPoint_solution`,
    `TauCeti.exists_ordinaryPoint_solution_eball`, `TauCeti.exists_ordinaryPoint_solution_ball`,
    `TauCeti.exists_entire_ordinaryPoint_solution`).

### Coefficient normalization

`TauCeti.linearSystemCoeff` and `TauCeti.ordinaryPointCoeff` take and produce **factorial-scaled
Taylor coefficients** `(n ! : ℂ)⁻¹ • iteratedDeriv n f z₀` (the coefficients of `∑ₙ cₙ (z - z₀)ⁿ`),
whereas `LinearEquation.initialJet` records the **unscaled derivatives** `iteratedDeriv j y a` for
`j < n`.

## Implementation notes

Full-disc convergence (`TauCeti.le_radius_mkPiRingSeries_linearSystemCoeff`) is proved directly by
Cauchy's method of majorants: on every smaller radius `ρ < r`, Cauchy coefficient bounds dominate
`‖cₙ‖ ρⁿ` by a scalar sequence satisfying `(n + 1) μ_{n+1} = (n + 1 + α) μₙ`, whose consecutive
ratios tend to `1`. Termwise differentiation (`HasFPowerSeriesOnBall.deriv`) and Banach-space
Cauchy products (`HasFPowerSeriesOnBall.clm_apply`) verify the differential equation on the disc,
while global uniqueness on preconnected open domains combines local power-series vanishing at `z₀`
with analytic continuation (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`).

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §1.1.
* NIST Digital Library of Mathematical Functions, §2.7(i), <https://dlmf.nist.gov/2.7>.
* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, 1955, Ch. 3, §6.
-/

public noncomputable section

open Complex Filter Finset Metric Set TopologicalSpace Topology
open scoped BigOperators ENNReal Matrix NNReal Nat

namespace TauCeti

/-! ### First-order complex linear ODE systems in a Banach space -/

section FirstOrderSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Formal Taylor coefficients of the solution to `v'(z) = A(z) (v(z)) + b(z)` with `v(z₀) = v₀`,
given the Taylor coefficient sequences `A` and `b` around `z₀`. -/
def linearSystemCoeff (A : ℕ → E →L[ℂ] E) (b : ℕ → E) (v₀ : E) : ℕ → E
  | 0 => v₀
  | n + 1 => ((n + 1 : ℂ))⁻¹ • (b n + ∑ k : Fin (n + 1), A (n - k) (linearSystemCoeff A b v₀ k))

/-- The zeroth Taylor coefficient of the system solution is the initial value `v₀`. -/
@[simp]
theorem linearSystemCoeff_zero (A : ℕ → E →L[ℂ] E) (b : ℕ → E) (v₀ : E) :
    linearSystemCoeff A b v₀ 0 = v₀ := by
  rw [linearSystemCoeff]

/-- Recurrence for the `(n + 1)`-st Taylor coefficient of a first-order linear system. -/
theorem linearSystemCoeff_succ (A : ℕ → E →L[ℂ] E) (b : ℕ → E) (v₀ : E) (n : ℕ) :
    linearSystemCoeff A b v₀ (n + 1) =
      ((n + 1 : ℂ))⁻¹ • (b n + ∑ k ∈ Finset.range (n + 1),
        A (n - k) (linearSystemCoeff A b v₀ k)) := by
  rw [linearSystemCoeff, Fin.sum_univ_eq_sum_range (fun k ↦ A (n - k) (linearSystemCoeff A b v₀ k))]

/-- Cleared-denominator form of `TauCeti.linearSystemCoeff_succ`. -/
theorem natCast_add_one_smul_linearSystemCoeff_succ (A : ℕ → E →L[ℂ] E) (b : ℕ → E) (v₀ : E)
    (n : ℕ) :
    ((n + 1 : ℂ)) • linearSystemCoeff A b v₀ (n + 1) =
      b n + ∑ k ∈ Finset.range (n + 1), A (n - k) (linearSystemCoeff A b v₀ k) := by
  rw [linearSystemCoeff_succ, smul_inv_smul₀ (Nat.cast_add_one_ne_zero n)]

/-- Uniqueness characterization of `TauCeti.linearSystemCoeff` by its initial value and
cleared-denominator Cauchy-product recurrence. -/
theorem eq_linearSystemCoeff_iff {A : ℕ → E →L[ℂ] E} {b c : ℕ → E} {v₀ : E} :
    c = linearSystemCoeff A b v₀ ↔
      c 0 = v₀ ∧ ∀ n : ℕ, ((n + 1 : ℂ)) • c (n + 1) =
        b n + ∑ k ∈ Finset.range (n + 1), A (n - k) (c k) := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨linearSystemCoeff_zero A b v₀, natCast_add_one_smul_linearSystemCoeff_succ A b v₀⟩
  · rintro ⟨hc0, hstep⟩
    ext n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      rcases n with _ | n
      · simpa using hc0
      · have hn : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
        rw [linearSystemCoeff_succ, ← inv_smul_smul₀ hn (c (n + 1)), hstep n]
        congr 2
        exact Finset.sum_congr rfl fun k hk ↦ by rw [ih k (Finset.mem_range.mp hk)]

/-- Homogeneous linear systems with zero initial value have identically zero Taylor coefficients. -/
@[simp]
theorem linearSystemCoeff_zero_zero (A : ℕ → E →L[ℂ] E) :
    linearSystemCoeff A 0 0 = 0 := by
  symm
  exact eq_linearSystemCoeff_iff.mpr ⟨rfl, fun n ↦ by simp⟩

/-- `TauCeti.linearSystemCoeff` is additive in the forcing series `b` and initial value `v₀`. -/
theorem linearSystemCoeff_add (A : ℕ → E →L[ℂ] E) (b₁ b₂ : ℕ → E) (v₁ v₂ : E) :
    linearSystemCoeff A (b₁ + b₂) (v₁ + v₂) =
      linearSystemCoeff A b₁ v₁ + linearSystemCoeff A b₂ v₂ := by
  symm
  refine eq_linearSystemCoeff_iff.mpr ⟨by simp, fun n ↦ ?_⟩
  simp only [Pi.add_apply, smul_add, natCast_add_one_smul_linearSystemCoeff_succ, map_add,
    Finset.sum_add_distrib]
  abel

/-- `TauCeti.linearSystemCoeff` commutes with complex scalar multiplication in `(b, v₀)`. -/
theorem linearSystemCoeff_smul (A : ℕ → E →L[ℂ] E) (c : ℂ) (b : ℕ → E) (v₀ : E) :
    linearSystemCoeff A (c • b) (c • v₀) = c • linearSystemCoeff A b v₀ := by
  symm
  refine eq_linearSystemCoeff_iff.mpr ⟨by simp, fun n ↦ ?_⟩
  simp only [Pi.smul_apply, smul_comm ((n + 1 : ℂ)) c,
    natCast_add_one_smul_linearSystemCoeff_succ, smul_add, Finset.smul_sum, map_smul]

/-- `TauCeti.linearSystemCoeff` commutes with negation in `(b, v₀)`. -/
theorem linearSystemCoeff_neg (A : ℕ → E →L[ℂ] E) (b : ℕ → E) (v₀ : E) :
    linearSystemCoeff A (-b) (-v₀) = -linearSystemCoeff A b v₀ := by
  simpa using linearSystemCoeff_smul A (-1 : ℂ) b v₀

/-- `TauCeti.linearSystemCoeff` commutes with subtraction in `(b, v₀)`. -/
theorem linearSystemCoeff_sub (A : ℕ → E →L[ℂ] E) (b₁ b₂ : ℕ → E) (v₁ v₂ : E) :
    linearSystemCoeff A (b₁ - b₂) (v₁ - v₂) =
      linearSystemCoeff A b₁ v₁ - linearSystemCoeff A b₂ v₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg v₁ v₂, linearSystemCoeff_add, linearSystemCoeff_neg,
    sub_eq_add_neg]

private def majorantSeq (μ₀ α : ℝ) : ℕ → ℝ
  | 0 => μ₀
  | k + 1 => ((k + 1 + α) / (k + 1)) * majorantSeq μ₀ α k

private theorem majorantSeq_pos {μ₀ α : ℝ} (hμ₀ : 0 < μ₀) (hα : 0 ≤ α) (n : ℕ) :
    0 < majorantSeq μ₀ α n := by
  induction n <;> dsimp [majorantSeq] <;> positivity

private theorem majorantSeq_step (μ₀ α : ℝ) (n : ℕ) :
    (n + 1 : ℝ) * majorantSeq μ₀ α (n + 1) = (n + 1 + α) * majorantSeq μ₀ α n := by
  dsimp [majorantSeq]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn1]

private theorem majorantSeq_sum_le {μ₀ α : ℝ} (hμ₀ : 0 < μ₀) (hα : 0 ≤ α) (n : ℕ) :
    μ₀ + α * ∑ k ∈ Finset.range (n + 1), majorantSeq μ₀ α k ≤
      (n + 1 : ℝ) * majorantSeq μ₀ α (n + 1) := by
  induction n with
  | zero =>
    rw [majorantSeq_step μ₀ α 0]
    simp only [range_one, sum_singleton, Nat.cast_zero, zero_add, majorantSeq]
    linarith
  | succ n ih =>
    rw [sum_range_succ, mul_add, majorantSeq_step μ₀ α (n + 1)]
    push_cast
    linarith [majorantSeq_pos hμ₀ hα (n + 1)]

private theorem summable_majorantSeq_mul_pow {μ₀ α q : ℝ} (hμ₀ : 0 < μ₀) (hα : 0 ≤ α)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    Summable fun n ↦ majorantSeq μ₀ α n * q ^ n := by
  refine summable_of_ratio_test_tendsto_lt_one hq₁
    (Eventually.of_forall fun n ↦ ne_of_gt (mul_pos (majorantSeq_pos hμ₀ hα n) (pow_pos hq₀ n))) ?_
  have hrat : (fun n : ℕ ↦ ‖majorantSeq μ₀ α (n + 1) * q ^ (n + 1)‖ /
      ‖majorantSeq μ₀ α n * q ^ n‖) = fun n : ℕ ↦ (1 + α / (n + 1 : ℝ)) * q := by
    ext n
    have h1 := majorantSeq_pos hμ₀ hα n
    have h3 := pow_pos hq₀ n
    rw [Real.norm_of_nonneg (mul_pos (majorantSeq_pos hμ₀ hα (n + 1)) (pow_pos hq₀ (n + 1))).le,
      Real.norm_of_nonneg (mul_pos h1 h3).le]
    dsimp [majorantSeq]
    rw [pow_succ]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [h1.ne', h3.ne', hn1]
  rw [hrat]
  have hinv : Tendsto (fun n : ℕ ↦ α / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).mul (tendsto_const_nhds (x := q))

private theorem norm_linearSystemCoeff_mul_pow_le_majorantSeq
    {A : ℕ → E →L[ℂ] E} {b : ℕ → E} {v₀ : E} {ρ CA Cb : ℝ}
    (hρ : 0 ≤ ρ) (hCA_nonneg : 0 ≤ CA)
    (hCA : ∀ n, ‖A n‖ * ρ ^ n ≤ CA) (hCb : ∀ n, ‖b n‖ * ρ ^ n ≤ Cb) (n : ℕ) :
    ‖linearSystemCoeff A b v₀ n‖ * ρ ^ n ≤
      majorantSeq (max ‖v₀‖ (ρ * Cb) + 1) (ρ * CA) n := by
  let μ₀ : ℝ := max ‖v₀‖ (ρ * Cb) + 1
  let α : ℝ := ρ * CA
  have hμ₀ : 0 < μ₀ := by positivity
  have hα : 0 ≤ α := mul_nonneg hρ hCA_nonneg
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | n
    · simp only [linearSystemCoeff_zero, pow_zero, mul_one, majorantSeq]
      exact (le_max_left _ _).trans (lt_add_one _).le
    · have hn_norm : ‖((n + 1 : ℂ))‖ = (n + 1 : ℝ) := mod_cast Complex.norm_natCast (n + 1)
      have hlhs : ((n + 1 : ℝ)) * (‖linearSystemCoeff A b v₀ (n + 1)‖ * ρ ^ (n + 1)) =
          ‖((n + 1 : ℂ)) • linearSystemCoeff A b v₀ (n + 1)‖ * ρ ^ (n + 1) := by
        rw [norm_smul, hn_norm, mul_assoc]
      have hbound : ((n + 1 : ℝ)) * (‖linearSystemCoeff A b v₀ (n + 1)‖ * ρ ^ (n + 1)) ≤
          (n + 1 : ℝ) * majorantSeq μ₀ α (n + 1) := by
        rw [hlhs, natCast_add_one_smul_linearSystemCoeff_succ]
        calc
          ‖b n + ∑ k ∈ Finset.range (n + 1), A (n - k) (linearSystemCoeff A b v₀ k)‖ * ρ ^ (n + 1)
              ≤ (‖b n‖ + ∑ k ∈ Finset.range (n + 1),
                  ‖A (n - k) (linearSystemCoeff A b v₀ k)‖) * ρ ^ (n + 1) := by
                gcongr
                exact (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
          _ = ρ * (‖b n‖ * ρ ^ n) + ρ * ∑ k ∈ Finset.range (n + 1),
                  ‖A (n - k) (linearSystemCoeff A b v₀ k)‖ * ρ ^ n := by
                rw [pow_succ, add_mul, Finset.sum_mul, Finset.mul_sum]
                exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun _ _ ↦ by ring)
          _ ≤ ρ * Cb + ρ * ∑ k ∈ Finset.range (n + 1), CA * majorantSeq μ₀ α k := by
                refine add_le_add (mul_le_mul_of_nonneg_left (hCb n) hρ)
                  (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk ↦ ?_) hρ)
                have hkn : n - k + k = n :=
                  Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
                calc
                  ‖A (n - k) (linearSystemCoeff A b v₀ k)‖ * ρ ^ n
                      ≤ (‖A (n - k)‖ * ‖linearSystemCoeff A b v₀ k‖) * ρ ^ (n - k + k) := by
                        rw [hkn]; gcongr; exact (A (n - k)).le_opNorm _
                  _ = (‖A (n - k)‖ * ρ ^ (n - k)) *
                        (‖linearSystemCoeff A b v₀ k‖ * ρ ^ k) := by rw [pow_add]; ring
                  _ ≤ CA * majorantSeq μ₀ α k :=
                        mul_le_mul (hCA (n - k)) (ih k (Finset.mem_range.mp hk))
                          (by positivity) hCA_nonneg
          _ = ρ * Cb + α * ∑ k ∈ Finset.range (n + 1), majorantSeq μ₀ α k := by
                rw [← Finset.mul_sum]; dsimp [α]; ring
          _ ≤ μ₀ + α * ∑ k ∈ Finset.range (n + 1), majorantSeq μ₀ α k := by
                gcongr; exact (le_max_right _ _).trans (lt_add_one _).le
          _ ≤ (n + 1 : ℝ) * majorantSeq μ₀ α (n + 1) := majorantSeq_sum_le hμ₀ hα n
      exact le_of_mul_le_mul_left hbound (by positivity)

/-- **Cauchy majorant convergence bound for first-order linear systems.** If the formal power series
for `A` and `b` have convergence radius at least `r`, then so does the formal solution series
`mkPiRingSeries ℂ (linearSystemCoeff A b v₀)`. -/
theorem le_radius_mkPiRingSeries_linearSystemCoeff
    {A : ℕ → E →L[ℂ] E} {b : ℕ → E} (v₀ : E) {r : ℝ≥0∞}
    (hA : r ≤ (mkPiRingSeries ℂ A).radius) (hb : r ≤ (mkPiRingSeries ℂ b).radius) :
    r ≤ (mkPiRingSeries ℂ (linearSystemCoeff A b v₀)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun R hRr ↦ ?_
  rcases eq_or_ne R 0 with rfl | hR0
  · simp
  obtain ⟨ρ, hRρ_coe, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hRr
  have hRρ : (R : ℝ) < ρ := ENNReal.coe_lt_coe.mp hRρ_coe
  have hR_pos : (0 : ℝ) < R := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hR0)
  have hρ_pos : (0 : ℝ) < ρ := hR_pos.trans hRρ
  obtain ⟨CA, hCA_pos, hCA⟩ :=
    (mkPiRingSeries ℂ A).norm_mul_pow_le_of_lt_radius (hρr.trans_le hA)
  obtain ⟨Cb, _, hCb⟩ :=
    (mkPiRingSeries ℂ b).norm_mul_pow_le_of_lt_radius (hρr.trans_le hb)
  simp only [norm_mkPiRingSeries] at hCA hCb
  let q : ℝ := R / ρ
  have hq_pos : 0 < q := div_pos hR_pos hρ_pos
  have hq_lt : q < 1 := (div_lt_one hρ_pos).mpr hRρ
  have hμq_sum := summable_majorantSeq_mul_pow (μ₀ := max ‖v₀‖ ((ρ : ℝ) * Cb) + 1)
    (α := (ρ : ℝ) * CA) (by positivity) (mul_nonneg ρ.2 hCA_pos.le) hq_pos hq_lt
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) hμq_sum
  rw [norm_mkPiRingSeries, show (R : ℝ) = ρ * q by dsimp [q]; field_simp [hρ_pos.ne'],
    mul_pow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (norm_linearSystemCoeff_mul_pow_le_majorantSeq ρ.2 hCA_pos.le hCA hCb n)
    (pow_nonneg hq_pos.le n)

variable [CompleteSpace E]

/-- Any solution of `v'(z) = A(z) (v(z)) + b(z)` on `Metric.eball z₀ r`, where `A` and `b` admit
formal power series `mkPiRingSeries ℂ As` and `mkPiRingSeries ℂ bs` on `Metric.eball z₀ r`, is
represented on `Metric.eball z₀ r` by `mkPiRingSeries ℂ (linearSystemCoeff As bs (v z₀))`. -/
theorem hasFPowerSeriesOnBall_of_hasDerivAt_clm_apply_add
    {A : ℂ → E →L[ℂ] E} {b v : ℂ → E} {As : ℕ → E →L[ℂ] E} {bs : ℕ → E}
    {z₀ : ℂ} {r : ℝ≥0∞}
    (hA : HasFPowerSeriesOnBall A (mkPiRingSeries ℂ As) z₀ r)
    (hb : HasFPowerSeriesOnBall b (mkPiRingSeries ℂ bs) z₀ r)
    (hv : ∀ z ∈ Metric.eball z₀ r, HasDerivAt v (A z (v z) + b z) z) :
    HasFPowerSeriesOnBall v (mkPiRingSeries ℂ (linearSystemCoeff As bs (v z₀))) z₀ r := by
  let c : ℕ → E := fun n ↦ (n ! : ℂ)⁻¹ • iteratedDeriv n v z₀
  have hv_diff : DifferentiableOn ℂ v (Metric.eball z₀ r) :=
    fun z hz ↦ (hv z hz).differentiableAt.differentiableWithinAt
  have hv_ps : HasFPowerSeriesOnBall v (mkPiRingSeries ℂ c) z₀ r :=
    hv_diff.hasFPowerSeriesOnBall_eball hA.r_pos
  have hlhs_ps := hv_ps.deriv
  have hrhs_ps := (hA.clm_apply hv_ps).add hb
  have heq : deriv v =ᶠ[𝓝 z₀] fun z ↦ A z (v z) + b z :=
    Filter.eventually_of_mem (Metric.isOpen_eball.mem_nhds (mem_eball_self hA.r_pos))
      fun z hz ↦ (hv z hz).deriv
  have hser := hlhs_ps.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    hrhs_ps.hasFPowerSeriesAt heq
  have hc : c = linearSystemCoeff As bs (v z₀) := by
    refine eq_linearSystemCoeff_iff.mpr ⟨by simp [c], fun n ↦ ?_⟩
    simpa [add_comm] using congrArg (FormalMultilinearSeries.coeff · n) hser
  exact hc ▸ hv_ps

/-- If `A` and `b` are analytic at `z₀` and `v` satisfies `v'(z) = A(z) (v(z)) + b(z)` eventually
near `z₀`, then the factorial-scaled iterated derivatives of `v` at `z₀` equal
`TauCeti.linearSystemCoeff`. -/
theorem inv_factorial_smul_iteratedDeriv_eq_linearSystemCoeff_of_hasDerivAt_clm_apply_add
    {A : ℂ → E →L[ℂ] E} {b v : ℂ → E} {z₀ : ℂ}
    (hA : AnalyticAt ℂ A z₀) (hb : AnalyticAt ℂ b z₀)
    (hv : ∀ᶠ z in 𝓝 z₀, HasDerivAt v (A z (v z) + b z) z) (n : ℕ) :
    (n ! : ℂ)⁻¹ • iteratedDeriv n v z₀ =
      linearSystemCoeff (fun m ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m A z₀)
        (fun m ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m b z₀) (v z₀) n := by
  obtain ⟨r, hr_pos, hr⟩ := EMetric.mem_nhds_iff.mp
    (hA.eventually_analyticAt.and (hb.eventually_analyticAt.and hv))
  have hA_ps := (show DifferentiableOn ℂ A (Metric.eball z₀ r) from
    fun z hz ↦ (hr hz).1.differentiableAt.differentiableWithinAt).hasFPowerSeriesOnBall_eball hr_pos
  have hb_ps := (show DifferentiableOn ℂ b (Metric.eball z₀ r) from
    fun z hz ↦ (hr hz).2.1.differentiableAt.differentiableWithinAt).hasFPowerSeriesOnBall_eball
    hr_pos
  have hv_ps := (show DifferentiableOn ℂ v (Metric.eball z₀ r) from
    fun z hz ↦ (hr hz).2.2.differentiableAt.differentiableWithinAt).hasFPowerSeriesOnBall_eball
    hr_pos
  have hv_ps' := hasFPowerSeriesOnBall_of_hasDerivAt_clm_apply_add hA_ps hb_ps
    fun z hz ↦ (hr hz).2.2
  exact congrFun (mkPiRingSeries_inj.mp
    (hv_ps.hasFPowerSeriesAt.eq_formalMultilinearSeries hv_ps'.hasFPowerSeriesAt)) n

/-- If `A` is analytic at `z₀ ∈ U`, then any two solutions of `v'(z) = A(z) (v(z)) + b(z)` on an
open preconnected set `U ⊆ ℂ` that agree at `z₀` agree throughout `U`. No regularity hypothesis on
`b` is needed, and `A` need only be analytic at `z₀`. -/
theorem eqOn_of_hasDerivAt_clm_apply_add {A : ℂ → E →L[ℂ] E} {b v₁ v₂ : ℂ → E} {U : Set ℂ}
    {z₀ : ℂ} (hU : IsOpen U) (hU_conn : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hA : AnalyticAt ℂ A z₀)
    (hv₁ : ∀ z ∈ U, HasDerivAt v₁ (A z (v₁ z) + b z) z)
    (hv₂ : ∀ z ∈ U, HasDerivAt v₂ (A z (v₂ z) + b z) z) (h₀ : v₁ z₀ = v₂ z₀) :
    EqOn v₁ v₂ U := by
  let u : ℂ → E := v₁ - v₂
  have hu_deriv : ∀ z ∈ U, HasDerivAt u (A z (u z) + (fun _ : ℂ ↦ (0 : E)) z) z := fun z hz ↦ by
    simpa [u, map_sub, add_sub_add_right_eq_sub] using (hv₁ z hz).sub (hv₂ z hz)
  have hu_diff : DifferentiableOn ℂ u U :=
    fun z hz ↦ (hu_deriv z hz).differentiableAt.differentiableWithinAt
  obtain ⟨r, hr_pos, hrU⟩ := EMetric.isOpen_iff.mp hU z₀ hz₀
  have hu_ps := (hu_diff.mono hrU).hasFPowerSeriesOnBall_eball hr_pos
  have hu_coeff : (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • iteratedDeriv n u z₀) = 0 := by
    ext n
    rw [inv_factorial_smul_iteratedDeriv_eq_linearSystemCoeff_of_hasDerivAt_clm_apply_add
      hA analyticAt_const (Filter.eventually_of_mem (hU.mem_nhds hz₀) hu_deriv) n]
    have hb0 : (fun m : ℕ ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m (fun _ : ℂ ↦ (0 : E)) z₀) = 0 := by
      ext m; simp
    rw [show u z₀ = 0 from sub_eq_zero.mpr h₀, hb0, linearSystemCoeff_zero_zero]
  rw [hu_coeff, mkPiRingSeries_zero] at hu_ps
  have hu_zero : EqOn u 0 U :=
    (hu_diff.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hU_conn hz₀ hu_ps.eventually_eq_zero
  exact fun z hz ↦ sub_eq_zero.mp (hu_zero hz)

/-- If `A` and `b` admit formal power series `mkPiRingSeries ℂ As` and `mkPiRingSeries ℂ bs` on
`Metric.eball z₀ r`, then for every `v₀ : E` there exists a unique solution `v` of
`v'(z) = A(z) (v(z)) + b(z)` on `Metric.eball z₀ r` with `v z₀ = v₀`, represented on the whole disc
by `mkPiRingSeries ℂ (linearSystemCoeff As bs v₀)`. -/
theorem exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add_of_hasFPowerSeriesOnBall
    {A : ℂ → E →L[ℂ] E} {b : ℂ → E} {As : ℕ → E →L[ℂ] E} {bs : ℕ → E}
    {z₀ : ℂ} {r : ℝ≥0∞}
    (hA : HasFPowerSeriesOnBall A (mkPiRingSeries ℂ As) z₀ r)
    (hb : HasFPowerSeriesOnBall b (mkPiRingSeries ℂ bs) z₀ r) (v₀ : E) :
    let c := linearSystemCoeff As bs v₀
    ∃ v : ℂ → E,
      HasFPowerSeriesOnBall v (mkPiRingSeries ℂ c) z₀ r ∧
      v z₀ = v₀ ∧ (∀ z ∈ Metric.eball z₀ r, HasDerivAt v (A z (v z) + b z) z) ∧
      ∀ u : ℂ → E, (∀ z ∈ Metric.eball z₀ r, HasDerivAt u (A z (u z) + b z) z) →
        u z₀ = v₀ → EqOn u v (Metric.eball z₀ r) := by
  intro c
  have hr_le : r ≤ (mkPiRingSeries ℂ c).radius :=
    le_radius_mkPiRingSeries_linearSystemCoeff v₀ hA.r_le hb.r_le
  let v : ℂ → E := fun z ↦ (mkPiRingSeries ℂ c).sum (z - z₀)
  have hv_ps : HasFPowerSeriesOnBall v (mkPiRingSeries ℂ c) z₀ r := by
    simpa [v] using ((mkPiRingSeries ℂ c).hasFPowerSeriesOnBall (hA.r_pos.trans_le hr_le)
      |>.mono hA.r_pos hr_le).comp_sub z₀
  have hv₀ : v z₀ = v₀ := by simpa [c] using (hv_ps.coeff_zero 1).symm
  have hlhs_ps := hv_ps.deriv
  have hrhs_ps := (hA.clm_apply hv_ps).add hb
  have hser_eq :
      (mkPiRingSeries ℂ fun n ↦ ((n : ℂ) + 1) • (mkPiRingSeries ℂ c).coeff (n + 1)) =
      (mkPiRingSeries ℂ fun n ↦ ∑ k ∈ Finset.range (n + 1),
        (mkPiRingSeries ℂ As).coeff (n - k) ((mkPiRingSeries ℂ c).coeff k)) +
      mkPiRingSeries ℂ bs := by
    rw [← mkPiRingSeries_add]
    congr 1
    ext n
    simp [c, natCast_add_one_smul_linearSystemCoeff_succ, add_comm]
  have hv_ode : ∀ z ∈ Metric.eball z₀ r, HasDerivAt v (A z (v z) + b z) z := fun z hz ↦
    (hv_ps.analyticAt_of_mem hz).differentiableAt.hasDerivAt.congr_deriv
      ((hser_eq ▸ hlhs_ps).unique hrhs_ps hz)
  refine ⟨v, hv_ps, hv₀, hv_ode, fun u hu hu₀ ↦ ?_⟩
  exact eqOn_of_hasDerivAt_clm_apply_add Metric.isOpen_eball isPreconnected_eball
    (mem_eball_self hA.r_pos) hA.analyticAt hu hv_ode (hu₀.trans hv₀.symm)

/-- If `A : ℂ → E →L[ℂ] E` and `b : ℂ → E` are holomorphic on `Metric.eball z₀ r` (`0 < r ≤ ∞`),
then for every `v₀ : E` there is a unique holomorphic solution `v` of `v'(z) = A(z) (v(z)) + b(z)`
on `Metric.eball z₀ r` with `v z₀ = v₀`, represented on the whole disc by
`mkPiRingSeries ℂ (linearSystemCoeff ... v₀)`. -/
theorem exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add {A : ℂ → E →L[ℂ] E} {b : ℂ → E}
    {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r) (hA : DifferentiableOn ℂ A (Metric.eball z₀ r))
    (hb : DifferentiableOn ℂ b (Metric.eball z₀ r)) (v₀ : E) :
    let c := linearSystemCoeff (fun m ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m A z₀)
      (fun m ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m b z₀) v₀
    ∃ v : ℂ → E,
      HasFPowerSeriesOnBall v (mkPiRingSeries ℂ c) z₀ r ∧
      v z₀ = v₀ ∧ (∀ z ∈ Metric.eball z₀ r, HasDerivAt v (A z (v z) + b z) z) ∧
      ∀ u : ℂ → E, (∀ z ∈ Metric.eball z₀ r, HasDerivAt u (A z (u z) + b z) z) →
        u z₀ = v₀ → EqOn u v (Metric.eball z₀ r) :=
  exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add_of_hasFPowerSeriesOnBall
    (hA.hasFPowerSeriesOnBall_eball hr) (hb.hasFPowerSeriesOnBall_eball hr) v₀

/-- If `A : ℂ → E →L[ℂ] E` and `b : ℂ → E` are entire, then for every `z₀ : ℂ` and `v₀ : E` there
is a unique `v : ℂ → E` satisfying `HasDerivAt v (A z (v z) + b z) z` everywhere and `v z₀ = v₀`. -/
theorem existsUnique_hasDerivAt_clm_apply_add {A : ℂ → E →L[ℂ] E} {b : ℂ → E}
    (hA : Differentiable ℂ A) (hb : Differentiable ℂ b) (z₀ : ℂ) (v₀ : E) :
    ∃! v : ℂ → E, (∀ z, HasDerivAt v (A z (v z) + b z) z) ∧ v z₀ = v₀ := by
  obtain ⟨v, -, hv₀, hv_ode, hv_uniq⟩ :=
    exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add (z₀ := z₀) (r := ∞) ENNReal.coe_lt_top
      hA.differentiableOn hb.differentiableOn v₀
  have hall : ∀ z : ℂ, z ∈ Metric.eball z₀ ∞ := fun z ↦ by simp
  refine ⟨v, ⟨fun z ↦ hv_ode z (hall z), hv₀⟩, fun u ⟨hu, hu₀⟩ ↦ funext fun z ↦ ?_⟩
  exact hv_uniq u (fun w _ ↦ hu w) hu₀ (hall z)

end FirstOrderSystem

/-! ### Initial-jet equivalence and solution-space dimension for `TauCeti.LinearEquation` -/

namespace LinearEquation

variable {U : Opens ℂ} {n : ℕ}

private theorem differentiableOn_companionCLM (E : LinearEquation U n) :
    DifferentiableOn ℂ (fun z ↦ (Matrix.toLin' (E.companion z)).toContinuousLinearMap) U :=
  Matrix.differentiableOn_toContinuousLinearMap_toLin'.mpr fun i j ↦
    (E.analyticOnNhd_companion i j).differentiableOn

private theorem analyticAt_companionCLM (E : LinearEquation U n) {a : ℂ} (ha : a ∈ U) :
    AnalyticAt ℂ (fun z ↦ (Matrix.toLin' (E.companion z)).toContinuousLinearMap) a :=
  E.differentiableOn_companionCLM.analyticOnNhd U.isOpen a ha

/-- On a preconnected open domain, scalar solutions of `E` are uniquely determined by their
initial `n`-jet at any point of the domain. -/
theorem IsSolution.eqOn_of_isPreconnected {E : LinearEquation U n} {y₁ y₂ : ℂ → ℂ}
    (hy₁ : E.IsSolution y₁) (hy₂ : E.IsSolution y₂) (hU : IsPreconnected (U : Set ℂ)) {a : ℂ}
    (ha : a ∈ U) (hjet : ∀ j < n, iteratedDeriv j y₁ a = iteratedDeriv j y₂ a) :
    EqOn y₁ y₂ U := by
  have heq := eqOn_of_hasDerivAt_clm_apply_add (b := 0) U.isOpen hU ha
    (E.analyticAt_companionCLM ha)
    (fun z hz ↦ by simpa using hy₁.isCompanionSolution.hasDerivAt z hz)
    (fun z hz ↦ by simpa using hy₂.isCompanionSolution.hasDerivAt z hz)
    (funext fun j ↦ hjet j j.isLt)
  exact fun z hz ↦ by simpa using congrFun (heq hz) ⟨0, E.order_pos⟩

/-- On a preconnected open domain, the initial-jet map on `E.solutionSpace` is injective. -/
theorem initialJet_injective (E : LinearEquation U n) (hU : IsPreconnected (U : Set ℂ)) {a : ℂ}
    (ha : a ∈ U) : Function.Injective (E.initialJet ha) := by
  intro f₁ f₂ h
  have hjet : ∀ j < n, iteratedDeriv j (HolomorphicFunctions.extend f₁.val) a =
      iteratedDeriv j (HolomorphicFunctions.extend f₂.val) a := fun j hj ↦ by
    simpa [initialJet_apply] using congrFun h ⟨j, hj⟩
  have heq := IsSolution.eqOn_of_isPreconnected
    ((E.mem_solutionSpace f₁.1).mp f₁.2) ((E.mem_solutionSpace f₂.1).mp f₂.2) hU ha hjet
  apply Subtype.ext; apply Subtype.ext; ext ⟨z, hz⟩
  simpa [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩] using heq hz

/-- On a preconnected open domain, the solution space of a monic order-`n` linear differential
equation is finite-dimensional. -/
theorem finiteDimensional_solutionSpace_of_isPreconnected (E : LinearEquation U n)
    (hU : IsPreconnected (U : Set ℂ)) : FiniteDimensional ℂ E.solutionSpace := by
  rcases Set.eq_empty_or_nonempty (U : Set ℂ) with hU_empty | ⟨a, ha⟩
  · have : Subsingleton E.solutionSpace :=
      ⟨fun f₁ f₂ ↦ Subtype.ext <| Subtype.ext <| ContinuousMap.ext fun ⟨z, hz⟩ ↦
        False.elim (by rw [← SetLike.mem_coe, hU_empty] at hz; exact hz)⟩
    exact FiniteDimensional.of_injective (0 : E.solutionSpace →ₗ[ℂ] Fin 0 → ℂ)
      (fun _ _ _ ↦ Subsingleton.elim _ _)
  · exact FiniteDimensional.of_injective (E.initialJet ha) (E.initialJet_injective hU ha)

/-- On a preconnected open domain, `E.solutionSpace` has dimension at most `n`. -/
theorem finrank_solutionSpace_le_of_isPreconnected (E : LinearEquation U n)
    (hU : IsPreconnected (U : Set ℂ)) : Module.finrank ℂ E.solutionSpace ≤ n := by
  rcases Set.eq_empty_or_nonempty (U : Set ℂ) with hU_empty | ⟨a, ha⟩
  · have : Subsingleton E.solutionSpace :=
      ⟨fun f₁ f₂ ↦ Subtype.ext <| Subtype.ext <| ContinuousMap.ext fun ⟨z, hz⟩ ↦
        False.elim (by rw [← SetLike.mem_coe, hU_empty] at hz; exact hz)⟩
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le n
  · simpa using LinearMap.finrank_le_finrank_of_injective (E.initialJet_injective hU ha)

/-- On any open disc `(U : Set ℂ) = Metric.eball c r`, the initial-jet map `E.initialJet ha` at any
point `a ∈ U` (not necessarily the disc center `c`) is a `ℂ`-linear equivalence between
`E.solutionSpace` and `Fin n → ℂ`. -/
def initialJetEquivOfEqEBall (E : LinearEquation U n) {c a : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) (ha : a ∈ U) :
    E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (E.initialJet ha)
    ⟨E.initialJet_injective (hU ▸ isPreconnected_eball) ha, by
      have ha_eball : a ∈ Metric.eball c r := by rwa [← hU, SetLike.mem_coe]
      have hr : 0 < r := zero_le.trans_lt (Metric.mem_eball.mp ha_eball)
      have hc : c ∈ U := by
        rw [← SetLike.mem_coe, hU]
        exact mem_eball_self hr
      have hsurj_c : Function.Surjective (E.initialJet hc) := fun v₀ ↦ by
        have hA : DifferentiableOn ℂ
            (fun z ↦ (Matrix.toLin' (E.companion z)).toContinuousLinearMap) (Metric.eball c r) :=
          hU ▸ E.differentiableOn_companionCLM
        obtain ⟨v, hv_ps, hv₀, hv_ode, -⟩ :=
          exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add (b := 0) hr hA
            (differentiableOn_const 0) v₀
        have hv_comp : E.IsCompanionSolution v :=
          (E.isCompanionSolution_iff v).mpr
            ⟨hU.symm ▸ hv_ps.analyticOnNhd, fun z hz ↦ by
              simpa using hv_ode z (by rwa [← hU, SetLike.mem_coe])⟩
        exact ⟨hv_comp.toSolutionSpace, (hv_comp.initialJet_toSolutionSpace hc).trans hv₀⟩
      let ec : E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
        LinearEquiv.ofBijective (E.initialJet hc)
          ⟨E.initialJet_injective (hU ▸ isPreconnected_eball) hc, hsurj_c⟩
      have : FiniteDimensional ℂ E.solutionSpace :=
        E.finiteDimensional_solutionSpace_of_isPreconnected (hU ▸ isPreconnected_eball)
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ec.finrank_eq).mp
        (E.initialJet_injective (hU ▸ isPreconnected_eball) ha)⟩

/-- Applying `initialJetEquivOfEqEBall` agrees with `E.initialJet ha`. -/
@[simp]
theorem initialJetEquivOfEqEBall_apply (E : LinearEquation U n) {c a : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) (ha : a ∈ U) (f : E.solutionSpace) :
    E.initialJetEquivOfEqEBall hU ha f = E.initialJet ha f :=
  (rfl)

/-- The underlying linear map of `initialJetEquivOfEqEBall` is `E.initialJet ha`. -/
@[simp]
theorem initialJetEquivOfEqEBall_toLinearMap (E : LinearEquation U n) {c a : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) (ha : a ∈ U) :
    (E.initialJetEquivOfEqEBall hU ha).toLinearMap = E.initialJet ha :=
  (rfl)

/-- `E.initialJet ha` is a left inverse to `(E.initialJetEquivOfEqEBall hU ha).symm`. -/
@[simp]
theorem initialJet_initialJetEquivOfEqEBall_symm (E : LinearEquation U n) {c a : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) (ha : a ∈ U) (v : Fin n → ℂ) :
    E.initialJet ha ((E.initialJetEquivOfEqEBall hU ha).symm v) = v :=
  (E.initialJetEquivOfEqEBall hU ha).apply_symm_apply v

/-- `(E.initialJetEquivOfEqEBall hU ha).symm` recovers a solution from its initial jet at `a`. -/
@[simp]
theorem initialJetEquivOfEqEBall_symm_initialJet (E : LinearEquation U n) {c a : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) (ha : a ∈ U) (f : E.solutionSpace) :
    (E.initialJetEquivOfEqEBall hU ha).symm (E.initialJet ha f) = f :=
  (E.initialJetEquivOfEqEBall hU ha).symm_apply_apply f

/-- On an open disc `(U : Set ℂ) = Metric.eball c r`, `E.solutionSpace` is finite-dimensional. -/
theorem finiteDimensional_solutionSpace_of_eq_eball (E : LinearEquation U n) {c : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) : FiniteDimensional ℂ E.solutionSpace :=
  E.finiteDimensional_solutionSpace_of_isPreconnected (hU ▸ isPreconnected_eball)

/-- On a nonempty open disc `(U : Set ℂ) = Metric.eball c r` (`0 < r`), `E.solutionSpace` has
dimension `n`. -/
theorem finrank_solutionSpace_of_eq_eball (E : LinearEquation U n) {c : ℂ} {r : ℝ≥0∞}
    (hr : 0 < r) (hU : (U : Set ℂ) = Metric.eball c r) :
    Module.finrank ℂ E.solutionSpace = n := by
  have hc : c ∈ U := by
    rw [← SetLike.mem_coe, hU]
    exact mem_eball_self hr
  simpa using (E.initialJetEquivOfEqEBall hU hc).finrank_eq

/-- On the entire complex plane `⊤ : Opens ℂ`, the initial-jet map at any point `a` is a linear
equivalence `E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ)`. -/
def initialJetEquivTop (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ) :
    E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
  E.initialJetEquivOfEqEBall (c := 0) (r := ∞) (by ext z; simp) (Set.mem_univ a)

/-- Applying `initialJetEquivTop` agrees with `E.initialJet`. -/
@[simp]
theorem initialJetEquivTop_apply (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ)
    (f : E.solutionSpace) :
    E.initialJetEquivTop a f = E.initialJet (Set.mem_univ a) f :=
  (rfl)

/-- The underlying linear map of `initialJetEquivTop` is `E.initialJet`. -/
@[simp]
theorem initialJetEquivTop_toLinearMap (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ) :
    (E.initialJetEquivTop a).toLinearMap = E.initialJet (Set.mem_univ a) :=
  (rfl)

/-- `E.initialJet` is a left inverse to `(E.initialJetEquivTop a).symm`. -/
@[simp]
theorem initialJet_initialJetEquivTop_symm (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ)
    {ha : a ∈ (⊤ : Opens ℂ)} (v : Fin n → ℂ) :
    E.initialJet ha ((E.initialJetEquivTop a).symm v) = v :=
  (E.initialJetEquivTop a).apply_symm_apply v

/-- `(E.initialJetEquivTop a).symm` recovers an entire solution from its initial jet at `a`. -/
@[simp]
theorem initialJetEquivTop_symm_initialJet (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ)
    {ha : a ∈ (⊤ : Opens ℂ)} (f : E.solutionSpace) :
    (E.initialJetEquivTop a).symm (E.initialJet ha f) = f :=
  (E.initialJetEquivTop a).symm_apply_apply f

/-- On the entire complex plane `⊤ : Opens ℂ`, `E.solutionSpace` is finite-dimensional. -/
instance instFiniteDimensionalSolutionSpaceTop (E : LinearEquation (⊤ : Opens ℂ) n) :
    FiniteDimensional ℂ E.solutionSpace :=
  E.finiteDimensional_solutionSpace_of_isPreconnected (by simpa using isPreconnected_univ)

/-- On the entire complex plane `⊤ : Opens ℂ`, `E.solutionSpace` has dimension `n`. -/
@[simp]
theorem finrank_solutionSpace_top (E : LinearEquation (⊤ : Opens ℂ) n) :
    Module.finrank ℂ E.solutionSpace = n := by
  simpa using (E.initialJetEquivTop 0).finrank_eq

end LinearEquation

/-! ### Second-order linear differential equations at an ordinary point -/

section SecondOrder

/-- Formal Taylor coefficients around `z₀` of the solution to `w'' + f(z) w' + g(z) w = 0` with
`w(z₀) = w₀` and `w'(z₀) = w₁`, given the Taylor coefficient sequences `f` and `g` around `z₀`. -/
def ordinaryPointCoeff (f g : ℕ → ℂ) (w₀ w₁ : ℂ) : ℕ → ℂ
  | 0 => w₀
  | 1 => w₁
  | n + 2 => -((((n + 2 : ℂ) * (n + 1 : ℂ))⁻¹) *
      ∑ k : Fin (n + 1), (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
        g (n - k) * ordinaryPointCoeff f g w₀ w₁ k))

/-- The constant Taylor coefficient `ordinaryPointCoeff f g w₀ w₁ 0` is `w₀`. -/
@[simp]
theorem ordinaryPointCoeff_zero (f g : ℕ → ℂ) (w₀ w₁ : ℂ) :
    ordinaryPointCoeff f g w₀ w₁ 0 = w₀ := by
  rw [ordinaryPointCoeff]

/-- The linear Taylor coefficient `ordinaryPointCoeff f g w₀ w₁ 1` is `w₁`. -/
@[simp]
theorem ordinaryPointCoeff_one (f g : ℕ → ℂ) (w₀ w₁ : ℂ) :
    ordinaryPointCoeff f g w₀ w₁ 1 = w₁ := by
  rw [ordinaryPointCoeff]

/-- Explicit Cauchy-product recurrence for `ordinaryPointCoeff` at `n + 2`. -/
theorem ordinaryPointCoeff_add_two (f g : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) :
    ordinaryPointCoeff f g w₀ w₁ (n + 2) =
      -((((n + 2 : ℂ) * (n + 1 : ℂ))⁻¹) *
        ∑ k ∈ Finset.range (n + 1),
          (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
            g (n - k) * ordinaryPointCoeff f g w₀ w₁ k)) := by
  rw [ordinaryPointCoeff, Fin.sum_univ_eq_sum_range (fun k ↦
    ((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
      g (n - k) * ordinaryPointCoeff f g w₀ w₁ k)]

/-- Cleared-denominator coefficient-equating recurrence for `w'' + f(z) w' + g(z) w = 0`:
`(n + 2)(n + 1) a_{n+2} = -∑_{k=0}^n ((k + 1) f_{n-k} a_{k+1} + g_{n-k} a_k)`. -/
theorem mul_ordinaryPointCoeff_add_two (f g : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) :
    ((n + 2 : ℂ) * (n + 1 : ℂ)) * ordinaryPointCoeff f g w₀ w₁ (n + 2) =
      -∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
          g (n - k) * ordinaryPointCoeff f g w₀ w₁ k) := by
  have hn1 : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hn2 : (n + 2 : ℂ) ≠ 0 := mod_cast Nat.succ_ne_zero (n + 1)
  rw [ordinaryPointCoeff_add_two, mul_neg, mul_inv_cancel_left₀ (mul_ne_zero hn2 hn1)]

/-- Uniqueness characterization of `TauCeti.ordinaryPointCoeff` by its first two terms and its
cleared-denominator recurrence. -/
theorem eq_ordinaryPointCoeff_iff {f g a : ℕ → ℂ} {w₀ w₁ : ℂ} :
    a = ordinaryPointCoeff f g w₀ w₁ ↔
      a 0 = w₀ ∧ a 1 = w₁ ∧ ∀ n : ℕ, ((n + 2 : ℂ) * (n + 1 : ℂ)) * a (n + 2) +
        ∑ k ∈ Finset.range (n + 1),
          (((k : ℂ) + 1) * f (n - k) * a (k + 1) + g (n - k) * a k) = 0 := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    refine ⟨ordinaryPointCoeff_zero f g w₀ w₁, ordinaryPointCoeff_one f g w₀ w₁, fun n ↦ ?_⟩
    rw [mul_ordinaryPointCoeff_add_two, neg_add_cancel]
  · rintro ⟨ha0, ha1, hrec⟩
    ext n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      rcases n with _ | _ | n
      · simpa using ha0
      · simpa using ha1
      · have hn1 : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
        have hn2 : (n + 2 : ℂ) ≠ 0 := mod_cast Nat.succ_ne_zero (n + 1)
        rw [ordinaryPointCoeff_add_two, ← inv_mul_cancel_left₀ (mul_ne_zero hn2 hn1) (a (n + 2)),
          eq_neg_of_add_eq_zero_left (hrec n), mul_neg]
        congr 2
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [ih (k + 1) (by omega), ih k (by omega)]

/-- Zero initial values produce identically zero formal Taylor coefficients. -/
@[simp]
theorem ordinaryPointCoeff_zero_zero (f g : ℕ → ℂ) :
    ordinaryPointCoeff f g 0 0 = 0 := by
  symm
  exact eq_ordinaryPointCoeff_iff.mpr ⟨rfl, rfl, fun _ ↦ by simp⟩

/-- `TauCeti.ordinaryPointCoeff` is additive in the initial data `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_add (f g : ℕ → ℂ) (w₀ w₁ u₀ u₁ : ℂ) :
    ordinaryPointCoeff f g (w₀ + u₀) (w₁ + u₁) =
      ordinaryPointCoeff f g w₀ w₁ + ordinaryPointCoeff f g u₀ u₁ := by
  symm
  refine eq_ordinaryPointCoeff_iff.mpr ⟨by simp, by simp, fun n ↦ ?_⟩
  have h1 := mul_ordinaryPointCoeff_add_two f g w₀ w₁ n
  have h2 := mul_ordinaryPointCoeff_add_two f g u₀ u₁ n
  have hsum :
      ∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) *
            (ordinaryPointCoeff f g w₀ w₁ (k + 1) + ordinaryPointCoeff f g u₀ u₁ (k + 1)) +
          g (n - k) * (ordinaryPointCoeff f g w₀ w₁ k + ordinaryPointCoeff f g u₀ u₁ k)) =
      (∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
          g (n - k) * ordinaryPointCoeff f g w₀ w₁ k)) +
      ∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g u₀ u₁ (k + 1) +
          g (n - k) * ordinaryPointCoeff f g u₀ u₁ k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp only [Pi.add_apply]
  rw [hsum]
  linear_combination h1 + h2

/-- `TauCeti.ordinaryPointCoeff` commutes with scalar multiplication in `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_smul (f g : ℕ → ℂ) (c w₀ w₁ : ℂ) :
    ordinaryPointCoeff f g (c • w₀) (c • w₁) = c • ordinaryPointCoeff f g w₀ w₁ := by
  symm
  refine eq_ordinaryPointCoeff_iff.mpr ⟨by simp, by simp, fun n ↦ ?_⟩
  have h := mul_ordinaryPointCoeff_add_two f g w₀ w₁ n
  have hsum :
      ∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) * (c * ordinaryPointCoeff f g w₀ w₁ (k + 1)) +
          g (n - k) * (c * ordinaryPointCoeff f g w₀ w₁ k)) =
      c * ∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
          g (n - k) * ordinaryPointCoeff f g w₀ w₁ k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  linear_combination c * h

/-- `TauCeti.ordinaryPointCoeff` commutes with negation in `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_neg (f g : ℕ → ℂ) (w₀ w₁ : ℂ) :
    ordinaryPointCoeff f g (-w₀) (-w₁) = -ordinaryPointCoeff f g w₀ w₁ := by
  simpa using ordinaryPointCoeff_smul f g (-1 : ℂ) w₀ w₁

/-- `TauCeti.ordinaryPointCoeff` commutes with subtraction in `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_sub (f g : ℕ → ℂ) (w₀ w₁ u₀ u₁ : ℂ) :
    ordinaryPointCoeff f g (w₀ - u₀) (w₁ - u₁) =
      ordinaryPointCoeff f g w₀ w₁ - ordinaryPointCoeff f g u₀ u₁ := by
  rw [sub_eq_add_neg, sub_eq_add_neg w₁ u₁, ordinaryPointCoeff_add, ordinaryPointCoeff_neg,
    sub_eq_add_neg]

/-- Superposition of `TauCeti.ordinaryPointCoeff` into the two canonical fundamental Taylor
sequences with initial data `(1, 0)` and `(0, 1)`. -/
theorem ordinaryPointCoeff_eq_add_mul (f g : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) :
    ordinaryPointCoeff f g w₀ w₁ n =
      w₀ * ordinaryPointCoeff f g 1 0 n + w₁ * ordinaryPointCoeff f g 0 1 n := by
  have h : ordinaryPointCoeff f g w₀ w₁ =
      w₀ • ordinaryPointCoeff f g 1 0 + w₁ • ordinaryPointCoeff f g 0 1 := by
    rw [← ordinaryPointCoeff_smul, ← ordinaryPointCoeff_smul, ← ordinaryPointCoeff_add]
    simp
  simpa [Pi.add_apply, Pi.smul_apply] using congrFun h n

private def secondOrderMatrix (f g : ℂ → ℂ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j ↦ if i = 0 then (if j = 0 then 0 else 1) else (if j = 0 then -g z else -f z)

@[simp]
private theorem secondOrderMatrix_mulVec (f g : ℂ → ℂ) (z : ℂ) (v : Fin 2 → ℂ) :
    secondOrderMatrix f g z *ᵥ v = fun i ↦ if i = 0 then v 1 else -g z * v 0 - f z * v 1 := by
  ext i
  fin_cases i <;>
    simp [secondOrderMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

private theorem differentiableOn_secondOrderCLM {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ
      (fun z ↦ (Matrix.toLin' (secondOrderMatrix f g z)).toContinuousLinearMap) U := by
  refine Matrix.differentiableOn_toContinuousLinearMap_toLin'.mpr fun i j ↦ ?_
  dsimp only [secondOrderMatrix]
  split_ifs
  · exact differentiableOn_const 0
  · exact differentiableOn_const 1
  · exact hg.neg
  · exact hf.neg

private theorem analyticAt_secondOrderCLM {f g : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀) :
    AnalyticAt ℂ (fun z ↦ (Matrix.toLin' (secondOrderMatrix f g z)).toContinuousLinearMap) z₀ := by
  obtain ⟨r, hr_pos, hr⟩ := EMetric.mem_nhds_iff.mp (hf.eventually_analyticAt.and
    hg.eventually_analyticAt)
  exact (differentiableOn_secondOrderCLM
    (fun z hz ↦ (hr hz).1.differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hr hz).2.differentiableAt.differentiableWithinAt)).analyticOnNhd
    Metric.isOpen_eball z₀ (mem_eball_self hr_pos)

private theorem hasDerivAt_secondOrder_vec {f g h w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hw : DifferentiableOn ℂ w U)
    (hode : ∀ z ∈ U, deriv (deriv w) z + f z * deriv w z + g z * w z = h z) :
    ∀ z ∈ U, HasDerivAt (fun z (i : Fin 2) ↦ if i = 0 then w z else deriv w z)
      ((Matrix.toLin' (secondOrderMatrix f g z)).toContinuousLinearMap
        (fun i ↦ if i = 0 then w z else deriv w z) +
        fun i ↦ if i = 0 then 0 else h z) z := by
  have hwd : DifferentiableOn ℂ (deriv w) U := hw.deriv hU
  intro z hz
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa using (hw.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  · refine (hwd.differentiableAt (hU.mem_nhds hz)).hasDerivAt.congr_deriv ?_
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply,
      secondOrderMatrix_mulVec, Pi.add_apply, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    linear_combination hode z hz

private theorem secondOrder_of_hasDerivAt_vec {f g : ℂ → ℂ} {b v : ℂ → Fin 2 → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hb0 : ∀ z ∈ U, b z 0 = 0)
    (hv : ∀ z ∈ U, HasDerivAt v
      ((Matrix.toLin' (secondOrderMatrix f g z)).toContinuousLinearMap (v z) + b z) z) :
    DifferentiableOn ℂ (fun z ↦ v z 0) U ∧
      (∀ z ∈ U, deriv (fun w ↦ v w 0) z = v z 1) ∧
      ∀ z ∈ U, deriv (deriv fun w ↦ v w 0) z + f z * deriv (fun w ↦ v w 0) z +
        g z * v z 0 = b z 1 := by
  have hv_fst : ∀ z ∈ U, HasDerivAt (fun w ↦ v w 0) (v z 1) z := fun z hz ↦ by
    simpa [hb0 z hz] using hasDerivAt_pi.mp (hv z hz) 0
  have hv_snd : ∀ z ∈ U, deriv (fun w ↦ v w 0) z = v z 1 := fun z hz ↦ (hv_fst z hz).deriv
  refine ⟨fun z hz ↦ (hv_fst z hz).differentiableAt.differentiableWithinAt, hv_snd, fun z hz ↦ ?_⟩
  have hd2 := (hasDerivAt_pi.mp (hv z hz) 1).deriv
  have hcongr : (fun u ↦ v u 1) =ᶠ[𝓝 z] deriv (fun w ↦ v w 0) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hz, fun u hu ↦ (hv_snd u hu).symm⟩
  have hddw : deriv (deriv fun w ↦ v w 0) z =
      -g z * v z 0 - f z * deriv (fun w ↦ v w 0) z + b z 1 := by
    rw [← hcongr.deriv_eq, hv_snd z hz]
    simpa using hd2
  rw [hddw]
  ring

/-- If `f` and `g` are analytic at an ordinary point `z₀ ∈ U` of an open preconnected set `U ⊆ ℂ`,
and two holomorphic functions `w₁, w₂` on `U` satisfy the same second-order equation
`w'' + f w' + g w` near `z₀` and agree to first order at `z₀`, then `EqOn w₁ w₂ U`. -/
theorem eqOn_of_secondOrder_linear_ode {f g w₁ w₂ : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U) (hU_conn : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀)
    (hw₁ : DifferentiableOn ℂ w₁ U) (hw₂ : DifferentiableOn ℂ w₂ U)
    (hode : ∀ᶠ z in 𝓝 z₀, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z =
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z)
    (hw₀ : w₁ z₀ = w₂ z₀) (hdw₀ : deriv w₁ z₀ = deriv w₂ z₀) :
    EqOn w₁ w₂ U := by
  obtain ⟨r, hr_pos, hr⟩ := EMetric.mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hz₀) hode)
  have hVU : Metric.eball z₀ r ⊆ U := fun z hz ↦ (hr hz).1
  let h : ℂ → ℂ := fun z ↦ deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z
  have hp₁ := hasDerivAt_secondOrder_vec Metric.isOpen_eball (hw₁.mono hVU) (h := h)
    fun z hz ↦ (hr hz).2
  have hp₂ := hasDerivAt_secondOrder_vec Metric.isOpen_eball (hw₂.mono hVU) (h := h)
    fun _ _ ↦ rfl
  have hinit : (fun i : Fin 2 ↦ if i = 0 then w₁ z₀ else deriv w₁ z₀) =
      (fun i : Fin 2 ↦ if i = 0 then w₂ z₀ else deriv w₂ z₀) := by
    ext i; fin_cases i <;> simp [hw₀, hdw₀]
  have heq_ball := eqOn_of_hasDerivAt_clm_apply_add Metric.isOpen_eball isPreconnected_eball
    (mem_eball_self hr_pos) (analyticAt_secondOrderCLM hf hg) hp₁ hp₂ hinit
  have hu_ev : (w₁ - w₂) =ᶠ[𝓝 z₀] 0 :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Metric.eball z₀ r, Metric.isOpen_eball.mem_nhds (mem_eball_self hr_pos),
        fun z hz ↦ sub_eq_zero.mpr (congrFun (heq_ball hz) 0)⟩
  have hu_zero :=
    ((hw₁.sub hw₂).analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hU_conn hz₀ hu_ev
  exact fun z hz ↦ sub_eq_zero.mp (hu_zero hz)

/-- Two entire functions `w₁, w₂` satisfying the same second-order equation `w'' + f w' + g w`
near an ordinary point `z₀` (where `f` and `g` are analytic) and agreeing to first order at `z₀`
are equal everywhere on `ℂ`. -/
theorem eq_of_entire_secondOrder_linear_ode {f g w₁ w₂ : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀)
    (hw₁ : Differentiable ℂ w₁) (hw₂ : Differentiable ℂ w₂)
    (hode : ∀ᶠ z in 𝓝 z₀, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z =
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z)
    (hw₀ : w₁ z₀ = w₂ z₀) (hdw₀ : deriv w₁ z₀ = deriv w₂ z₀) :
    w₁ = w₂ := by
  ext z
  exact eqOn_of_secondOrder_linear_ode isOpen_univ isPreconnected_univ (mem_univ z₀)
    hf hg hw₁.differentiableOn hw₂.differentiableOn hode hw₀ hdw₀ (mem_univ z)

/-- Any holomorphic solution of `w'' + f(z) w' + g(z) w = 0` on `Metric.eball z₀ r` (`0 < r`),
where `f` and `g` have scalar power series `fs` and `gs` on `Metric.eball z₀ r`, is represented on
the whole disc by
`FormalMultilinearSeries.ofScalars ℂ (ordinaryPointCoeff fs gs (w z₀) (deriv w z₀))`. -/
theorem hasFPowerSeriesOnBall_of_ordinaryPoint_solution {f g w : ℂ → ℂ} {fs gs : ℕ → ℂ}
    {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ gs) z₀ r)
    (hw : DifferentiableOn ℂ w (Metric.eball z₀ r))
    (hode : ∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) :
    HasFPowerSeriesOnBall w
      (FormalMultilinearSeries.ofScalars ℂ (ordinaryPointCoeff fs gs (w z₀) (deriv w z₀)))
      z₀ r := by
  let a : ℕ → ℂ := fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n w z₀
  have hw_ps : HasFPowerSeriesOnBall w (mkPiRingSeries ℂ a) z₀ r := by
    simpa [a, smul_eq_mul] using hw.hasFPowerSeriesOnBall_eball hf.r_pos
  have hdw_ps : HasFPowerSeriesOnBall (deriv w)
      (mkPiRingSeries ℂ fun n ↦ ((n + 1 : ℂ)) * a (n + 1)) z₀ r := by
    simpa [smul_eq_mul] using hw_ps.deriv
  have hddw_ps : HasFPowerSeriesOnBall (deriv (deriv w))
      (mkPiRingSeries ℂ fun n ↦ ((n + 2 : ℂ) * (n + 1 : ℂ)) * a (n + 2)) z₀ r := by
    convert hdw_ps.deriv using 2
    ext n
    simp only [coeff_mkPiRingSeries, smul_eq_mul]
    push_cast
    ring
  have hsum_ps := (hddw_ps.add (hf.fun_mul hdw_ps)).add (hg.fun_mul hw_ps)
  have hzero_ev :
      (deriv (deriv w) + (fun z ↦ f z * deriv w z) + (fun z ↦ g z * w z)) =ᶠ[𝓝 z₀] 0 :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Metric.eball z₀ r, Metric.isOpen_eball.mem_nhds (mem_eball_self hf.r_pos), hode⟩
  have hser_zero := hsum_ps.hasFPowerSeriesAt.eq_zero_of_eventually hzero_ev
  have ha_eq : a = ordinaryPointCoeff fs gs (w z₀) (deriv w z₀) := by
    refine eq_ordinaryPointCoeff_iff.mpr ⟨by simp [a], by simp [a], fun n ↦ ?_⟩
    have hn := congrArg (FormalMultilinearSeries.coeff · n) hser_zero
    simp only [FormalMultilinearSeries.coeff_add, FormalMultilinearSeries.coeff_zero,
      coeff_mkPiRingSeries, FormalMultilinearSeries.coeff_ofScalars] at hn
    rw [add_assoc, ← Finset.sum_add_distrib] at hn
    convert hn using 2
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rwa [← mkPiRingSeries_eq_ofScalars, ← ha_eq]

/-- If `f`, `g`, and `w` are analytic at `z₀` and `w` satisfies `w'' + f(z) w' + g(z) w = 0`
eventually near `z₀`, then the factorial-scaled iterated derivatives of `w` at `z₀` equal
`TauCeti.ordinaryPointCoeff`. -/
theorem inv_factorial_mul_iteratedDeriv_eq_ordinaryPointCoeff {f g w : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀) (hw : AnalyticAt ℂ w z₀)
    (hode : ∀ᶠ z in 𝓝 z₀, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) (n : ℕ) :
    (n ! : ℂ)⁻¹ * iteratedDeriv n w z₀ =
      ordinaryPointCoeff (fun m ↦ (m ! : ℂ)⁻¹ * iteratedDeriv m f z₀)
        (fun m ↦ (m ! : ℂ)⁻¹ * iteratedDeriv m g z₀) (w z₀) (deriv w z₀) n := by
  obtain ⟨r, hr_pos, hr⟩ := EMetric.mem_nhds_iff.mp
    (hf.eventually_analyticAt.and (hg.eventually_analyticAt.and
      (hw.eventually_analyticAt.and hode)))
  have hf_ps : HasFPowerSeriesOnBall f
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ (m ! : ℂ)⁻¹ * iteratedDeriv m f z₀) z₀ r := by
    rw [← mkPiRingSeries_eq_ofScalars]
    simpa [smul_eq_mul] using (show DifferentiableOn ℂ f (Metric.eball z₀ r) from
      fun z hz ↦ (hr hz).1.differentiableAt.differentiableWithinAt).hasFPowerSeriesOnBall_eball
      hr_pos
  have hg_ps : HasFPowerSeriesOnBall g
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ (m ! : ℂ)⁻¹ * iteratedDeriv m g z₀) z₀ r := by
    rw [← mkPiRingSeries_eq_ofScalars]
    simpa [smul_eq_mul] using (show DifferentiableOn ℂ g (Metric.eball z₀ r) from
      fun z hz ↦ (hr hz).2.1.differentiableAt.differentiableWithinAt).hasFPowerSeriesOnBall_eball
      hr_pos
  have hw_diff : DifferentiableOn ℂ w (Metric.eball z₀ r) :=
    fun z hz ↦ (hr hz).2.2.1.differentiableAt.differentiableWithinAt
  have hw_ps := hw_diff.hasFPowerSeriesOnBall_eball hr_pos
  have hw_ps' := hasFPowerSeriesOnBall_of_ordinaryPoint_solution hf_ps hg_ps hw_diff
    fun z hz ↦ (hr hz).2.2.2
  rw [← mkPiRingSeries_eq_ofScalars] at hw_ps'
  simpa [smul_eq_mul] using congrFun (mkPiRingSeries_inj.mp
    (hw_ps.hasFPowerSeriesAt.eq_formalMultilinearSeries hw_ps'.hasFPowerSeriesAt)) n

/-- If `f`, `g`, and `h` are holomorphic on `Metric.eball z₀ r` (`0 < r ≤ ∞`), then for all
`w₀, w₁ : ℂ` there exists a unique holomorphic solution `w` of `w'' + f(z) w' + g(z) w = h(z)` on
`Metric.eball z₀ r` with `w z₀ = w₀` and `deriv w z₀ = w₁`. -/
theorem exists_secondOrder_linear_ode_eball {f g h : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
        (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
        (hg : DifferentiableOn ℂ g (Metric.eball z₀ r))
        (hh : DifferentiableOn ℂ h (Metric.eball z₀ r)) (w₀ w₁ : ℂ) :
    ∃ w : ℂ → ℂ,
      DifferentiableOn ℂ w (Metric.eball z₀ r) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = h z) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        (∀ z ∈ Metric.eball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = h z) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.eball z₀ r) := by
  have hb : DifferentiableOn ℂ (fun z (i : Fin 2) ↦ if i = 0 then (0 : ℂ) else h z)
      (Metric.eball z₀ r) := by
    rw [differentiableOn_pi]
    intro i; fin_cases i <;> simp [differentiableOn_const, hh]
  obtain ⟨v, -, hv₀, hv_ode, -⟩ :=
    exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add hr
      (differentiableOn_secondOrderCLM hf hg) hb
      (fun i : Fin 2 ↦ if i = 0 then w₀ else w₁)
  obtain ⟨hw_diff, hv_snd, hw_ode⟩ :=
    secondOrder_of_hasDerivAt_vec Metric.isOpen_eball (fun _ _ ↦ rfl) hv_ode
  let w : ℂ → ℂ := fun z ↦ v z 0
  have hw₀ : w z₀ = w₀ := by simpa [w] using congrFun hv₀ 0
  have hdw₀ : deriv w z₀ = w₁ :=
    (hv_snd z₀ (mem_eball_self hr)).trans (by simpa using congrFun hv₀ 1)
  refine ⟨w, hw_diff, hw₀, hdw₀, hw_ode, fun u hu hu_ode hu₀ hdu₀ ↦ ?_⟩
  have hode_ev : ∀ᶠ z in 𝓝 z₀,
      deriv (deriv u) z + f z * deriv u z + g z * u z =
        deriv (deriv w) z + f z * deriv w z + g z * w z :=
    Filter.eventually_of_mem (Metric.isOpen_eball.mem_nhds (mem_eball_self hr))
      fun z hz ↦ (hu_ode z hz).trans (hw_ode z hz).symm
  exact eqOn_of_secondOrder_linear_ode Metric.isOpen_eball isPreconnected_eball
    (mem_eball_self hr)
    (hf.analyticOnNhd Metric.isOpen_eball z₀ (mem_eball_self hr))
    (hg.analyticOnNhd Metric.isOpen_eball z₀ (mem_eball_self hr))
    hu hw_diff hode_ev (hu₀.trans hw₀.symm) (hdu₀.trans hdw₀.symm)

/-- If `f` and `g` admit scalar power series `fs` and `gs` on `Metric.eball z₀ r`, then for all
`w₀, w₁ : ℂ` there exists a unique holomorphic solution `w` of `w'' + f(z) w' + g(z) w = 0` on
`Metric.eball z₀ r` with `w z₀ = w₀` and `deriv w z₀ = w₁`, given by `ordinaryPointCoeff`. -/
theorem exists_ordinaryPoint_solution_of_hasFPowerSeriesOnBall {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ gs) z₀ r) (w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff fs gs w₀ w₁
    ∃ w : ℂ → ℂ,
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r ∧
      (∀ z ∈ Metric.eball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        (∀ z ∈ Metric.eball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.eball z₀ r) := by
  intro a
  obtain ⟨w, hw_diff, hw₀, hdw₀, hw_ode, hw_uniq⟩ :=
    exists_secondOrder_linear_ode_eball (h := 0) hf.r_pos hf.differentiableOn hg.differentiableOn
      (differentiableOn_const 0) w₀ w₁
  have hw_ps : HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r := by
    dsimp only [a]; rw [← hw₀, ← hdw₀]
    exact hasFPowerSeriesOnBall_of_ordinaryPoint_solution hf hg hw_diff hw_ode
  have hw_sum : ∀ z ∈ Metric.eball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z) := fun z hz ↦ by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hw_ps.hasSum_sub hz
  exact ⟨w, hw_ps, hw_sum, hw₀, hdw₀, hw_ode, hw_uniq⟩

/-- If `f` and `g` are holomorphic on `Metric.eball z₀ r` (`0 < r ≤ ∞`), then for all `w₀, w₁ : ℂ`
there exists a unique holomorphic solution `w` of `w'' + f(z) w' + g(z) w = 0` on
`Metric.eball z₀ r` with `w z₀ = w₀` and `deriv w z₀ = w₁`, given by `ordinaryPointCoeff`. -/
theorem exists_ordinaryPoint_solution_eball {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r)) (w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f z₀)
      (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n g z₀) w₀ w₁
    ∃ w : ℂ → ℂ,
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r ∧
      (∀ z ∈ Metric.eball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        (∀ z ∈ Metric.eball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.eball z₀ r) := by
  have hf_ps : HasFPowerSeriesOnBall f
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f z₀) z₀ r := by
    rw [← mkPiRingSeries_eq_ofScalars]
    simpa [smul_eq_mul] using hf.hasFPowerSeriesOnBall_eball hr
  have hg_ps : HasFPowerSeriesOnBall g
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n g z₀) z₀ r := by
    rw [← mkPiRingSeries_eq_ofScalars]
    simpa [smul_eq_mul] using hg.hasFPowerSeriesOnBall_eball hr
  exact exists_ordinaryPoint_solution_of_hasFPowerSeriesOnBall hf_ps hg_ps w₀ w₁

/-- If `f` and `g` are holomorphic on a finite open disc `Metric.ball z₀ r` (`0 < r`), then for all
`w₀, w₁ : ℂ` there exists a unique holomorphic solution `w` of `w'' + f(z) w' + g(z) w = 0` on
`Metric.ball z₀ r` with `w z₀ = w₀` and `deriv w z₀ = w₁`, converging on the whole disc. -/
theorem exists_ordinaryPoint_solution_ball {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.ball z₀ r)) (w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f z₀)
      (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n g z₀) w₀ w₁
    ∃ w : ℂ → ℂ,
      DifferentiableOn ℂ w (Metric.ball z₀ r) ∧
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ (ENNReal.ofReal r) ∧
      (∀ z ∈ Metric.ball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.ball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.ball z₀ r) →
        (∀ z ∈ Metric.ball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.ball z₀ r) := by
  have heball : Metric.eball z₀ (ENNReal.ofReal r) = Metric.ball z₀ r := Metric.eball_ofReal
  have hr_enn : (0 : ℝ≥0∞) < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr hr
  obtain ⟨w, hw_ps, hw_sum, hw₀, hdw₀, hw_ode, hw_uniq⟩ :=
    exists_ordinaryPoint_solution_eball hr_enn (heball.symm ▸ hf) (heball.symm ▸ hg) w₀ w₁
  refine ⟨w, heball ▸ hw_ps.differentiableOn, hw_ps, fun z hz ↦ hw_sum z (heball.symm ▸ hz),
    hw₀, hdw₀, fun z hz ↦ hw_ode z (heball.symm ▸ hz), fun u hu hu_ode hu₀ hdu₀ ↦ ?_⟩
  simpa only [heball] using hw_uniq u (heball.symm ▸ hu)
    (fun z hz ↦ hu_ode z (heball ▸ hz)) hu₀ hdu₀

/-- For entire `f, g, h : ℂ → ℂ`, every initial-value problem `w'' + f(z) w' + g(z) w = h(z)` with
`w z₀ = w₀` and `deriv w z₀ = w₁` has a unique entire solution. -/
theorem existsUnique_entire_secondOrder_linear_ode {f g h : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hh : Differentiable ℂ h)
    (z₀ w₀ w₁ : ℂ) :
    ∃! w : ℂ → ℂ, Differentiable ℂ w ∧
      (∀ z, deriv (deriv w) z + f z * deriv w z + g z * w z = h z) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  obtain ⟨w, hw_diff_on, hw₀, hdw₀, hw_ode_on, hw_uniq⟩ :=
    exists_secondOrder_linear_ode_eball (z₀ := z₀) (r := ∞) ENNReal.coe_lt_top
      hf.differentiableOn hg.differentiableOn hh.differentiableOn w₀ w₁
  have hall : ∀ z : ℂ, z ∈ Metric.eball z₀ ∞ := fun z ↦ by simp
  have hw_diff : Differentiable ℂ w := differentiableOn_univ.mp (by simpa using hw_diff_on)
  refine ⟨w, ⟨hw_diff, fun z ↦ hw_ode_on z (hall z), hw₀, hdw₀⟩,
    fun u ⟨hu_diff, hu_ode, hu₀, hdu₀⟩ ↦ funext fun z ↦ ?_⟩
  exact hw_uniq u hu_diff.differentiableOn (fun y _ ↦ hu_ode y) hu₀ hdu₀ (hall z)

/-- For entire `f, g : ℂ → ℂ`, every initial-value problem `w'' + f(z) w' + g(z) w = 0` with
`w z₀ = w₀` and `deriv w z₀ = w₁` has a unique entire solution `w`, and its Taylor series around
`z₀` with coefficients `ordinaryPointCoeff` converges everywhere on `ℂ`. -/
theorem exists_entire_ordinaryPoint_solution {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (z₀ w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f z₀)
      (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n g z₀) w₀ w₁
    ∃ w : ℂ → ℂ,
      Differentiable ℂ w ∧
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ ∞ ∧
      (∀ z : ℂ, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z : ℂ, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, Differentiable ℂ u →
        (∀ z : ℂ, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → u = w := by
  obtain ⟨w, hw_ps, hw_sum, hw₀, hdw₀, hw_ode, hw_uniq⟩ :=
    exists_ordinaryPoint_solution_eball (z₀ := z₀) (r := ∞) ENNReal.coe_lt_top
      hf.differentiableOn hg.differentiableOn w₀ w₁
  have hall : ∀ z : ℂ, z ∈ Metric.eball z₀ ∞ := fun z ↦ by simp
  have hw_diff : Differentiable ℂ w :=
    differentiableOn_univ.mp (by simpa using hw_ps.differentiableOn)
  refine ⟨w, hw_diff, hw_ps, fun z ↦ hw_sum z (hall z), hw₀, hdw₀,
    fun z ↦ hw_ode z (hall z), fun u hu hu_ode hu₀ hdu₀ ↦ funext fun z ↦ ?_⟩
  exact hw_uniq u hu.differentiableOn (fun y _ ↦ hu_ode y) hu₀ hdu₀ (hall z)

/-! ### Sign, normalization, and recurrence checks -/

-- Check 1: `w'' = 0` produces `a₀ = w₀`, `a₁ = w₁`, and `a_{n+2} = 0`.
example (w₀ w₁ : ℂ) (n : ℕ) : ordinaryPointCoeff 0 0 w₀ w₁ (n + 2) = 0 := by
  simp [ordinaryPointCoeff_add_two]

-- Check 2: For `w'' - w = 0` (`f = 0`, `g = -1`), `a₂ = w₀ / 2`, fixing the minus sign in the
-- coefficient recurrence.
example (w₀ w₁ : ℂ) :
    ordinaryPointCoeff 0 (Pi.single 0 (-1)) w₀ w₁ 2 = w₀ / 2 := by
  rw [ordinaryPointCoeff_add_two]; norm_num; ring

-- Check 3: Airy's equation `w'' - z w = 0` around `z₀ = 0` (`f = 0`, `g(z) = -z`, so `g₁ = -1`
-- and `g_m = 0` for `m ≠ 1`) has `a₂ = 0` and `(n + 3)(n + 2) a_{n+3} = a_n` (DLMF 9.4.1).
example (w₀ w₁ : ℂ) :
    ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ 2 = 0 := by
  rw [ordinaryPointCoeff_add_two]; simp

example (w₀ w₁ : ℂ) (n : ℕ) :
    ((n + 3 : ℂ) * (n + 2 : ℂ)) *
      ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ (n + 3) =
      ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ n := by
  have h := mul_ordinaryPointCoeff_add_two 0 (Pi.single 1 (-1)) w₀ w₁ (n + 1)
  have hlhs : ((n + 3 : ℂ) * (n + 2 : ℂ)) *
      ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ (n + 3) =
      (((n + 1 : ℕ) + 2 : ℂ) * ((n + 1 : ℕ) + 1 : ℂ)) *
        ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ ((n + 1) + 2) := by
    push_cast; ring_nf
  rw [hlhs, h, Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    have hk_le : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hne : n + 1 - k ≠ 1 := by omega
    simp [Pi.single_eq_of_ne hne]
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

end SecondOrder

end TauCeti

end
