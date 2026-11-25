/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Analysis.Analytic.TaylorSeries
import TauCeti.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Complex.Taylor.Basic
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Data.Nat.Choose.Sum

/-!
# First-order complex linear ODE systems in a Banach space

This module develops existence, uniqueness, and Taylor-series representation for first-order
complex linear differential systems `v'(z) = A(z) (v(z)) + b(z)` around an ordinary point `z₀ ∈ ℂ`
in a complex Banach space `E`:

* **Formal Taylor coefficients**: `TauCeti.linearSystemCoeff` defines the factorial-scaled Taylor
  coefficients `(n ! : ℂ)⁻¹ • iteratedDeriv n v z₀` of the formal solution series
  `∑ₙ cₙ (z - z₀)ⁿ`, together with its recurrence, uniqueness characterization, and linearity in
  `(b, v₀)`.
* **Cauchy majorant convergence**: `TauCeti.le_radius_mkPiRingSeries_linearSystemCoeff` proves that
  the formal solution series `TauCeti.mkPiRingSeries ℂ (TauCeti.linearSystemCoeff A b v₀)` has
  convergence radius at least `r` whenever the coefficient series for `A` and `b` do.
* **Global uniqueness**: On any open preconnected set `U ⊆ ℂ`, two holomorphic functions on `U` that
  satisfy `v'(z) = A(z) (v(z)) + b(z)` near a point `z₀ ∈ U` where `A` is analytic and agree at
  `z₀` coincide throughout `U`, with no regularity hypothesis on `b`
  (`TauCeti.eqOn_of_hasDerivAt_clm_apply_add`).
* **Existence on discs and on `ℂ`**: On an open extended disc `Metric.eball z₀ r` (`0 < r ≤ ∞`)
  where `A` and `b` are holomorphic (or admit formal power series), every initial value `v₀`
  determines a unique holomorphic solution represented by `TauCeti.linearSystemCoeff` across the
  entire disc (`TauCeti.exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add`,
  `TauCeti.exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add_of_hasFPowerSeriesOnBall`, and
  `TauCeti.existsUnique_hasDerivAt_clm_apply_add` for entire systems).

## Implementation notes

Full-disc convergence (`TauCeti.le_radius_mkPiRingSeries_linearSystemCoeff`) is proved directly by
Cauchy's method of majorants: on every smaller radius `ρ < r`, choosing `m : ℕ` with `ρ * CA ≤ m`
bounds `‖cₙ‖ ρⁿ` by `max ‖v₀‖ (ρ * Cb) * (n + m).choose m` via
`Nat.one_add_mul_sum_range_add_choose_le`, whose weighted geometric series converges on `R < ρ` by
`summable_choose_mul_geometric_of_norm_lt_one`. Termwise differentiation
(`HasFPowerSeriesOnBall.deriv`) and Banach-space Cauchy products (`HasFPowerSeriesOnBall.clm_apply`)
verify the differential equation on the disc, while global uniqueness on preconnected open domains
combines local power-series vanishing at `z₀` with analytic continuation
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`).

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §1.1.
* NIST Digital Library of Mathematical Functions, §2.7(i), <https://dlmf.nist.gov/2.7>.
* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, 1955, Ch. 3, §6.
-/

public noncomputable section

open Complex Filter Finset Metric Set Topology
open scoped BigOperators ENNReal NNReal Nat

namespace TauCeti

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

private theorem norm_linearSystemCoeff_mul_pow_le_mul_choose
    {A : ℕ → E →L[ℂ] E} {b : ℕ → E} {v₀ : E} {ρ CA Cb : ℝ} {m : ℕ}
    (hρ : 0 ≤ ρ)
    (hCA : ∀ n, ‖A n‖ * ρ ^ n ≤ CA) (hCb : ∀ n, ‖b n‖ * ρ ^ n ≤ Cb)
    (hm : ρ * CA ≤ m) (n : ℕ) :
    ‖linearSystemCoeff A b v₀ n‖ * ρ ^ n ≤
      max ‖v₀‖ (ρ * Cb) * (n + m).choose m := by
  let μ₀ : ℝ := max ‖v₀‖ (ρ * Cb)
  have hμ₀ : 0 ≤ μ₀ := (norm_nonneg v₀).trans (le_max_left _ _)
  have hCA_nonneg : 0 ≤ CA := le_trans (by positivity) (hCA 0)
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | n
    · simp only [linearSystemCoeff_zero, pow_zero, mul_one, zero_add, Nat.choose_self,
        Nat.cast_one]
      exact le_max_left _ _
    · -- Express `(n + 1) * ‖c_{n+1}‖ ρ^{n+1}` via the cleared-denominator recurrence.
      have hn_norm : ‖((n + 1 : ℂ))‖ = (n + 1 : ℝ) := mod_cast Complex.norm_natCast (n + 1)
      have hlhs : ((n + 1 : ℝ)) * (‖linearSystemCoeff A b v₀ (n + 1)‖ * ρ ^ (n + 1)) =
          ‖((n + 1 : ℂ)) • linearSystemCoeff A b v₀ (n + 1)‖ * ρ ^ (n + 1) := by
        rw [norm_smul, hn_norm, mul_assoc]
      have hbinom :
          (1 : ℝ) + (m : ℝ) * ∑ k ∈ Finset.range (n + 1), ((k + m).choose m : ℝ) ≤
            (n + 1 : ℝ) * ((n + 1 + m).choose m : ℝ) := by
        exact_mod_cast Nat.one_add_mul_sum_range_add_choose_le n m
      -- Bound the Cauchy-product recurrence termwise by the binomial majorant.
      have hbound : ((n + 1 : ℝ)) * (‖linearSystemCoeff A b v₀ (n + 1)‖ * ρ ^ (n + 1)) ≤
          (n + 1 : ℝ) * (μ₀ * ((n + 1 + m).choose m : ℝ)) := by
        rw [hlhs, natCast_add_one_smul_linearSystemCoeff_succ]
        calc
          ‖b n + ∑ k ∈ Finset.range (n + 1), A (n - k) (linearSystemCoeff A b v₀ k)‖ * ρ ^ (n + 1)
              ≤ (‖b n‖ + ‖∑ k ∈ Finset.range (n + 1),
                  A (n - k) (linearSystemCoeff A b v₀ k)‖) * ρ ^ (n + 1) := by
                gcongr
                exact norm_add_le _ _
          _ = ρ * (‖b n‖ * ρ ^ n) + ρ * (‖∑ k ∈ Finset.range (n + 1),
                A (n - k) (linearSystemCoeff A b v₀ k)‖ * ρ ^ n) := by
                rw [pow_succ]
                ring
          _ ≤ ρ * Cb + ρ * ∑ k ∈ Finset.range (n + 1),
                (‖A (n - k)‖ * ρ ^ (n - k)) * (‖linearSystemCoeff A b v₀ k‖ * ρ ^ k) :=
                add_le_add (mul_le_mul_of_nonneg_left (hCb n) hρ)
                  (mul_le_mul_of_nonneg_left
                    (norm_sum_range_clm_apply_mul_pow_le A (linearSystemCoeff A b v₀) hρ n) hρ)
          _ ≤ ρ * Cb + ρ * ∑ k ∈ Finset.range (n + 1), CA * (μ₀ * ((k + m).choose m : ℝ)) :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk ↦
                  mul_le_mul (hCA (n - k)) (ih k (Finset.mem_range.mp hk))
                    (by positivity) hCA_nonneg) hρ)
          _ = ρ * Cb + (ρ * CA) * (μ₀ * ∑ k ∈ Finset.range (n + 1), ((k + m).choose m : ℝ)) := by
                simp_rw [← mul_assoc]
                rw [← Finset.mul_sum]
                ring
          _ ≤ μ₀ * (1 + (m : ℝ) * ∑ k ∈ Finset.range (n + 1), ((k + m).choose m : ℝ)) := by
                have h1 : ρ * Cb ≤ μ₀ := le_max_right _ _
                have h2 : (ρ * CA) * (μ₀ * ∑ k ∈ Finset.range (n + 1), ((k + m).choose m : ℝ)) ≤
                    (m : ℝ) * (μ₀ * ∑ k ∈ Finset.range (n + 1), ((k + m).choose m : ℝ)) :=
                  mul_le_mul_of_nonneg_right hm (by positivity)
                linarith
          _ ≤ μ₀ * ((n + 1 : ℝ) * ((n + 1 + m).choose m : ℝ)) :=
                mul_le_mul_of_nonneg_left hbinom hμ₀
          _ = (n + 1 : ℝ) * (μ₀ * ((n + 1 + m).choose m : ℝ)) := by ring
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
  obtain ⟨CA, _, hCA⟩ :=
    (mkPiRingSeries ℂ A).norm_mul_pow_le_of_lt_radius (hρr.trans_le hA)
  obtain ⟨Cb, _, hCb⟩ :=
    (mkPiRingSeries ℂ b).norm_mul_pow_le_of_lt_radius (hρr.trans_le hb)
  simp only [norm_mkPiRingSeries] at hCA hCb
  obtain ⟨m, hm⟩ := exists_nat_ge ((ρ : ℝ) * CA)
  let q : ℝ := R / ρ
  have hq_pos : 0 < q := div_pos hR_pos hρ_pos
  have hR : (R : ℝ) = ρ * q := (mul_div_cancel₀ _ hρ_pos.ne').symm
  have hq_norm : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq_pos.le]
    exact (div_lt_one hρ_pos).mpr hRρ
  have hchoose_sum :=
    (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) m hq_norm).mul_left
      (max ‖v₀‖ ((ρ : ℝ) * Cb))
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) hchoose_sum
  rw [norm_mkPiRingSeries, hR, mul_pow, ← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (norm_linearSystemCoeff_mul_pow_le_mul_choose ρ.property hCA hCb hm n)
    (pow_nonneg hq_pos.le n)

variable [CompleteSpace E]

/-- Any holomorphic function `v` on `Metric.eball z₀ r` (`0 < r ≤ ∞`) that satisfies
`v'(z) = A(z) (v(z)) + b(z)` eventually near `z₀`, where `A` and `b` admit formal power series
`mkPiRingSeries ℂ As` and `mkPiRingSeries ℂ bs` at `z₀`, is represented on `Metric.eball z₀ r` by
`mkPiRingSeries ℂ (linearSystemCoeff As bs (v z₀))`. -/
theorem hasFPowerSeriesOnBall_of_hasDerivAt_clm_apply_add
    {A : ℂ → E →L[ℂ] E} {b v : ℂ → E} {As : ℕ → E →L[ℂ] E} {bs : ℕ → E}
    {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hA : HasFPowerSeriesAt A (mkPiRingSeries ℂ As) z₀)
    (hb : HasFPowerSeriesAt b (mkPiRingSeries ℂ bs) z₀)
    (hv : DifferentiableOn ℂ v (Metric.eball z₀ r))
    (hode : ∀ᶠ z in 𝓝 z₀, HasDerivAt v (A z (v z) + b z) z) :
    HasFPowerSeriesOnBall v (mkPiRingSeries ℂ (linearSystemCoeff As bs (v z₀))) z₀ r := by
  let c : ℕ → E := fun n ↦ (n ! : ℂ)⁻¹ • iteratedDeriv n v z₀
  have hv_ps : HasFPowerSeriesOnBall v (mkPiRingSeries ℂ c) z₀ r :=
    hv.hasFPowerSeriesOnBall_eball hr
  obtain ⟨rA, hA_ball⟩ := hA
  obtain ⟨rb, hb_ball⟩ := hb
  let r₀ : ℝ≥0∞ := min r (min rA rb)
  have hr₀ : 0 < r₀ := lt_min hr (lt_min hA_ball.r_pos hb_ball.r_pos)
  have hv_r₀ := hv_ps.mono hr₀ (min_le_left _ _)
  have hA_r₀ := hA_ball.mono hr₀ ((min_le_right _ _).trans (min_le_left _ _))
  have hb_r₀ := hb_ball.mono hr₀ ((min_le_right _ _).trans (min_le_right _ _))
  have hlhs_ps := hv_r₀.deriv
  have hrhs_ps := (hA_r₀.clm_apply hv_r₀).add hb_r₀
  have heq : deriv v =ᶠ[𝓝 z₀] fun z ↦ A z (v z) + b z := hode.mono fun _ hz ↦ hz.deriv
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
  have hA_diff : DifferentiableOn ℂ A (Metric.eball z₀ r) :=
    fun z hz ↦ (hr hz).1.differentiableAt.differentiableWithinAt
  have hb_diff : DifferentiableOn ℂ b (Metric.eball z₀ r) :=
    fun z hz ↦ (hr hz).2.1.differentiableAt.differentiableWithinAt
  have hv_diff : DifferentiableOn ℂ v (Metric.eball z₀ r) :=
    fun z hz ↦ (hr hz).2.2.differentiableAt.differentiableWithinAt
  have hA_ps := hA_diff.hasFPowerSeriesOnBall_eball hr_pos
  have hb_ps := hb_diff.hasFPowerSeriesOnBall_eball hr_pos
  have hv_ps := hv_diff.hasFPowerSeriesOnBall_eball hr_pos
  have hv_ps' := hasFPowerSeriesOnBall_of_hasDerivAt_clm_apply_add hr_pos
    hA_ps.hasFPowerSeriesAt hb_ps.hasFPowerSeriesAt hv_diff hv
  exact congrFun (mkPiRingSeries_inj.mp
    (hv_ps.hasFPowerSeriesAt.eq_formalMultilinearSeries hv_ps'.hasFPowerSeriesAt)) n

/-- If `A` is analytic at `z₀ ∈ U`, then any two holomorphic functions `v₁, v₂` on an open
preconnected set `U ⊆ ℂ` that satisfy `v'(z) = A(z) (v(z)) + b(z)` eventually near `z₀` and agree
at `z₀` agree throughout `U`. No regularity hypothesis on `b` is needed, and `A` need only be
analytic at `z₀`. -/
theorem eqOn_of_hasDerivAt_clm_apply_add {A : ℂ → E →L[ℂ] E} {b v₁ v₂ : ℂ → E} {U : Set ℂ}
    {z₀ : ℂ} (hU : IsOpen U) (hU_conn : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hA : AnalyticAt ℂ A z₀)
    (hv₁ : DifferentiableOn ℂ v₁ U) (hv₂ : DifferentiableOn ℂ v₂ U)
    (hode₁ : ∀ᶠ z in 𝓝 z₀, HasDerivAt v₁ (A z (v₁ z) + b z) z)
    (hode₂ : ∀ᶠ z in 𝓝 z₀, HasDerivAt v₂ (A z (v₂ z) + b z) z) (h₀ : v₁ z₀ = v₂ z₀) :
    EqOn v₁ v₂ U := by
  let u : ℂ → E := v₁ - v₂
  have hu_deriv : ∀ᶠ z in 𝓝 z₀, HasDerivAt u (A z (u z) + (fun _ : ℂ ↦ (0 : E)) z) z :=
    (hode₁.and hode₂).mono fun z ⟨h₁, h₂⟩ ↦ by
      simpa [u, map_sub, add_sub_add_right_eq_sub] using h₁.sub h₂
  have hu_diff : DifferentiableOn ℂ u U := hv₁.sub hv₂
  obtain ⟨r, hr_pos, hrU⟩ := EMetric.isOpen_iff.mp hU z₀ hz₀
  have hu_ps := (hu_diff.mono hrU).hasFPowerSeriesOnBall_eball hr_pos
  have hu_coeff : (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • iteratedDeriv n u z₀) = 0 := by
    ext n
    rw [inv_factorial_smul_iteratedDeriv_eq_linearSystemCoeff_of_hasDerivAt_clm_apply_add
      hA analyticAt_const hu_deriv n]
    have hb0 : (fun m : ℕ ↦ (m ! : ℂ)⁻¹ • iteratedDeriv m (fun _ : ℂ ↦ (0 : E)) z₀) = 0 := by
      ext m; simp
    have hu₀ : u z₀ = 0 := by simp [u, h₀]
    rw [hu₀, hb0, linearSystemCoeff_zero_zero]
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
  have heball_nhds : Metric.eball z₀ r ∈ 𝓝 z₀ :=
    Metric.isOpen_eball.mem_nhds (mem_eball_self hA.r_pos)
  exact eqOn_of_hasDerivAt_clm_apply_add Metric.isOpen_eball isPreconnected_eball
    (mem_eball_self hA.r_pos) hA.analyticAt
    (fun z hz ↦ (hu z hz).differentiableAt.differentiableWithinAt) hv_ps.differentiableOn
    (Filter.eventually_of_mem heball_nhds hu) (Filter.eventually_of_mem heball_nhds hv_ode)
    (hu₀.trans hv₀.symm)

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

end TauCeti

end
