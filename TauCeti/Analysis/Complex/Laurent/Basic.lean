/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Contour.Winding.Number.Circle

/-!
# Circle Laurent coefficients and the two-circle Cauchy formula

The circle integral defining a Laurent coefficient is independent of its positive radius
provided the function is continuous on the intervening closed annulus and complex
differentiable outside a countable exceptional set in its open interior. Under the same
hypotheses, the two-circle Cauchy formula represents the function between the circles by
the difference of its outer and inner Cauchy integrals, even at exceptional points.
Neither result assumes that the function extends across the center: isolated essential
singularities are allowed.

The construction uses Mathlib's Cauchy-Goursat theorem for annuli,
`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`, and its removable
divided difference `dslope`. These are the integral ingredients for splitting a Laurent
expansion into its positive and negative parts. The divided-difference proof of the
two-circle formula is adapted from Mathlib's
`Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux`,
by Yury Kudryashov, from a disc to an annulus. To include exceptional evaluation points,
we reuse Mathlib's local power-series theorem, whose Cauchy formula extends to those points
by continuity and closure.

For the classical Cauchy and Laurent formulas, see John B. Conway,
*Functions of One Complex Variable I*, Chapters IV (Complex Integration) and V (Singularities).
-/

public section

open Complex Set Metric Filter
open scoped Real Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The coefficient of degree `n` extracted by a circle of radius `R` centered at `c`.
For functions continuous on a closed annulus and complex differentiable outside a countable
set in its interior, `circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable`
makes this independent of the choice of circle within that annulus. -/
noncomputable def circleLaurentCoeff (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℤ) : E :=
  (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-n - 1) • f z

/-- The circle-integral formula for the integer-indexed Laurent coefficient. -/
theorem circleLaurentCoeff_def (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℤ) :
    circleLaurentCoeff f c R n =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-n - 1) • f z := (rfl)

/-- The nonnegative Laurent coefficients are exactly the coefficients of Mathlib's
Cauchy power series, even for the degenerate circle of radius zero. -/
theorem circleLaurentCoeff_natCast (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℕ) :
    circleLaurentCoeff f c R (n : ℤ) = (cauchyPowerSeries f c R).coeff n := by
  have h := (cauchyPowerSeries f c R).apply_eq_pow_smul_coeff (n := n) (z := 1)
  rw [one_pow, one_smul] at h
  rw [← h, cauchyPowerSeries_apply, circleLaurentCoeff_def]
  simp only [one_div, smul_smul,
    show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, pow_succ, mul_inv, inv_pow]

/-- Coefficient extraction depends only on the values on the integrating circle. -/
theorem circleLaurentCoeff_congr {f g : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hfg : EqOn f g (sphere c R)) (n : ℤ) :
    circleLaurentCoeff f c R n = circleLaurentCoeff g c R n := by
  rw [circleLaurentCoeff_def, circleLaurentCoeff_def]
  congr 1
  exact circleIntegral.integral_congr hR (fun z hz => by rw [hfg hz])

/-- Every coefficient of the zero function vanishes. -/
@[simp] theorem circleLaurentCoeff_zero (c : ℂ) (R : ℝ) (n : ℤ) :
    circleLaurentCoeff (fun _ => (0 : E)) c R n = 0 := by
  simp [circleLaurentCoeff_def, circleIntegral]

/-- Extracting coefficients commutes with complex scalar multiplication. -/
@[simp] theorem circleLaurentCoeff_smul (a : ℂ) (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℤ) :
    circleLaurentCoeff (fun z => a • f z) c R n = a • circleLaurentCoeff f c R n := by
  simp only [circleLaurentCoeff_def, smul_comm _ a, circleIntegral.integral_smul]

/-- Extracting coefficients is additive for functions integrable on the circle. -/
theorem circleLaurentCoeff_add {f g : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) (n : ℤ) :
    circleLaurentCoeff (fun z => f z + g z) c R n =
      circleLaurentCoeff f c R n + circleLaurentCoeff g c R n := by
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [circleLaurentCoeff_def, circleIntegral.integral_radius_zero, smul_zero, add_zero]
  have hc : c ∉ sphere c |R| := by simpa [eq_comm] using hR
  simp only [circleLaurentCoeff_def, smul_add]
  rw [circleIntegral.integral_add (hf.sub_zpow_smul (-n - 1) hc)
    (hg.sub_zpow_smul (-n - 1) hc), smul_add]

/-- The Cauchy estimate for any integer Laurent coefficient, including negative degrees
and the degenerate circle of radius zero. -/
theorem norm_circleLaurentCoeff_le {f : ℂ → E} {c : ℂ} {R M : ℝ} (hR : 0 ≤ R)
    (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (n : ℤ) :
    ‖circleLaurentCoeff f c R n‖ ≤ M * R ^ (-n) := by
  rcases hR.eq_or_lt with (rfl | hR)
  · simp only [circleLaurentCoeff_def, circleIntegral.integral_radius_zero, smul_zero,
      norm_zero]
    exact mul_nonneg ((norm_nonneg _).trans (hf c (by simp))) (zpow_nonneg le_rfl _)
  have hp : R * R ^ (-n - 1) = R ^ (-n) := by
    calc
      R * R ^ (-n - 1) = R ^ (1 : ℤ) * R ^ (-n - 1) := by rw [zpow_one]
      _ = R ^ (1 + (-n - 1)) := (zpow_add₀ hR.ne' _ _).symm
      _ = R ^ (-n) := by congr 1; ring
  calc
    ‖circleLaurentCoeff f c R n‖ ≤ R * (R ^ (-n - 1) * M) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
      intro z hz
      rw [norm_smul, norm_zpow, mem_sphere_iff_norm.mp hz]
      exact mul_le_mul_of_nonneg_left (hf z hz) (zpow_nonneg hR.le _)
    _ = M * R ^ (-n) := by rw [← mul_assoc, hp, mul_comm]

/-- The Laurent coefficient does not change when a circle moves through a closed annulus
on which the function is continuous and complex differentiable away from a countable
exceptional set in the open annulus. -/
theorem circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable
    {f : ℂ → E} {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) (n : ℤ) :
    circleLaurentCoeff f c R n = circleLaurentCoeff f c r n := by
  have hn : ∀ z ∈ closedBall c R \ ball c r, z - c ≠ 0 := by
    intro z hz
    exact sub_ne_zero.mpr fun h => hz.2 (h.symm ▸ mem_ball_self hr)
  unfold circleLaurentCoeff
  congr 1
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR hs
  · exact ((continuousOn_id.sub continuousOn_const).zpow₀ (-n - 1)
      fun z hz => Or.inl (hn z hz)).smul hc
  · intro z hz
    have hzA : z ∈ closedBall c R \ ball c r :=
      ⟨ball_subset_closedBall hz.1.1, fun h => hz.1.2 (ball_subset_closedBall h)⟩
    exact ((differentiableAt_id.sub_const c).zpow (Or.inl (hn z hzA))).smul (hd z hz)

variable [CompleteSpace E]

/-- A Laurent monomial has precisely its prescribed coefficient, in every integer degree. -/
@[simp] theorem circleLaurentCoeff_sub_zpow_smul (a : E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (m n : ℤ) :
    circleLaurentCoeff (fun z => (z - c) ^ m • a) c R n = if n = m then a else 0 := by
  have heq : (∮ z in C(c, R), (z - c) ^ (-n - 1) • (z - c) ^ m • a) =
      (∮ z in C(c, R), (z - c) ^ (-n - 1 + m)) • a := by
    rw [← circleIntegral.integral_smul_const]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hzc : z - c ≠ 0 := sub_ne_zero.mpr (ne_of_mem_sphere hz hR.ne')
    dsimp only
    rw [smul_smul, ← zpow_add₀ hzc]
  rw [circleLaurentCoeff_def, heq]
  split_ifs with hnm
  · subst n
    simp only [show -m - 1 + m = (-1 : ℤ) by ring, zpow_neg_one]
    rw [circleIntegral.integral_sub_center_inv c hR.ne',
      inv_smul_smul₀ (by simp [Real.pi_ne_zero])]
  · rw [circleIntegral.integral_sub_zpow_of_ne (by omega), zero_smul, smul_zero]

/-- The two-circle Cauchy formula on an annulus. The function is continuous on the closed
annulus and complex differentiable outside a countable exceptional set in the open annulus.
The evaluation point may belong to the exceptional set. -/
theorem
    two_pi_I_inv_smul_circleIntegral_sub_inv_smul_sub_of_differentiable_on_annulus_off_countable
    {f : ℂ → E} {c w : ℂ} {r R : ℝ} (hr : 0 < r)
    {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R \ closedBall c r)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    (2 * π * I : ℂ)⁻¹ •
        ((∮ z in C(c, R), (z - w)⁻¹ • f z) -
          ∮ z in C(c, r), (z - w)⁻¹ • f z) = f w := by
  have hrw : r < dist w c := lt_of_not_ge hw.2
  have hrR : r ≤ R := (hrw.trans hw.1).le
  have hR : 0 < R := hr.trans_le hrR
  have hU : IsOpen (ball c R \ closedBall c r) := isOpen_ball.sdiff isClosed_closedBall
  have hUA : ball c R \ closedBall c r ⊆ closedBall c R \ ball c r :=
    fun _ hz => ⟨ball_subset_closedBall hz.1, fun h => hz.2 (ball_subset_closedBall h)⟩
  have hA : closedBall c R \ ball c r ∈ 𝓝 w := mem_of_superset (hU.mem_nhds hw) hUA
  -- Mathlib's local Cauchy formula removes countable exceptions by continuity and closure.
  have hdf : DifferentiableAt ℂ f w := by
    obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hw)
    have hf := Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable
      (R := ⟨ε, hε.le⟩) hs (hc.mono (hεU.trans hUA))
      (fun z hz => hd z ⟨hεU (ball_subset_closedBall hz.1), hz.2⟩) hε
    exact hf.analyticAt.differentiableAt
  -- Fill the divided difference at w; Cauchy-Goursat permits the enlarged exceptional set.
  have hcd : ContinuousOn (dslope f w) (closedBall c R \ ball c r) :=
    (continuousOn_dslope hA).2 ⟨hc, hdf⟩
  have hid := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR (hs.insert w) hcd (fun z hz =>
      (differentiableAt_dslope_of_ne
        (ne_of_mem_of_not_mem (mem_insert w s) hz.2).symm).2
          (hd z (sdiff_subset_sdiff_right (subset_insert w s) hz)))
  have hRA : sphere c R ⊆ closedBall c R \ ball c r := by
    intro z hz
    exact ⟨sphere_subset_closedBall hz, fun hzr =>
      (not_lt_of_ge hrR) ((mem_sphere.mp hz) ▸ hzr)⟩
  have hrA : sphere c r ⊆ closedBall c R \ ball c r := by
    intro z hz
    exact ⟨closedBall_subset_closedBall hrR (sphere_subset_closedBall hz),
      fun h => (ne_of_lt h) (mem_sphere.mp hz)⟩
  have hwR : w ∉ sphere c R := fun h => (ne_of_lt hw.1) (mem_sphere.mp h)
  have hwr : w ∉ sphere c r := fun h => hw.2 (sphere_subset_closedBall h)
  have hdslope (ρ : ℝ) (hρ : 0 ≤ ρ)
      (hρA : sphere c ρ ⊆ closedBall c R \ ball c r) (hwρ : w ∉ sphere c ρ) :
      (∮ z in C(c, ρ), dslope f w z) =
        (∮ z in C(c, ρ), (z - w)⁻¹ • f z) -
          (∮ z in C(c, ρ), (z - w)⁻¹) • f w := by
    have hne : ∀ z ∈ sphere c ρ, z ≠ w :=
      fun _ hz => ne_of_mem_of_not_mem hz hwρ
    have hwρ' : w ∉ sphere c |ρ| := by rwa [abs_of_nonneg hρ]
    have hi₁ : CircleIntegrable (fun z => (z - w)⁻¹ • f z) c ρ := by
      simpa only [zpow_neg_one] using
        ((hc.mono hρA).circleIntegrable hρ).sub_zpow_smul (-1) hwρ'
    have hi₂ : CircleIntegrable (fun z => (z - w)⁻¹ • f w) c ρ := by
      simpa only [zpow_neg_one] using
        (circleIntegrable_const (f w) c ρ).sub_zpow_smul (-1) hwρ'
    rw [← circleIntegral.integral_smul_const, ← circleIntegral.integral_sub hi₁ hi₂]
    apply circleIntegral.integral_congr hρ
    intro z hz
    simp only [dslope_of_ne _ (hne z hz), slope, vsub_eq_sub, smul_sub]
  rw [hdslope R hR.le hRA hwR, hdslope r hr.le hrA hwr,
    circleIntegral.integral_sub_inv_of_mem_ball hw.1,
    Contour.circleIntegral_sub_inv_eq_zero_of_lt_dist hr.le hrw, zero_smul, sub_zero] at hid
  have hdiff : (∮ z in C(c, R), (z - w)⁻¹ • f z) -
      (∮ z in C(c, r), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w :=
    sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hid).trans (add_comm _ _))
  rw [hdiff, inv_smul_smul₀ (by simp [Real.pi_ne_zero])]

end TauCeti
