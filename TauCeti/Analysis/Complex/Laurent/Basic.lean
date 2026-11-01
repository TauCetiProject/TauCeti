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
as long as the intervening closed annulus lies in the domain of holomorphy. The two-circle
Cauchy formula represents a holomorphic function between two concentric circles by the
difference of its outer and inner Cauchy integrals. Neither result assumes that the function
extends across the center: isolated essential singularities are allowed.

The construction uses Mathlib's Cauchy-Goursat theorem for annuli,
`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`, and its removable
divided difference `dslope`. These are the integral ingredients for splitting a Laurent
expansion into its positive and negative parts.

For the classical Cauchy and Laurent formulas, see John B. Conway,
*Functions of One Complex Variable I*, Chapters IV (Complex Integration) and V (Singularities).
-/

public section

open Complex Set Metric Filter
open scoped Real Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The coefficient of degree `n` extracted by a circle of radius `R` centered at `c`.
For holomorphic functions on an annulus, `circleLaurentCoeff_eq` makes this independent
of the choice of circle within that annulus. -/
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

/-- The Cauchy estimate for any integer Laurent coefficient, including negative degrees. -/
theorem norm_circleLaurentCoeff_le {f : ℂ → E} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (n : ℤ) :
    ‖circleLaurentCoeff f c R n‖ ≤ M * R ^ (-n) := by
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
on which the function is continuous, with holomorphic interior. -/
theorem circleLaurentCoeff_eq {f : ℂ → E} {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : DifferentiableOn ℂ f (ball c R \ closedBall c r)) (n : ℤ) :
    circleLaurentCoeff f c R n = circleLaurentCoeff f c r n := by
  have hn : ∀ z ∈ closedBall c R \ ball c r, z - c ≠ 0 := by
    intro z hz heq
    have : z = c := sub_eq_zero.mp heq
    subst z
    exact hz.2 (by simpa using hr)
  unfold circleLaurentCoeff
  congr 1
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    countable_empty
  · exact ((continuousOn_id.sub continuousOn_const).zpow₀ (-n - 1)
      fun z hz => Or.inl (hn z hz)).smul hc
  · intro z hz
    have hz' : z ∈ ball c R \ closedBall c r := hz.1
    have hzA : z ∈ closedBall c R \ ball c r :=
      ⟨ball_subset_closedBall hz'.1, fun h => hz'.2 (ball_subset_closedBall h)⟩
    exact ((differentiableAt_id.sub_const c).zpow (Or.inl (hn z hzA))).smul
      (hd.differentiableAt ((isOpen_ball.sdiff isClosed_closedBall).mem_nhds hz'))

variable [CompleteSpace E]

/-- A Laurent monomial has precisely its prescribed coefficient, in every integer degree. -/
@[simp] theorem circleLaurentCoeff_zpow_smul (a : E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (m n : ℤ) :
    circleLaurentCoeff (fun z => (z - c) ^ m • a) c R n = if n = m then a else 0 := by
  have heq : (∮ z in C(c, R), (z - c) ^ (-n - 1) • (z - c) ^ m • a) =
      (∮ z in C(c, R), (z - c) ^ (-n - 1 + m)) • a := by
    rw [← circleIntegral.integral_smul_const]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hzc : z - c ≠ 0 := by
      intro h
      have : z = c := sub_eq_zero.mp h
      subst z
      have hz0 : (0 : ℝ) = R := by simpa using hz
      exact hR.ne' hz0.symm
    dsimp only
    rw [smul_smul, ← zpow_add₀ hzc]
  rw [circleLaurentCoeff_def, heq]
  split_ifs with hnm
  · subst n
    simp only [show -m - 1 + m = (-1 : ℤ) by ring, zpow_neg_one]
    rw [circleIntegral.integral_sub_center_inv c hR.ne',
      inv_smul_smul₀ (by simp [Real.pi_ne_zero])]
  · rw [circleIntegral.integral_sub_zpow_of_ne (by omega), zero_smul, smul_zero]

/-- The two-circle Cauchy formula on an annulus. The function need only be continuous on
the boundary circles and holomorphic in the intervening open annulus. -/
theorem two_pi_I_inv_smul_circleIntegral_sub_inv_smul_sub_of_differentiable_on_annulus
    {f : ℂ → E} {c w : ℂ} {r R : ℝ} (hr : 0 < r)
    (hw : w ∈ ball c R \ closedBall c r)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : DifferentiableOn ℂ f (ball c R \ closedBall c r)) :
    (2 * π * I : ℂ)⁻¹ •
        ((∮ z in C(c, R), (z - w)⁻¹ • f z) -
          ∮ z in C(c, r), (z - w)⁻¹ • f z) = f w := by
  have hrw : r < dist w c := lt_of_not_ge hw.2
  have hrR : r ≤ R := (hrw.trans hw.1).le
  have hR : 0 < R := hr.trans_le hrR
  have hA : closedBall c R \ ball c r ∈ 𝓝 w := by
    apply mem_of_superset
      (inter_mem (closedBall_mem_nhds_of_mem hw.1)
        (isClosed_closedBall.isOpen_compl.mem_nhds hw.2))
    rintro z ⟨hzR, hzr⟩
    exact ⟨hzR, fun hz => hzr (ball_subset_closedBall hz)⟩
  -- Fill the divided difference at w; Cauchy-Goursat permits this one exceptional point.
  have hdf : DifferentiableAt ℂ f w :=
    hd.differentiableAt ((isOpen_ball.sdiff isClosed_closedBall).mem_nhds hw)
  have hcd : ContinuousOn (dslope f w) (closedBall c R \ ball c r) :=
    (continuousOn_dslope hA).2 ⟨hc, hdf⟩
  have hid := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR (countable_singleton w) hcd (fun z hz =>
      (differentiableAt_dslope_of_ne (by simpa using hz.2)).2
        (hd.differentiableAt ((isOpen_ball.sdiff isClosed_closedBall).mem_nhds hz.1)))
  -- On either boundary, the divided difference splits into the two Cauchy kernels.
  have heq (s : ℝ) (hs : 0 ≤ s) (hsA : sphere c s ⊆ closedBall c R \ ball c r)
      (hsw : w ∉ sphere c s) :
      (∮ z in C(c, s), dslope f w z) =
        (∮ z in C(c, s), (z - w)⁻¹ • f z) -
          (∮ z in C(c, s), (z - w)⁻¹) • f w := by
    have hne : ∀ z ∈ sphere c s, z ≠ w :=
      fun z hz h => hsw (h ▸ hz)
    have hki : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (sphere c s) :=
      (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => sub_ne_zero.mpr (hne z hz))
    have hi₁ : CircleIntegrable (fun z => (z - w)⁻¹ • f z) c s :=
      (hki.smul (hc.mono hsA)).circleIntegrable hs
    have hi₂ : CircleIntegrable (fun z => (z - w)⁻¹ • f w) c s :=
      (hki.smul continuousOn_const).circleIntegrable hs
    rw [← circleIntegral.integral_smul_const, ← circleIntegral.integral_sub hi₁ hi₂]
    apply circleIntegral.integral_congr hs
    intro z hz
    simp only [dslope_of_ne _ (hne z hz), slope, vsub_eq_sub, smul_sub]
  rw [heq R hR.le (fun z hz => ⟨sphere_subset_closedBall hz, by
      intro hzr
      have : dist z c = R := hz
      have : R < r := this ▸ hzr
      exact (not_lt_of_ge hrR) this⟩) (by
        exact fun h => (ne_of_lt hw.1) h),
    heq r hr.le (fun z hz => ⟨closedBall_subset_closedBall hrR
      (sphere_subset_closedBall hz), by
        exact fun h => (ne_of_lt h) hz⟩) (by
        exact fun h => hw.2 (sphere_subset_closedBall h)),
    circleIntegral.integral_sub_inv_of_mem_ball hw.1,
    Contour.circleIntegral_sub_inv_eq_zero_of_lt_dist hr.le hrw, zero_smul, sub_zero] at hid
  have hdiff : (∮ z in C(c, R), (z - w)⁻¹ • f z) -
      (∮ z in C(c, r), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w :=
    sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hid).trans (add_comm _ _))
  rw [hdiff, inv_smul_smul₀ (by simp [Real.pi_ne_zero])]

end TauCeti
