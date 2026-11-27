/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Topology.MetricSpace.EBall

/-!
# Circle Laurent coefficients

The circle integral defining a Laurent coefficient is independent of its positive radius
provided the function is continuous on the intervening closed annulus and complex
differentiable outside a countable exceptional set in its open interior.
This result does not assume that the function extends across the center: isolated essential
singularities are allowed. When `f` is complex-differentiable on a circle with circle-integrable
derivative, integrating around the circle also expresses the Laurent coefficients of `deriv f` in
terms of those of `f` (`circleLaurentCoeff_deriv_of_differentiableAt`, `circleLaurentCoeff_deriv`).
Iterating, the coefficient of degree `n - m` of the `m`-th derivative is the falling factorial
`n (n - 1) ⋯ (n - m + 1)` times the coefficient of degree `n` (`circleLaurentCoeff_iteratedDeriv`).

The construction uses Mathlib's Cauchy-Goursat theorem for annuli,
`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`.

For the classical Cauchy and Laurent formulas, see John B. Conway,
*Functions of One Complex Variable I*, Chapters IV (Complex Integration) and V (Singularities).
-/

public section

open Complex Set Metric Filter
open scoped Real ENNReal Topology

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

/-- On the degenerate circle of radius zero every coefficient vanishes. -/
@[simp] theorem circleLaurentCoeff_radius_zero (f : ℂ → E) (c : ℂ) (n : ℤ) :
    circleLaurentCoeff f c 0 n = 0 := by
  simp only [circleLaurentCoeff_def, circleIntegral.integral_radius_zero, smul_zero]

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

/-- Multiplying a function by `(z - c) ^ m` shifts its coefficients by `m`: the coefficient of
degree `n` of `(z - c) ^ m • f z` is the coefficient of degree `n - m` of `f`. -/
theorem circleLaurentCoeff_sub_zpow_smul_apply (f : ℂ → E) (c : ℂ) (R : ℝ) (m n : ℤ) :
    circleLaurentCoeff (fun z => (z - c) ^ m • f z) c R n = circleLaurentCoeff f c R (n - m) := by
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [circleLaurentCoeff_radius_zero]
  simp only [circleLaurentCoeff_def, circleIntegral]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hz : circleMap c R θ - c ≠ 0 := sub_ne_zero.2 (circleMap_ne_center hR)
  simp only [smul_smul, ← zpow_add₀ hz]
  congr 3
  ring

/-- Extracting coefficients is additive for functions integrable on the circle. -/
theorem circleLaurentCoeff_add {f g : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) (n : ℤ) :
    circleLaurentCoeff (fun z => f z + g z) c R n =
      circleLaurentCoeff f c R n + circleLaurentCoeff g c R n := by
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [circleLaurentCoeff_radius_zero, add_zero]
  have hc : c ∉ sphere c |R| := by simpa [eq_comm] using hR
  simp only [circleLaurentCoeff_def, smul_add]
  rw [circleIntegral.integral_add (hf.sub_zpow_smul (-n - 1) hc)
    (hg.sub_zpow_smul (-n - 1) hc), smul_add]

/-- Extracting coefficients commutes with subtraction of functions integrable on the circle. -/
theorem circleLaurentCoeff_sub {f g : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) (n : ℤ) :
    circleLaurentCoeff (fun z => f z - g z) c R n =
      circleLaurentCoeff f c R n - circleLaurentCoeff g c R n := by
  rw [eq_sub_iff_add_eq, ← circleLaurentCoeff_add (f := fun z => f z - g z) (hf.sub hg) hg n]
  simp only [sub_add_cancel]

/-- The Cauchy estimate for any integer Laurent coefficient, including negative degrees
and the degenerate circle of radius zero. -/
theorem norm_circleLaurentCoeff_le {f : ℂ → E} {c : ℂ} {R M : ℝ} (hR : 0 ≤ R)
    (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (n : ℤ) :
    ‖circleLaurentCoeff f c R n‖ ≤ M * R ^ (-n) := by
  rcases hR.eq_or_lt with (rfl | hR)
  · simp only [circleLaurentCoeff_radius_zero, norm_zero]
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

/-- On an open concentric annulus `Metric.eball c R \ Metric.closedBall c r`, any two interior
radii `ρ₁, ρ₂ ∈ (r, R)` yield identical `circleLaurentCoeff` values when `f` is continuous on the
open annulus and complex-differentiable outside a countable subset. -/
theorem circleLaurentCoeff_eq_of_differentiable_on_open_annulus_off_countable
    {f : ℂ → E} {c : ℂ} {r ρ₁ ρ₂ : ℝ} {R : ℝ≥0∞} {s : Set ℂ}
    (hr : 0 ≤ r) (hr₁ : r < ρ₁) (hr₂ : r < ρ₂)
    (hR₁ : ENNReal.ofReal ρ₁ < R) (hR₂ : ENNReal.ofReal ρ₂ < R) (hs : s.Countable)
    (hc : ContinuousOn f (eball c R \ closedBall c r))
    (hd : ∀ z ∈ (eball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) (n : ℤ) :
    circleLaurentCoeff f c ρ₁ n = circleLaurentCoeff f c ρ₂ n := by
  let r' : ℝ := min ρ₁ ρ₂
  let R' : ℝ := max ρ₁ ρ₂
  have hr'_pos : 0 < r' := hr.trans_lt (lt_min hr₁ hr₂)
  have hR'R : ENNReal.ofReal R' < R := by
    dsimp only [R']
    rcases max_choice ρ₁ ρ₂ with hmax | hmax <;> rwa [hmax]
  have hsub : closedBall c R' \ ball c r' ⊆ eball c R \ closedBall c r :=
    closedBall_sdiff_ball_subset_eball_sdiff_closedBall (lt_min hr₁ hr₂) hR'R
  have hsub_open : (ball c R' \ closedBall c r') \ s ⊆ (eball c R \ closedBall c r) \ s :=
    sdiff_subset_sdiff ((sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall).trans
      hsub) Subset.rfl
  have heq := circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable
    hr'_pos (min_le_max) hs (hc.mono hsub) (fun z hz => hd z (hsub_open hz)) n
  rcases le_total ρ₁ ρ₂ with hle | hle
  · simpa only [r', R', min_eq_left hle, max_eq_right hle] using heq.symm
  · simpa only [r', R', min_eq_right hle, max_eq_left hle] using heq

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

/-- If `f` is complex-differentiable at every point of `Metric.sphere c R` (`0 < R`) and `deriv f`
is circle-integrable on `C(c, R)`, then the `n`-th circle Laurent coefficient of `deriv f` equals
`(n + 1) • circleLaurentCoeff f c R (n + 1)`. -/
theorem circleLaurentCoeff_deriv_of_differentiableAt {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hd : ∀ z ∈ sphere c R, DifferentiableAt ℂ f z)
    (hderiv : CircleIntegrable (deriv f) c R) (n : ℤ) :
    circleLaurentCoeff (deriv f) c R n = ((n + 1 : ℤ) : ℂ) • circleLaurentCoeff f c R (n + 1) := by
  have hc_not_mem : c ∉ sphere c |R| := by
    rw [abs_of_pos hR, mem_sphere, dist_self]
    exact hR.ne
  have hf_cont : ContinuousOn f (sphere c R) :=
    fun z hz => (hd z hz).continuousAt.continuousWithinAt
  have hf_int : CircleIntegrable f c R := hf_cont.circleIntegrable hR.le
  have hi₁ : CircleIntegrable (fun z => (((-n - 1 : ℤ) : ℂ) * (z - c) ^ (-n - 2)) • f z) c R := by
    simpa only [mul_smul] using
      (hf_int.sub_zpow_smul (-n - 2) hc_not_mem).const_fun_smul (a := ((-n - 1 : ℤ) : ℂ))
  have hi₂ : CircleIntegrable (fun z => (z - c) ^ (-n - 1) • deriv f z) c R :=
    hderiv.sub_zpow_smul (-n - 1) hc_not_mem
  have hzero : (∮ z in C(c, R),
      (((-n - 1 : ℤ) : ℂ) * (z - c) ^ (-n - 2)) • f z +
        (z - c) ^ (-n - 1) • deriv f z) = 0 := by
    refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt
      (f := fun w : ℂ => (w - c) ^ (-n - 1) • f w) hR.le fun z hz => ?_
    have hzc : z - c ≠ 0 := sub_ne_zero.mpr (ne_of_mem_sphere hz hR.ne')
    have hzpow : HasDerivAt (fun w : ℂ => (w - c) ^ (-n - 1))
        (((-n - 1 : ℤ) : ℂ) * (z - c) ^ (-n - 2)) z := by
      have hexp : -n - 1 - 1 = -n - 2 := by omega
      simpa only [Function.comp_def, id_eq, hexp, mul_one] using
        (hasDerivAt_zpow (-n - 1) (z - c) (Or.inl hzc)).comp z
          ((hasDerivAt_id (𝕜 := ℂ) z).sub_const c)
    exact ((hzpow.smul (hd z hz).hasDerivAt).congr_deriv (add_comm _ _)).hasDerivWithinAt
  rw [circleIntegral.integral_add hi₁ hi₂] at hzero
  have hpull : (∮ z in C(c, R), (((-n - 1 : ℤ) : ℂ) * (z - c) ^ (-n - 2)) • f z) =
      (-((n + 1 : ℤ) : ℂ)) • ∮ z in C(c, R), (z - c) ^ (-(n + 1) - 1) • f z := by
    have hexp : -n - 2 = -(n + 1) - 1 := by omega
    have hcast : ((-n - 1 : ℤ) : ℂ) = -((n + 1 : ℤ) : ℂ) := by push_cast; ring
    simp only [mul_smul, hexp, hcast, circleIntegral.integral_smul]
  rw [hpull, neg_smul, neg_add_eq_zero] at hzero
  rw [circleLaurentCoeff_def, circleLaurentCoeff_def, ← hzero, smul_comm]

/-- For `f` complex-differentiable on an open concentric annulus
`Metric.eball c R \ Metric.closedBall c r` and any interior circle radius `ρ ∈ (r, R)`, the `n`-th
circle Laurent coefficient of `deriv f` equals `(n + 1) • circleLaurentCoeff f c ρ (n + 1)`. -/
theorem circleLaurentCoeff_deriv {f : ℂ → E} {c : ℂ} {r ρ : ℝ} {R : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (eball c R \ closedBall c r))
    (hr : 0 ≤ r) (hrρ : r < ρ) (hρR : ENNReal.ofReal ρ < R) (n : ℤ) :
    circleLaurentCoeff (deriv f) c ρ n = ((n + 1 : ℤ) : ℂ) • circleLaurentCoeff f c ρ (n + 1) := by
  have hρ_pos : 0 < ρ := hr.trans_lt hrρ
  have hopen : IsOpen (eball c R \ closedBall c r) := isOpen_eball.sdiff isClosed_closedBall
  have hsphere : sphere c ρ ⊆ eball c R \ closedBall c r :=
    sphere_subset_eball_sdiff_closedBall hrρ hρR
  have hdf : DifferentiableOn ℂ (deriv f) (eball c R \ closedBall c r) := hf.deriv hopen
  exact circleLaurentCoeff_deriv_of_differentiableAt hρ_pos
    (fun z hz => (hf z (hsphere hz)).differentiableAt (hopen.mem_nhds (hsphere hz)))
    ((hdf.continuousOn.mono hsphere).circleIntegrable hρ_pos.le) n

/-- For `f` complex-differentiable on an open set `U` containing the circle `|z - c| = ρ`
(`0 < ρ`), the coefficient of degree `n - m` of the `m`-th derivative of `f` is the falling
factorial `n (n - 1) ⋯ (n - m + 1)` times the coefficient of degree `n` of `f`. -/
theorem circleLaurentCoeff_iteratedDeriv {f : ℂ → E} {c : ℂ} {ρ : ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hρ : 0 < ρ) (hsph : sphere c ρ ⊆ U) (m : ℕ)
    (n : ℤ) :
    circleLaurentCoeff (iteratedDeriv m f) c ρ (n - m) =
      (descPochhammer ℂ m).eval (n : ℂ) • circleLaurentCoeff f c ρ n := by
  induction m generalizing f n with
  | zero => simp
  | succ m ih =>
    have hdeg : n - ((m + 1 : ℕ) : ℤ) = (n - 1) - m := by omega
    have hdf : DifferentiableOn ℂ (deriv f) U := hf.deriv hU
    rw [iteratedDeriv_succ', hdeg, ih hdf, circleLaurentCoeff_deriv_of_differentiableAt hρ
        (fun z hz ↦ hf.differentiableAt (hU.mem_nhds (hsph hz)))
        ((hdf.continuousOn.mono hsph).circleIntegrable hρ.le),
      sub_add_cancel, smul_smul]
    -- What remains is the recurrence `n · (n - 1)_m = n_{m + 1}` for the falling factorial.
    congr 1
    simp [descPochhammer_succ_left, mul_comm]

end TauCeti
