/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import TauCeti.Analysis.Contour.Cauchy.Circle
import TauCeti.Topology.MetricSpace.EBall
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Circle Laurent coefficients and isolated-singularity subtraction

The circle integral defining a Laurent coefficient is independent of its positive radius
provided the function is continuous on the intervening closed annulus and complex
differentiable outside a countable exceptional set in its open interior.
Neither result assumes that the function extends across the center: isolated essential
singularities are allowed. When `f` is complex-differentiable on a circle with circle-integrable
derivative, integrating around the circle also expresses the Laurent coefficients of `deriv f` in
terms of those of `f` (`circleLaurentCoeff_deriv_of_differentiableAt`, `circleLaurentCoeff_deriv`).
For finitely many isolated singularities inside pairwise disjoint closed discs in the interior of
a region, subtracting the corresponding exterior Cauchy integrals extends continuously to the
region and holomorphically to its interior
(`exists_continuousOn_differentiableOn_sub_sum_circleIntegral`).

The construction uses Mathlib's Cauchy-Goursat theorem for annuli,
`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`, together with the
two-circle Cauchy formula and exterior Cauchy kernel lemmas from
`TauCeti.Analysis.Contour.Cauchy.Circle`.

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
  · simp only [circleLaurentCoeff_def, circleIntegral.integral_radius_zero]
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

/-- The singularity-removed gluing of
`f - ∑ ρ ∈ P, (2πi)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w`: inside each closed disc
`closedBall ρ r` (`ρ ∈ P`) it uses the interior Cauchy integral over `C(ρ, r')` minus the
exterior Cauchy integrals of the other singularities. -/
private noncomputable def gluedRegular (f : ℂ → E) (P : Finset ℂ) (r r' : ℝ) (z : ℂ) : E := by
  classical
  exact if h : ∃ ρ ∈ P, z ∈ closedBall ρ r then
    (2 * π * I : ℂ)⁻¹ • (∮ w in C(h.choose, r'), (w - z)⁻¹ • f w) -
      ∑ ρ' ∈ P.erase h.choose, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ', r), (z - w)⁻¹ • f w
  else
    f z - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w

omit [CompleteSpace E] in
/-- Outside all closed discs `closedBall ρ r`, `gluedRegular` agrees with
`f - ∑ ρ ∈ P, (2πi)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w`. -/
private theorem gluedRegular_eq_out {f : ℂ → E} {P : Finset ℂ} {r r' : ℝ} {z : ℂ}
    (hz : ∀ ρ ∈ P, z ∉ closedBall ρ r) :
    gluedRegular f P r r' z =
      f z - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w := by
  classical
  have hneg : ¬ ∃ ρ ∈ P, z ∈ closedBall ρ r := by push Not; exact hz
  simp only [gluedRegular, hneg, ↓reduceDIte]

/-- On each open ball `ball ρ r'` (`ρ ∈ P`), `gluedRegular` agrees with the holomorphic formula
`(2πi)⁻¹ • ∮ w in C(ρ, r'), (w - z)⁻¹ • f w -
  ∑ ρ' ∈ P.erase ρ, (2πi)⁻¹ • ∮ w in C(ρ', r), (z - w)⁻¹ • f w`. -/
private theorem gluedRegular_eq_on_ball {f : ℂ → E} {P : Finset ℂ} {U : Set ℂ}
    {r r' : ℝ} (hr : 0 < r) (hrr' : r < r') (hU : IsOpen U)
    (hP' : ∀ ρ ∈ P, closedBall ρ r' ⊆ U)
    (hdisj' : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r') (closedBall ρ' r'))
    (hd : DifferentiableOn ℂ f (U \ P)) {ρ : ℂ} (hρ : ρ ∈ P) :
    EqOn (gluedRegular f P r r')
      (fun z ↦ (2 * π * I : ℂ)⁻¹ • (∮ w in C(ρ, r'), (w - z)⁻¹ • f w) -
        ∑ ρ' ∈ P.erase ρ, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ', r), (z - w)⁻¹ • f w)
      (ball ρ r') := by
  classical
  intro z hz
  have hr' : 0 < r' := hr.trans hrr'
  have hsub_ann : closedBall ρ r' \ {ρ} ⊆ U \ P := fun w hw ↦
    ⟨hP' ρ hρ hw.1, fun hwP ↦ hw.2 <| by_contra fun hne ↦
      disjoint_left.1 (hdisj' hρ hwP (Ne.symm hne)) hw.1 (mem_closedBall_self hr'.le)⟩
  by_cases hzr : z ∈ closedBall ρ r
  · have hex : ∃ ρ' ∈ P, z ∈ closedBall ρ' r := ⟨ρ, hρ, hzr⟩
    have hch : hex.choose = ρ := by_contra fun hne ↦
      disjoint_left.1 (hdisj' hex.choose_spec.1 hρ hne)
        (closedBall_subset_closedBall hrr'.le hex.choose_spec.2)
        (closedBall_subset_closedBall hrr'.le hzr)
    simp only [gluedRegular, hex, ↓reduceDIte, hch]
  · have hnone : ∀ ρ' ∈ P, z ∉ closedBall ρ' r := fun ρ' hρ' hz' ↦ by
      rcases eq_or_ne ρ' ρ with rfl | hne
      · exact hzr hz'
      · exact disjoint_left.1 (hdisj' hρ hρ' hne.symm) (ball_subset_closedBall hz)
          (closedBall_subset_closedBall hrr'.le hz')
    have hsub := Contour.sub_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_eq hr countable_empty
      ⟨hz, hzr⟩
      (hd.continuousOn.mono fun w hw ↦
        hsub_ann ⟨hw.1, fun heq ↦ hw.2 (heq ▸ mem_ball_self hr)⟩)
      (fun w hw ↦ hd.differentiableAt ((hU.sdiff P.finite_toSet.isClosed).mem_nhds
        (hsub_ann ⟨ball_subset_closedBall hw.1.1,
          fun heq ↦ hw.1.2 (heq ▸ mem_closedBall_self hr.le)⟩)))
    rw [gluedRegular_eq_out hnone, ← Finset.add_sum_erase _ _ hρ, ← sub_sub, hsub]

/-- `gluedRegular` is complex differentiable at every point of each open ball `ball ρ r'`. -/
private theorem differentiableAt_gluedRegular_of_mem_ball {f : ℂ → E}
    {P : Finset ℂ} {U : Set ℂ} {r r' : ℝ} (hr : 0 < r) (hrr' : r < r') (hU : IsOpen U)
    (hP' : ∀ ρ ∈ P, closedBall ρ r' ⊆ U)
    (hdisj' : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r') (closedBall ρ' r'))
    (hd : DifferentiableOn ℂ f (U \ P)) {ρ z : ℂ} (hρ : ρ ∈ P) (hz : z ∈ ball ρ r') :
    DifferentiableAt ℂ (gluedRegular f P r r') z := by
  classical
  have hr' : 0 < r' := hr.trans hrr'
  have hcont_r' := continuousOn_sphere_of_closedBall_subset hr' le_rfl hP' hdisj' hd.continuousOn hρ
  have hz' : z ∉ sphere ρ |r'| := by
    rw [abs_of_pos hr', mem_sphere]; exact ne_of_lt (mem_ball.1 hz)
  have hint : DifferentiableAt ℂ (fun s ↦ (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r'), (w - s)⁻¹ • f w)
      z := (hasDerivAt_circleIntegral_sub_inv_smul
        (hcont_r'.circleIntegrable hr'.le) hz').differentiableAt.const_smul _
  have hsum : DifferentiableAt ℂ
      (fun s ↦ ∑ ρ' ∈ P.erase ρ, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ', r), (s - w)⁻¹ • f w) z := by
    refine DifferentiableAt.fun_sum fun ρ' hρ' ↦ ?_
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hρ'
    have hcont_r :=
      continuousOn_sphere_of_closedBall_subset hr hrr'.le hP' hdisj' hd.continuousOn hmem
    refine Contour.differentiableAt_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_left
      (hcont_r.circleIntegrable hr.le) fun hsp ↦ ?_
    rw [abs_of_pos hr] at hsp
    exact disjoint_left.1 (hdisj' hρ hmem hne.symm) (ball_subset_closedBall hz)
      (closedBall_subset_closedBall hrr'.le (sphere_subset_closedBall hsp))
  exact (hint.sub hsum).congr_of_eventuallyEq <|
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)
      (gluedRegular_eq_on_ball hr hrr' hU hP' hdisj' hd hρ)

/-- `gluedRegular` is continuous on `D`. -/
private theorem continuousOn_gluedRegular {D : Set ℂ} {r r' : ℝ} (hr : 0 < r)
    (hrr' : r < r') {P : Finset ℂ}
    (hP' : ∀ ρ ∈ P, closedBall ρ r' ⊆ interior D)
    (hdisj' : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r') (closedBall ρ' r'))
    {f : ℂ → E} (hc : ContinuousOn f (D \ P))
    (hd : DifferentiableOn ℂ f (interior D \ P)) :
    ContinuousOn (gluedRegular f P r r') D := by
  have hopen_out : IsOpen (⋃ ρ ∈ P, closedBall ρ r)ᶜ :=
    (P.finite_toSet.isClosed_biUnion fun _ _ ↦ isClosed_closedBall).isOpen_compl
  intro z hz
  by_cases hex : ∃ ρ ∈ P, z ∈ closedBall ρ r
  · obtain ⟨ρ, hρ, hzr⟩ := hex
    exact (differentiableAt_gluedRegular_of_mem_ball hr hrr' isOpen_interior hP' hdisj' hd hρ
      (closedBall_subset_ball hrr' hzr)).continuousAt.continuousWithinAt
  · push Not at hex
    have hmem : z ∈ (⋃ ρ ∈ P, closedBall ρ r)ᶜ := by simpa using hex
    have hsub : D ∩ (⋃ ρ ∈ P, closedBall ρ r)ᶜ ⊆ D \ P := fun w hw ↦
      ⟨hw.1, fun hwP ↦ by
        have := hw.2; simp only [mem_compl_iff, mem_iUnion] at this
        exact this ⟨w, hwP, mem_closedBall_self hr.le⟩⟩
    have hsum_diff : DifferentiableAt ℂ
        (fun s ↦ ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (s - w)⁻¹ • f w) z :=
      DifferentiableAt.fun_sum fun ρ hρ ↦
        Contour.differentiableAt_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_left
          ((continuousOn_sphere_of_closedBall_subset hr hrr'.le hP' hdisj' hd.continuousOn hρ
            ).circleIntegrable hr.le)
          fun hsp ↦ hex ρ hρ (sphere_subset_closedBall (abs_of_pos hr ▸ hsp))
    have hloc : ContinuousWithinAt
        (fun s ↦ f s - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (s - w)⁻¹ • f w) D z :=
      (hc.continuousWithinAt (hsub ⟨hz, hmem⟩) |>.mono_of_mem_nhdsWithin
        (mem_of_superset (inter_mem_nhdsWithin D (hopen_out.mem_nhds hmem)) hsub)).sub
        hsum_diff.continuousAt.continuousWithinAt
    exact hloc.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (nhdsWithin_le_nhds (hopen_out.mem_nhds hmem)) fun w hw ↦ by
        simp only [mem_compl_iff, mem_iUnion, not_exists] at hw
        exact gluedRegular_eq_out hw)
      (gluedRegular_eq_out hex)

/-- `gluedRegular` is complex differentiable on `interior D`. -/
private theorem differentiableOn_gluedRegular {D : Set ℂ} {r r' : ℝ}
    (hr : 0 < r) (hrr' : r < r') {P : Finset ℂ}
    (hP' : ∀ ρ ∈ P, closedBall ρ r' ⊆ interior D)
    (hdisj' : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r') (closedBall ρ' r'))
    {f : ℂ → E} (hd : DifferentiableOn ℂ f (interior D \ P)) :
    DifferentiableOn ℂ (gluedRegular f P r r') (interior D) := by
  have hopen_out : IsOpen (⋃ ρ ∈ P, closedBall ρ r)ᶜ :=
    (P.finite_toSet.isClosed_biUnion fun _ _ ↦ isClosed_closedBall).isOpen_compl
  intro z hz
  by_cases hex : ∃ ρ ∈ P, z ∈ closedBall ρ r
  · obtain ⟨ρ, hρ, hzr⟩ := hex
    exact (differentiableAt_gluedRegular_of_mem_ball hr hrr' isOpen_interior hP' hdisj' hd hρ
      (closedBall_subset_ball hrr' hzr)).differentiableWithinAt
  · push Not at hex
    have hmem : z ∈ (⋃ ρ ∈ P, closedBall ρ r)ᶜ := by simpa using hex
    have hloc : DifferentiableAt ℂ
        (fun s ↦ f s - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (s - w)⁻¹ • f w) z :=
      (hd.differentiableAt ((isOpen_interior.sdiff P.finite_toSet.isClosed).mem_nhds
        ⟨hz, fun hzP ↦ hex z hzP (mem_closedBall_self hr.le)⟩)).sub
        (DifferentiableAt.fun_sum fun ρ hρ ↦
          Contour.differentiableAt_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_left
            ((continuousOn_sphere_of_closedBall_subset hr hrr'.le hP' hdisj' hd.continuousOn hρ
              ).circleIntegrable hr.le)
            fun hsp ↦ hex ρ hρ (sphere_subset_closedBall (abs_of_pos hr ▸ hsp)))
    exact (hloc.congr_of_eventuallyEq <|
      Filter.eventuallyEq_of_mem (hopen_out.mem_nhds hmem) fun w hw ↦ by
        simp only [mem_compl_iff, mem_iUnion, not_exists] at hw
        exact gluedRegular_eq_out hw).differentiableWithinAt

/-- **Finite-disc singularity removal.** Let `D : Set ℂ`, `r > 0`, and `P` a finite set whose
closed discs `closedBall ρ r` are pairwise disjoint and contained in `interior D`. If `f : ℂ → E`
is continuous on `D \ P` and complex differentiable on `interior D \ P`, then subtracting the
exterior Cauchy integrals `(2πi)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w` (`ρ ∈ P`) extends to a
function continuous on `D` and complex differentiable on `interior D` that agrees with
`f z - ∑ ρ ∈ P, (2πi)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w` outside `⋃ ρ ∈ P, closedBall ρ r`.

No open neighbourhood of `D` and no meromorphy at `P` are assumed, so points of `P` may be
essential singularities. -/
theorem exists_continuousOn_differentiableOn_sub_sum_circleIntegral {D : Set ℂ} {r : ℝ}
    (hr : 0 < r) {P : Finset ℂ} (hP : ∀ ρ ∈ P, closedBall ρ r ⊆ interior D)
    (hdisj : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r) (closedBall ρ' r))
    {f : ℂ → E} (hc : ContinuousOn f (D \ P)) (hd : DifferentiableOn ℂ f (interior D \ P)) :
    ∃ g : ℂ → E, ContinuousOn g D ∧ DifferentiableOn ℂ g (interior D) ∧
      EqOn g (fun z ↦ f z - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w)
        (⋃ ρ ∈ P, closedBall ρ r)ᶜ := by
  obtain ⟨r', hrr', hP', hdisj'⟩ := TauCeti.exists_gt_closedBall_subset_and_pairwiseDisjoint
    (U := fun _ ↦ interior D) (fun _ _ ↦ isOpen_interior) hP hdisj
  refine ⟨gluedRegular f P r r',
    continuousOn_gluedRegular hr hrr' hP' hdisj' hc hd,
    differentiableOn_gluedRegular hr hrr' hP' hdisj' hd,
    fun z hz ↦ ?_⟩
  simp only [mem_compl_iff, mem_iUnion, not_exists] at hz
  exact gluedRegular_eq_out hz

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

end TauCeti
