/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.MeasureTheory.Integral.NormRpow
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Asymptotics.Lemmas
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The Cauchy transform at infinity

Let `f : ℂ → F` be integrable and supported in the closed disc `closedBall c r`, and write
`M = π⁻¹ ∫ f` for its normalized mass. Outside the disc the Cauchy transform
`T f w = π⁻¹ ∫ (w - z)⁻¹ • f z` is holomorphic (indeed it is holomorphic off the closed support of
any integrable `f`, by `TauCeti.hasDerivAt_cauchyTransform_of_notMem_tsupport`), and it is the
reciprocal tail `M / (w - c)` up to an error of order `‖w‖⁻²`:

* `‖T f w - (w - c)⁻¹ • M‖ ≤ 2 π⁻¹ r ‖f‖₁ / ‖w - c‖²` for `2 r < ‖w - c‖`;
* `‖(T f)' w + ((w - c)²)⁻¹ • M‖ ≤ 6 π⁻¹ r ‖f‖₁ / ‖w - c‖³` for `2 r < ‖w - c‖`.

In particular `T f → 0` at infinity (`HasCompactSupport.tendsto_cauchyTransform_cobounded`),
while for nonzero mass `T f` belongs to no `Lᵖ`, `0 < p ≤ 2`, on the complement of any disc, in
particular not to `Lᵖ(ℂ)`. In contrast its derivative is in `Lᵖ` of the complement of every
disc `ball c R` with `r < R`, for every `1 < p < ∞`. This is why the global `Lᵖ` estimate for the
Cauchy transform concerns only its derivative.

The explicit disc indicator computations of `Pompeiu.Disc.Basic` and `Pompeiu.Disc.Lp` are
instances: there `M = r²` and the remainder vanishes identically outside the disc.

## Main results

* `TauCeti.cauchyTransform_sub_inv_smul_isBigO`: `T f w - (w - c)⁻¹ • M = O(w⁻²)` at infinity.
* `TauCeti.deriv_cauchyTransform_add_inv_sq_smul_isBigO`:
  `(T f)' w + ((w - c)²)⁻¹ • M = O(w⁻³)` at infinity.
* `TauCeti.not_memLp_cauchyTransform_compl_closedBall` and `TauCeti.not_memLp_cauchyTransform`:
  for `∫ f ≠ 0` and `0 < p ≤ 2`, `T f ∉ Lᵖ`.
* `TauCeti.memLp_deriv_cauchyTransform_compl_ball` and
  `TauCeti.memLp_wirtingerDeriv_cauchyTransform_compl_ball`: `∂ (T f) ∈ Lᵖ((ball c R)ᶜ)` for
  `r < R` and `1 < p < ∞`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.2.
-/

public section

open MeasureTheory Complex Set Filter Metric Asymptotics Function Bornology
open scoped NNReal ENNReal Real Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F} {c w : ℂ} {r : ℝ≥0}

/-- Outside the disc the Cauchy transform minus its reciprocal tail is the transform against the
difference of kernels `(w - z)⁻¹ - (w - c)⁻¹`. -/
theorem cauchyTransform_sub_inv_smul_eq (hf : Integrable f) (hsupp : support f ⊆ closedBall c r)
    (hw : (r : ℝ) < ‖w - c‖) :
    cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z) =
      (Real.pi : ℂ)⁻¹ • ∫ z, ((w - z)⁻¹ - (w - c)⁻¹) • f z := by
  have hint : Integrable fun z ↦ (w - z)⁻¹ • f z :=
    hf.smul_of_support_subset hsupp (by fun_prop) fun z hz ↦
      norm_inv_sub_le_of_mem_closedBall hz hw
  simp_rw [sub_smul]
  rw [integral_sub hint (hf.smul (w - c)⁻¹ : Integrable fun z ↦ (w - c)⁻¹ • f z),
    integral_smul, cauchyTransform_apply, smul_sub,
    smul_comm (w - c)⁻¹]

/-- **The reciprocal tail of the Cauchy transform**, with the exact kernel constant. -/
theorem norm_cauchyTransform_sub_inv_smul_le (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hw : (r : ℝ) < ‖w - c‖) :
    ‖cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)‖ ≤
      π⁻¹ * (r / ((‖w - c‖ - r) * ‖w - c‖) * ∫ z, ‖f z‖) := by
  rw [cauchyTransform_sub_inv_smul_eq hf hsupp hw, norm_pi_inv_smul]
  gcongr
  exact norm_integral_smul_le_of_support_subset hf hsupp fun z hz ↦
    norm_inv_sub_sub_inv_sub_le_of_mem_closedBall hz hw

/-- The reciprocal tail of the Cauchy transform beyond twice the support radius:
`‖T f w - (w - c)⁻¹ • M‖ ≤ 2 π⁻¹ r ‖f‖₁ / ‖w - c‖²`. -/
theorem norm_cauchyTransform_sub_inv_smul_le_of_two_mul_lt (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hw : 2 * (r : ℝ) < ‖w - c‖) :
    ‖cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)‖ ≤
      2 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 2 := by
  have hw' : (r : ℝ) < ‖w - c‖ := by linarith [r.coe_nonneg]
  refine (norm_cauchyTransform_sub_inv_smul_le hf hsupp hw').trans ?_
  have hk := div_sub_mul_le_two_mul_div_sq r.coe_nonneg hw
  calc π⁻¹ * (r / ((‖w - c‖ - r) * ‖w - c‖) * ∫ z, ‖f z‖)
      ≤ π⁻¹ * (2 * r / ‖w - c‖ ^ 2 * ∫ z, ‖f z‖) := by gcongr
    _ = 2 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 2 := by ring

/-- **A lower bound for the Cauchy transform at infinity.** Far enough from the disc, the
reciprocal tail dominates the remainder: `‖M‖ / (2 ‖w - c‖) ≤ ‖T f w‖`. -/
theorem div_le_norm_cauchyTransform_of_two_mul_lt (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hw : 2 * (r : ℝ) < ‖w - c‖)
    (hwM : 4 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖(Real.pi : ℂ)⁻¹ • ∫ z, f z‖ < ‖w - c‖) :
    ‖(Real.pi : ℂ)⁻¹ • ∫ z, f z‖ / 2 / ‖w - c‖ ≤ ‖cauchyTransform f w‖ := by
  set M : F := (Real.pi : ℂ)⁻¹ • ∫ z, f z
  have hρ0 : 0 < ‖w - c‖ := by linarith [r.coe_nonneg]
  rcases (norm_nonneg M).eq_or_lt with hM0 | hM0
  · rw [← hM0, zero_div, zero_div]
    exact norm_nonneg _
  have hrem := norm_cauchyTransform_sub_inv_smul_le_of_two_mul_lt hf hsupp hw
  have htri := norm_sub_norm_le ((w - c)⁻¹ • M) (cauchyTransform f w)
  rw [norm_sub_rev, norm_smul, norm_inv] at htri
  have hB : 2 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 2 ≤ ‖M‖ / 2 / ‖w - c‖ := by
    rw [div_lt_iff₀ hM0] at hwM
    rw [div_le_div_iff₀ (by positivity) hρ0]
    nlinarith
  have hsplit : ‖w - c‖⁻¹ * ‖M‖ = ‖M‖ / 2 / ‖w - c‖ + ‖M‖ / 2 / ‖w - c‖ := by
    field_simp; ring
  linarith

/-- **The Cauchy transform at infinity.** For integrable data supported in `closedBall c r`,
`T f w = (w - c)⁻¹ • π⁻¹ ∫ f + O(‖w‖⁻²)` along `cobounded ℂ`. -/
theorem cauchyTransform_sub_inv_smul_isBigO (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) :
    (fun w ↦ cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)) =O[cobounded ℂ]
      fun w : ℂ ↦ w⁻¹ ^ 2 :=
  isBigO_inv_pow_cobounded_of_norm_le (R := 2 * r) 2 fun _ hw ↦
    norm_cauchyTransform_sub_inv_smul_le_of_two_mul_lt hf hsupp hw

/-- A pointwise bound for the derivative off the disc:
`‖(T f)' w‖ ≤ π⁻¹ ‖f‖₁ / (‖w - c‖ - r)²`. -/
theorem norm_deriv_cauchyTransform_le (hf : Integrable f) (hsupp : support f ⊆ closedBall c r)
    (hw : (r : ℝ) < ‖w - c‖) :
    ‖deriv (cauchyTransform f) w‖ ≤ π⁻¹ * (((‖w - c‖ - r) ^ 2)⁻¹ * ∫ z, ‖f z‖) := by
  have hw' := notMem_tsupport_of_support_subset_closedBall hsupp (by rwa [dist_eq_norm])
  rw [(hasDerivAt_cauchyTransform_of_notMem_tsupport hf hw').deriv, norm_neg, norm_pi_inv_smul]
  gcongr
  exact norm_integral_smul_le_of_support_subset hf hsupp fun z hz ↦
    norm_inv_sub_pow_le_of_mem_closedBall hz hw 2

/-- The derivative of the Cauchy transform at infinity, with the exact kernel constant. -/
theorem norm_deriv_cauchyTransform_add_inv_sq_smul_le (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hw : (r : ℝ) < ‖w - c‖) :
    ‖deriv (cauchyTransform f) w + ((w - c) ^ 2)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)‖ ≤
      π⁻¹ * (r / ((‖w - c‖ - r) * ‖w - c‖) * ((‖w - c‖ - r)⁻¹ + ‖w - c‖⁻¹) *
        ∫ z, ‖f z‖) := by
  have hw' := notMem_tsupport_of_support_subset_closedBall hsupp (by rwa [dist_eq_norm])
  have hint : Integrable fun z ↦ ((w - z) ^ 2)⁻¹ • f z :=
    hf.smul_of_support_subset hsupp (by fun_prop) fun z hz ↦
      norm_inv_sub_pow_le_of_mem_closedBall hz hw 2
  have heq : deriv (cauchyTransform f) w + ((w - c) ^ 2)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z) =
      -((Real.pi : ℂ)⁻¹ • ∫ z, (((w - z) ^ 2)⁻¹ - ((w - c) ^ 2)⁻¹) • f z) := by
    simp_rw [sub_smul]
    rw [(hasDerivAt_cauchyTransform_of_notMem_tsupport hf hw').deriv,
      integral_sub hint (hf.smul ((w - c) ^ 2)⁻¹ : Integrable fun z ↦ ((w - c) ^ 2)⁻¹ • f z),
      integral_smul, smul_sub, smul_comm ((w - c) ^ 2)⁻¹]
    abel
  rw [heq, norm_neg, norm_pi_inv_smul]
  gcongr
  refine norm_integral_smul_le_of_support_subset hf hsupp fun z hz ↦ ?_
  rw [← inv_pow, ← inv_pow, sq_sub_sq, norm_mul, mul_comm]
  refine mul_le_mul (norm_inv_sub_sub_inv_sub_le_of_mem_closedBall hz hw)
    ((norm_add_le _ _).trans
      (add_le_add (norm_inv_sub_le_of_mem_closedBall hz hw) (by rw [norm_inv])))
    (norm_nonneg _) (by have := sub_pos.mpr hw; have := r.coe_nonneg; positivity)

/-- The derivative of the Cauchy transform beyond twice the support radius:
`‖(T f)' w + ((w - c)²)⁻¹ • M‖ ≤ 6 π⁻¹ r ‖f‖₁ / ‖w - c‖³`. -/
theorem norm_deriv_cauchyTransform_add_inv_sq_smul_le_of_two_mul_lt (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hw : 2 * (r : ℝ) < ‖w - c‖) :
    ‖deriv (cauchyTransform f) w + ((w - c) ^ 2)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)‖ ≤
      6 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 3 := by
  have hr := r.coe_nonneg
  have hρ : 0 < ‖w - c‖ := by linarith
  have hδ0 : 0 < ‖w - c‖ - r := by linarith
  refine (norm_deriv_cauchyTransform_add_inv_sq_smul_le hf hsupp (by linarith)).trans ?_
  have hk : (r : ℝ) / ((‖w - c‖ - r) * ‖w - c‖) * ((‖w - c‖ - r)⁻¹ + ‖w - c‖⁻¹) ≤
      6 * r / ‖w - c‖ ^ 3 := by
    have h1 := div_sub_mul_le_two_mul_div_sq r.coe_nonneg hw
    have h2 : (‖w - c‖ - r)⁻¹ + ‖w - c‖⁻¹ ≤ 3 / ‖w - c‖ := by
      have := inv_sub_le_two_div hρ hw
      have h3 : (3 : ℝ) / ‖w - c‖ = 2 / ‖w - c‖ + ‖w - c‖⁻¹ := by ring
      linarith
    calc (r : ℝ) / ((‖w - c‖ - r) * ‖w - c‖) * ((‖w - c‖ - r)⁻¹ + ‖w - c‖⁻¹)
        ≤ 2 * r / ‖w - c‖ ^ 2 * (3 / ‖w - c‖) := by gcongr
      _ = 6 * r / ‖w - c‖ ^ 3 := by field_simp; ring
  calc π⁻¹ * ((r : ℝ) / ((‖w - c‖ - r) * ‖w - c‖) * ((‖w - c‖ - r)⁻¹ + ‖w - c‖⁻¹) *
        ∫ z, ‖f z‖)
      ≤ π⁻¹ * (6 * r / ‖w - c‖ ^ 3 * ∫ z, ‖f z‖) := by gcongr
    _ = 6 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 3 := by ring

/-- **The derivative of the Cauchy transform at infinity.** For integrable data supported in
`closedBall c r`, `(T f)' w = -((w - c)²)⁻¹ • π⁻¹ ∫ f + O(‖w‖⁻³)` along `cobounded ℂ`. -/
theorem deriv_cauchyTransform_add_inv_sq_smul_isBigO (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) :
    (fun w ↦ deriv (cauchyTransform f) w + ((w - c) ^ 2)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z))
      =O[cobounded ℂ] fun w : ℂ ↦ w⁻¹ ^ 3 :=
  isBigO_inv_pow_cobounded_of_norm_le (R := 2 * r) 3 fun _ hw ↦
    norm_deriv_cauchyTransform_add_inv_sq_smul_le_of_two_mul_lt hf hsupp hw

section Lp

/-- **The Cauchy transform is not `Lᵖ` at infinity for `p ≤ 2`.** If `∫ f ≠ 0`, then on the
complement of every disc `closedBall c R` the transform belongs to no `Lᵖ` with `0 < p ≤ 2`:
outside a sufficiently large disc it is bounded below by a multiple of `‖w - c‖⁻¹`. -/
theorem not_memLp_cauchyTransform_compl_closedBall (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hf0 : ∫ z, f z ≠ 0) (R : ℝ) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp_top : p ≠ ∞) (hp : p.toReal ≤ 2) :
    ¬ MemLp (cauchyTransform f) p (volume.restrict (closedBall c R)ᶜ) := by
  set M : F := (Real.pi : ℂ)⁻¹ • ∫ z, f z
  have hM0 : 0 < ‖M‖ := norm_pos_iff.mpr
    (smul_ne_zero (inv_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) hf0)
  set R₁ : ℝ := max (max R 1) (max (2 * r) (4 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖M‖))
  have hR₁ : 0 < R₁ := lt_of_lt_of_le one_pos ((le_max_right R 1).trans (le_max_left _ _))
  intro hmem
  have hsub : (closedBall c R₁)ᶜ ⊆ (closedBall c R)ᶜ :=
    compl_subset_compl.mpr (closedBall_subset_closedBall
      ((le_max_left R 1).trans (le_max_left _ _)))
  have hmem₁ := hmem.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hlow : MemLp (fun w : ℂ ↦ ((‖M‖ / 2 : ℝ) : ℂ) / (w - c) ^ 1) p
      (volume.restrict (closedBall c R₁)ᶜ) := by
    refine hmem₁.of_le
      (by fun_prop : Measurable fun w : ℂ ↦ ((‖M‖ / 2 : ℝ) : ℂ) / (w - c) ^ 1).aestronglyMeasurable
      ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with w hw
    have hρ : R₁ < ‖w - c‖ := by simpa [mem_closedBall, dist_eq_norm] using hw
    rw [pow_one, norm_div, norm_real, Real.norm_of_nonneg (by positivity)]
    exact div_le_norm_cauchyTransform_of_two_mul_lt hf hsupp
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hρ)
      (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hρ)
  rw [memLp_div_sub_pow_compl_closedBall_iff (ofReal_ne_zero.mpr (by positivity)) c hR₁ 1
    hp0 hp_top] at hlow
  push_cast at hlow
  linarith

/-- If `∫ f ≠ 0` then the Cauchy transform is not in `Lᵖ(ℂ)` for `0 < p ≤ 2`. -/
theorem not_memLp_cauchyTransform (hf : Integrable f) (hsupp : support f ⊆ closedBall c r)
    (hf0 : ∫ z, f z ≠ 0) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞) (hp : p.toReal ≤ 2) :
    ¬ MemLp (cauchyTransform f) p volume := fun h ↦
  not_memLp_cauchyTransform_compl_closedBall hf hsupp hf0 0 hp0 hp_top hp (h.restrict _)

/-- **The derivative of the Cauchy transform is `Lᵖ` at infinity for `p > 1`.** On the
complement of every disc `ball c R` with `r < R`, the derivative is bounded by a multiple of
`‖w - c‖⁻²`, so it belongs to every `Lᵖ` with `1 < p < ∞`. -/
theorem memLp_deriv_cauchyTransform_compl_ball [CompleteSpace F] (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) {R : ℝ} (hR : r < R) {p : ℝ≥0∞} (hp : 1 < p.toReal) :
    MemLp (deriv (cauchyTransform f)) p (volume.restrict (ball c R)ᶜ) := by
  have hp0 : p ≠ 0 := by rintro rfl; norm_num at hp
  have hp_top : p ≠ ∞ := by rintro rfl; norm_num at hp
  set R' : ℝ := (r + R) / 2
  have hrR' : (r : ℝ) < R' := by simp only [R']; linarith
  have hR' : 0 < R' := lt_of_le_of_lt r.coe_nonneg hrR'
  have hq : 0 < 1 - r / R' := by rw [sub_pos, div_lt_one hR']; exact hrR'
  set K : ℝ := π⁻¹ * (((1 - r / R') ^ 2)⁻¹ * ∫ z, ‖f z‖) + 1
  have hK : 0 < K := by
    have : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg fun z ↦ norm_nonneg (f z)
    positivity
  have hdom : MemLp (fun w : ℂ ↦ (K : ℂ) / (w - c) ^ 2) p
      (volume.restrict (closedBall c R')ᶜ) :=
    (memLp_div_sub_pow_compl_closedBall_iff (ofReal_ne_zero.mpr hK.ne') c hR' 2 hp0
      hp_top).mpr (by push_cast; linarith)
  have hsub : (ball c R)ᶜ ⊆ (closedBall c R')ᶜ :=
    compl_subset_compl.mpr (closedBall_subset_ball (by simp only [R']; linarith))
  refine (hdom.of_le (aestronglyMeasurable_deriv _ _) ?_).mono_measure
    (Measure.restrict_mono hsub le_rfl)
  filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with w hw
  have hρ : R' < ‖w - c‖ := by simpa [mem_closedBall, dist_eq_norm] using hw
  have hρ0 : 0 < ‖w - c‖ := hR'.trans hρ
  have hrρ : (r : ℝ) < ‖w - c‖ := hrR'.trans hρ
  refine (norm_deriv_cauchyTransform_le hf hsupp hrρ).trans ?_
  rw [norm_div, norm_pow, norm_real, Real.norm_of_nonneg hK.le]
  -- `‖w - c‖ - r ≥ (1 - r / R') ‖w - c‖`.
  have hlin : (1 - r / R') * ‖w - c‖ ≤ ‖w - c‖ - r := by
    have : r / R' * ‖w - c‖ ≥ r := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hR']
      exact mul_le_mul_of_nonneg_left hρ.le r.coe_nonneg
    linarith
  have hpos : 0 < (1 - r / R') * ‖w - c‖ := mul_pos hq hρ0
  have hsq : ((‖w - c‖ - r) ^ 2)⁻¹ ≤ ((1 - r / R') ^ 2)⁻¹ / ‖w - c‖ ^ 2 :=
    calc ((‖w - c‖ - r) ^ 2)⁻¹ ≤ (((1 - r / R') * ‖w - c‖) ^ 2)⁻¹ :=
          inv_anti₀ (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hlin 2)
      _ = ((1 - r / R') ^ 2)⁻¹ / ‖w - c‖ ^ 2 := by rw [mul_pow, mul_inv, ← div_eq_mul_inv]
  calc π⁻¹ * (((‖w - c‖ - r) ^ 2)⁻¹ * ∫ z, ‖f z‖)
      ≤ π⁻¹ * (((1 - r / R') ^ 2)⁻¹ / ‖w - c‖ ^ 2 * ∫ z, ‖f z‖) := by gcongr
    _ = (K - 1) / ‖w - c‖ ^ 2 := by simp only [K]; ring
    _ ≤ K / ‖w - c‖ ^ 2 := by gcongr; linarith

/-- The holomorphic Wirtinger derivative `∂ (T f)` is `Lᵖ` on the complement of every disc
`ball c R` with `r < R`, for every `1 < p < ∞`. -/
theorem memLp_wirtingerDeriv_cauchyTransform_compl_ball [CompleteSpace F] (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) {R : ℝ} (hR : r < R) {p : ℝ≥0∞} (hp : 1 < p.toReal) :
    MemLp (fun w ↦ wirtingerDeriv (cauchyTransform f) w 1) p (volume.restrict (ball c R)ᶜ) := by
  refine (memLp_congr_ae ?_).mpr (memLp_deriv_cauchyTransform_compl_ball hf hsupp hR hp)
  filter_upwards [ae_restrict_mem measurableSet_ball.compl] with w hw
  have hRw : R ≤ dist w c := by simpa [mem_ball] using hw
  exact wirtingerDeriv_cauchyTransform_apply_one_of_notMem_tsupport hf
    (notMem_tsupport_of_support_subset_closedBall hsupp (hR.trans_le hRw))

end Lp

end TauCeti
