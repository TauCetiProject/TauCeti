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
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Bornology.BoundedOperation

/-!
# The Cauchy transform at infinity

Let `f : ℂ → F` be integrable and supported in the closed disc `closedBall c r`, and write
`M = π⁻¹ ∫ f` for its normalized mass. Outside the disc the Cauchy transform
`T f w = π⁻¹ ∫ (w - z)⁻¹ • f z` is holomorphic, and it is the reciprocal tail `M / (w - c)` up
to an error of order `‖w‖⁻²`:

* `‖T f w - (w - c)⁻¹ • M‖ ≤ 2 π⁻¹ r ‖f‖₁ / ‖w - c‖²` for `2 r < ‖w - c‖`;
* `‖(T f)' w + ((w - c)²)⁻¹ • M‖ ≤ 6 π⁻¹ r ‖f‖₁ / ‖w - c‖³` for `2 r < ‖w - c‖`.

Consequently `T f → 0` at infinity, while for nonzero mass `T f` belongs to no `Lᵖ`, `0 < p ≤ 2`,
on the complement of any disc, in particular not to `Lᵖ(ℂ)`. In contrast its derivative is in
`Lᵖ` of the complement of every disc `ball c R` with `r < R`, for every `1 < p < ∞`. This is why
the global `Lᵖ` estimate for the Cauchy transform concerns only its derivative.

The explicit disc indicator computations of `Pompeiu.Disc.Basic` and `Pompeiu.Disc.Lp` are
instances: there `M = r²` and the remainder vanishes identically outside the disc.

## Main results

* `TauCeti.cauchyTransform_sub_inv_smul_isBigO`: `T f w - (w - c)⁻¹ • M = O(w⁻²)` at infinity.
* `TauCeti.tendsto_cauchyTransform_cobounded`: `T f → 0` at infinity.
* `TauCeti.hasDerivAt_cauchyTransform_of_lt` and
  `TauCeti.differentiableOn_cauchyTransform_compl_closedBall`: holomorphy off the disc.
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

section Pointwise

/-- A point of the closed disc is at distance at least `‖w - c‖ - r` from `w`. -/
private lemma sub_le_norm_sub {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖w - c‖ - r ≤ ‖w - z‖ := by
  have := norm_sub_le_norm_sub_add_norm_sub w z c
  have := mem_closedBall_iff_norm.mp hz
  linarith

private lemma norm_inv_sub_le {z : ℂ} (hz : z ∈ closedBall c r) (hw : (r : ℝ) < ‖w - c‖) :
    ‖(w - z)⁻¹‖ ≤ (‖w - c‖ - r)⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ (sub_pos.mpr hw) (sub_le_norm_sub hz)

private lemma norm_inv_sub_sub_inv_sub_le {z : ℂ} (hz : z ∈ closedBall c r)
    (hw : (r : ℝ) < ‖w - c‖) :
    ‖(w - z)⁻¹ - (w - c)⁻¹‖ ≤ r / ((‖w - c‖ - r) * ‖w - c‖) := by
  have hρ : 0 < ‖w - c‖ := lt_of_le_of_lt r.coe_nonneg hw
  have hδ : 0 < ‖w - c‖ - r := sub_pos.mpr hw
  have hwz : 0 < ‖w - z‖ := hδ.trans_le (sub_le_norm_sub hz)
  rw [inv_sub_inv (norm_pos_iff.mp hwz) (norm_pos_iff.mp hρ), sub_sub_sub_cancel_left,
    norm_div, norm_mul]
  exact div_le_div₀ r.coe_nonneg (mem_closedBall_iff_norm.mp hz) (mul_pos hδ hρ)
    (mul_le_mul_of_nonneg_right (sub_le_norm_sub hz) hρ.le)

/-- A kernel bounded by `K` on the disc gives an integrand dominated by `K • ‖f‖`. -/
private lemma norm_smul_le_of_support (hsupp : support f ⊆ closedBall c r) {g : ℂ → ℂ} {K : ℝ}
    (hK : ∀ z ∈ closedBall c r, ‖g z‖ ≤ K) (z : ℂ) : ‖g z • f z‖ ≤ K * ‖f z‖ := by
  by_cases hz : f z = 0
  · simp [hz]
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hK z (hsupp hz)) (norm_nonneg _)

private lemma integrable_smul_of_support (hf : Integrable f) (hsupp : support f ⊆ closedBall c r)
    {g : ℂ → ℂ} (hg : Measurable g) {K : ℝ} (hK : ∀ z ∈ closedBall c r, ‖g z‖ ≤ K) :
    Integrable fun z ↦ g z • f z :=
  (hf.norm.const_mul K).mono' (hg.aestronglyMeasurable.smul hf.1)
    (ae_of_all _ (norm_smul_le_of_support hsupp hK))

private lemma norm_integral_smul_le_of_support (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) {g : ℂ → ℂ} {K : ℝ}
    (hK : ∀ z ∈ closedBall c r, ‖g z‖ ≤ K) :
    ‖∫ z, g z • f z‖ ≤ K * ∫ z, ‖f z‖ := by
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le (hf.norm.const_mul K)
    (ae_of_all _ (norm_smul_le_of_support hsupp hK))

end Pointwise

/-- Outside the disc the Cauchy transform minus its reciprocal tail is the transform against the
difference of kernels `(w - z)⁻¹ - (w - c)⁻¹`. -/
theorem cauchyTransform_sub_inv_smul_eq (hf : Integrable f) (hsupp : support f ⊆ closedBall c r)
    (hw : (r : ℝ) < ‖w - c‖) :
    cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z) =
      (Real.pi : ℂ)⁻¹ • ∫ z, ((w - z)⁻¹ - (w - c)⁻¹) • f z := by
  have hint : Integrable fun z ↦ (w - z)⁻¹ • f z :=
    integrable_smul_of_support hf hsupp (by fun_prop) fun z hz ↦ norm_inv_sub_le hz hw
  simp_rw [sub_smul]
  rw [integral_sub hint (hf.smul (w - c)⁻¹ : Integrable fun z ↦ (w - c)⁻¹ • f z),
    integral_smul, cauchyTransform_apply, smul_sub,
    smul_comm (w - c)⁻¹]

/-- **The reciprocal tail of the Cauchy transform**, with the exact kernel constant. -/
theorem norm_cauchyTransform_sub_inv_smul_le (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hw : (r : ℝ) < ‖w - c‖) :
    ‖cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)‖ ≤
      π⁻¹ * (r / ((‖w - c‖ - r) * ‖w - c‖) * ∫ z, ‖f z‖) := by
  rw [cauchyTransform_sub_inv_smul_eq hf hsupp hw, norm_smul, norm_inv, norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  gcongr
  exact norm_integral_smul_le_of_support hf hsupp fun z hz ↦ norm_inv_sub_sub_inv_sub_le hz hw

/-- The reciprocal tail of the Cauchy transform beyond twice the support radius:
`‖T f w - (w - c)⁻¹ • M‖ ≤ 2 π⁻¹ r ‖f‖₁ / ‖w - c‖²`. -/
theorem norm_cauchyTransform_sub_inv_smul_le_of_two_mul_lt (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hw : 2 * (r : ℝ) < ‖w - c‖) :
    ‖cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)‖ ≤
      2 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 2 := by
  have hr := r.coe_nonneg
  have hρ : 0 < ‖w - c‖ := by linarith
  have hw' : (r : ℝ) < ‖w - c‖ := by linarith
  refine (norm_cauchyTransform_sub_inv_smul_le hf hsupp hw').trans_eq' ?_ |>.trans ?_
  · rfl
  have hk : (r : ℝ) / ((‖w - c‖ - r) * ‖w - c‖) ≤ 2 * r / ‖w - c‖ ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos (by linarith) hρ) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hr hρ.le) (sub_nonneg.mpr hw.le)]
  have hI : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg fun _ ↦ norm_nonneg _
  calc π⁻¹ * (r / ((‖w - c‖ - r) * ‖w - c‖) * ∫ z, ‖f z‖)
      ≤ π⁻¹ * (2 * r / ‖w - c‖ ^ 2 * ∫ z, ‖f z‖) := by gcongr
    _ = 2 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 2 := by ring

/-- Eventually along `cobounded ℂ`, `0 < ‖w‖ ≤ 2 ‖w - c‖` and `2 r < ‖w - c‖`. -/
private lemma eventually_cobounded_norm_le (c : ℂ) (r : ℝ≥0) :
    ∀ᶠ w in cobounded ℂ, 0 < ‖w‖ ∧ ‖w‖ ≤ 2 * ‖w - c‖ ∧ 2 * (r : ℝ) < ‖w - c‖ := by
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop (2 * ‖c‖ + 4 * r + 1)]
    with w hw
  have := norm_sub_norm_le w c
  have := norm_nonneg c
  have := r.coe_nonneg
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- **The Cauchy transform at infinity.** For integrable data supported in `closedBall c r`,
`T f w = (w - c)⁻¹ • π⁻¹ ∫ f + O(‖w‖⁻²)` along `cobounded ℂ`. -/
theorem cauchyTransform_sub_inv_smul_isBigO (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) :
    (fun w ↦ cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)) =O[cobounded ℂ]
      fun w : ℂ ↦ w⁻¹ ^ 2 := by
  refine IsBigO.of_bound (8 * π⁻¹ * r * ∫ z, ‖f z‖) ?_
  filter_upwards [eventually_cobounded_norm_le c r] with w ⟨hw0, hw, hw2⟩
  have hρ : 0 < ‖w - c‖ := lt_of_le_of_lt (by positivity) hw2
  have hA : 0 ≤ 2 * π⁻¹ * r * ∫ z, ‖f z‖ := by
    have : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg fun z ↦ norm_nonneg (f z)
    positivity
  have hsq : ‖w‖ ^ 2 ≤ 4 * ‖w - c‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hinv : (‖w - c‖ ^ 2)⁻¹ ≤ 4 * (‖w‖ ^ 2)⁻¹ := by
    calc (‖w - c‖ ^ 2)⁻¹ = 4 * (4 * ‖w - c‖ ^ 2)⁻¹ := by field_simp
      _ ≤ 4 * (‖w‖ ^ 2)⁻¹ := by gcongr
  calc ‖cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)‖
      ≤ 2 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 2 :=
        norm_cauchyTransform_sub_inv_smul_le_of_two_mul_lt hf hsupp hw2
    _ = (2 * π⁻¹ * r * ∫ z, ‖f z‖) * (‖w - c‖ ^ 2)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (2 * π⁻¹ * r * ∫ z, ‖f z‖) * (4 * (‖w‖ ^ 2)⁻¹) := by gcongr
    _ = 8 * π⁻¹ * r * (∫ z, ‖f z‖) * ‖w⁻¹ ^ 2‖ := by rw [norm_pow, norm_inv, inv_pow]; ring

/-- The Cauchy transform of integrable data with bounded support tends to zero at infinity. -/
theorem tendsto_cauchyTransform_cobounded (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) :
    Tendsto (cauchyTransform f) (cobounded ℂ) (𝓝 0) := by
  have htail : Tendsto (fun w : ℂ ↦ (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)) (cobounded ℂ)
      (𝓝 0) := by
    simpa using (tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded c)).smul_const
      ((Real.pi : ℂ)⁻¹ • ∫ z, f z)
  have hrem := (cauchyTransform_sub_inv_smul_isBigO hf hsupp).trans_tendsto
    (by simpa using (tendsto_inv₀_cobounded (α := ℂ)).pow 2)
  simpa using hrem.add htail

/-- **Holomorphy off the disc.** At every point outside the closed disc carrying the data, the
Cauchy transform has complex derivative `-π⁻¹ ∫ ((w - z)²)⁻¹ • f z`. -/
theorem hasDerivAt_cauchyTransform_of_lt (hf : Integrable f) (hsupp : support f ⊆ closedBall c r)
    (hw : (r : ℝ) < ‖w - c‖) :
    HasDerivAt (cauchyTransform f) (-((Real.pi : ℂ)⁻¹ • ∫ z, ((w - z) ^ 2)⁻¹ • f z)) w := by
  set ε := (‖w - c‖ - r) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  -- On `ball w ε` every point is at distance at least `ε` from the disc.
  have hfar {w' z : ℂ} (hw' : w' ∈ ball w ε) (hz : z ∈ closedBall c r) : ε ≤ ‖w' - z‖ := by
    have h1 := sub_le_norm_sub (w := w) hz
    have h2 := norm_sub_le_norm_sub_add_norm_sub w w' z
    have h3 : ‖w - w'‖ < ε := by rw [← dist_eq_norm, dist_comm]; exact hw'
    rw [hε] at h3 ⊢
    linarith
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun w' z ↦ (w' - z)⁻¹ • f z) (F' := fun w' z ↦ -((w' - z) ^ 2)⁻¹ • f z)
    (bound := fun z ↦ (ε ^ 2)⁻¹ * ‖f z‖) (ball_mem_nhds w hε0)
    (Eventually.of_forall fun w' ↦ (by fun_prop : Measurable fun z : ℂ ↦ (w' - z)⁻¹)
      |>.aestronglyMeasurable.smul hf.1)
    (integrable_smul_of_support hf hsupp (by fun_prop) fun z hz ↦ norm_inv_sub_le hz hw)
    ((by fun_prop : Measurable fun z : ℂ ↦ -((w - z) ^ 2)⁻¹).aestronglyMeasurable.smul hf.1)
    (ae_of_all _ fun z w' hw' ↦ norm_smul_le_of_support (K := (ε ^ 2)⁻¹) hsupp (fun z hz ↦ by
      rw [norm_neg, norm_inv, norm_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hε0.le (hfar hw' hz) 2)) z)
    (hf.norm.const_mul _)
    (ae_of_all _ fun z w' hw' ↦ by
      by_cases hz : f z = 0
      · simpa [hz] using hasDerivAt_const w' (0 : F)
      · have hne : w' - z ≠ 0 :=
          norm_pos_iff.mp (hε0.trans_le (hfar hw' (hsupp hz)))
        exact (((hasDerivAt_id w').sub_const z).inv hne).smul_const (f z) |>.congr_deriv
          (by simp only [neg_div, one_div, neg_smul, id]))
  rw [show cauchyTransform f = fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z from
    funext (cauchyTransform_apply f)]
  convert hderiv.2.const_smul (Real.pi : ℂ)⁻¹ using 1
  simp_rw [neg_smul, integral_neg, smul_neg]

/-- The Cauchy transform of integrable data supported in `closedBall c r` is holomorphic on the
complement of the disc. -/
theorem differentiableOn_cauchyTransform_compl_closedBall (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) :
    DifferentiableOn ℂ (cauchyTransform f) (closedBall c r)ᶜ := fun w hw ↦
  (hasDerivAt_cauchyTransform_of_lt hf hsupp
    (by simpa only [mem_compl_iff, mem_closedBall_iff_norm, not_le] using hw))
    |>.differentiableAt.differentiableWithinAt

/-- Outside the disc the holomorphic Wirtinger derivative of the Cauchy transform is its complex
derivative. -/
theorem wirtingerDeriv_cauchyTransform_apply_one_of_lt (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hw : (r : ℝ) < ‖w - c‖) :
    wirtingerDeriv (cauchyTransform f) w 1 = deriv (cauchyTransform f) w := by
  have hd := (hasDerivAt_cauchyTransform_of_lt hf hsupp hw).differentiableAt
  rw [hd.wirtingerDeriv_eq_fderiv, fderiv_apply_one_eq_deriv]

/-- A pointwise bound for the derivative off the disc:
`‖(T f)' w‖ ≤ π⁻¹ ‖f‖₁ / (‖w - c‖ - r)²`. -/
theorem norm_deriv_cauchyTransform_le (hf : Integrable f) (hsupp : support f ⊆ closedBall c r)
    (hw : (r : ℝ) < ‖w - c‖) :
    ‖deriv (cauchyTransform f) w‖ ≤ π⁻¹ * (((‖w - c‖ - r) ^ 2)⁻¹ * ∫ z, ‖f z‖) := by
  rw [(hasDerivAt_cauchyTransform_of_lt hf hsupp hw).deriv, norm_neg, norm_smul, norm_inv,
    norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  gcongr
  refine norm_integral_smul_le_of_support hf hsupp fun z hz ↦ ?_
  rw [norm_inv, norm_pow]
  exact inv_anti₀ (pow_pos (sub_pos.mpr hw) 2)
    (pow_le_pow_left₀ (sub_pos.mpr hw).le (sub_le_norm_sub hz) 2)

/-- The derivative of the Cauchy transform at infinity, with the exact kernel constant. -/
theorem norm_deriv_cauchyTransform_add_inv_sq_smul_le (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hw : (r : ℝ) < ‖w - c‖) :
    ‖deriv (cauchyTransform f) w + ((w - c) ^ 2)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)‖ ≤
      π⁻¹ * (r / ((‖w - c‖ - r) * ‖w - c‖) * ((‖w - c‖ - r)⁻¹ + ‖w - c‖⁻¹) *
        ∫ z, ‖f z‖) := by
  have hint : Integrable fun z ↦ ((w - z) ^ 2)⁻¹ • f z :=
    integrable_smul_of_support hf hsupp (by fun_prop) fun z hz ↦ by
      rw [norm_inv, norm_pow, ← inv_pow, ← norm_inv]
      exact pow_le_pow_left₀ (by positivity) (norm_inv_sub_le hz hw) 2
  have heq : deriv (cauchyTransform f) w + ((w - c) ^ 2)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z) =
      -((Real.pi : ℂ)⁻¹ • ∫ z, (((w - z) ^ 2)⁻¹ - ((w - c) ^ 2)⁻¹) • f z) := by
    simp_rw [sub_smul]
    rw [(hasDerivAt_cauchyTransform_of_lt hf hsupp hw).deriv, integral_sub hint
      (hf.smul ((w - c) ^ 2)⁻¹ : Integrable fun z ↦ ((w - c) ^ 2)⁻¹ • f z),
      integral_smul, smul_sub, smul_comm ((w - c) ^ 2)⁻¹]
    abel
  rw [heq, norm_neg, norm_smul, norm_inv, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  gcongr
  refine norm_integral_smul_le_of_support hf hsupp fun z hz ↦ ?_
  rw [← inv_pow, ← inv_pow, sq_sub_sq, norm_mul, mul_comm]
  refine mul_le_mul (norm_inv_sub_sub_inv_sub_le hz hw)
    ((norm_add_le _ _).trans (add_le_add (norm_inv_sub_le hz hw) (by rw [norm_inv])))
    (norm_nonneg _) (by have := sub_pos.mpr hw; have := r.coe_nonneg; positivity)

/-- The derivative of the Cauchy transform beyond twice the support radius:
`‖(T f)' w + ((w - c)²)⁻¹ • M‖ ≤ 6 π⁻¹ r ‖f‖₁ / ‖w - c‖³`. -/
theorem norm_deriv_cauchyTransform_add_inv_sq_smul_le_of_two_mul_lt (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hw : 2 * (r : ℝ) < ‖w - c‖) :
    ‖deriv (cauchyTransform f) w + ((w - c) ^ 2)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)‖ ≤
      6 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 3 := by
  have hr := r.coe_nonneg
  have hρ : 0 < ‖w - c‖ := by linarith
  have hδ : ‖w - c‖ / 2 ≤ ‖w - c‖ - r := by linarith
  have hδ0 : 0 < ‖w - c‖ - r := by linarith
  refine (norm_deriv_cauchyTransform_add_inv_sq_smul_le hf hsupp (by linarith)).trans ?_
  have hk : (r : ℝ) / ((‖w - c‖ - r) * ‖w - c‖) * ((‖w - c‖ - r)⁻¹ + ‖w - c‖⁻¹) ≤
      6 * r / ‖w - c‖ ^ 3 := by
    have h1 : (r : ℝ) / ((‖w - c‖ - r) * ‖w - c‖) ≤ 2 * r / ‖w - c‖ ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos hδ0 hρ) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hr hρ.le) (sub_nonneg.mpr hw.le)]
    have h2 : (‖w - c‖ - r)⁻¹ + ‖w - c‖⁻¹ ≤ 3 / ‖w - c‖ := by
      have : (‖w - c‖ - r)⁻¹ ≤ 2 / ‖w - c‖ := by
        rw [inv_le_iff_one_le_mul₀ hδ0, div_mul_eq_mul_div, le_div_iff₀ hρ]
        linarith
      have h3 : (3 : ℝ) / ‖w - c‖ = 2 / ‖w - c‖ + ‖w - c‖⁻¹ := by ring
      linarith
    calc (r : ℝ) / ((‖w - c‖ - r) * ‖w - c‖) * ((‖w - c‖ - r)⁻¹ + ‖w - c‖⁻¹)
        ≤ 2 * r / ‖w - c‖ ^ 2 * (3 / ‖w - c‖) := by gcongr
      _ = 6 * r / ‖w - c‖ ^ 3 := by field_simp; ring
  have hI : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg fun _ ↦ norm_nonneg _
  calc π⁻¹ * ((r : ℝ) / ((‖w - c‖ - r) * ‖w - c‖) * ((‖w - c‖ - r)⁻¹ + ‖w - c‖⁻¹) *
        ∫ z, ‖f z‖)
      ≤ π⁻¹ * (6 * r / ‖w - c‖ ^ 3 * ∫ z, ‖f z‖) := by gcongr
    _ = 6 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 3 := by ring

/-- **The derivative of the Cauchy transform at infinity.** For integrable data supported in
`closedBall c r`, `(T f)' w = -((w - c)²)⁻¹ • π⁻¹ ∫ f + O(‖w‖⁻³)` along `cobounded ℂ`. -/
theorem deriv_cauchyTransform_add_inv_sq_smul_isBigO (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) :
    (fun w ↦ deriv (cauchyTransform f) w + ((w - c) ^ 2)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z))
      =O[cobounded ℂ] fun w : ℂ ↦ w⁻¹ ^ 3 := by
  refine IsBigO.of_bound (48 * π⁻¹ * r * ∫ z, ‖f z‖) ?_
  filter_upwards [eventually_cobounded_norm_le c r] with w ⟨hw0, hw, hw2⟩
  have hρ : 0 < ‖w - c‖ := lt_of_le_of_lt (by positivity) hw2
  have hA : 0 ≤ 6 * π⁻¹ * r * ∫ z, ‖f z‖ := by
    have : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg fun z ↦ norm_nonneg (f z)
    positivity
  have hcube : ‖w‖ ^ 3 ≤ 8 * ‖w - c‖ ^ 3 := by
    have := pow_le_pow_left₀ (norm_nonneg w) hw 3
    nlinarith
  have hinv : (‖w - c‖ ^ 3)⁻¹ ≤ 8 * (‖w‖ ^ 3)⁻¹ := by
    calc (‖w - c‖ ^ 3)⁻¹ = 8 * (8 * ‖w - c‖ ^ 3)⁻¹ := by field_simp
      _ ≤ 8 * (‖w‖ ^ 3)⁻¹ := by gcongr
  calc ‖deriv (cauchyTransform f) w + ((w - c) ^ 2)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)‖
      ≤ 6 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 3 :=
        norm_deriv_cauchyTransform_add_inv_sq_smul_le_of_two_mul_lt hf hsupp hw2
    _ = (6 * π⁻¹ * r * ∫ z, ‖f z‖) * (‖w - c‖ ^ 3)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (6 * π⁻¹ * r * ∫ z, ‖f z‖) * (8 * (‖w‖ ^ 3)⁻¹) := by gcongr
    _ = 48 * π⁻¹ * r * (∫ z, ‖f z‖) * ‖w⁻¹ ^ 3‖ := by rw [norm_pow, norm_inv, inv_pow]; ring

section Lp

/-- Translated reciprocal powers on the complement of a disc: `a / (w - c)ᵐ` is in `Lᵖ` there
exactly when `2 < m p`. -/
private lemma memLp_div_sub_pow_compl_closedBall_iff {a : ℂ} (ha : a ≠ 0) (c : ℂ) {R : ℝ}
    (hR : 0 < R) (m : ℕ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞) :
    MemLp (fun w : ℂ ↦ a / (w - c) ^ m) p (volume.restrict (closedBall c R)ᶜ) ↔
      2 < (m : ℝ) * p.toReal := by
  have hpres := (measurePreserving_add_right (volume : Measure ℂ) c).restrict_preimage
    (measurableSet_closedBall (x := c) (ε := R)).compl
  have hpre : (fun z : ℂ ↦ z + c) ⁻¹' (closedBall c R)ᶜ = (closedBall 0 R)ᶜ := by
    ext z
    simp [mem_closedBall, dist_eq_norm]
  rw [hpre] at hpres
  rw [← hpres.map_eq, (measurableEmbedding_addRight c).memLp_map_measure_iff]
  simpa [Function.comp_def] using memLp_div_pow_compl_closedBall_iff ha hR m hp0 hp_top

/-- **The Cauchy transform is not `Lᵖ` at infinity for `p ≤ 2`.** If `∫ f ≠ 0`, then on the
complement of every disc `closedBall c R` the transform is bounded below by a multiple of
`‖w - c‖⁻¹`, so it belongs to no `Lᵖ` with `0 < p ≤ 2`. -/
theorem not_memLp_cauchyTransform_compl_closedBall (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hf0 : ∫ z, f z ≠ 0) (R : ℝ) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp_top : p ≠ ∞) (hp : p.toReal ≤ 2) :
    ¬ MemLp (cauchyTransform f) p (volume.restrict (closedBall c R)ᶜ) := by
  set M : F := (Real.pi : ℂ)⁻¹ • ∫ z, f z with hM
  have hM0 : 0 < ‖M‖ := norm_pos_iff.mpr
    (smul_ne_zero (inv_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) hf0)
  set B : ℝ := 2 * π⁻¹ * r * ∫ z, ‖f z‖
  set R₁ : ℝ := max (max R 1) (max (2 * r) (2 * B / ‖M‖))
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
    have h2r : 2 * (r : ℝ) < ‖w - c‖ :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hρ
    have hBM : 2 * B / ‖M‖ < ‖w - c‖ :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hρ
    have hρ0 : 0 < ‖w - c‖ := hR₁.trans hρ
    have hrem := norm_cauchyTransform_sub_inv_smul_le_of_two_mul_lt hf hsupp h2r
    have htri := norm_sub_norm_le ((w - c)⁻¹ • M) (cauchyTransform f w)
    rw [norm_sub_rev, norm_smul, norm_inv] at htri
    rw [pow_one, norm_div, norm_real, Real.norm_of_nonneg (by positivity)]
    have hB : B / ‖w - c‖ ^ 2 ≤ ‖M‖ / 2 / ‖w - c‖ := by
      rw [div_lt_iff₀ hM0] at hBM
      rw [div_le_div_iff₀ (by positivity) hρ0]
      nlinarith
    have hsplit : ‖w - c‖⁻¹ * ‖M‖ = ‖M‖ / 2 / ‖w - c‖ + ‖M‖ / 2 / ‖w - c‖ := by
      field_simp; ring
    linarith
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
    (hsupp : support f ⊆ closedBall c r) {R : ℝ} (hR : r < R) {p : ℝ≥0∞} (hp_top : p ≠ ∞)
    (hp : 1 < p.toReal) :
    MemLp (deriv (cauchyTransform f)) p (volume.restrict (ball c R)ᶜ) := by
  have hp0 : p ≠ 0 := by rintro rfl; norm_num at hp
  set R' : ℝ := (r + R) / 2
  have hrR' : (r : ℝ) < R' := by simp only [R']; linarith
  have hR' : 0 < R' := lt_of_le_of_lt r.coe_nonneg hrR'
  set K : ℝ := π⁻¹ * (((1 - r / R') ^ 2)⁻¹ * ∫ z, ‖f z‖) + 1
  have hK : 0 < K := by
    have : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg fun z ↦ norm_nonneg (f z)
    have : 0 < 1 - r / R' := by rw [sub_pos, div_lt_one hR']; exact hrR'
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
  have hq : 0 < 1 - r / R' := by rw [sub_pos, div_lt_one hR']; exact hrR'
  have hlin : (1 - r / R') * ‖w - c‖ ≤ ‖w - c‖ - r := by
    have : r / R' * ‖w - c‖ ≥ r := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hR']
      exact mul_le_mul_of_nonneg_left hρ.le r.coe_nonneg
    linarith
  have hsq : ((‖w - c‖ - r) ^ 2)⁻¹ ≤ ((1 - r / R') ^ 2)⁻¹ / ‖w - c‖ ^ 2 := by
    rw [← inv_pow, ← inv_pow, div_eq_mul_inv, ← inv_pow, ← mul_pow, ← mul_inv]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) hlin) 2
  have hI : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg fun z ↦ norm_nonneg (f z)
  calc π⁻¹ * (((‖w - c‖ - r) ^ 2)⁻¹ * ∫ z, ‖f z‖)
      ≤ π⁻¹ * (((1 - r / R') ^ 2)⁻¹ / ‖w - c‖ ^ 2 * ∫ z, ‖f z‖) := by gcongr
    _ = (K - 1) / ‖w - c‖ ^ 2 := by simp only [K]; ring
    _ ≤ K / ‖w - c‖ ^ 2 := by gcongr; linarith

/-- The holomorphic Wirtinger derivative `∂ (T f)` is `Lᵖ` on the complement of every disc
`ball c R` with `r < R`, for every `1 < p < ∞`. -/
theorem memLp_wirtingerDeriv_cauchyTransform_compl_ball [CompleteSpace F] (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) {R : ℝ} (hR : r < R) {p : ℝ≥0∞} (hp_top : p ≠ ∞)
    (hp : 1 < p.toReal) :
    MemLp (fun w ↦ wirtingerDeriv (cauchyTransform f) w 1) p (volume.restrict (ball c R)ᶜ) := by
  refine (memLp_congr_ae ?_).mpr (memLp_deriv_cauchyTransform_compl_ball hf hsupp hR hp_top hp)
  filter_upwards [ae_restrict_mem measurableSet_ball.compl] with w hw
  have hRw : R ≤ ‖w - c‖ := by simpa [mem_ball, dist_eq_norm] using hw
  exact wirtingerDeriv_cauchyTransform_apply_one_of_lt hf hsupp (hR.trans_le hRw)

end Lp

end TauCeti
