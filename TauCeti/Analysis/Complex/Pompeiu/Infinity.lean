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
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# The Cauchy transform at infinity

Let `f : ℂ → F` be integrable and supported in the closed disc `closedBall c r`, and write
`M = π⁻¹ ∫ f` for its normalized mass. Outside the disc the Cauchy transform
`T f w = π⁻¹ ∫ (w - z)⁻¹ • f z` is holomorphic (indeed it is holomorphic off the closed support of
any integrable `f`), and it is the reciprocal tail `M / (w - c)` up
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
* `TauCeti.hasDerivAt_cauchyTransform_of_notMem_tsupport` and
  `TauCeti.differentiableOn_cauchyTransform_compl_tsupport`: holomorphy off `tsupport f`.
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

end Pointwise

/-- Outside the disc the Cauchy transform minus its reciprocal tail is the transform against the
difference of kernels `(w - z)⁻¹ - (w - c)⁻¹`. -/
theorem cauchyTransform_sub_inv_smul_eq (hf : Integrable f) (hsupp : support f ⊆ closedBall c r)
    (hw : (r : ℝ) < ‖w - c‖) :
    cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z) =
      (Real.pi : ℂ)⁻¹ • ∫ z, ((w - z)⁻¹ - (w - c)⁻¹) • f z := by
  have hint : Integrable fun z ↦ (w - z)⁻¹ • f z :=
    hf.smul_of_support_subset hsupp (by fun_prop) fun z hz ↦ norm_inv_sub_le hz hw
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
  exact norm_integral_smul_le_of_support_subset hf hsupp fun z hz ↦
    norm_inv_sub_sub_inv_sub_le hz hw

/-- Beyond twice the support radius the kernel constant is at most `2 r / ‖w - c‖²`. -/
private lemma div_sub_mul_le_two_mul_div_sq (hw : 2 * (r : ℝ) < ‖w - c‖) :
    (r : ℝ) / ((‖w - c‖ - r) * ‖w - c‖) ≤ 2 * r / ‖w - c‖ ^ 2 := by
  have hr := r.coe_nonneg
  have hρ : 0 < ‖w - c‖ := by linarith
  rw [div_le_div_iff₀ (mul_pos (by linarith) hρ) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hr hρ.le) (sub_nonneg.mpr hw.le)]

/-- The reciprocal tail of the Cauchy transform beyond twice the support radius:
`‖T f w - (w - c)⁻¹ • M‖ ≤ 2 π⁻¹ r ‖f‖₁ / ‖w - c‖²`. -/
theorem norm_cauchyTransform_sub_inv_smul_le_of_two_mul_lt (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) (hw : 2 * (r : ℝ) < ‖w - c‖) :
    ‖cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)‖ ≤
      2 * π⁻¹ * r * (∫ z, ‖f z‖) / ‖w - c‖ ^ 2 := by
  have hw' : (r : ℝ) < ‖w - c‖ := by linarith [r.coe_nonneg]
  refine (norm_cauchyTransform_sub_inv_smul_le hf hsupp hw').trans ?_
  have hk := div_sub_mul_le_two_mul_div_sq hw
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

/-- A bound `‖g w‖ ≤ A / ‖w - c‖ ^ n` beyond twice the radius gives `g = O(w⁻ⁿ)` at infinity. -/
private lemma isBigO_inv_pow_of_norm_le {E : Type*} [NormedAddCommGroup E] {g : ℂ → E} {A : ℝ}
    (n : ℕ) (hg : ∀ w : ℂ, 2 * (r : ℝ) < ‖w - c‖ → ‖g w‖ ≤ A / ‖w - c‖ ^ n) :
    g =O[cobounded ℂ] fun w : ℂ ↦ w⁻¹ ^ n := by
  refine IsBigO.of_bound (2 ^ n * A) ?_
  filter_upwards [eventually_cobounded_norm_le c r] with w ⟨hw0, hw, hw2⟩
  have hρ : 0 < ‖w - c‖ := lt_of_le_of_lt (by positivity) hw2
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hg w hw2)
    rwa [le_div_iff₀ (by positivity), zero_mul] at this
  have hinv : (‖w - c‖ ^ n)⁻¹ ≤ 2 ^ n * (‖w‖ ^ n)⁻¹ := by
    calc (‖w - c‖ ^ n)⁻¹ = 2 ^ n * ((2 * ‖w - c‖) ^ n)⁻¹ := by
          rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ 2 ^ n * (‖w‖ ^ n)⁻¹ := by gcongr
  calc ‖g w‖ ≤ A / ‖w - c‖ ^ n := hg w hw2
    _ = A * (‖w - c‖ ^ n)⁻¹ := div_eq_mul_inv _ _
    _ ≤ A * (2 ^ n * (‖w‖ ^ n)⁻¹) := by gcongr
    _ = 2 ^ n * A * ‖w⁻¹ ^ n‖ := by rw [norm_pow, norm_inv, inv_pow]; ring

/-- **The Cauchy transform at infinity.** For integrable data supported in `closedBall c r`,
`T f w = (w - c)⁻¹ • π⁻¹ ∫ f + O(‖w‖⁻²)` along `cobounded ℂ`. -/
theorem cauchyTransform_sub_inv_smul_isBigO (hf : Integrable f)
    (hsupp : support f ⊆ closedBall c r) :
    (fun w ↦ cauchyTransform f w - (w - c)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z)) =O[cobounded ℂ]
      fun w : ℂ ↦ w⁻¹ ^ 2 :=
  isBigO_inv_pow_of_norm_le 2 fun _ hw ↦
    norm_cauchyTransform_sub_inv_smul_le_of_two_mul_lt hf hsupp hw

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

/-- **Holomorphy off the support.** At every point outside the closed support of integrable data,
the Cauchy transform has complex derivative `-π⁻¹ ∫ ((w - z)²)⁻¹ • f z`. -/
theorem hasDerivAt_cauchyTransform_of_notMem_tsupport (hf : Integrable f) (hw : w ∉ tsupport f) :
    HasDerivAt (cauchyTransform f) (-((Real.pi : ℂ)⁻¹ • ∫ z, ((w - z) ^ 2)⁻¹ • f z)) w := by
  obtain ⟨δ, hδ0, hδ⟩ := Metric.isOpen_iff.mp (isClosed_tsupport f).isOpen_compl w hw
  set ε := δ / 2 with hε
  have hε0 : 0 < ε := half_pos hδ0
  -- On `ball w ε` every point is at distance at least `ε` from the support.
  have hfar {w' z : ℂ} (hw' : w' ∈ ball w ε) (hz : z ∈ support f) : ε ≤ ‖w' - z‖ := by
    have h1 : δ ≤ ‖w - z‖ :=
      not_lt.mp fun h ↦ hδ (mem_ball_iff_norm'.mpr h) (subset_tsupport f hz)
    have h2 := norm_sub_le_norm_sub_add_norm_sub w w' z
    have h3 : ‖w - w'‖ < ε := by rw [← dist_eq_norm, dist_comm]; exact hw'
    linarith
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun w' z ↦ (w' - z)⁻¹ • f z) (F' := fun w' z ↦ -((w' - z) ^ 2)⁻¹ • f z)
    (bound := fun z ↦ (ε ^ 2)⁻¹ * ‖f z‖) (ball_mem_nhds w hε0)
    (Eventually.of_forall fun w' ↦ (by fun_prop : Measurable fun z : ℂ ↦ (w' - z)⁻¹)
      |>.aestronglyMeasurable.smul hf.1)
    (hf.smul_of_support_subset subset_rfl (by fun_prop) (K := ε⁻¹) fun z hz ↦ by
      rw [norm_inv]
      exact inv_anti₀ hε0 (hfar (mem_ball_self hε0) hz))
    ((by fun_prop : Measurable fun z : ℂ ↦ -((w - z) ^ 2)⁻¹).aestronglyMeasurable.smul hf.1)
    (ae_of_all _ fun z w' hw' ↦ norm_smul_le_mul_norm_of_support_subset
      (g := fun z ↦ -((w' - z) ^ 2)⁻¹) (K := (ε ^ 2)⁻¹) subset_rfl (fun z hz ↦ by
      rw [norm_neg, norm_inv, norm_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hε0.le (hfar hw' hz) 2)) z)
    (hf.norm.const_mul _)
    (ae_of_all _ fun z w' hw' ↦ by
      by_cases hz : f z = 0
      · simpa [hz] using hasDerivAt_const w' (0 : F)
      · have hne : w' - z ≠ 0 :=
          norm_pos_iff.mp (hε0.trans_le (hfar hw' hz))
        exact (((hasDerivAt_id w').sub_const z).inv hne).smul_const (f z) |>.congr_deriv
          (by simp only [neg_div, one_div, neg_smul, id]))
  rw [show cauchyTransform f = fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z from
    funext (cauchyTransform_apply f)]
  convert hderiv.2.const_smul (Real.pi : ℂ)⁻¹ using 1
  simp_rw [neg_smul, integral_neg, smul_neg]

/-- The Cauchy transform of integrable data is holomorphic off its closed support. -/
theorem differentiableOn_cauchyTransform_compl_tsupport (hf : Integrable f) :
    DifferentiableOn ℂ (cauchyTransform f) (tsupport f)ᶜ := fun _ hw ↦
  (hasDerivAt_cauchyTransform_of_notMem_tsupport hf hw).differentiableAt.differentiableWithinAt

/-- Off the closed support the holomorphic Wirtinger derivative of the Cauchy transform is its
complex derivative. -/
theorem wirtingerDeriv_cauchyTransform_apply_one_of_notMem_tsupport (hf : Integrable f)
    (hw : w ∉ tsupport f) :
    wirtingerDeriv (cauchyTransform f) w 1 = deriv (cauchyTransform f) w := by
  have hd := (hasDerivAt_cauchyTransform_of_notMem_tsupport hf hw).differentiableAt
  rw [hd.wirtingerDeriv_eq_fderiv, fderiv_apply_one_eq_deriv]

omit [NormedSpace ℂ F] in
/-- A point outside the closed disc carrying the data is outside its closed support. -/
private lemma notMem_tsupport_of_gt (hsupp : support f ⊆ closedBall c r)
    (hw : (r : ℝ) < ‖w - c‖) : w ∉ tsupport f := fun h ↦
  (mem_closedBall_iff_norm.mp (closure_minimal hsupp isClosed_closedBall h)).not_gt hw

/-- A pointwise bound for the derivative off the disc:
`‖(T f)' w‖ ≤ π⁻¹ ‖f‖₁ / (‖w - c‖ - r)²`. -/
theorem norm_deriv_cauchyTransform_le (hf : Integrable f) (hsupp : support f ⊆ closedBall c r)
    (hw : (r : ℝ) < ‖w - c‖) :
    ‖deriv (cauchyTransform f) w‖ ≤ π⁻¹ * (((‖w - c‖ - r) ^ 2)⁻¹ * ∫ z, ‖f z‖) := by
  rw [(hasDerivAt_cauchyTransform_of_notMem_tsupport hf (notMem_tsupport_of_gt hsupp hw)).deriv,
    norm_neg, norm_smul, norm_inv, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  gcongr
  refine norm_integral_smul_le_of_support_subset hf hsupp fun z hz ↦ ?_
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
    hf.smul_of_support_subset hsupp (by fun_prop) fun z hz ↦ by
      rw [norm_inv, norm_pow, ← inv_pow, ← norm_inv]
      exact pow_le_pow_left₀ (by positivity) (norm_inv_sub_le hz hw) 2
  have heq : deriv (cauchyTransform f) w + ((w - c) ^ 2)⁻¹ • ((Real.pi : ℂ)⁻¹ • ∫ z, f z) =
      -((Real.pi : ℂ)⁻¹ • ∫ z, (((w - z) ^ 2)⁻¹ - ((w - c) ^ 2)⁻¹) • f z) := by
    simp_rw [sub_smul]
    rw [(hasDerivAt_cauchyTransform_of_notMem_tsupport hf (notMem_tsupport_of_gt hsupp hw)).deriv,
      integral_sub hint (hf.smul ((w - c) ^ 2)⁻¹ : Integrable fun z ↦ ((w - c) ^ 2)⁻¹ • f z),
      integral_smul, smul_sub, smul_comm ((w - c) ^ 2)⁻¹]
    abel
  rw [heq, norm_neg, norm_smul, norm_inv, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  gcongr
  refine norm_integral_smul_le_of_support_subset hf hsupp fun z hz ↦ ?_
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
    have h1 := div_sub_mul_le_two_mul_div_sq hw
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
      =O[cobounded ℂ] fun w : ℂ ↦ w⁻¹ ^ 3 :=
  isBigO_inv_pow_of_norm_le 3 fun _ hw ↦
    norm_deriv_cauchyTransform_add_inv_sq_smul_le_of_two_mul_lt hf hsupp hw

section Lp

/-- **The Cauchy transform is not `Lᵖ` at infinity for `p ≤ 2`.** If `∫ f ≠ 0`, then on the
complement of every disc `closedBall c R` the transform belongs to no `Lᵖ` with `0 < p ≤ 2`:
outside a sufficiently large disc it is bounded below by a multiple of `‖w - c‖⁻¹`. -/
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
  have hI : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg fun z ↦ norm_nonneg (f z)
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
  have hRw : R ≤ ‖w - c‖ := by simpa [mem_ball, dist_eq_norm] using hw
  exact wirtingerDeriv_cauchyTransform_apply_one_of_notMem_tsupport hf
    (notMem_tsupport_of_gt hsupp (hR.trans_le hRw))

end Lp

end TauCeti
