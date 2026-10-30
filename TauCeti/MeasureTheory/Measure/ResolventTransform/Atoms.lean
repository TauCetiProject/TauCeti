/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Atoms from the resolvent transform

For a finite measure on the real line, the imaginary part of its resolvent transform
is the integral of the positive kernel `im z / ((x - re z)² + (im z)²)`.
Multiplying by `η` and approaching `a` vertically from above recovers the mass of `{a}`.
This detects atoms, including atoms at endpoints when using Stieltjes inversion.

We use Mathlib's `MeasureTheory.resolventTransform`, with sign `(x - z)⁻¹`, not
`(z - x)⁻¹`. In particular the imaginary part is positive in the upper half-plane
for every nonzero finite measure. No moment assumptions are needed.

## References

* Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*, Appendix B,
  for the Stieltjes transform and its inversion.
-/

public section

noncomputable section

open MeasureTheory Filter Complex
open scoped Topology

namespace Complex

/-- The imaginary part of the real resolvent kernel, with sign `(x - z)⁻¹`. -/
theorem im_resolvent_real (z : ℂ) (x : ℝ) :
    (resolvent z x).im = z.im / ((x - z.re) ^ 2 + z.im ^ 2) := by
  simp [resolvent, Ring.inverse_eq_inv', Complex.inv_im, Complex.normSq_apply, sq]

/-- The real resolvent kernel is bounded by the reciprocal distance to the real axis. -/
theorem norm_resolvent_real_le (z : ℂ) (x : ℝ) (hz : z.im ≠ 0) :
    ‖resolvent z x‖ ≤ |z.im|⁻¹ := by
  rw [resolvent, Ring.inverse_eq_inv', norm_inv]
  apply inv_anti₀ (abs_pos.mpr hz)
  simpa using abs_im_le_norm ((x : ℂ) - z)

end Complex

namespace MeasureTheory

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- The imaginary part of the transform is the integral of the positive Poisson kernel
(without the factor `π⁻¹`). -/
theorem im_resolventTransform {z : ℂ} (hz : z.im ≠ 0) :
    (resolventTransform μ z).im =
      ∫ x, z.im / ((x - z.re) ^ 2 + z.im ^ 2) ∂μ := by
  have hi : Integrable (resolvent (R := ℝ) z) μ :=
    integrable_resolvent (by
      rintro ⟨x, _, hx⟩
      exact hz (by simpa using (congrArg Complex.im hx).symm))
  simpa only [resolventTransform_apply, RCLike.im_eq_complex_im,
    Complex.im_resolvent_real] using (integral_im hi).symm

/-- A uniform bound for the transform of a finite measure away from the real axis. -/
theorem norm_resolventTransform_le {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform μ z‖ ≤ |z.im|⁻¹ * μ.real Set.univ := by
  rw [resolventTransform_apply]
  exact norm_integral_le_of_norm_le_const
    (ae_of_all _ fun x => Complex.norm_resolvent_real_le z x hz)

/-- A nonzero finite measure has strictly positive imaginary transform in the upper half-plane. -/
theorem im_resolventTransform_pos (hμ : μ ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    0 < (resolventTransform μ z).im := by
  have hi : Integrable (resolvent (R := ℝ) z) μ :=
    integrable_resolvent (by
      rintro ⟨x, _, hx⟩
      exact hz.ne' (by simpa using (congrArg Complex.im hx).symm))
  have hp (x : ℝ) : 0 < z.im / ((x - z.re) ^ 2 + z.im ^ 2) := by
    exact div_pos hz (by positivity)
  rw [im_resolventTransform hz.ne']
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) ?_).2
  · simpa [Function.support, ne_of_gt (hp _)] using (Measure.measure_univ_pos.mpr hμ)
  · simpa only [RCLike.im_eq_complex_im, Complex.im_resolvent_real] using hi.im

/-- The rescaled imaginary transform is an integral of kernels taking values in `[0,1]`. -/
theorem mul_im_resolventTransform {a η : ℝ} (hη : η ≠ 0) :
    η * (resolventTransform μ ((a : ℂ) + η * I)).im =
      ∫ x, η ^ 2 / ((x - a) ^ 2 + η ^ 2) ∂μ := by
  rw [im_resolventTransform (by simpa using hη), ← integral_const_mul]
  congr 1
  ext x
  simp [sq, mul_div_assoc]

/-- **Atom recovery for the Stieltjes transform.** Approaching `a` vertically from the upper
half-plane, `η Im m(a + iη)` tends to the mass of `{a}`. The mass is real-valued since `μ`
is finite. -/
theorem tendsto_mul_im_resolventTransform (a : ℝ) :
    Tendsto (fun η : ℝ => η * (resolventTransform μ ((a : ℂ) + η * I)).im)
      (𝓝[>] 0) (𝓝 (μ.real {a})) := by
  have hlim : Tendsto (fun η : ℝ => ∫ x, η ^ 2 / ((x - a) ^ 2 + η ^ 2) ∂μ)
      (𝓝[>] 0) (𝓝 (∫ x, Set.indicator {a} (fun _ : ℝ => (1 : ℝ)) x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall fun η =>
        (measurable_const.div ((measurable_id.sub_const a).pow_const 2 |>.add_const
          (η ^ 2))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with η hη
      have hpos : 0 < η := hη
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact (div_le_one (by positivity : 0 < (x - a) ^ 2 + η ^ 2)).2
          (by nlinarith [sq_nonneg (x - a)])
    · exact integrable_const 1
    · -- The bounded kernels tend to one at the atom and to zero everywhere else.
      exact ae_of_all _ fun x => by
        by_cases hx : x = a
        · subst x
          simp only [Set.indicator_of_mem (Set.mem_singleton a), sub_self, zero_pow,
            ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add]
          apply tendsto_const_nhds.congr'
          filter_upwards [self_mem_nhdsWithin] with η hη
          exact (div_self (pow_ne_zero 2 (ne_of_gt hη))).symm
        · have hxa : x ∉ ({a} : Set ℝ) := by simpa using hx
          rw [Set.indicator_of_notMem hxa]
          have hden : (x - a) ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by
            simpa using pow_ne_zero 2 (sub_ne_zero.mpr hx)
          have ht : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
          simpa only [zero_pow (by decide : 2 ≠ 0), zero_div] using!
            (ht.pow 2).div (tendsto_const_nhds.add (ht.pow 2)) hden
  have heq : (∫ x, Set.indicator {a} (fun _ : ℝ => (1 : ℝ)) x ∂μ) = μ.real {a} := by
    exact integral_indicator_one (measurableSet_singleton a)
  rw [heq] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (mul_im_resolventTransform (ne_of_gt hη)).symm

end MeasureTheory
