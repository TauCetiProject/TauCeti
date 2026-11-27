/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Folding integrals under reciprocal symmetry

For the logarithmic measure `dt/t` on the positive half-line, reciprocal reflection about
`a > 0` exchanges `(0, a)` and `(a, ∞)` without changing the measure.
-/

public section

open Set

namespace MeasureTheory

/-- For a function invariant under `t ↦ a²/t`, convergence above `a` implies convergence
on the positive half-line, and the full logarithmic integral is twice the upper tail. -/
theorem integral_inv_smul_eq_two_smul_integral_Ioi_of_div_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) {f : ℝ → E} (hsymm : ∀ t > a, f (a ^ 2 / t) = f t)
    (hf : IntegrableOn (fun t ↦ t⁻¹ • f t) (Ioi a)) :
    IntegrableOn (fun t ↦ t⁻¹ • f t) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), t⁻¹ • f t) = (2 : ℝ) • ∫ t in Ioi a, t⁻¹ • f t := by
  let φ : ℝ → ℝ := fun t ↦ a ^ 2 / t
  have himage : φ '' Ioi a = Ioo 0 a := by
    calc
      φ '' Ioi a = (a ^ 2 * ·) '' ((fun t : ℝ ↦ t⁻¹) '' Ioi a) := by
        rw [Set.image_image]
        exact Set.image_congr fun t _ ↦ div_eq_mul_inv _ _
      _ = Ioo 0 a := by
        rw [Set.image_inv_eq_inv, Set.inv_Ioi₀ ha, Set.image_mul_left_Ioo (sq_pos_of_pos ha)]
        simp [pow_two, ha.ne']
  have hderiv (t : ℝ) (ht : t ∈ Ioi a) :
      HasDerivWithinAt φ (a ^ 2 * -(t ^ 2)⁻¹) (Ioi a) t := by
    simpa only [φ, div_eq_mul_inv] using
      ((hasDerivAt_inv (ha.trans ht).ne').const_mul (a ^ 2)).hasDerivWithinAt
  have hinj : InjOn φ (Ioi a) := by
    intro x _ y _ h
    exact inv_injective (mul_left_cancel₀ (sq_pos_of_pos ha).ne' (by
      simpa only [φ, div_eq_mul_inv] using h))
  have hJac (t : ℝ) (ht : t ∈ Ioi a) :
      |a ^ 2 * -(t ^ 2)⁻¹| • ((φ t)⁻¹ • f (φ t)) = t⁻¹ • f t := by
    have ht₀ : 0 < t := ha.trans ht
    have hft : f (φ t) = f t := hsymm t ht
    rw [hft, smul_smul]
    congr 1
    simp only [φ, mul_neg, abs_neg, abs_of_pos (by positivity : 0 < a ^ 2 * (t ^ 2)⁻¹)]
    field_simp
  have hlow : IntegrableOn (fun t ↦ t⁻¹ • f t) (Ioo 0 a) := by
    rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
    exact hf.congr_fun (fun t ht ↦ (hJac t ht).symm) measurableSet_Ioi
  have hopp : (∫ t in Ioo 0 a, t⁻¹ • f t) = ∫ t in Ioi a, t⁻¹ • f t := by
    rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
    exact setIntegral_congr_fun measurableSet_Ioi hJac
  have hlow' := (integrableOn_Ioc_iff_integrableOn_Ioo (μ := volume)).mpr hlow
  rw [← Ioc_union_Ioi_eq_Ioi ha.le]
  refine ⟨hlow'.union hf, ?_⟩
  rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hlow' hf,
    integral_Ioc_eq_integral_Ioo, hopp, two_smul]

end MeasureTheory
