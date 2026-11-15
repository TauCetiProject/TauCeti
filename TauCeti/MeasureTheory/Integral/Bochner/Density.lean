/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Basic
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Basis independence of density integrals

A basis `b` of a real normed space `E` determines both a scalar density coefficient `x ↦ μ x b`
and a normalized additive Haar measure `b.addHaar`. Under a change of basis from `b` to `b'`, the
normalized Haar measure scales by `|b.det b'|⁻¹` while the density evaluation scales by
`|b.det b'|`. These two positive factors cancel identically, so both integrability and the Bochner
integral of a density-valued function are independent of the chosen basis without any orientation
sign, including in dimension zero.

## Main results

* `Module.Basis.integrable_density_apply_iff`, `Module.Basis.integrableOn_density_apply_iff`:
  integrability of `x ↦ μ x b` against `b.addHaar` is independent of the basis `b`.
* `Module.Basis.integral_density_apply_eq`, `Module.Basis.setIntegral_density_apply_eq`:
  the integral `∫ x, μ x b ∂b.addHaar` (and its restriction to any set) is independent of `b`.
-/

public section

noncomputable section

open MeasureTheory

namespace Module.Basis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {m : ℕ}

/-- Integrability of a density coefficient against normalized basis Haar measure is independent of
the chosen basis, including in dimension zero. -/
theorem integrable_density_apply_iff (b b' : Basis (Fin m) ℝ E)
    (μ : E → TauCeti.Density E m) :
    Integrable (fun x ↦ μ x b') b'.addHaar ↔ Integrable (fun x ↦ μ x b) b.addHaar := by
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  rw [addHaar_eq_smul_of_basis b b', integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero hd))) ENNReal.ofReal_ne_top]
  simp_rw [TauCeti.Density.apply_eq_abs_det_mul _ b b']
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (abs_ne_zero.mpr hd)) _

/-- Set integrability of a density coefficient against normalized basis Haar measure is independent
of the chosen basis, with no measurability assumption on the set. -/
theorem integrableOn_density_apply_iff (b b' : Basis (Fin m) ℝ E)
    (μ : E → TauCeti.Density E m) (s : Set E) :
    IntegrableOn (fun x ↦ μ x b') s b'.addHaar ↔
      IntegrableOn (fun x ↦ μ x b) s b.addHaar := by
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  simp only [IntegrableOn, addHaar_eq_smul_of_basis b b', Measure.restrict_smul]
  rw [integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero hd))) ENNReal.ofReal_ne_top]
  simp_rw [TauCeti.Density.apply_eq_abs_det_mul _ b b']
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (abs_ne_zero.mpr hd)) _

/-- The Bochner integral of a density evaluated on a basis against that basis's normalized Haar
measure is independent of the chosen basis, with no orientation sign and including dimension
zero. -/
theorem integral_density_apply_eq (b b' : Basis (Fin m) ℝ E)
    (μ : E → TauCeti.Density E m) :
    (∫ x, μ x b ∂b.addHaar) = ∫ x, μ x b' ∂b'.addHaar := by
  have hd : |b.det b'| ≠ 0 := abs_ne_zero.mpr (b.isUnit_det b').ne_zero
  rw [addHaar_eq_smul_of_basis b b', integral_smul_measure]
  simp_rw [TauCeti.Density.apply_eq_abs_det_mul _ b b']
  rw [integral_const_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

/-- The set integral of a density evaluated on a basis against that basis's normalized Haar measure
is independent of the chosen basis, with no measurability assumption on the set. -/
theorem setIntegral_density_apply_eq (b b' : Basis (Fin m) ℝ E)
    (μ : E → TauCeti.Density E m) (s : Set E) :
    (∫ x in s, μ x b ∂b.addHaar) = ∫ x in s, μ x b' ∂b'.addHaar := by
  have hd : |b.det b'| ≠ 0 := abs_ne_zero.mpr (b.isUnit_det b').ne_zero
  rw [addHaar_eq_smul_of_basis b b', Measure.restrict_smul, integral_smul_measure]
  simp_rw [TauCeti.Density.apply_eq_abs_det_mul _ b b']
  rw [integral_const_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

end Module.Basis
