/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Basic
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Basis independence of density integrals

A basis `b` of a real normed space `E` determines both a scalar evaluation `μ ↦ μ b` of top-degree
densities and a normalized additive Haar measure `b.addHaar`. Under a change of basis from `b` to
`b'`, the density evaluation scales by `|b.det b'|`, whereas `b'.addHaar` scales by `|b.det b'|⁻¹`.
The two positive factors cancel identically, so both integrability and the Bochner integral of a
density-valued function are independent of the chosen basis, with no orientation sign required
and including dimension zero.

This is the orientation-free counterpart of `TauCeti.MeasureTheory.Integral.Bochner.Alternating`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
-/

public section

noncomputable section

open MeasureTheory Set TauCeti

namespace Module.Basis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {m : ℕ}

/-- The set integral of a density field over any subset of `E` is independent of the chosen basis
and its normalized Haar measure. -/
theorem setIntegral_density_apply_eq (b b' : Basis (Fin m) ℝ E) (ω : E → Density E m)
    (s : Set E) :
    (∫ x in s, ω x b' ∂b'.addHaar) = ∫ x in s, ω x b ∂b.addHaar := by
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  rw [addHaar_eq_smul_of_basis b b', Measure.restrict_smul, integral_smul_measure]
  simp_rw [Density.apply_eq_abs_det_mul _ b b']
  rw [integral_const_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  simp only [smul_eq_mul]
  field_simp

/-- The integral of a density field against the normalized Haar measure of a basis does not depend
on the choice of basis, including in dimension zero and without any orientation assumption. -/
theorem integral_density_apply_eq (b b' : Basis (Fin m) ℝ E) (ω : E → Density E m) :
    (∫ x, ω x b' ∂b'.addHaar) = ∫ x, ω x b ∂b.addHaar := by
  simpa only [Measure.restrict_univ] using setIntegral_density_apply_eq b b' ω univ

/-- Set-integrability of the basis evaluation of a density field against the basis's normalized
Haar measure is independent of the chosen basis. -/
theorem integrableOn_density_apply_basis_iff (b b' : Basis (Fin m) ℝ E)
    (ω : E → Density E m) (s : Set E) :
    IntegrableOn (fun x ↦ ω x b') s b'.addHaar ↔ IntegrableOn (fun x ↦ ω x b) s b.addHaar := by
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  rw [IntegrableOn, IntegrableOn, addHaar_eq_smul_of_basis b b', Measure.restrict_smul,
    integrable_smul_measure
      (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero hd))) ENNReal.ofReal_ne_top]
  simp_rw [Density.apply_eq_abs_det_mul _ b b']
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (abs_ne_zero.mpr hd)) _

/-- Integrability of the basis evaluation of a density field against the basis's normalized Haar
measure is independent of the chosen basis. -/
theorem integrable_density_apply_basis_iff (b b' : Basis (Fin m) ℝ E)
    (ω : E → Density E m) :
    Integrable (fun x ↦ ω x b') b'.addHaar ↔ Integrable (fun x ↦ ω x b) b.addHaar := by
  simpa only [integrableOn_univ] using integrableOn_density_apply_basis_iff b b' ω univ

end Module.Basis
