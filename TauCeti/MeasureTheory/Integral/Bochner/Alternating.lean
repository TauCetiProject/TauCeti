/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.LinearAlgebra.Orientation.Basis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Basis independence of alternating-form integrals

A basis determines a real top-degree coefficient and normalized Haar measure. Their integral
changes by the orientation sign of the basis change. Relative orientation signs make it
independent of an arbitrary basis, including negative orientations in dimension zero.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Module.Basis

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]

/-- Arbitrary basis changes transform the actual top-form coefficient integral by their
orientation sign. Positive Haar scaling and signed form coefficients are both retained. -/
theorem integral_apply_basis_change (b b' : Basis ι ℝ E) (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    (∫ x, ω x b' ∂b'.addHaar) = (b.det b' / |b.det b'|) * ∫ x, ω x b ∂b.addHaar := by
  rw [addHaar_eq_smul_of_basis b b', integral_smul_measure]
  simp_rw [ContinuousAlternatingMap.apply_eq_det_mul (b := b) (v := b')]
  rw [integral_const_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  simp only [smul_eq_mul]
  field_simp

/-- The actual integral of a top-form coefficient is invariant under an orientation-compatible
basis change. The compensating Haar normalization is essential. -/
theorem integral_apply_eq_of_orientation_eq (b b' : Basis ι ℝ E)
    (ho : b.orientation = b'.orientation) (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    (∫ x, ω x b ∂b.addHaar) = ∫ x, ω x b' ∂b'.addHaar := by
  have hd : 0 < b.det b' := (b.orientation_eq_iff_det_pos b').mp ho
  rw [integral_apply_basis_change b b' ω, abs_of_pos hd, div_self hd.ne', one_mul]

/-- The actual signed coefficient integral is independent of an arbitrary basis. The model
orientation is fixed; the relative basis sign handles both determinant signs and dimension zero. -/
theorem integral_signed_apply_eq (o : Orientation ℝ E ι) (b b' : Basis ι ℝ E)
    (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    (Orientation.signBasis o b : ℝ) * (∫ x, ω x b ∂b.addHaar) =
      (Orientation.signBasis o b' : ℝ) * (∫ x, ω x b' ∂b'.addHaar) := by
  rw [integral_apply_basis_change b b' ω, ← mul_assoc,
    Orientation.signBasis_mul_det_div_abs]

omit [DecidableEq ι] in
/-- Top-form coefficient integrability is independent of the basis and its Haar normalization. -/
theorem integrable_apply_basis_iff (b b' : Basis ι ℝ E)
    (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    Integrable (fun x ↦ ω x b') b'.addHaar ↔ Integrable (fun x ↦ ω x b) b.addHaar := by
  classical
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  rw [addHaar_eq_smul_of_basis b b', integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero hd))) ENNReal.ofReal_ne_top]
  simp_rw [ContinuousAlternatingMap.apply_eq_det_mul (b := b) (v := b')]
  exact integrable_const_mul_iff (b.isUnit_det b') _

end Module.Basis
