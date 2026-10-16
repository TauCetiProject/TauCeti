/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.TopDegree
public import TauCeti.LinearAlgebra.Orientation.Basis

/-!
# Basis-independent signed top-form integrals

An arbitrary basis determines a coefficient and normalized Haar measure. Its sign relative to
an actual model orientation compensates for a reversing basis change. This includes empty bases:
the negative orientation in dimension zero has no positively oriented basis, but its signed
integral is still defined using any basis. No new orientation carrier is introduced.
-/

public section

noncomputable section

open MeasureTheory


namespace Module.Basis

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]

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

omit [FiniteDimensional ℝ E] in
/-- Multiplication by the relative orientation sign preserves genuine integrability. -/
theorem integrable_signed_apply_iff (o : Orientation ℝ E ι) (b : Basis ι ℝ E)
    (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    Integrable (fun x ↦ (Orientation.signBasis o b : ℝ) * ω x b) b.addHaar ↔
      Integrable (fun x ↦ ω x b) b.addHaar := by
  apply integrable_const_mul_iff
  apply isUnit_iff_ne_zero.mpr
  exact_mod_cast (Orientation.signBasis o b).ne_zero

end Module.Basis
