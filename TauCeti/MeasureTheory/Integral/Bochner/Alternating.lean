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
public import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Basis independence of alternating-form integrals

A basis determines a real top-degree coefficient and normalized Haar measure. Their integral
changes by the orientation sign of the basis change. Relative orientation signs make it
independent of an arbitrary basis, including negative orientations in dimension zero.
The Lebesgue integral of the absolute value of a coefficient is independent of the basis outright:
the absolute determinant of the basis change cancels the Haar rescaling. This is the coordinate
expression of the measure of a top form. Over a product of measurable sets, a coefficient integral
whose integrand factors in a product basis is the product of the factor integrals
(`Module.Basis.setLIntegral_ofReal_abs_apply_prod`).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Module.Basis

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

omit [DecidableEq ι] in
/-- The Lebesgue integral of the absolute value of a top-form coefficient against the Haar measure
normalized by the same basis does not depend on the basis. -/
theorem setLIntegral_ofReal_abs_apply_basis_change (b b' : Basis ι ℝ E)
    (ω : E → E [⋀^ι]→L[ℝ] ℝ) (s : Set E) :
    ∫⁻ x in s, ENNReal.ofReal |ω x b'| ∂b'.addHaar =
      ∫⁻ x in s, ENNReal.ofReal |ω x b| ∂b.addHaar := by
  classical
  rw [addHaar_eq_smul_of_basis b b', Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  rw [ContinuousAlternatingMap.apply_eq_det_mul (ω x) b b', ← ENNReal.ofReal_mul (abs_nonneg _),
    ← abs_mul, ← mul_assoc, inv_mul_cancel₀ (b.isUnit_det b').ne_zero, one_mul]

section Prod

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k l p : ℕ}

/-- A top-form coefficient integral over a product set whose integrand factors in the product
basis is the product of the factor integrals. The Borel structure on `E × F` is arbitrary, so this
applies to the chart measurable structure of `TauCeti.RoughForm.measure`. -/
theorem setLIntegral_ofReal_abs_apply_prod [MeasurableSpace F] [BorelSpace F]
    [mEF : MeasurableSpace (E × F)] [BorelSpace (E × F)] (hp : k + l = p)
    (b₀ : Basis (Fin p) ℝ (E × F)) (b₁ : Basis (Fin k) ℝ E) (b₂ : Basis (Fin l) ℝ F)
    {A₁ : Set E} {A₂ : Set F} (hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂)
    (ψ : E × F → (E × F) [⋀^Fin p]→L[ℝ] ℝ) {f : E → ℝ≥0∞} {g : F → ℝ≥0∞}
    (hf : AEMeasurable f (b₁.addHaar.restrict A₁)) (hg : AEMeasurable g (b₂.addHaar.restrict A₂))
    (hψ : ∀ z ∈ A₁ ×ˢ A₂, ENNReal.ofReal
      |ψ z ((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr hp)))| = f z.1 * g z.2) :
    ∫⁻ z in A₁ ×ˢ A₂, ENNReal.ofReal |ψ z b₀| ∂b₀.addHaar =
      (∫⁻ y in A₁, f y ∂b₁.addHaar) * ∫⁻ z in A₂, g z ∂b₂.addHaar := by
  have : FiniteDimensional ℝ F := b₂.finiteDimensional_of_finite
  obtain rfl : mEF = Prod.instMeasurableSpace :=
    BorelSpace.measurable_eq.trans (Prod.borelSpace (α := E) (β := F)).measurable_eq.symm
  rw [setLIntegral_ofReal_abs_apply_basis_change
      ((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr hp))),
    setLIntegral_congr_fun (hA₁.prod hA₂) hψ, addHaar_reindex, prod_addHaar,
    ← Measure.prod_restrict, lintegral_prod_mul hf hg]

end Prod

end Module.Basis
