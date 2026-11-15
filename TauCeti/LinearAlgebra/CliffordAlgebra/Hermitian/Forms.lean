/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorAlgebra
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Tensor
public import TauCeti.LinearAlgebra.CliffordAlgebra.SpinorForms

/-!
# Basis-free Hermitian metric comparisons for spinor forms

For a finite-dimensional real inner product space `V` with geometric Clifford quadratic form
`Q v = -‖v‖²` and a full complex spinor representation
`ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S` on a Hermitian spinor module `S`
whose real vector generators act skew-adjointly, `AlgEquiv.cliffordFormsEquivEnd` identifies the
native complexified exterior algebra `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` with `Module.End ℂ S`, and
`AlgEquiv.cliffordFormsEquivTensor` identifies it with `S ⊗[ℂ] Dual ℂ S`.

Combining the basis-free exterior Gram metric `(TauCeti.ExteriorAlgebra.gramBilinForm V)` and its
sesquilinear complexification with the scalar-trace and spinor-tensor identities gives basis-free
metric comparisons across all degrees:

* `AlgEquiv.cliffordFormsEquivEnd` is an isometry from
  `(TauCeti.ExteriorAlgebra.gramBilinForm V).sesqComplexification` to the normalized
  Hilbert–Schmidt pairing `2 ^ (-dim V / 2) * tr(A† B)`;
* in homogeneous degree `k`, this pairing recovers
  `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))`, and distinct degrees are
  Hilbert–Schmidt orthogonal;
* under `AlgEquiv.cliffordFormsEquivTensor`, the ordinary product metric
  `InnerProductSpace.tensorDualMetric ℂ S S` (built from the spinor inner product on `S` and the
  Riesz dual metric `InnerProductSpace.dualMetric ℂ S` on `Dual ℂ S`) is `2 ^ (dim V / 2)` times
  `(TauCeti.ExteriorAlgebra.gramBilinForm V).sesqComplexification`.

## Main results

* `AlgEquiv.inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_mul` and
  `AlgEquiv.trace_adjoint_cliffordFormsEquivEnd_mul`: normalized and unnormalized Hilbert–Schmidt
  comparisons for `cliffordFormsEquivEnd`.
* `AlgEquiv.inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_subtype_baseChange_mul` and
  `AlgEquiv.trace_adjoint_cliffordFormsEquivEnd_subtype_baseChange_mul_eq_zero_of_ne`: degree-`k`
  restriction and Hilbert–Schmidt orthogonality of distinct exterior degrees.
* `AlgEquiv.tensorDualMetric_cliffordFormsEquivTensor`,
  `AlgEquiv.sesqComplexification_gramBilinForm_cliffordFormsEquivTensor_symm`, and
  `AlgEquiv.sesqComplexification_gramBilinForm_cliffordFormsEquivTensor_symm_tmul`: comparisons
  between `(gramBilinForm V).sesqComplexification` and `tensorDualMetric ℂ S S` (including its
  factorization on pure spinor tensors via `dualMetric ℂ S`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* N. Berline, E. Getzler, and M. Vergne, *Heat Kernels and Dirac Operators* (2004), §3.2.
-/

public section

noncomputable section

open CliffordAlgebra InnerProductSpace Module
open scoped TensorProduct

namespace AlgEquiv

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hρ : ∀ v : V, (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
    -ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))

include hQ hρ

/-- **Basis-free normalized Hilbert–Schmidt isometry**: `cliffordFormsEquivEnd` carries the
complexified exterior Gram metric `(gramBilinForm V).sesqComplexification` to
`2 ^ (-dim V / 2) * tr(A† B)`. -/
theorem inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_mul
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * LinearMap.trace ℂ S
        ((ρ.cliffordFormsEquivEnd x).adjoint * ρ.cliffordFormsEquivEnd y) =
      (TauCeti.ExteriorAlgebra.gramBilinForm V).sesqComplexification x y := by
  let e := stdOrthonormalBasis ℝ V
  rw [ρ.cliffordFormsEquivEnd_eq_equivExterior_symm_baseChangeEquiv x,
    ρ.cliffordFormsEquivEnd_eq_equivExterior_symm_baseChangeEquiv y,
    inv_two_pow_mul_trace_adjoint_map_equivExterior_symm_mul hQ ρ hρ e,
    TauCeti.ExteriorAlgebra.toLinearMapₛₗ₂_baseChange_exteriorAlgebra_baseChangeEquiv e]

/-- **Unnormalized Hilbert–Schmidt pairing** on complexified forms: `tr(A† B)` is
`2 ^ (dim V / 2)` times `(gramBilinForm V).sesqComplexification`. -/
theorem trace_adjoint_cliffordFormsEquivEnd_mul
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    LinearMap.trace ℂ S ((ρ.cliffordFormsEquivEnd x).adjoint * ρ.cliffordFormsEquivEnd y) =
      (2 ^ (finrank ℝ V / 2) : ℂ) *
        (TauCeti.ExteriorAlgebra.gramBilinForm V).sesqComplexification x y := by
  have h2 : (2 ^ (finrank ℝ V / 2) : ℂ) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [← ρ.inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_mul hQ hρ x y, ← mul_assoc,
    mul_inv_cancel₀ h2, one_mul]

/-- **Degree-`k` Hilbert–Schmidt comparison**: on `ℂ ⊗[ℝ] ⋀[ℝ]^k V`, the normalized
Hilbert–Schmidt pairing of `cliffordFormsEquivEnd` recovers
`LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))`. -/
theorem inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_subtype_baseChange_mul
    {k : ℕ} (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * LinearMap.trace ℂ S
        ((ρ.cliffordFormsEquivEnd ((⋀[ℝ]^k V).subtype.baseChange ℂ x)).adjoint *
          ρ.cliffordFormsEquivEnd ((⋀[ℝ]^k V).subtype.baseChange ℂ y)) =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) x y := by
  rw [ρ.inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_mul hQ hρ,
    TauCeti.ExteriorAlgebra.sesqComplexification_gramBilinForm_subtype_baseChange]

/-- **Distinct exterior degrees are Hilbert–Schmidt orthogonal** under `cliffordFormsEquivEnd`. -/
theorem trace_adjoint_cliffordFormsEquivEnd_subtype_baseChange_mul_eq_zero_of_ne
    {p q : ℕ} (hpq : p ≠ q) (x : ℂ ⊗[ℝ] ⋀[ℝ]^p V) (y : ℂ ⊗[ℝ] ⋀[ℝ]^q V) :
    LinearMap.trace ℂ S
        ((ρ.cliffordFormsEquivEnd ((⋀[ℝ]^p V).subtype.baseChange ℂ x)).adjoint *
          ρ.cliffordFormsEquivEnd ((⋀[ℝ]^q V).subtype.baseChange ℂ y)) = 0 := by
  rw [ρ.trace_adjoint_cliffordFormsEquivEnd_mul hQ hρ,
    TauCeti.ExteriorAlgebra.sesqComplexification_gramBilinForm_subtype_baseChange_eq_zero_of_ne
      hpq x y,
    mul_zero]

/-- **Spinor tensor metric comparison**: under `cliffordFormsEquivTensor`, the ordinary product
metric `tensorDualMetric ℂ S S` on `S ⊗[ℂ] Dual ℂ S` is `2 ^ (dim V / 2)` times the complexified
exterior Gram metric `(gramBilinForm V).sesqComplexification`. -/
theorem tensorDualMetric_cliffordFormsEquivTensor
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    tensorDualMetric ℂ S S (ρ.cliffordFormsEquivTensor x) (ρ.cliffordFormsEquivTensor y) =
      (2 ^ (finrank ℝ V / 2) : ℂ) *
        (TauCeti.ExteriorAlgebra.gramBilinForm V).sesqComplexification x y := by
  let e := stdOrthonormalBasis ℝ V
  rw [ρ.cliffordFormsEquivTensor_eq_equivExterior_symm_baseChangeEquiv x,
    ρ.cliffordFormsEquivTensor_eq_equivExterior_symm_baseChangeEquiv y,
    tensorDualMetric_equivExterior_symm hQ ρ hρ e,
    TauCeti.ExteriorAlgebra.toLinearMapₛₗ₂_baseChange_exteriorAlgebra_baseChangeEquiv e]

/-- **Inverse spinor tensor metric comparison**: on `S ⊗[ℂ] Dual ℂ S`, pulling
`(gramBilinForm V).sesqComplexification` back along `cliffordFormsEquivTensor.symm` gives
`2 ^ (-dim V / 2)` times `tensorDualMetric ℂ S S`. -/
theorem sesqComplexification_gramBilinForm_cliffordFormsEquivTensor_symm
    (a b : S ⊗[ℂ] Dual ℂ S) :
    (TauCeti.ExteriorAlgebra.gramBilinForm V).sesqComplexification
        (ρ.cliffordFormsEquivTensor.symm a) (ρ.cliffordFormsEquivTensor.symm b) =
      (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * tensorDualMetric ℂ S S a b := by
  have h2 : (2 ^ (finrank ℝ V / 2) : ℂ) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h := ρ.tensorDualMetric_cliffordFormsEquivTensor hQ hρ
    (ρ.cliffordFormsEquivTensor.symm a) (ρ.cliffordFormsEquivTensor.symm b)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]

/-- On pure spinor tensors `s₁ ⊗ₜ φ₁` and `s₂ ⊗ₜ φ₂`, the exterior Gram pairing of their
corresponding forms is `2 ^ (-dim V / 2)` times `⟪s₁, s₂⟫ * dualMetric ℂ S φ₁ φ₂`. -/
theorem sesqComplexification_gramBilinForm_cliffordFormsEquivTensor_symm_tmul
    (s₁ s₂ : S) (φ₁ φ₂ : Dual ℂ S) :
    (TauCeti.ExteriorAlgebra.gramBilinForm V).sesqComplexification
        (ρ.cliffordFormsEquivTensor.symm (s₁ ⊗ₜ φ₁))
        (ρ.cliffordFormsEquivTensor.symm (s₂ ⊗ₜ φ₂)) =
      (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * (inner ℂ s₁ s₂ * dualMetric ℂ S φ₁ φ₂) := by
  rw [ρ.sesqComplexification_gramBilinForm_cliffordFormsEquivTensor_symm hQ hρ,
    tensorDualMetric_tmul]

end AlgEquiv
