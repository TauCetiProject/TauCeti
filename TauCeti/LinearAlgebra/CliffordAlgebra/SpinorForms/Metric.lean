/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorAlgebra.HermitianMetric
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Tensor
public import TauCeti.LinearAlgebra.CliffordAlgebra.SpinorForms.Basic

/-!
# Metric comparison for complexified exterior forms and spinor modules

Let `V` be a finite-dimensional real inner product space with `Q v = -‖v‖²`, and let `S` be a
finite-dimensional complex inner product space carrying a full spinor representation
`ρ : Cℓ(ℂ ⊗ V, Q_ℂ) ≃ₐ[ℂ] End_ℂ S` in which real vectors act skew-adjointly. Existence of `ρ`
forces `dim V` to be even (`CliffordAlgebra.even_finrank_of_algEquiv_end`), including `dim V = 0`
where `2 ^ (0 / 2) = 1`.

Combining the basis-free complexified exterior Gram metric
`(ExteriorAlgebra.gramForm V).sesqComplexification` on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` with the
Clifford scalar-trace and tensor-metric comparisons yields basis-free metric identities for
`AlgEquiv.cliffordFormsEquivEnd` and `AlgEquiv.cliffordFormsEquivTensor`:

* `AlgEquiv.inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_mul` and
  `AlgEquiv.trace_adjoint_cliffordFormsEquivEnd_mul`: the normalized Hilbert–Schmidt pairing
  `2 ^ (-dim V / 2) * tr(A† B)` on `End_ℂ S` pulls back along `ρ.cliffordFormsEquivEnd` to
  `(ExteriorAlgebra.gramForm V).sesqComplexification`.
* `AlgEquiv.inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_subtype_baseChange`: on
  complexified homogeneous `k`-forms this recovers `(innerₗ (⋀[ℝ]^k V)).sesqComplexification`,
  and `AlgEquiv.trace_adjoint_cliffordFormsEquivEnd_subtype_baseChange_mul_eq_zero_of_ne`:
  distinct degrees are Hilbert–Schmidt orthogonal.
* `AlgEquiv.tensorDualMetric_cliffordFormsEquivTensor`,
  `AlgEquiv.tensorDualMetric_cliffordFormsEquivTensor_subtype_baseChange`, and
  `AlgEquiv.sesqComplexification_gramForm_cliffordFormsEquivTensor_symm`, and
  `AlgEquiv.sesqComplexification_gramForm_cliffordFormsEquivTensor_symm_tmul`: the ordinary spinor
  tensor metric `InnerProductSpace.tensorDualMetric ℂ S S` on `S ⊗[ℂ] Dual ℂ S` equals
  `2 ^ (dim V / 2)` times the complexified exterior Gram metric (and `2 ^ (dim V / 2)` times the
  complexified `k`-form inner product on each homogeneous degree).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open scoped TensorProduct
open CliffordAlgebra InnerProductSpace Module

namespace AlgEquiv

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hρ : ∀ v : V, (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint = -ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))

include hQ hρ

/-- **The normalized Hilbert–Schmidt comparison on complexified exterior forms**: pulling back
`2 ^ (-dim V / 2) * tr(A† B)` along `ρ.cliffordFormsEquivEnd` gives the sesquilinear
complexification of `ExteriorAlgebra.gramForm V`, with no choice of basis. -/
theorem inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_mul
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * LinearMap.trace ℂ S
        ((ρ.cliffordFormsEquivEnd x).adjoint * ρ.cliffordFormsEquivEnd y) =
      LinearMap.BilinForm.sesqComplexification (ExteriorAlgebra.gramForm V) x y := by
  rw [ρ.cliffordFormsEquivEnd_eq_equivExterior_symm_baseChangeEquiv,
    ρ.cliffordFormsEquivEnd_eq_equivExterior_symm_baseChangeEquiv,
    inv_two_pow_mul_trace_adjoint_map_equivExterior_symm_mul hQ ρ hρ (stdOrthonormalBasis ℝ V),
    (stdOrthonormalBasis ℝ V).toLinearMapₛₗ₂_baseChange_exteriorAlgebra_baseChangeEquiv]

/-- **The unnormalized Hilbert–Schmidt pairing on complexified exterior forms** is
`2 ^ (dim V / 2)` times `(ExteriorAlgebra.gramForm V).sesqComplexification`. -/
theorem trace_adjoint_cliffordFormsEquivEnd_mul
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    LinearMap.trace ℂ S ((ρ.cliffordFormsEquivEnd x).adjoint * ρ.cliffordFormsEquivEnd y) =
      (2 ^ (finrank ℝ V / 2) : ℂ) *
        LinearMap.BilinForm.sesqComplexification (ExteriorAlgebra.gramForm V) x y := by
  rw [← ρ.inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_mul hQ hρ x y, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]

/-- **Normalized Hilbert–Schmidt comparison on homogeneous `k`-forms**: on `ℂ ⊗[ℝ] ⋀[ℝ]^k V`,
`2 ^ (-dim V / 2) * tr(A† B)` agrees with `(innerₗ (⋀[ℝ]^k V)).sesqComplexification`. -/
theorem inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_subtype_baseChange {k : ℕ}
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * LinearMap.trace ℂ S
        ((ρ.cliffordFormsEquivEnd ((⋀[ℝ]^k V).subtype.baseChange ℂ x)).adjoint *
          ρ.cliffordFormsEquivEnd ((⋀[ℝ]^k V).subtype.baseChange ℂ y)) =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) x y := by
  rw [ρ.inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_mul hQ hρ,
    ExteriorAlgebra.sesqComplexification_gramForm_subtype_baseChange]

/-- **Distinct exterior degrees are Hilbert–Schmidt orthogonal** under
`ρ.cliffordFormsEquivEnd`. -/
theorem trace_adjoint_cliffordFormsEquivEnd_subtype_baseChange_mul_eq_zero_of_ne
    {k l : ℕ} (hkl : k ≠ l) (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) (y : ℂ ⊗[ℝ] ⋀[ℝ]^l V) :
    LinearMap.trace ℂ S
        ((ρ.cliffordFormsEquivEnd ((⋀[ℝ]^k V).subtype.baseChange ℂ x)).adjoint *
          ρ.cliffordFormsEquivEnd ((⋀[ℝ]^l V).subtype.baseChange ℂ y)) = 0 := by
  rw [ρ.trace_adjoint_cliffordFormsEquivEnd_mul hQ hρ,
    ExteriorAlgebra.sesqComplexification_gramForm_subtype_baseChange_eq_zero hkl x y, mul_zero]

/-- **Spinor tensor metric comparison**: under `ρ.cliffordFormsEquivTensor`, the ordinary tensor
metric `tensorDualMetric ℂ S S` on `S ⊗[ℂ] Dual ℂ S` is `2 ^ (dim V / 2)` times
`(ExteriorAlgebra.gramForm V).sesqComplexification`. -/
theorem tensorDualMetric_cliffordFormsEquivTensor
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    tensorDualMetric ℂ S S (ρ.cliffordFormsEquivTensor x) (ρ.cliffordFormsEquivTensor y) =
      (2 ^ (finrank ℝ V / 2) : ℂ) *
        LinearMap.BilinForm.sesqComplexification (ExteriorAlgebra.gramForm V) x y := by
  rw [ρ.cliffordFormsEquivTensor_eq_equivExterior_symm_baseChangeEquiv,
    ρ.cliffordFormsEquivTensor_eq_equivExterior_symm_baseChangeEquiv,
    tensorDualMetric_equivExterior_symm hQ ρ hρ (stdOrthonormalBasis ℝ V),
    (stdOrthonormalBasis ℝ V).toLinearMapₛₗ₂_baseChange_exteriorAlgebra_baseChangeEquiv]

/-- **Spinor tensor metric comparison on homogeneous `k`-forms**: on `ℂ ⊗[ℝ] ⋀[ℝ]^k V`,
`tensorDualMetric ℂ S S` under `ρ.cliffordFormsEquivTensor` is `2 ^ (dim V / 2)` times
`(innerₗ (⋀[ℝ]^k V)).sesqComplexification`. -/
theorem tensorDualMetric_cliffordFormsEquivTensor_subtype_baseChange {k : ℕ}
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    tensorDualMetric ℂ S S
        (ρ.cliffordFormsEquivTensor ((⋀[ℝ]^k V).subtype.baseChange ℂ x))
        (ρ.cliffordFormsEquivTensor ((⋀[ℝ]^k V).subtype.baseChange ℂ y)) =
      (2 ^ (finrank ℝ V / 2) : ℂ) *
        LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) x y := by
  rw [ρ.tensorDualMetric_cliffordFormsEquivTensor hQ hρ,
    ExteriorAlgebra.sesqComplexification_gramForm_subtype_baseChange]

/-- **Inverse spinor tensor metric comparison**: under `ρ.cliffordFormsEquivTensor.symm`, the
complexified exterior Gram metric is `2 ^ (-dim V / 2)` times `tensorDualMetric ℂ S S`. -/
theorem sesqComplexification_gramForm_cliffordFormsEquivTensor_symm
    (u v : S ⊗[ℂ] Dual ℂ S) :
    LinearMap.BilinForm.sesqComplexification (ExteriorAlgebra.gramForm V)
        (ρ.cliffordFormsEquivTensor.symm u) (ρ.cliffordFormsEquivTensor.symm v) =
      (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * tensorDualMetric ℂ S S u v := by
  have h := ρ.tensorDualMetric_cliffordFormsEquivTensor hQ hρ
    (ρ.cliffordFormsEquivTensor.symm u) (ρ.cliffordFormsEquivTensor.symm v)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  rw [h, inv_mul_cancel_left₀ (pow_ne_zero _ two_ne_zero)]

/-- **The inverse spinor tensor metric comparison on pure tensors**: the complexified exterior
Gram pairing of the forms of `s₁ ⊗ₜ φ₁` and `s₂ ⊗ₜ φ₂` is `2 ^ (-dim V / 2)` times
`⟪s₁, s₂⟫ * dualMetric ℂ S φ₁ φ₂`. -/
theorem sesqComplexification_gramForm_cliffordFormsEquivTensor_symm_tmul
    (s₁ s₂ : S) (φ₁ φ₂ : Dual ℂ S) :
    LinearMap.BilinForm.sesqComplexification (ExteriorAlgebra.gramForm V)
        (ρ.cliffordFormsEquivTensor.symm (s₁ ⊗ₜ φ₁))
        (ρ.cliffordFormsEquivTensor.symm (s₂ ⊗ₜ φ₂)) =
      (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * (inner ℂ s₁ s₂ * dualMetric ℂ S φ₁ φ₂) := by
  rw [ρ.sesqComplexification_gramForm_cliffordFormsEquivTensor_symm hQ hρ, tensorDualMetric_tmul]

end AlgEquiv
