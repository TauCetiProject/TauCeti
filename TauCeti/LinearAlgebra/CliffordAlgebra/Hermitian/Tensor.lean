/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Complexification
public import TauCeti.Analysis.InnerProductSpace.TensorProduct
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Representation
public import TauCeti.LinearAlgebra.CliffordAlgebra.SpinorForms

/-!
# The spinor endomorphism and spinor tensor metrics vs the exterior Gram metric

For a full complex spinor representation `ρ : Cl_ℂ(V) ≃ End_ℂ(S)` of a finite-dimensional real
inner product space `V` with negative-definite quadratic form `Q(v) = -‖v‖²` and skew-adjoint real
Clifford generators, the identification `ρ.cliffordFormsEquivEnd` of complexified exterior forms
`ℂ ⊗[ℝ] ⋀ V` with spinor endomorphisms `End_ℂ(S)` is an isometry from the complexified Euclidean
exterior Gram metric `LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra` to
the normalized Hilbert–Schmidt pairing `2 ^ (-ℓ) tr(A† B)` (`dim V = 2ℓ`).

Composing with inverse evaluation identifies endomorphisms with `S ⊗ S*` via
`ρ.cliffordFormsEquivTensor`. Because the ordinary tensor/dual metric `tensorDualMetric ℂ S S`
(using the positive Riesz dual metric on `S*`) equals the **unnormalized** Hilbert–Schmidt metric,
`ρ.cliffordFormsEquivTensor` multiplies the exterior Gram metric by `2 ^ ℓ` (which is `1` in
dimension zero). Both the basis-indexed statements on `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` and the
basis-free statements on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` are recorded below.

## Main results

* `CliffordAlgebra.tensorDualMetric_equivExterior_symm` and
  `CliffordAlgebra.exteriorGram_eq_inv_two_pow_mul_tensorDualMetric`: basis-indexed comparisons on
  `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)`.
* `AlgEquiv.inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_mul`: `ρ.cliffordFormsEquivEnd` is
  an isometry from the complexified exterior Gram metric to `2 ^ (-dim V / 2) * tr(A† B)`.
* `AlgEquiv.tensorDualMetric_cliffordFormsEquivTensor`,
  `AlgEquiv.inv_two_pow_mul_tensorDualMetric_cliffordFormsEquivTensor`, and
  `AlgEquiv.sesqComplexification_cliffordFormsEquivTensor_symm`: basis-free comparisons between the
  complexified exterior Gram metric and `tensorDualMetric ℂ S S` under `ρ.cliffordFormsEquivTensor`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open Module InnerProductSpace
open scoped TensorProduct

namespace CliffordAlgebra

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
  (hρ : ∀ v : V, (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
    -ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))
  {I : Type*} [Fintype I] [LinearOrder I] (e : OrthonormalBasis I ℝ V)

include hQ hρ

/-- The ordinary spinor tensor metric is `2 ^ (dim V / 2)` times the exterior Gram metric
under the inverse Chevalley map, the full spinor action and inverse evaluation. -/
theorem tensorDualMetric_equivExterior_symm
    (a b : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) :
    tensorDualMetric ℂ S S
      (TensorProduct.comm ℂ (Dual ℂ S) S
        ((dualTensorHomEquiv ℂ S S).symm (ρ ((equivExterior (Q.baseChange ℂ)).symm a))))
      (TensorProduct.comm ℂ (Dual ℂ S) S
        ((dualTensorHomEquiv ℂ S S).symm (ρ ((equivExterior (Q.baseChange ℂ)).symm b)))) =
      (2 ^ (finrank ℝ V / 2) : ℂ) * Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ)
        (e.toBasis.baseChange ℂ).ExteriorAlgebra (e.toBasis.baseChange ℂ).ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) ℂ) a b := by
  have : FiniteDimensional ℝ V := Module.Finite.of_basis e.toBasis
  rw [tensorDualMetric_eq_trace]
  simp only [TensorProduct.comm_comm, dualTensorHom_dualTensorHomEquiv_symm]
  have hpair := inv_two_pow_mul_trace_adjoint_map_equivExterior_symm_mul hQ ρ hρ e a b
  have hnonzero : (2 ^ (finrank ℝ V / 2) : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    _ = (2 ^ (finrank ℝ V / 2) : ℂ) *
        ((2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * LinearMap.trace ℂ S
          ((ρ ((equivExterior (Q.baseChange ℂ)).symm a)).adjoint *
            ρ ((equivExterior (Q.baseChange ℂ)).symm b))) := by
      rw [← mul_assoc, mul_inv_cancel₀ hnonzero, one_mul, Module.End.mul_eq_comp]
    _ = _ := by rw [hpair]

/-- In the inverse direction, the exterior Gram pairing is `2 ^ (-dim V / 2)` times the
ordinary tensor/dual pairing. This also pins the squared-norm normalization. -/
theorem exteriorGram_eq_inv_two_pow_mul_tensorDualMetric
    (a b : S ⊗[ℂ] Dual ℂ S) :
    Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ)
      (e.toBasis.baseChange ℂ).ExteriorAlgebra (e.toBasis.baseChange ℂ).ExteriorAlgebra
      (1 : Matrix (Finset I) (Finset I) ℂ)
      (equivExterior (Q.baseChange ℂ)
        (ρ.symm (dualTensorHom ℂ S S (TensorProduct.comm ℂ S (Dual ℂ S) a))))
      (equivExterior (Q.baseChange ℂ)
        (ρ.symm (dualTensorHom ℂ S S (TensorProduct.comm ℂ S (Dual ℂ S) b)))) =
      (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * tensorDualMetric ℂ S S a b := by
  have : FiniteDimensional ℝ V := Module.Finite.of_basis e.toBasis
  rw [tensorDualMetric_eq_trace]
  have hpair := inv_two_pow_mul_trace_adjoint_map_equivExterior_symm_mul hQ ρ hρ e
    (equivExterior (Q.baseChange ℂ)
      (ρ.symm (dualTensorHom ℂ S S (TensorProduct.comm ℂ S (Dual ℂ S) a))))
    (equivExterior (Q.baseChange ℂ)
      (ρ.symm (dualTensorHom ℂ S S (TensorProduct.comm ℂ S (Dual ℂ S) b))))
  simpa only [LinearEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply,
    Module.End.mul_eq_comp] using hpair.symm

end CliffordAlgebra

namespace AlgEquiv

open CliffordAlgebra

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hρ : ∀ v : V, (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
    -ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))

include hQ hρ

/-- **Isometry from complexified exterior forms to normalized Hilbert–Schmidt endomorphisms**:
`ρ.cliffordFormsEquivEnd` carries the complexified Euclidean exterior Gram metric on
`ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` to `2 ^ (-dim V / 2) * tr(A† B)` on `End_ℂ(S)`. -/
theorem inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_mul
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * LinearMap.trace ℂ S
        ((ρ.cliffordFormsEquivEnd x).adjoint * ρ.cliffordFormsEquivEnd y) =
      LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra x y := by
  have : FiniteDimensional ℝ V := by
    have : Nontrivial (CliffordAlgebra (Q.baseChange ℂ)) :=
      (equivExterior (Q.baseChange ℂ)).toEquiv.nontrivial
    have : Nontrivial (Module.End ℂ S) := ρ.symm.toEquiv.nontrivial
    have : FiniteDimensional ℝ (Module.End ℂ S) := Module.Finite.trans ℂ (Module.End ℂ S)
    let f : V →ₗ[ℝ] Module.End ℂ S :=
      ((ρ.toLinearMap.comp (ι (Q.baseChange ℂ))).restrictScalars ℝ).comp
        (TensorProduct.mk ℝ ℂ V 1)
    refine FiniteDimensional.of_injective f (injective_iff_map_eq_zero _ |>.mpr fun v hv ↦ ?_)
    have hsq : f v * f v = algebraMap ℂ (Module.End ℂ S) (-(‖v‖ ^ 2 : ℝ)) := by
      simp only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        AlgEquiv.toLinearMap_apply, TensorProduct.mk_apply, ← map_mul, ι_sq_scalar,
        QuadraticForm.baseChange_tmul, mul_one, hQ, AlgEquiv.commutes, Complex.real_smul,
        Complex.ofReal_neg, Complex.ofReal_pow]
    rw [hv, zero_mul] at hsq
    have hnorm : (-(‖v‖ ^ 2 : ℝ) : ℂ) = 0 :=
      (map_eq_zero_iff _ (RingHom.injective (algebraMap ℂ (Module.End ℂ S)))).mp hsq.symm
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (Complex.ofReal_eq_zero.mp (neg_eq_zero.mp hnorm)))
  let e := stdOrthonormalBasis ℝ V
  rw [ρ.cliffordFormsEquivEnd_eq_equivExterior_symm_baseChangeEquiv,
    ρ.cliffordFormsEquivEnd_eq_equivExterior_symm_baseChangeEquiv,
    inv_two_pow_mul_trace_adjoint_map_equivExterior_symm_mul hQ ρ hρ e,
    e.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_baseChangeEquiv]

/-- **Spinor tensor metric comparison**: under `ρ.cliffordFormsEquivTensor`, the ordinary
tensor/dual metric `tensorDualMetric ℂ S S` on `S ⊗[ℂ] Dual ℂ S` is `2 ^ (dim V / 2)` times the
complexified Euclidean exterior Gram metric. -/
theorem tensorDualMetric_cliffordFormsEquivTensor
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    tensorDualMetric ℂ S S (ρ.cliffordFormsEquivTensor x) (ρ.cliffordFormsEquivTensor y) =
      (2 ^ (finrank ℝ V / 2) : ℂ) *
        LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra x y := by
  have hnonzero : (2 ^ (finrank ℝ V / 2) : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [tensorDualMetric_eq_trace, ← Module.End.mul_eq_comp,
    ← toLinearMap_dualTensorHomEquiv, LinearEquiv.coe_toLinearMap,
    ρ.dualTensorHomEquiv_comm_cliffordFormsEquivTensor,
    ρ.dualTensorHomEquiv_comm_cliffordFormsEquivTensor,
    ← ρ.inv_two_pow_mul_trace_adjoint_cliffordFormsEquivEnd_mul hQ hρ,
    mul_inv_cancel_left₀ hnonzero]

/-- **Normalized spinor tensor metric comparison**: `2 ^ (-dim V / 2)` times
`tensorDualMetric ℂ S S` pulls back under `ρ.cliffordFormsEquivTensor` to the complexified
Euclidean exterior Gram metric. -/
theorem inv_two_pow_mul_tensorDualMetric_cliffordFormsEquivTensor
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ *
        tensorDualMetric ℂ S S (ρ.cliffordFormsEquivTensor x) (ρ.cliffordFormsEquivTensor y) =
      LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra x y := by
  have hnonzero : (2 ^ (finrank ℝ V / 2) : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [ρ.tensorDualMetric_cliffordFormsEquivTensor hQ hρ, inv_mul_cancel_left₀ hnonzero]

/-- **Inverse spinor tensor metric comparison**: `ρ.cliffordFormsEquivTensor.symm` carries
`2 ^ (-dim V / 2)` times `tensorDualMetric ℂ S S` to the complexified Euclidean exterior Gram
metric. -/
theorem sesqComplexification_cliffordFormsEquivTensor_symm
    (a b : S ⊗[ℂ] Dual ℂ S) :
    LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra
        (ρ.cliffordFormsEquivTensor.symm a) (ρ.cliffordFormsEquivTensor.symm b) =
      (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * tensorDualMetric ℂ S S a b := by
  rw [← ρ.inv_two_pow_mul_tensorDualMetric_cliffordFormsEquivTensor hQ hρ,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end AlgEquiv
