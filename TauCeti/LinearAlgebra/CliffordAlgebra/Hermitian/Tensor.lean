/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Representation
public import TauCeti.Analysis.InnerProductSpace.TensorProduct

/-!
# The spinor tensor metric and the exterior metric

For a full complex spinor representation `ρ : Cl(V) ≃ End(S)`, inverse evaluation identifies
endomorphisms with `S ⊗ S*`. The ordinary tensor metric, using the positive Riesz dual metric,
is the **unnormalized** Hilbert–Schmidt metric. Consequently the inverse Chevalley map,
followed by `ρ` and inverse evaluation, multiplies the exterior Gram metric by `2 ^ ℓ`,
where `dim V = 2ℓ`. The factor is one in dimension zero.

We state the comparison using Mathlib's existing evaluation equivalence and tensor
commutor, rather than introducing a second forms-to-spinor-tensors equivalence. The two
equations below give both the pullback of the tensor metric and the inverse metric comparison.
They use the same increasing orthonormal wedge basis as the exterior Gram metric.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open Module InnerProductSpace
open scoped TensorProduct

namespace CliffordAlgebra

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V}
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
  rw [tensorDualMetric_eq_trace]
  have hpair := inv_two_pow_mul_trace_adjoint_map_equivExterior_symm_mul hQ ρ hρ e
    (equivExterior (Q.baseChange ℂ)
      (ρ.symm (dualTensorHom ℂ S S (TensorProduct.comm ℂ S (Dual ℂ S) a))))
    (equivExterior (Q.baseChange ℂ)
      (ρ.symm (dualTensorHom ℂ S S (TensorProduct.comm ℂ S (Dual ℂ S) b))))
  simpa only [LinearEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply,
    Module.End.mul_eq_comp] using hpair.symm

end CliffordAlgebra
