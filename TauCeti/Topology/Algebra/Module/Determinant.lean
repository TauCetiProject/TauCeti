/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.Module.Equiv.Pi

/-!
# Determinants of continuous linear maps: relative determinants and the cofactor contraction

For continuous linear equivalences `T U : M ≃L[R] N` and a continuous linear map `S : M →L[R] N`,
the determinants on `M` of `T⁻¹ ∘ U`, `U⁻¹ ∘ S` and `T⁻¹ ∘ S` satisfy
`det (T⁻¹ ∘ U) * det (U⁻¹ ∘ S) = det (T⁻¹ ∘ S)`. These relative determinants compare the volumes
of the images of a fixed body under maps into `N` without choosing a volume on `N`.

For a continuous linear automorphism `L` of `ι → R`, write `(L⁻¹)ⱼᵢ = L.symm (Pi.single i 1) j`
for the `(j, i)` entry of the matrix of `L⁻¹`, so that `det L • L⁻¹` is the cofactor (adjugate)
matrix of `L`. Contracting a family of continuous linear maps `F' i` precomposed with `L` against
this matrix and taking the trace recovers `det L` times the trace of `F'`:

`∑ j, (det L • ∑ i, (L⁻¹)ⱼᵢ • F' i ∘ L) (Pi.single j 1) = det L • ∑ i, F' i (Pi.single i 1)`,

because `∑ j, (L⁻¹)ⱼᵢ • L (Pi.single j 1) = L (L⁻¹ (Pi.single i 1)) = Pi.single i 1`. With `F' i`
the derivative of the `i`-th component of a flux field, this is the pointwise Piola identity of
the affine cofactor pullback, `ContinuousLinearEquiv.sum_fderiv_affineFluxPullback`.

## Main declarations

* `ContinuousLinearMap.det_id`, `ContinuousLinearMap.det_smul`: the determinant of the identity
  and of a scalar multiple.
* `ContinuousLinearEquiv.det_symm_comp_mul_det_symm_comp`: relative determinants multiply.
* `ContinuousLinearEquiv.sum_cofactor_comp_apply_single`: the cofactor contraction identity.
-/

public section

namespace ContinuousLinearMap

variable {R M : Type*} [CommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

/-- The identity has determinant one. -/
@[simp]
theorem det_id : (ContinuousLinearMap.id R M).det = 1 :=
  LinearMap.det_id

/-- Multiplying a map by a scalar `c` multiplies its determinant by `c ^ finrank R M`. -/
@[simp]
theorem det_smul [ContinuousConstSMul R M] [Module.Free R M] (c : R) (f : M →L[R] M) :
    (c • f).det = c ^ Module.finrank R M * f.det :=
  LinearMap.det_smul c (f : M →ₗ[R] M)

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section Relative

variable {R M N : Type*} [CommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [TopologicalSpace N] [AddCommGroup N] [Module R N]

/-- Determinants relative to equivalences `M ≃L[R] N` multiply: comparing `S` with `T` is
comparing `U` with `T` and then `S` with `U`. -/
theorem det_symm_comp_mul_det_symm_comp (T U : M ≃L[R] N) (S : M →L[R] N) :
    ((T.symm : N →L[R] M).comp (U : M →L[R] N)).det * ((U.symm : N →L[R] M).comp S).det =
      ((T.symm : N →L[R] M).comp S).det := by
  have h : ((T.symm : N →L[R] M).comp (U : M →L[R] N)).comp ((U.symm : N →L[R] M).comp S) =
      (T.symm : N →L[R] M).comp S := by
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc _ (U.symm : N →L[R] M),
      U.coe_comp_coe_symm, ContinuousLinearMap.id_comp]
  rw [← h]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]

end Relative

variable {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]

/-- The cofactor contraction identity: the trace of the cofactor transform
`det L • ∑ i, (L⁻¹)ⱼᵢ • (F' i ∘ L)` of a family `F'` of continuous linear maps is `det L` times
the trace `∑ i, F' i (Pi.single i 1)`, as
`∑ j, (L⁻¹)ⱼᵢ • L (Pi.single j 1) = L (L⁻¹ (Pi.single i 1)) = Pi.single i 1`. -/
theorem sum_cofactor_comp_apply_single (L : (ι → R) ≃L[R] (ι → R))
    (F' : ι → (ι → R) →L[R] M) :
    ∑ j, (LinearMap.det (L : (ι → R) →ₗ[R] ι → R) •
        ∑ i, L.symm (Pi.single i 1) j • (F' i).comp (L : (ι → R) →L[R] ι → R))
          (Pi.single j 1) =
      LinearMap.det (L : (ι → R) →ₗ[R] ι → R) • ∑ i, F' i (Pi.single i 1) := by
  simp only [_root_.smul_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- Pull the coefficients through the linear map `F' i ∘ L`, then expand `L⁻¹ (Pi.single i 1)`
  -- in the standard basis.
  calc ∑ j, L.symm (Pi.single i 1) j • F' i (L (Pi.single j 1))
      _ = F' i (L (∑ j, L.symm (Pi.single i 1) j • Pi.single j 1)) := by
        simp only [map_sum, map_smul, ContinuousLinearMap.map_smul]
      _ = F' i (Pi.single i 1) := by rw [← pi_eq_sum_univ', apply_symm_apply]

end ContinuousLinearEquiv
