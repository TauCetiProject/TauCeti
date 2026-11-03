/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.Module.Equiv.Pi

/-!
# The cofactor contraction for continuous linear automorphisms of `ι → R`

For a continuous linear automorphism `L` of `ι → R`, write `(L⁻¹)ⱼᵢ = L.symm (Pi.single i 1) j`
for the `(j, i)` entry of the matrix of `L⁻¹`, so that `det L • L⁻¹` is the cofactor (adjugate)
matrix of `L`. Contracting a family of continuous linear maps `F' i` precomposed with `L` against
this matrix and taking the trace recovers `det L` times the trace of `F'`:

`∑ j, (det L • ∑ i, (L⁻¹)ⱼᵢ • F' i ∘ L) (Pi.single j 1) = det L • ∑ i, F' i (Pi.single i 1)`,

because `∑ j, (L⁻¹)ⱼᵢ • L (Pi.single j 1) = L (L⁻¹ (Pi.single i 1)) = Pi.single i 1`. With `F' i`
the derivative of the `i`-th component of a flux field, this is the pointwise Piola identity of
the affine cofactor pullback, `ContinuousLinearEquiv.sum_fderiv_affineFluxPullback`.

## Main declarations

* `ContinuousLinearEquiv.sum_cofactor_comp_apply_single`: the cofactor contraction identity.
-/

public section

namespace ContinuousLinearEquiv

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
