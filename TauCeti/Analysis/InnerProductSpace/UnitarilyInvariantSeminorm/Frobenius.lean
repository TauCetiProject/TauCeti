/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.KyFan

/-!
# The Frobenius seminorm

For a linear map `A : E →ₗ[𝕜] F` out of a finite-dimensional inner product space, the sum
`∑ᵢ ‖A bᵢ‖²` over an orthonormal basis `(bᵢ)` of `E` does not depend on the basis; when `F` is
finite-dimensional it is the trace of `A† A`. Its square root is the **Frobenius seminorm** (the
Hilbert–Schmidt norm) `‖A‖_F = √(∑ᵢ ‖A bᵢ‖²)`, the Euclidean norm of the tuple `(A bᵢ)ᵢ`. It is a
unitarily invariant seminorm, and only the source needs to be finite-dimensional. When `F` is
finite-dimensional as well, `‖A‖_F = √(∑ᵢ σᵢ(A)²)` in terms of the singular values, and the
Frobenius seminorm controls the nuclear seminorm with the rank-sharp constant:
`‖A‖₁ ≤ √(rank A) ‖A‖_F`.

## Main declarations

* `LinearMap.trace_adjoint_comp_self_eq_sum_norm_apply_sq`: `tr (A† A) = ∑ᵢ ‖A bᵢ‖²` for every
  orthonormal basis `(bᵢ)`.
* `LinearMap.trace_adjoint_comp_self_eq_sum_sq_singularValues`: `tr (A† A) = ∑ᵢ σᵢ(A)²`.
* `LinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq`: `∑ᵢ ‖A bᵢ‖²` is independent of the
  orthonormal basis.
* `TauCeti.UnitarilyInvariantSeminorm.frobenius`: the Frobenius seminorm.
* `TauCeti.UnitarilyInvariantSeminorm.frobenius_apply`: `‖A‖_F = √(∑ᵢ ‖A bᵢ‖²)` for every
  orthonormal basis `(bᵢ)`.
* `TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues`:
  `‖A‖_F = √(∑ᵢ σᵢ(A)²)`.
* `TauCeti.UnitarilyInvariantSeminorm.nuclear_apply_le_sqrt_finrank_range_mul_frobenius_apply`:
  `‖A‖₁ ≤ √(rank A) ‖A‖_F`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 5.6.
-/

public section

open Module

variable {𝕜 E F ι ι' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Fintype ι] [Fintype ι']

namespace LinearMap

/-- The trace of `A† A` is `∑ᵢ ‖A bᵢ‖²` for every orthonormal basis `(bᵢ)` of the source. -/
theorem trace_adjoint_comp_self_eq_sum_norm_apply_sq [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F)
    (b : OrthonormalBasis ι 𝕜 E) :
    trace 𝕜 E (adjoint A ∘ₗ A) = ((∑ i, ‖A (b i)‖ ^ 2 : ℝ) : 𝕜) := by
  rw [trace_eq_sum_inner _ b, RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]

/-- **Basis independence of the Frobenius sum**: `∑ᵢ ‖A bᵢ‖²` takes the same value on any two
orthonormal bases `(bᵢ)` and `(b'ⱼ)` of the source. -/
theorem sum_norm_apply_sq_eq_sum_norm_apply_sq (A : E →ₗ[𝕜] F) (b : OrthonormalBasis ι 𝕜 E)
    (b' : OrthonormalBasis ι' 𝕜 E) : ∑ i, ‖A (b i)‖ ^ 2 = ∑ i, ‖A (b' i)‖ ^ 2 := by
  -- Corestrict `A` to its range, which is finite-dimensional, and compare both sums with the
  -- trace of `A† A` there.
  have h := (A.rangeRestrict.trace_adjoint_comp_self_eq_sum_norm_apply_sq b).symm.trans
    (A.rangeRestrict.trace_adjoint_comp_self_eq_sum_norm_apply_sq b')
  exact_mod_cast h

end LinearMap

namespace TauCeti.UnitarilyInvariantSeminorm

variable (𝕜 E F)

/-- The coordinates `A ↦ (A bᵢ)ᵢ` of a linear map in the standard orthonormal basis `(bᵢ)` of the
source, as a tuple in the Euclidean product of copies of `F`. -/
private noncomputable def frobeniusCoords :
    (E →ₗ[𝕜] F) →ₗ[𝕜] PiLp 2 (fun _ : Fin (finrank 𝕜 E) ↦ F) :=
  (WithLp.linearEquiv 2 𝕜 _).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i ↦ LinearMap.applyₗ (stdOrthonormalBasis 𝕜 E i)

variable {𝕜 E F} in
private theorem norm_frobeniusCoords (A : E →ₗ[𝕜] F) :
    ‖frobeniusCoords 𝕜 E F A‖ = √(∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) := by
  simp [frobeniusCoords, PiLp.norm_eq_of_L2]

/-- The **Frobenius seminorm** (Hilbert–Schmidt norm) `‖A‖_F = √(∑ᵢ ‖A bᵢ‖²)`, for any orthonormal
basis `(bᵢ)` of the source, as a unitarily invariant seminorm. -/
noncomputable def frobenius : UnitarilyInvariantSeminorm 𝕜 E F where
  toSeminorm := (normSeminorm 𝕜 _).comp (frobeniusCoords 𝕜 E F)
  map_linearIsometryEquiv_comp_comp' U V A := by
    simp only [Seminorm.comp_apply, coe_normSeminorm, norm_frobeniusCoords]
    congr 1
    -- `U` preserves norms, and `V` carries the standard basis to the orthonormal basis `V bᵢ`.
    simpa using A.sum_norm_apply_sq_eq_sum_norm_apply_sq ((stdOrthonormalBasis 𝕜 E).map V)
      (stdOrthonormalBasis 𝕜 E)

variable {𝕜 E F}

private theorem frobenius_apply_eq_norm_frobeniusCoords (A : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F A = ‖frobeniusCoords 𝕜 E F A‖ :=
  (rfl)

/-- The **Frobenius seminorm in an orthonormal basis**: `‖A‖_F = √(∑ᵢ ‖A bᵢ‖²)` for every
orthonormal basis `(bᵢ)` of the source. -/
theorem frobenius_apply (b : OrthonormalBasis ι 𝕜 E) (A : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F A = √(∑ i, ‖A (b i)‖ ^ 2) := by
  rw [← A.sum_norm_apply_sq_eq_sum_norm_apply_sq (stdOrthonormalBasis 𝕜 E) b,
    frobenius_apply_eq_norm_frobeniusCoords, norm_frobeniusCoords]

/-- The square of the Frobenius seminorm is `∑ᵢ ‖A bᵢ‖²` for every orthonormal basis `(bᵢ)` of the
source. -/
theorem sq_frobenius_apply (b : OrthonormalBasis ι 𝕜 E) (A : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F A ^ 2 = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [frobenius_apply b, Real.sq_sqrt (by positivity)]

end TauCeti.UnitarilyInvariantSeminorm

section SingularValues

variable [FiniteDimensional 𝕜 F]

namespace LinearMap

/-- The trace of `A† A` is the sum `∑ᵢ σᵢ(A)²` of the squared singular values of `A`. -/
theorem trace_adjoint_comp_self_eq_sum_sq_singularValues (A : E →ₗ[𝕜] F) :
    trace 𝕜 E (adjoint A ∘ₗ A) = ((A.singularValues.sum fun _ s ↦ s ^ 2 : ℝ) : 𝕜) := by
  rw [A.trace_adjoint_comp_self_eq_sum_norm_apply_sq A.rightSingularBasis]
  simp_rw [norm_apply_rightSingularBasis]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ A.singularValues i ^ 2),
    Finsupp.sum_of_support_subset _ (support_singularValues A ▸
      Finset.range_subset_range.mpr A.finrank_range_le) _ fun _ _ ↦ by simp]

end LinearMap

namespace TauCeti.UnitarilyInvariantSeminorm

/-- The **Frobenius seminorm in terms of singular values**: `‖A‖_F = √(∑ᵢ σᵢ(A)²)`. -/
@[simp]
theorem frobenius_apply_eq_sqrt_sum_sq_singularValues (A : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F A = √(A.singularValues.sum fun _ s ↦ s ^ 2) := by
  rw [frobenius_apply (stdOrthonormalBasis 𝕜 E)]
  congr 1
  exact_mod_cast (A.trace_adjoint_comp_self_eq_sum_norm_apply_sq _).symm.trans
    A.trace_adjoint_comp_self_eq_sum_sq_singularValues

/-- **Rank-sharp comparison of the nuclear and Frobenius seminorms**:
`‖A‖₁ ≤ √(rank A) ‖A‖_F`. -/
theorem nuclear_apply_le_sqrt_finrank_range_mul_frobenius_apply (A : E →ₗ[𝕜] F) :
    nuclear 𝕜 E F A ≤ √(finrank 𝕜 (LinearMap.range A)) * frobenius 𝕜 E F A := by
  rw [nuclear_apply, frobenius_apply_eq_sqrt_sum_sq_singularValues, Finsupp.sum, Finsupp.sum,
    LinearMap.support_singularValues, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.le_sqrt_of_sq_le ?_
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range (finrank 𝕜 (LinearMap.range A)))
    (f := fun i ↦ A.singularValues i)

end TauCeti.UnitarilyInvariantSeminorm

end SingularValues
