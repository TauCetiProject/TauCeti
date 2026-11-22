/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.InnerProductSpace.Trace.Projection
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

In finite orthonormal source and target bases, the Frobenius seminorm equals the Frobenius
norm of the rectangular coordinate matrix, and its square is the sum of the squared moduli of
the matrix coefficients. This connects basis-independent operator estimates to entrywise
calculations: in orthonormal eigenbases, for instance, it turns the coordinate form
`(αᵢ - βⱼ)Xᵢⱼ = Cᵢⱼ` of a Sylvester equation `AX - XB = C` into the bound
`δ ‖X‖_F ≤ ‖C‖_F` under a spectral gap `δ ≤ |αᵢ - βⱼ|`.

## Main declarations

* `LinearMap.trace_adjoint_comp_self_eq_sum_norm_apply_sq`: `tr (A† A) = ∑ᵢ ‖A bᵢ‖²` for every
  orthonormal basis `(bᵢ)`.
* `LinearMap.trace_adjoint_comp_self_eq_sum_sq_singularValues`: `tr (A† A) = ∑ᵢ σᵢ(A)²`.
* `LinearMap.frobenius_norm_toMatrix`, `Matrix.frobenius_toEuclideanLin`: the Frobenius norm of
  the coordinate matrix and of `A.toEuclideanLin` equal the operator Frobenius seminorm.
* `LinearMap.sum_norm_apply_sq_eq_sum_norm_apply_sq`: `∑ᵢ ‖A bᵢ‖²` is independent of the
  orthonormal basis.
* `LinearMap.sum_sq_norm_apply_orthonormal_le`: compression to an orthonormal family
  cannot increase the squared Frobenius sum.
* `TauCeti.UnitarilyInvariantSeminorm.frobenius`: the Frobenius seminorm.
* `TauCeti.UnitarilyInvariantSeminorm.frobenius_apply`: `‖A‖_F = √(∑ᵢ ‖A bᵢ‖²)` for every
  orthonormal basis `(bᵢ)`.
* `TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply_eq_sum_norm_inner_sq`:
  `‖A‖_F² = ∑ᵢ ∑ⱼ ‖⟪cⱼ, A bᵢ⟫‖²` in orthonormal bases `(bᵢ)` of the source and `(cⱼ)` of the
  target.
* `TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues`:
  `‖A‖_F = √(∑ᵢ σᵢ(A)²)`.
* `TauCeti.UnitarilyInvariantSeminorm.frobenius_rankOne`: `‖u ⊗ v‖_F = ‖u‖ ‖v‖`.
* `TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_add` and
  `TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_add_of_re_trace_adjoint_comp_eq_zero`:
  expansion of `‖A + B‖_F²` via the trace pairing `re tr(A† B)` and the Frobenius Pythagorean
  identity.
* `TauCeti.UnitarilyInvariantSeminorm.frobenius_sub_starProjection_comp_le`,
  `TauCeti.UnitarilyInvariantSeminorm.frobenius_sub_normalPart_le`:
  Frobenius contraction of the tangent–normal projection split.
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

omit [FiniteDimensional 𝕜 E] in
/-- **Basis independence of the Frobenius sum**: `∑ᵢ ‖A bᵢ‖²` takes the same value on any two
orthonormal bases `(bᵢ)` and `(b'ⱼ)` of the source. -/
theorem sum_norm_apply_sq_eq_sum_norm_apply_sq (A : E →ₗ[𝕜] F) (b : OrthonormalBasis ι 𝕜 E)
    (b' : OrthonormalBasis ι' 𝕜 E) : ∑ i, ‖A (b i)‖ ^ 2 = ∑ i, ‖A (b' i)‖ ^ 2 := by
  -- Corestrict `A` to its range, which is finite-dimensional, and compare both sums with the
  -- trace of `A† A` there.
  have := b.toBasis.finiteDimensional_of_finite
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

open scoped InnerProductSpace in
/-- The square of the Frobenius seminorm is the sum of the squared moduli of the matrix
coefficients `⟪cⱼ, A bᵢ⟫` in any orthonormal bases `(bᵢ)` of the source and `(cⱼ)` of the
target. -/
theorem sq_frobenius_apply_eq_sum_norm_inner_sq (b : OrthonormalBasis ι 𝕜 E)
    (c : OrthonormalBasis ι' 𝕜 F) (A : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F A ^ 2 = ∑ i, ∑ j, ‖⟪c j, A (b i)⟫_𝕜‖ ^ 2 := by
  simp_rw [sq_frobenius_apply b, c.sum_sq_norm_inner_right]

open scoped InnerProductSpace in
/-- The Frobenius seminorm of a rank-one map `x ↦ ⟪v, x⟫ u` is `‖u‖ * ‖v‖`. -/
@[simp]
theorem frobenius_rankOne (u : F) (v : E) :
    frobenius 𝕜 E F (InnerProductSpace.rankOne 𝕜 u v).toLinearMap = ‖u‖ * ‖v‖ := by
  let b := stdOrthonormalBasis 𝕜 E
  rw [frobenius_apply b]
  have hsum : ∑ i, ‖(InnerProductSpace.rankOne 𝕜 u v) (b i)‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    simp only [InnerProductSpace.rankOne_apply, norm_smul, mul_pow, ← Finset.sum_mul]
    rw [mul_comm, ← b.sum_sq_norm_inner_right v]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [norm_inner_symm]
  simp only [ContinuousLinearMap.coe_coe, hsum, ← mul_pow,
    Real.sqrt_sq (mul_nonneg (norm_nonneg u) (norm_nonneg v))]

end TauCeti.UnitarilyInvariantSeminorm

namespace LinearMap

open scoped InnerProductSpace Matrix.Norms.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The Frobenius norm of the matrix of a rectangular operator in any orthonormal domain and
codomain bases equals its unitarily invariant Frobenius seminorm. -/
@[simp]
theorem frobenius_norm_toMatrix [DecidableEq n] (A : E →ₗ[𝕜] F) (b : OrthonormalBasis n 𝕜 E)
    (c : OrthonormalBasis m 𝕜 F) :
    ‖A.toMatrix b.toBasis c.toBasis‖ = TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F A := by
  symm
  rw [TauCeti.UnitarilyInvariantSeminorm.frobenius_apply b A,
    Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simpa [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, Real.rpow_two] using
    (c.sum_sq_norm_inner_right (A (b i))).symm

end LinearMap

section Matrix

open scoped Matrix.Norms.Frobenius

/-- The Frobenius seminorm of `A.toEuclideanLin` is the scoped Frobenius norm of `A`. -/
theorem _root_.Matrix.frobenius_toEuclideanLin {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n 𝕜) :
    TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜
        (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) A.toEuclideanLin =
      ‖A‖ := by
  classical
  have h := LinearMap.frobenius_norm_toMatrix A.toEuclideanLin
    (EuclideanSpace.basisFun n 𝕜) (EuclideanSpace.basisFun m 𝕜)
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin] at h
  exact h.symm

end Matrix

section SingularValues

variable [FiniteDimensional 𝕜 F]

namespace LinearMap

/-- The trace of `A† A` is the sum `∑ᵢ σᵢ(A)²` of the squared singular values of `A`. -/
theorem trace_adjoint_comp_self_eq_sum_sq_singularValues (A : E →ₗ[𝕜] F) :
    trace 𝕜 E (adjoint A ∘ₗ A) = ((A.singularValues.sum fun _ s ↦ s ^ 2 : ℝ) : 𝕜) := by
  rw [A.trace_adjoint_comp_self_eq_sum_norm_apply_sq A.rightSingularBasis]
  simp_rw [norm_apply_rightSingularBasis]
  rw [A.sum_fin_singularValues (· ^ 2) (by simp)]

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

end TauCeti.UnitarilyInvariantSeminorm

namespace LinearMap

/-- The squared Frobenius seminorm is the sum of the squared singular values. -/
theorem sq_frobenius_apply_eq_sum_sq_singularValues (A : E →ₗ[𝕜] F) :
    TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F A ^ 2 =
      ∑ i : Fin (finrank 𝕜 E), A.singularValues i ^ 2 := by
  rw [TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues,
    ← A.sum_fin_singularValues (· ^ 2) (by simp)]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg (A.singularValues i))

end LinearMap

namespace TauCeti.UnitarilyInvariantSeminorm

open scoped InnerProductSpace in
/-- Expansion of the squared Frobenius seminorm of a sum through the Hilbert–Schmidt trace pairing:
`‖A + B‖_F² = ‖A‖_F² + 2 re tr(A† B) + ‖B‖_F²`. -/
theorem sq_frobenius_add (A B : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F (A + B) ^ 2 =
      frobenius 𝕜 E F A ^ 2 +
        2 * RCLike.re (LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B)) +
        frobenius 𝕜 E F B ^ 2 := by
  let b := stdOrthonormalBasis 𝕜 E
  have htr : 2 * RCLike.re (LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B)) =
      ∑ i, 2 * RCLike.re ⟪A (b i), B (b i)⟫_𝕜 := by
    rw [LinearMap.trace_eq_sum_inner _ b, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  simp only [sq_frobenius_apply b, htr, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.add_apply, norm_add_sq (𝕜 := 𝕜)]

/-- **Frobenius Pythagorean identity**: if `re tr(A† B) = 0`, then
`‖A + B‖_F² = ‖A‖_F² + ‖B‖_F²`. -/
theorem sq_frobenius_add_of_re_trace_adjoint_comp_eq_zero {A B : E →ₗ[𝕜] F}
    (h : RCLike.re (LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B)) = 0) :
    frobenius 𝕜 E F (A + B) ^ 2 = frobenius 𝕜 E F A ^ 2 + frobenius 𝕜 E F B ^ 2 := by
  rw [sq_frobenius_add, h, mul_zero, add_zero]

/-- The tangent part `Δ - P_W Δ P_K` has Frobenius seminorm at most `‖Δ‖_F`. -/
theorem frobenius_sub_starProjection_comp_le (W : Submodule 𝕜 F) (K : Submodule 𝕜 E)
    (Δ : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F (Δ - W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap) ≤
      frobenius 𝕜 E F Δ := by
  set Δ₂ := W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap
  have hpyth := sq_frobenius_add_of_re_trace_adjoint_comp_eq_zero (A := Δ - Δ₂) (B := Δ₂) (by
    rw [Δ.trace_adjoint_comp_eq_zero_sub_starProjection_comp W K, map_zero])
  rw [sub_add_cancel] at hpyth
  have hsq : frobenius 𝕜 E F (Δ - Δ₂) ^ 2 ≤ frobenius 𝕜 E F Δ ^ 2 := by
    rw [hpyth]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact le_of_sq_le_sq hsq (apply_nonneg _ _)

/-- The canonical tangent part `Δ - Θ.normalPart Δ` has Frobenius seminorm at most `‖Δ‖_F`. -/
theorem frobenius_sub_normalPart_le (Θ Δ : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F (Δ - Θ.normalPart Δ) ≤ frobenius 𝕜 E F Δ := by
  rw [LinearMap.normalPart_def]
  exact frobenius_sub_starProjection_comp_le (LinearMap.range Θ)ᗮ (LinearMap.ker Θ) Δ

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

/-- A linear map's total squared norm on an orthonormal family is bounded by
its total squared norm on an orthonormal basis of the source. The target need
not be finite-dimensional.

Generalized from `YuWangSamworth2015/Core/Residual.lean` in the Kitware DKPS
formalization (Jon Crall and GPT 5.6 High; Apache-2.0), using orthonormal basis
extension in place of symmetry. -/
theorem LinearMap.sum_sq_norm_apply_orthonormal_le
    {𝕜 E F ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Fintype ι] [Fintype κ]
    (M : E →ₗ[𝕜] F) (b : OrthonormalBasis ι 𝕜 E)
    {w : κ → E} (hw : Orthonormal 𝕜 w) :
    ∑ i, ‖M (w i)‖ ^ 2 ≤ ∑ k, ‖M (b k)‖ ^ 2 := by
  classical
  have := Module.Finite.of_basis b.toBasis
  have hwrange : Orthonormal 𝕜 ((↑) : Set.range w → E) :=
    (orthonormal_subtype_range hw.linearIndependent.injective).mpr hw
  obtain ⟨t, c, ht, hc⟩ := hwrange.exists_orthonormalBasis_extension
  let g : κ ↪ t := ⟨fun i ↦ ⟨w i, ht ⟨i, rfl⟩⟩,
    fun _ _ h ↦ hw.linearIndependent.injective (congrArg Subtype.val h)⟩
  have hg (i : κ) : c (g i) = w i := by
    rw [hc]
    rfl
  calc ∑ i, ‖M (w i)‖ ^ 2 = ∑ i, ‖M (c (g i))‖ ^ 2 := by simp only [hg]
    _ ≤ ∑ k, ‖M (c k)‖ ^ 2 := by
      rw [← Finset.sum_map Finset.univ g (fun k ↦ ‖M (c k)‖ ^ 2)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ ↦ sq_nonneg _
    _ = ∑ k, ‖M (b k)‖ ^ 2 := M.sum_norm_apply_sq_eq_sum_norm_apply_sq c b
