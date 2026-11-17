/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.InnerProductSpace.Nondegenerate

/-!
# Simultaneous orthonormal diagonalization of real quadratic forms

Every symmetric bilinear form `B` on a finite-dimensional real inner product space `E` is
represented by a symmetric linear operator `T` with `⟪T x, y⟫ = B x y`, constructed via
`LinearMap.BilinForm.symmCompOfNondegenerate` and the nondegeneracy of the real inner product
(`TauCeti.nondegenerate_inner`). By the real spectral theorem
(`LinearMap.IsSymmetric.eigenvectorBasis`), `T` has an orthonormal eigenbasis of `E`, which is
simultaneously orthogonal for `B`.

Applying this to the associated bilinear form of a real quadratic form `Q : QuadraticForm ℝ E`
yields an orthonormal basis of `E` that is orthogonal for `Q`.

## Main results

* `LinearMap.IsSymm.exists_orthonormalBasis_isOrthoᵢ`: every symmetric real bilinear form on a
  finite-dimensional real inner product space admits an orthonormal basis orthogonal for the form.
* `QuadraticMap.exists_orthonormalBasis_isOrthoᵢ`: every real quadratic form on a
  finite-dimensional real inner product space admits an orthonormal basis orthogonal for its
  associated bilinear form.

## References

* P. R. Halmos, *Finite-Dimensional Vector Spaces* (1958), §79–80.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open scoped RealInnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Simultaneous orthonormal diagonalization of a symmetric real bilinear form.** Every symmetric
bilinear form `B` on a finite-dimensional real inner product space `E` admits an orthonormal basis
indexed by `Fin n` (where `Module.finrank ℝ E = n`) that is orthogonal for `B`. -/
theorem IsSymm.exists_orthonormalBasis_isOrthoᵢ {B : LinearMap.BilinForm ℝ E}
    (hB : LinearMap.IsSymm B) {n : ℕ} (hn : Module.finrank ℝ E = n) :
    ∃ b : OrthonormalBasis (Fin n) ℝ E, B.IsOrthoᵢ b.toBasis := by
  let T : E →ₗ[ℝ] E := B.symmCompOfNondegenerate (innerₗ E) TauCeti.nondegenerate_inner
  have hT : T.IsSymmetric := fun x y ↦ by
    rw [← innerₗ_apply_apply, LinearMap.BilinForm.symmCompOfNondegenerate_left_apply,
      real_inner_comm (T y) x, ← innerₗ_apply_apply,
      LinearMap.BilinForm.symmCompOfNondegenerate_left_apply]
    exact hB.eq x y
  let b : OrthonormalBasis (Fin n) ℝ E := hT.eigenvectorBasis hn
  refine ⟨b, LinearMap.isOrthoᵢ_def.mpr fun i j hij ↦ ?_⟩
  have key : ⟪T (b i), b j⟫ = B (b i) (b j) := by
    rw [← innerₗ_apply_apply]
    exact LinearMap.BilinForm.symmCompOfNondegenerate_left_apply _
      TauCeti.nondegenerate_inner (b j) (b i)
  rw [OrthonormalBasis.coe_toBasis, ← key, hT.apply_eigenvectorBasis, real_inner_smul_left,
    b.orthonormal.2 hij, mul_zero]

end LinearMap

namespace QuadraticMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every real quadratic form `Q` on a finite-dimensional real inner product space `E` admits an
orthonormal basis indexed by `Fin n` (where `Module.finrank ℝ E = n`) orthogonal for
`QuadraticMap.associated Q`. -/
theorem exists_orthonormalBasis_isOrthoᵢ (Q : QuadraticForm ℝ E)
    {n : ℕ} (hn : Module.finrank ℝ E = n) :
    ∃ b : OrthonormalBasis (Fin n) ℝ E, (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis :=
  (QuadraticForm.associated_isSymm ℝ Q).exists_orthonormalBasis_isOrthoᵢ hn

end QuadraticMap
