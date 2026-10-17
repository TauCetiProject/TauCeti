/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.JointEigenbasis

/-!
# The spectral theorem for normal operators

A linear operator `T` on a finite-dimensional complex inner product space is **normal** when it
commutes with its adjoint, `IsStarNormal T`. The spectral theorem says that `T` is then
diagonalized by an orthonormal basis: there is an orthonormal basis of eigenvectors of `T`.
Mathlib proves this for symmetric (self-adjoint) operators,
`LinearMap.IsSymmetric.eigenvectorBasis`; this file extends it to normal ones.

This is the singleton case of
`TauCeti.exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute`, which constructs a common
orthonormal eigenbasis for any commuting family of normal operators by decomposing their real
and imaginary parts into joint eigenspaces.

Unlike the self-adjoint case, the eigenvalues are complex, and the statement is specific to
complex scalars: a rotation of the real plane is normal but has no real eigenvector.

## Main results

* `LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal`: **the spectral theorem for
  normal operators**, a normal operator on a finite-dimensional complex inner product space has
  an orthonormal basis of eigenvectors, indexed by any finite type of the right cardinality.

## References

* S. Axler, *Linear Algebra Done Right*, 3rd ed., Springer (2015), Theorem 7.24 (the complex
  spectral theorem).
-/

public section

open Module

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **The spectral theorem for normal operators.** A normal operator on a finite-dimensional
complex inner product space has an orthonormal basis of eigenvectors. The basis may be indexed by
any finite type whose cardinality is the dimension of the space. -/
theorem exists_orthonormalBasis_apply_eq_smul_of_isStarNormal (T : E →ₗ[ℂ] E) [IsStarNormal T]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℂ E) :
    ∃ (b : OrthonormalBasis ι ℂ E) (μ : ι → ℂ), ∀ i, T (b i) = μ i • b i := by
  obtain ⟨b, μ, hb⟩ := TauCeti.exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute
    (fun _ : Unit => T) (fun _ => inferInstance) (fun _ _ _ => Commute.refl _) hι
  exact ⟨b, μ (), hb ()⟩

end LinearMap
