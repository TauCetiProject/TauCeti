/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# The spectral theorem for normal operators

A linear operator `T` on a finite-dimensional complex inner product space is **normal** when it
commutes with its adjoint, `IsStarNormal T`. The spectral theorem says that `T` is then
diagonalized by an orthonormal basis: there is an orthonormal basis of eigenvectors of `T`.
Mathlib proves this for symmetric (self-adjoint) operators,
`LinearMap.IsSymmetric.eigenvectorBasis`; this file extends it to normal ones.

The proof splits `T` into its real and imaginary parts, `T = ℜ T + i • ℑ T`, which are
self-adjoint and, exactly because `T` is normal, commute
(`isStarNormal_iff_commute_realPart_imaginaryPart`). Two commuting self-adjoint operators are
simultaneously diagonalizable: the space is the orthogonal direct sum of their joint eigenspaces
(`LinearMap.IsSymmetric.directSum_isInternal_of_commute`). On the joint eigenspace where `ℜ T`
acts by `a` and `ℑ T` by `b`, the operator `T` acts by `a + i b`, so an orthonormal basis
subordinate to this decomposition consists of eigenvectors of `T`.

Unlike the self-adjoint case, the eigenvalues are complex, and the statement is specific to
complex scalars: a rotation of the real plane is normal but has no real eigenvector.

## Main results

* `LinearMap.apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart`: on a joint eigenspace of
  `ℜ T` and `ℑ T` with eigenvalues `a` and `b`, the operator `T` acts by `a + i b`.
* `LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal`: **the spectral theorem for
  normal operators**, a normal operator on a finite-dimensional complex inner product space has
  an orthonormal basis of eigenvectors, indexed by any finite type of the right cardinality.

## References

* S. Axler, *Linear Algebra Done Right*, 3rd ed., Springer (2015), Theorem 7.24 (the complex
  spectral theorem).
-/

public section

open Module Module.End ComplexStarModule

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- On a joint eigenspace of the real and imaginary parts of `T`, where `ℜ T` acts by `a` and
`ℑ T` by `b`, the operator `T` acts by `a + i b`. Normality is not needed here; finite
dimensionality only enters because the adjoint, hence `ℜ T` and `ℑ T`, is defined on
finite-dimensional spaces. -/
theorem apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart (T : E →ₗ[ℂ] E)
    {a b : ℂ} {v : E} (ha : v ∈ eigenspace (ℜ T : E →ₗ[ℂ] E) a)
    (hb : v ∈ eigenspace (ℑ T : E →ₗ[ℂ] E) b) :
    T v = (a + Complex.I * b) • v := by
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  rw [add_apply, smul_apply, mem_eigenspace_iff.mp ha, mem_eigenspace_iff.mp hb, add_smul,
    mul_smul]

/-- **The spectral theorem for normal operators.** A normal operator on a finite-dimensional
complex inner product space has an orthonormal basis of eigenvectors. The basis may be indexed by
any finite type whose cardinality is the dimension of the space. -/
theorem exists_orthonormalBasis_apply_eq_smul_of_isStarNormal (T : E →ₗ[ℂ] E) [IsStarNormal T]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℂ E) :
    ∃ (b : OrthonormalBasis ι ℂ E) (μ : ι → ℂ), ∀ i, T (b i) = μ i • b i := by
  classical
  -- The real and imaginary parts of `T` are self-adjoint and commute because `T` is normal.
  have hA : (ℜ T : E →ₗ[ℂ] E).IsSymmetric := (isSymmetric_iff_isSelfAdjoint _).mpr (ℜ T).2
  have hB : (ℑ T : E →ₗ[ℂ] E).IsSymmetric := (isSymmetric_iff_isSelfAdjoint _).mpr (ℑ T).2
  have hV := IsSymmetric.directSum_isInternal_of_commute hA hB (Commute.realPart_imaginaryPart T)
  have hO := IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB
  -- Only finitely many joint eigenspaces are nonzero, and they still decompose the space.
  let V : ℂ × ℂ → Submodule ℂ E := fun p =>
    eigenspace (ℜ T : E →ₗ[ℂ] E) p.2 ⊓ eigenspace (ℑ T : E →ₗ[ℂ] E) p.1
  let J := {p : ℂ × ℂ // V p ≠ ⊥}
  let _ : Fintype J := hV.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hVJ : DirectSum.IsInternal fun p : J => V p := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hOJ := hO.comp (Subtype.val_injective (p := fun p => V p ≠ ⊥))
  -- An orthonormal basis subordinate to the joint eigenspaces diagonalizes `T`.
  let b := hVJ.subordinateOrthonormalBasis rfl hOJ
  let p : Fin (finrank ℂ E) → J := fun j => hVJ.subordinateOrthonormalBasisIndex rfl j hOJ
  let e : ι ≃ Fin (finrank ℂ E) := Fintype.equivFinOfCardEq hι
  refine ⟨b.reindex e.symm, fun i => (p (e i)).1.2 + Complex.I * (p (e i)).1.1, fun i => ?_⟩
  have hmem := hVJ.subordinateOrthonormalBasis_subordinate rfl (e i) hOJ
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
  exact apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart T (Submodule.mem_inf.mp hmem).1
    (Submodule.mem_inf.mp hmem).2

end LinearMap
