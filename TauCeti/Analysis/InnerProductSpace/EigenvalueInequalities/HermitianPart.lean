/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SchurHorn
public import TauCeti.Analysis.Matrix.Eigenvalues.Schur.Basic

/-!
# Ky Fan's majorization of the real parts of eigenvalues

Let `T` be an endomorphism of a finite-dimensional inner product space `E` over `𝕜 = ℝ, ℂ`, and
let `H` be its Hermitian part, the symmetric operator with `2 • H = T + T†`. If the
characteristic polynomial of `T` splits with roots `α₀, …, αₙ₋₁`, the tuple of real parts
`(re αⱼ)ⱼ` is majorized by the eigenvalues of `H`: it lies in the convex hull of the
rearrangements of the eigenvalues of `H`. Over `ℂ` the characteristic polynomial always splits,
so this holds for every enumeration of the eigenvalues of `T`.

In an orthonormal basis that triangularizes `T` with diagonal `α`, the diagonal entries of `H`
have real parts `re αⱼ`; the statement is therefore Schur's theorem on the diagonal of a
symmetric operator, transported along Schur triangularization.

## Main results

* `LinearMap.IsSymmetric.re_eigenvalues_mem_convexHull_of_charpoly_eq_prod`: Ky Fan's
  majorization over `𝕜`, for an operator whose characteristic polynomial is `∏ (X - αⱼ)`.
* `LinearMap.IsSymmetric.re_eigenvalues_mem_convexHull`: **Ky Fan's real-part majorization**
  over `ℂ`, for every enumeration of the characteristic roots.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997:
  Proposition III.5.3 (p. 74).
* K. Fan, *Maximum properties and inequalities for the eigenvalues of completely continuous
  operators*, Proc. Nat. Acad. Sci. U.S.A. **37** (1951), 760–766.
-/

public section

open Module Polynomial
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Ky Fan's majorization of real parts.** Let `H` be the Hermitian part of `T`, given by
`2 • H = T + T†`. If the characteristic polynomial of `T` is `∏ⱼ (X - αⱼ)`, the real parts
`re αⱼ` lie in the convex hull of the rearrangements of the eigenvalues of `H`. -/
theorem re_eigenvalues_mem_convexHull_of_charpoly_eq_prod {T H : E →ₗ[𝕜] E}
    (hH : H.IsSymmetric) (hHT : (2 : 𝕜) • H = T + adjoint T) {n : ℕ} (hn : finrank 𝕜 E = n)
    {α : Fin n → 𝕜} (hα : T.charpoly = ∏ j, (X - C (α j))) :
    (fun j ↦ RCLike.re (α j)) ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) ↦ hH.eigenvalues hn ∘ σ) := by
  obtain ⟨e, -, hdiag⟩ := (T.exists_orthonormalBasis_isUpperTriangular_diag_iff α).mpr hα
  -- The real quadratic forms of `H` and `T` agree, since `re ⟪T† x, x⟫ = re ⟪T x, x⟫`.
  have hre (x : E) : RCLike.re ⟪H x, x⟫_𝕜 = RCLike.re ⟪x, T x⟫_𝕜 := by
    have h := congrArg (fun y ↦ RCLike.re ⟪y, x⟫_𝕜) (LinearMap.congr_fun hHT x)
    simp only [LinearMap.smul_apply, LinearMap.add_apply, inner_add_left, inner_smul_left,
      adjoint_inner_left, map_add, map_ofNat, RCLike.ofNat_mul_re] at h
    linarith [inner_re_symm (𝕜 := 𝕜) x (T x)]
  -- In the triangularizing basis `e`, the diagonal entry `⟪e j, T (e j)⟫` is `α j`.
  have hdiag' (j : Fin n) : RCLike.re (α j) = RCLike.re ⟪H (e j), e j⟫_𝕜 := by
    rw [hre, ← congrFun hdiag j, Matrix.diag_apply, toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  simpa only [hdiag'] using hH.re_inner_apply_self_mem_convexHull_eigenvalues_comp_perm hn e

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Ky Fan's real-part majorization.** Let `H` be the Hermitian part of a complex operator
`T`, given by `2 • H = T + T†`. The real parts of the eigenvalues of `T`, in any enumeration
`α` of the roots of its characteristic polynomial with multiplicity, lie in the convex hull of
the rearrangements of the eigenvalues of `H`. -/
theorem re_eigenvalues_mem_convexHull {T H : E →ₗ[ℂ] E} (hH : H.IsSymmetric)
    (hHT : (2 : ℂ) • H = T + adjoint T) {n : ℕ} (hn : finrank ℂ E = n) {α : Fin n → ℂ}
    (hα : Multiset.map α Finset.univ.val = T.charpoly.roots) :
    (fun j ↦ (α j).re) ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) ↦ hH.eigenvalues hn ∘ σ) :=
  hH.re_eigenvalues_mem_convexHull_of_charpoly_eq_prod hHT hn <|
    (T.exists_orthonormalBasis_isUpperTriangular_diag_iff α).mp
      (T.exists_orthonormalBasis_isUpperTriangular_diag hα)

end LinearMap.IsSymmetric
