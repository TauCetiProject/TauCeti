/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Hermitian
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Indefinite

/-!
# Polarization for the indefinite unitary group

Over `ℝ` or `ℂ` (any `RCLike` field), a Hermitian matrix is determined by its quadratic form
`x ↦ star x ⬝ᵥ (A *ᵥ x)`. Applied to `star g * J * g - J`, this shows that an invertible matrix
lies in the indefinite unitary group `U(p, q)` as soon as it preserves the values `⟨z, z⟩` of the
Hermitian form `⟨z, w⟩ = star z ⬝ᵥ (J *ᵥ w)` on the diagonal. In this form membership does not
depend on which slot of the form is conjugate-linear.

## Main results

* `Matrix.IsHermitian.eq_zero_of_forall_star_dotProduct_mulVec_self`: a Hermitian matrix with
  vanishing quadratic form is zero.
* `Matrix.mem_indefiniteUnitaryGroup_iff_forall_dotProduct_self`: an invertible matrix lies in
  `U(p, q)` exactly when it preserves `⟨z, z⟩` for every `z`.
-/

public section

open LieAlgebra.Orthogonal

namespace Matrix

variable {n p q 𝕜 : Type*} [RCLike 𝕜]

/-- **Polarization for Hermitian matrices.** Over an `RCLike` field, a Hermitian matrix whose
quadratic form `x ↦ star x ⬝ᵥ (A *ᵥ x)` vanishes is zero. -/
theorem IsHermitian.eq_zero_of_forall_star_dotProduct_mulVec_self [Fintype n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (h : ∀ x : n → 𝕜, star x ⬝ᵥ (A *ᵥ x) = 0) : A = 0 := by
  classical
  have hT := (isSymmetric_toEuclideanLin_iff.mpr hA).inner_map_self_eq_zero.mp fun x => by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, star_dotProduct]
    simpa using congrArg star (h (WithLp.ofLp x))
  exact toEuclideanLin.injective (by rw [hT, map_zero])

variable [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- **`U(p, q)` by polarization.** Over an `RCLike` field, an invertible matrix lies in `U(p, q)`
exactly when it preserves the values `⟨z, z⟩ = star z ⬝ᵥ (J *ᵥ z)` of the indefinite Hermitian
form. -/
theorem mem_indefiniteUnitaryGroup_iff_forall_dotProduct_self {g : GL (p ⊕ q) 𝕜} :
    g ∈ indefiniteUnitaryGroup p q 𝕜 ↔
      ∀ z : p ⊕ q → 𝕜, star (g *ᵥ z) ⬝ᵥ (indefiniteDiagonal p q 𝕜 *ᵥ (g *ᵥ z)) =
        star z ⬝ᵥ (indefiniteDiagonal p q 𝕜 *ᵥ z) := by
  refine ⟨fun hg z => mem_indefiniteUnitaryGroup_iff_forall_dotProduct.mp hg z z, fun h => ?_⟩
  have hA : (star (g : Matrix (p ⊕ q) (p ⊕ q) 𝕜) * indefiniteDiagonal p q 𝕜 * g -
      indefiniteDiagonal p q 𝕜).IsHermitian := by
    rw [star_eq_conjTranspose]
    exact (isHermitian_conjTranspose_mul_mul _ isHermitian_indefiniteDiagonal).sub
      isHermitian_indefiniteDiagonal
  refine mem_indefiniteUnitaryGroup_iff.mpr <| sub_eq_zero.mp <|
    hA.eq_zero_of_forall_star_dotProduct_mulVec_self fun z => ?_
  rw [sub_mulVec, dotProduct_sub, star_eq_conjTranspose,
    star_dotProduct_conjTranspose_mul_mul_mulVec, h, sub_self]

end Matrix
