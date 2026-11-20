/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Submodule
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal.Complement

/-!
# Orthogonal complements for Lie actions closed under adjoints

If every operator of a Lie action has a left adjoint which also comes from the action,
the right orthogonal complement of each Lie submodule is again a Lie submodule. This extends
`LieAlgebra.InvariantForm.orthogonal`, where the left adjoint for `x` is the action of `-x`.
With an anisotropic form, a finite-dimensional Lie submodule and its orthogonal are complementary.
-/

public section

namespace LieSubmodule

variable {R L M : Type*} [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
  [LieRingModule L M]

/-- The right orthogonal complement of a Lie submodule for a bilinear form such that the
left adjoint of each action operator also belongs to the Lie action. -/
def orthogonalOfExistsAdjoint (N : LieSubmodule R L M) (B : LinearMap.BilinForm R M)
    (h : ∀ x : L, ∃ x' : L, ∀ m n : M, B ⁅x', m⁆ n = B m ⁅x, n⁆) :
    LieSubmodule R L M where
  toSubmodule := B.orthogonal N.toSubmodule
  lie_mem {x y} hy := LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn ↦ by
    obtain ⟨x', hx'⟩ := h x
    rw [← hx']
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp hy _ (N.lie_mem hn)

@[simp]
theorem orthogonalOfExistsAdjoint_toSubmodule (N : LieSubmodule R L M)
    (B : LinearMap.BilinForm R M)
    (h : ∀ x : L, ∃ x' : L, ∀ m n : M, B ⁅x', m⁆ n = B m ⁅x, n⁆) :
    (N.orthogonalOfExistsAdjoint B h).toSubmodule = B.orthogonal N.toSubmodule := (rfl)

@[simp]
theorem mem_orthogonalOfExistsAdjoint_iff (N : LieSubmodule R L M) (B : LinearMap.BilinForm R M)
    (h : ∀ x : L, ∃ x' : L, ∀ m n : M, B ⁅x', m⁆ n = B m ⁅x, n⁆) {m : M} :
    m ∈ N.orthogonalOfExistsAdjoint B h ↔ ∀ n ∈ N, B n m = 0 := by
  rw [← LieSubmodule.mem_toSubmodule, orthogonalOfExistsAdjoint_toSubmodule,
    LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [LieSubmodule.mem_toSubmodule]

/-- A finite-dimensional Lie submodule and its right orthogonal complement are complementary
when the form is nondegenerate on the submodule and the action is closed under left adjoints. -/
theorem isCompl_orthogonalOfExistsAdjoint {K : Type*} [Field K] [Module K M]
    (N : LieSubmodule K L M) [FiniteDimensional K N] (B : LinearMap.BilinForm K M)
    (h : ∀ x : L, ∃ x' : L, ∀ m n : M, B ⁅x', m⁆ n = B m ⁅x, n⁆)
    (hN : (B.restrict N.toSubmodule).Nondegenerate) :
    IsCompl N (N.orthogonalOfExistsAdjoint B h) := by
  rw [← LieSubmodule.isCompl_toSubmodule, orthogonalOfExistsAdjoint_toSubmodule]
  exact B.isCompl_orthogonal_of_finiteDimensional_of_restrict_nondegenerate _ hN

end LieSubmodule
