/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Comap
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.TitsSystem
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Normalizer

/-!
# The standard Tits systems of the special linear groups

Let `B` be the subgroup of upper-triangular matrices in `SLₙ₊₁(k)` and let `N` be the subgroup of
determinant-one monomial matrices. Over a field whose unit group is nontrivial, these form a Tits
system whose Weyl group is the symmetric group on the coordinates, with the adjacent
transpositions `(i i+1)` as simple reflections. In particular, the general Bruhat decomposition of
a Tits system applies to `SLₙ₊₁(k)`.

The Tits system is pulled back from the standard Tits system of `GLₙ₊₁(k)` along the inclusion
`SLₙ₊₁(k) → GLₙ₊₁(k)`: every invertible matrix is a determinant-one matrix times the diagonal
matrix `diag(det g, 1, …, 1)`, which lies in `B ∩ N` for `GLₙ₊₁(k)`.

When the determinant-one diagonal torus separates coordinates, as it does over every field with
a unit whose square is not one, `N` is the normalizer of the diagonal torus of `SLₙ₊₁(k)`
(`TauCeti.slTitsSystem_subgroupN_eq_normalizer`). Without that hypothesis the normalizer can be
larger: over `𝔽₃` the diagonal torus of `SL₂` is the centre `{±1}`, whose normalizer is all of
`SL₂(𝔽₃)`, while the monomial matrices still give a Tits system.

## Main declarations

* `TauCeti.slTitsSystem`: the standard Tits system of `SLₙ₊₁(k)`.
* `TauCeti.mem_slTitsSystem_subgroupB_iff`: its `B` consists of the upper-triangular matrices.
* `TauCeti.slTitsSystem_subgroupN_eq_normalizer`: its `N` is the normalizer of the diagonal torus
  when that torus separates coordinates.
* `TauCeti.slTitsSystemWeylGroupMulEquivPerm`: its Weyl group is the symmetric group on the
  coordinates.
* `TauCeti.slTitsSystem_simple`: its simple reflections are the adjacent transpositions.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 29.1 and 29.2.
* R. Steinberg, *Lectures on Chevalley Groups*, Section 3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter IV, §2.
-/

public section

open Matrix

namespace TauCeti

universe u

noncomputable section

variable (k : Type u) [Field k]

variable [Nontrivial kˣ] (n : ℕ)

/-- Every invertible matrix is a determinant-one matrix times an element of `B ∩ N` for the
standard `GLₙ₊₁` Tits system. -/
private theorem exists_toGL_mul_mem_inf (g : GL (Fin (n + 1)) k) :
    ∃ x : SpecialLinearGroup (Fin (n + 1)) k,
      ∃ t ∈ (glTitsSystem k n).subgroupB ⊓ (glTitsSystem k n).subgroupN,
        SpecialLinearGroup.toGL x * t = g := by
  obtain ⟨x, u, hxu⟩ := g.exists_toGL_mul_eq
  refine ⟨x, diagGL u, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, hxu⟩
  · rw [glTitsSystem_subgroupB]
    exact UpperTriangularGroup.diagonalTorus_le
      (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨u, rfl⟩)
  · rw [glTitsSystem_subgroupN]
    exact Subgroup.le_normalizer (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨u, rfl⟩)

/-- The standard Tits system of `SLₙ₊₁(k)`: `B` is the upper-triangular subgroup, `N` is the
subgroup of monomial matrices, and the simple reflections are the classes corresponding to the
adjacent transpositions `(i i+1)`. It is the pullback of the standard Tits system of `GLₙ₊₁(k)`
along the inclusion `SLₙ₊₁(k) → GLₙ₊₁(k)`. -/
def slTitsSystem : TitsSystem (SpecialLinearGroup (Fin (n + 1)) k) :=
  (glTitsSystem k n).comap SpecialLinearGroup.toGL (exists_toGL_mul_mem_inf k n)

/-- The `B` subgroup of the standard `SLₙ₊₁` Tits system is the preimage of the upper-triangular
subgroup of `GLₙ₊₁`. -/
theorem slTitsSystem_subgroupB :
    (slTitsSystem k n).subgroupB =
      (upperTriangularGroup (Fin (n + 1)) k).comap SpecialLinearGroup.toGL := by
  rw [slTitsSystem, TitsSystem.comap_subgroupB, glTitsSystem_subgroupB]

/-- An element of `SLₙ₊₁(k)` lies in the `B` subgroup of the standard Tits system exactly when it
is upper triangular. -/
@[simp]
theorem mem_slTitsSystem_subgroupB_iff {g : SpecialLinearGroup (Fin (n + 1)) k} :
    g ∈ (slTitsSystem k n).subgroupB ↔
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).IsUpperTriangular := by
  rw [slTitsSystem_subgroupB, Subgroup.mem_comap, UpperTriangularGroup.mem_iff,
    SpecialLinearGroup.coe_GL_coe_matrix]

/-- The `N` subgroup of the standard `SLₙ₊₁` Tits system is the preimage of the normalizer of the
diagonal torus of `GLₙ₊₁`, that is, the subgroup of determinant-one monomial matrices. -/
@[simp]
theorem slTitsSystem_subgroupN :
    (slTitsSystem k n).subgroupN =
      (Subgroup.normalizer (diagonalTorus k (n + 1) : Set (GL (Fin (n + 1)) k))).comap
        SpecialLinearGroup.toGL := by
  rw [slTitsSystem, TitsSystem.comap_subgroupN, glTitsSystem_subgroupN]

/-- When the determinant-one diagonal torus separates coordinates, the `N` subgroup of the
standard `SLₙ₊₁` Tits system is the normalizer of the diagonal torus of `SLₙ₊₁`. -/
theorem slTitsSystem_subgroupN_eq_normalizer
    (hsep : SpecialLinearGroup.DiagonalTorusSeparatesCoordinates k (n + 1)) :
    (slTitsSystem k n).subgroupN =
      Subgroup.normalizer
        (SpecialLinearGroup.diagonalTorus k (n + 1) :
          Set (SpecialLinearGroup (Fin (n + 1)) k)) := by
  ext g
  rw [slTitsSystem_subgroupN, Subgroup.mem_comap,
    SpecialLinearGroup.mem_normalizer_diagonalTorus_iff_toGL_mem hsep]

/-- The Weyl group of the standard `SLₙ₊₁` Tits system is the permutation group of its
coordinates. It is the Weyl group of the standard `GLₙ₊₁` Tits system, transported along the
inclusion. -/
def slTitsSystemWeylGroupMulEquivPerm :
    (slTitsSystem k n).WeylGroup ≃* Equiv.Perm (Fin (n + 1)) :=
  ((glTitsSystem k n).comapWeylGroupMulEquiv _ _).trans (glTitsSystemWeylGroupMulEquivPerm k n)

/-- The Weyl-group identification of `SLₙ₊₁` factors through that of `GLₙ₊₁`: the class of a
determinant-one monomial matrix goes to the permutation of its class in the `GLₙ₊₁` Weyl group. -/
@[simp]
theorem slTitsSystemWeylGroupMulEquivPerm_mk (g : (slTitsSystem k n).subgroupN) :
    slTitsSystemWeylGroupMulEquivPerm k n (QuotientGroup.mk g) =
      glTitsSystemWeylGroupMulEquivPerm k n
        (QuotientGroup.mk ⟨SpecialLinearGroup.toGL (g : SpecialLinearGroup (Fin (n + 1)) k), by
          simpa only [slTitsSystem_subgroupN, Subgroup.mem_comap, glTitsSystem_subgroupN]
            using g.2⟩) :=
  -- `slTitsSystem` is by definition the pullback of `glTitsSystem` along `toGL`.
  congrArg (glTitsSystemWeylGroupMulEquivPerm k n)
    ((glTitsSystem k n).comapWeylGroupMulEquiv_mk _ (exists_toGL_mul_mem_inf k n) g)

/-- The simple reflections of the standard `SLₙ₊₁` Tits system correspond to the adjacent
transpositions `(i i+1)`. -/
@[simp]
theorem slTitsSystem_simple :
    (slTitsSystem k n).simple =
      slTitsSystemWeylGroupMulEquivPerm k n ⁻¹'
        Set.range fun i : Fin n ↦ Equiv.swap i.castSucc i.succ := by
  have h := (glTitsSystem k n).comap_simple _ (exists_toGL_mul_mem_inf k n)
  rw [glTitsSystem_simple_eq_preimage, ← Set.preimage_comp] at h
  exact h

end

end TauCeti
