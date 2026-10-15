/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupWithZero.Units.Basic
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.PermutationGL
import TauCeti.Algebra.Notation.Pi.Basic

/-!
# The Weyl group of the unitary group

The **Weyl group** of `U(n) = Matrix.unitaryGroup (Fin n) ℂ` with respect to its diagonal torus
`T = TauCeti.unitaryTorus (Fin n)` is the quotient `N(T) / T` of the normalizer of the torus by the
torus. This file proves that it is the symmetric group on the `n` coordinates
(`TauCeti.unitaryTorusNormalizerQuotientMulEquivPerm`), acting on the torus by permuting the
diagonal entries (`TauCeti.unitaryTorusNormalizer_mul_unitaryTorusHom_mul_inv`). Since every
unitary matrix is conjugate into `T` with its eigenvalues on the diagonal
(`TauCeti.exists_isConj_unitaryTorusHom`), the Weyl group is the group that permutes those
eigenvalues.

The computation reduces to the one for the diagonal torus of `GL_n(ℂ)` in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer`. A unitary matrix normalizes
the unitary diagonal torus exactly when, as an invertible matrix, it normalizes the diagonal torus
of `GL_n(ℂ)` (`TauCeti.mem_normalizer_unitaryTorus_iff_toUnits_mem`): the unitary torus already
separates any two coordinates, which forces a normalizing matrix to be monomial. The coordinate
permutation of a normalizing unitary matrix is then the one it has in `GL_n(ℂ)`, every permutation
arises from a permutation matrix, which is unitary, and the permutation is trivial exactly on the
torus.

## Main definitions

* `TauCeti.unitaryTorusNormalizerPerm`: the coordinate permutation of a unitary matrix
  normalizing the diagonal torus.
* `TauCeti.unitaryTorusNormalizerQuotientMulEquivPerm`: the Weyl group `N(T) / T` of `U(n)` is the
  symmetric group `Equiv.Perm (Fin n)`.

## Main results

* `TauCeti.mem_normalizer_unitaryTorus_iff_toUnits_mem`: normalizing the unitary diagonal torus is
  normalizing the diagonal torus of `GL_n(ℂ)`.
* `TauCeti.unitaryTorusNormalizer_mul_unitaryTorusHom_mul_inv`: conjugation by a normalizer
  element permutes the diagonal entries of a torus element by its coordinate permutation.
* `TauCeti.unitaryTorusNormalizerPerm_eq_one_iff` and
  `TauCeti.unitaryTorusNormalizerPerm_surjective`: the coordinate permutation has kernel the torus,
  and every permutation arises.
* `TauCeti.unitaryTorusNormalizerPerm_permutationUnitary`: the coordinate permutation of the
  permutation matrix `Matrix.permutationUnitary σ` is `σ`.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, §3.
-/

public section

namespace TauCeti

open Matrix

variable {n : ℕ}

/-- A unitary matrix lies in the diagonal torus of `U(n)` exactly when, as an invertible matrix,
it lies in the diagonal torus of `GL_n(ℂ)`. -/
theorem mem_unitaryTorus_iff_toUnits_mem {g : unitaryGroup (Fin n) ℂ} :
    g ∈ unitaryTorus (Fin n) ↔ Unitary.toUnits g ∈ diagonalTorus ℂ n := by
  rw [mem_unitaryTorus_iff, mem_diagonalTorus_iff, Unitary.val_toUnits_apply]

/-- A unitary matrix normalizing the diagonal torus of `GL_n(ℂ)` normalizes the diagonal torus of
`U(n)`. -/
theorem mem_normalizer_unitaryTorus_of_toUnits_mem {g : unitaryGroup (Fin n) ℂ}
    (hg : Unitary.toUnits g ∈
      Subgroup.normalizer (diagonalTorus ℂ n : Set (GL (Fin n) ℂ))) :
    g ∈ Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)) := by
  have hT : unitaryTorus (Fin n) = (diagonalTorus ℂ n).comap Unitary.toUnits :=
    Subgroup.ext fun _ => mem_unitaryTorus_iff_toUnits_mem
  rw [hT]
  exact Subgroup.le_normalizer_comap _ (Subgroup.mem_comap.mpr hg)

/-- **A unitary matrix normalizes the diagonal torus of `U(n)` exactly when it normalizes the
diagonal torus of `GL_n(ℂ)`**, that is, exactly when it is a monomial matrix. -/
theorem mem_normalizer_unitaryTorus_iff_toUnits_mem {g : unitaryGroup (Fin n) ℂ} :
    g ∈ Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)) ↔
      Unitary.toUnits g ∈ Subgroup.normalizer (diagonalTorus ℂ n : Set (GL (Fin n) ℂ)) := by
  refine ⟨fun hg => ?_, mem_normalizer_unitaryTorus_of_toUnits_mem⟩
  -- The torus element with `-1` at `i` and `1` elsewhere separates `i` from every other index.
  have hsep (i j : Fin n) (hij : i ≠ j) : ∃ t : Fin n → ℂˣ,
      Unitary.toUnits g * diagGL t * (Unitary.toUnits g)⁻¹ ∈ diagonalTorus ℂ n ∧ t i ≠ t j := by
    let z : Fin n → Circle := Pi.mulSingle i (Circle.exp Real.pi)
    have hconj := (Subgroup.mem_normalizer_iff.mp hg _).mp (unitaryTorusHom_mem_unitaryTorus z)
    rw [mem_unitaryTorus_iff_toUnits_mem, map_mul, map_mul, map_inv,
      toUnits_unitaryTorusHom] at hconj
    exact ⟨_, hconj, (unitSphereToUnits_injective (𝕜 := ℂ)).ne
      (Pi.mulSingle_apply_ne_of_ne_one Circle.exp_pi_ne_one hij)⟩
  obtain ⟨d, σ, hdσ⟩ := exists_eq_diagGL_mul_permutationGL_of_forall_ne hsep
  rw [hdσ]
  exact (Subgroup.normalizer (diagonalTorus ℂ n : Set (GL (Fin n) ℂ))).mul_mem
    (Subgroup.le_normalizer (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩))
    (permutationGL_mem_normalizer σ)

/-- The coordinate permutation of a unitary matrix normalizing the diagonal torus of `U(n)`: the
coordinate permutation of the same matrix in `GL_n(ℂ)`. -/
noncomputable def unitaryTorusNormalizerPerm :
    Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)) →*
      Equiv.Perm (Fin n) :=
  diagonalNormalizerPerm.comp <|
    (Unitary.toUnits.comp (Subgroup.normalizer _).subtype).codRestrict _ fun g =>
      mem_normalizer_unitaryTorus_iff_toUnits_mem.mp g.property

/-- The coordinate permutation of a unitary normalizer element is the coordinate permutation of the
same matrix in `GL_n(ℂ)`. -/
theorem unitaryTorusNormalizerPerm_apply
    (g : Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ))) :
    unitaryTorusNormalizerPerm g =
      diagonalNormalizerPerm ⟨Unitary.toUnits (g : unitaryGroup (Fin n) ℂ),
        mem_normalizer_unitaryTorus_iff_toUnits_mem.mp g.property⟩ :=
  (rfl)

/-- **Conjugation by an element of the normalizer permutes the diagonal entries of a torus
element**: the entry at `i` becomes the original entry at the inverse image of `i` under the
coordinate permutation. -/
@[simp]
theorem unitaryTorusNormalizer_mul_unitaryTorusHom_mul_inv
    (g : Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)))
    (z : Fin n → Circle) :
    (g : unitaryGroup (Fin n) ℂ) * unitaryTorusHom (Fin n) z * (g : unitaryGroup (Fin n) ℂ)⁻¹ =
      unitaryTorusHom (Fin n) fun i => z ((unitaryTorusNormalizerPerm g).symm i) := by
  apply Unitary.toUnits_injective
  rw [map_mul, map_mul, map_inv, toUnits_unitaryTorusHom, toUnits_unitaryTorusHom,
    unitaryTorusNormalizerPerm_apply]
  exact diagonalNormalizer_mul_diagGL_mul_inv
    ⟨Unitary.toUnits (g : unitaryGroup (Fin n) ℂ), _⟩ fun i => Circle.toUnits (z i)

/-- The coordinate permutation of a unitary normalizer element is trivial exactly for elements of
the diagonal torus. -/
@[simp]
theorem unitaryTorusNormalizerPerm_eq_one_iff
    (g : Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ))) :
    unitaryTorusNormalizerPerm g = 1 ↔ (g : unitaryGroup (Fin n) ℂ) ∈ unitaryTorus (Fin n) := by
  rw [unitaryTorusNormalizerPerm_apply, diagonalNormalizerPerm_eq_one_iff,
    mem_unitaryTorus_iff_toUnits_mem]

/-- A permutation matrix normalizes the diagonal torus of `U(n)`. -/
theorem permutationUnitary_mem_normalizer (σ : Equiv.Perm (Fin n)) :
    permutationUnitary σ ∈
      Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)) :=
  mem_normalizer_unitaryTorus_of_toUnits_mem <| by
    rw [toUnits_permutationUnitary]
    exact permutationGL_mem_normalizer σ

/-- The coordinate permutation induced by a permutation matrix is the original permutation. -/
@[simp]
theorem unitaryTorusNormalizerPerm_permutationUnitary (σ : Equiv.Perm (Fin n)) :
    unitaryTorusNormalizerPerm ⟨permutationUnitary σ, permutationUnitary_mem_normalizer σ⟩ = σ := by
  rw [unitaryTorusNormalizerPerm_apply]
  refine diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL _ 1 σ ?_
  rw [map_one, one_mul]
  exact toUnits_permutationUnitary σ

/-- Every permutation of the coordinates is the coordinate permutation of a unitary matrix
normalizing the diagonal torus, namely of a permutation matrix. -/
theorem unitaryTorusNormalizerPerm_surjective :
    Function.Surjective (unitaryTorusNormalizerPerm (n := n)) := fun σ =>
  ⟨_, unitaryTorusNormalizerPerm_permutationUnitary σ⟩

/-- **The Weyl group of `U(n)`**: the normalizer of the diagonal torus modulo the torus is
canonically the symmetric group on the coordinates. -/
noncomputable def unitaryTorusNormalizerQuotientMulEquivPerm :
    Subgroup.normalizerQuotient (unitaryTorus (Fin n)) ≃* Equiv.Perm (Fin n) :=
  MulEquiv.ofBijective
    (Subgroup.normalizerQuotientLift _ unitaryTorusNormalizerPerm fun g =>
      (unitaryTorusNormalizerPerm_eq_one_iff g).mpr)
    ⟨(Subgroup.normalizerQuotientLift_injective_iff _ _ _).mpr
        unitaryTorusNormalizerPerm_eq_one_iff,
      Subgroup.normalizerQuotientLift_surjective_of_surjective _ _ _
        unitaryTorusNormalizerPerm_surjective⟩

/-- The Weyl-group equivalence sends the class of a normalizer element to its coordinate
permutation. -/
@[simp]
theorem unitaryTorusNormalizerQuotientMulEquivPerm_mk
    (g : Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ))) :
    unitaryTorusNormalizerQuotientMulEquivPerm
        (g : Subgroup.normalizerQuotient (unitaryTorus (Fin n))) =
      unitaryTorusNormalizerPerm g :=
  (rfl)

/-- The inverse of the Weyl-group equivalence sends a coordinate permutation to the class of its
permutation matrix. -/
@[simp]
theorem unitaryTorusNormalizerQuotientMulEquivPerm_symm_apply (σ : Equiv.Perm (Fin n)) :
    unitaryTorusNormalizerQuotientMulEquivPerm.symm σ =
      Subgroup.normalizerQuotientMk (unitaryTorus (Fin n))
        ⟨permutationUnitary σ, permutationUnitary_mem_normalizer σ⟩ := by
  apply unitaryTorusNormalizerQuotientMulEquivPerm.injective
  simp

end TauCeti
