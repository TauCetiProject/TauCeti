/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup
import Mathlib.Data.Finite.Perm

/-!
# The Weyl group of the unitary group

The **Weyl group** of a compact group with maximal torus `T` is the normalizer quotient
`N(T) / T`. This file computes it for the unitary group `U(n) = Matrix.unitaryGroup (Fin n) ℂ`
and its diagonal torus `T = TauCeti.unitaryTorus (Fin n)`: it is the symmetric group `Sₙ`, acting
on `T ≅ Circleⁿ` by permuting the diagonal entries, that is, the eigenvalues.

The normalizer is the group of **monomial unitary matrices**, the products
`diag (z₁, …, zₙ) · P_σ` of a diagonal unitary matrix and a permutation matrix
(`TauCeti.mem_normalizer_unitaryTorus_iff`). Conjugation by an element normalizing `T` keeps the
diagonal matrices `diag (1, …, -1, …, 1)` diagonal, and these separate the coordinates; that is
exactly the hypothesis of the monomial criterion
`TauCeti.exists_eq_diagGL_mul_permutationGL_of_forall_ne` for invertible matrices. So the
computation runs through `Unitary.toUnits : U(n) →* GL_n(ℂ)`: a unitary matrix normalizes `T`
exactly when it normalizes the diagonal torus of `GL_n(ℂ)`
(`TauCeti.mem_normalizer_unitaryTorus_iff_toUnits_mem_normalizer`), and the coordinate permutation
`TauCeti.diagonalNormalizerPerm` of the general linear group restricts to the unitary normalizer.
Its kernel is `T` and every permutation is realized by a permutation matrix, which is unitary, so
the coordinate permutation descends to an isomorphism `N(T) / T ≃* Sₙ`.

## Main definitions

* `TauCeti.unitaryTorusNormalizerPerm`: the coordinate permutation of an element normalizing the
  diagonal torus.
* `TauCeti.unitaryTorusNormalizerQuotientMulEquivPerm`: the Weyl group `N(T) / T` of `U(n)` is the
  symmetric group.

## Main results

* `TauCeti.mem_normalizer_unitaryTorus_iff`: the normalizer of the diagonal torus consists of the
  monomial unitary matrices.
* `TauCeti.unitaryTorusNormalizer_mul_unitaryTorusHom_mul_inv`: conjugation by a normalizer element
  permutes the diagonal entries by its coordinate permutation.
* `TauCeti.unitaryTorusNormalizerPerm_eq_one_iff`: the coordinate permutation is trivial exactly on
  the diagonal torus.
* `TauCeti.natCard_normalizerQuotient_unitaryTorus`: the Weyl group of `U(n)` has `n!` elements.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, §3.
-/

public section

namespace TauCeti

open Matrix

noncomputable section

section Embedding

/-- Viewed as an invertible matrix, `Matrix.UnitaryGroup.permMatrixHom σ` is
`TauCeti.permutationGL σ`. -/
@[simp]
theorem toUnits_unitaryGroup_permMatrixHom {R : Type*} [CommRing R] [StarRing R]
    {n : Type*} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) :
    Unitary.toUnits (UnitaryGroup.permMatrixHom (R := R) σ) = permutationGL (k := R) σ :=
  Units.ext <| by simp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Viewed as an invertible matrix, `TauCeti.unitaryTorusHom n z` is the diagonal matrix
`TauCeti.diagGL` of the units `z i`. -/
@[simp]
theorem toUnits_unitaryTorusHom (z : n → Circle) :
    Unitary.toUnits (unitaryTorusHom n z) = diagGL fun i => Circle.toUnits (z i) :=
  Units.ext <| by simp

end Embedding

variable {n : ℕ}

/-- A unitary matrix lies in the diagonal torus of `U(n)` exactly when, as an invertible matrix, it
lies in the diagonal torus of `GL_n(ℂ)`. -/
@[simp]
theorem toUnits_mem_diagonalTorus_iff {g : unitaryGroup (Fin n) ℂ} :
    Unitary.toUnits g ∈ diagonalTorus ℂ n ↔ g ∈ unitaryTorus (Fin n) := by
  rw [mem_diagonalTorus_iff, mem_unitaryTorus_iff, Unitary.val_toUnits_apply]

/-- An element normalizing the diagonal torus of `U(n)` is, as an invertible matrix, a diagonal
matrix followed by a permutation matrix: conjugation by it keeps the diagonal matrices
`diag (1, …, -1, …, 1)` diagonal, and these separate the coordinates. -/
private theorem exists_toUnits_eq_diagGL_mul_permutationGL {g : unitaryGroup (Fin n) ℂ}
    (hg : g ∈ Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ))) :
    ∃ d : Fin n → ℂˣ, ∃ σ : Equiv.Perm (Fin n),
      Unitary.toUnits g = diagGL d * permutationGL (k := ℂ) σ := by
  refine exists_eq_diagGL_mul_permutationGL_of_forall_ne fun i j hij =>
    ⟨fun l => Circle.toUnits ((Pi.mulSingle i (-1) : Fin n → Circle) l), ?_, ?_⟩
  · rw [← toUnits_unitaryTorusHom, ← map_inv, ← map_mul, ← map_mul, toUnits_mem_diagonalTorus_iff]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp (unitaryTorusHom_mem_unitaryTorus _)
  · rw [Ne, Units.ext_iff]
    norm_num [Pi.mulSingle_eq_of_ne hij.symm]

/-- **A unitary matrix normalizes the diagonal torus of `U(n)` exactly when it normalizes the
diagonal torus of `GL_n(ℂ)`.** -/
theorem mem_normalizer_unitaryTorus_iff_toUnits_mem_normalizer {g : unitaryGroup (Fin n) ℂ} :
    g ∈ Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)) ↔
      Unitary.toUnits g ∈ Subgroup.normalizer (diagonalTorus ℂ n : Set (GL (Fin n) ℂ)) := by
  refine ⟨fun hg => ?_, fun hg => Subgroup.mem_normalizer_iff.mpr fun h => ?_⟩
  · obtain ⟨d, σ, hdσ⟩ := exists_toUnits_eq_diagGL_mul_permutationGL hg
    rw [hdσ]
    exact Subgroup.mul_mem _
      (Subgroup.le_normalizer (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩))
      (permutationGL_mem_normalizer σ)
  · rw [← toUnits_mem_diagonalTorus_iff, ← toUnits_mem_diagonalTorus_iff, map_mul, map_mul,
      map_inv]
    exact Subgroup.mem_normalizer_iff.mp hg _

/-- Permutation matrices normalize the diagonal torus of `U(n)`. -/
theorem unitaryGroup_permMatrixHom_mem_normalizer (σ : Equiv.Perm (Fin n)) :
    UnitaryGroup.permMatrixHom (R := ℂ) σ ∈
      Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)) := by
  rw [mem_normalizer_unitaryTorus_iff_toUnits_mem_normalizer, toUnits_unitaryGroup_permMatrixHom]
  exact permutationGL_mem_normalizer σ

/-- **The normalizer of the diagonal torus of `U(n)` consists of the monomial unitary matrices**:
the products of a diagonal unitary matrix and a permutation matrix. -/
theorem mem_normalizer_unitaryTorus_iff {g : unitaryGroup (Fin n) ℂ} :
    g ∈ Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)) ↔
      ∃ z : Fin n → Circle, ∃ σ : Equiv.Perm (Fin n),
        g = unitaryTorusHom (Fin n) z * UnitaryGroup.permMatrixHom (R := ℂ) σ := by
  refine ⟨fun hg => ?_, ?_⟩
  · obtain ⟨d, σ, hdσ⟩ := exists_toUnits_eq_diagGL_mul_permutationGL hg
    -- Removing the permutation factor leaves a diagonal unitary matrix.
    have hdiag : g * (UnitaryGroup.permMatrixHom (R := ℂ) σ)⁻¹ ∈ unitaryTorus (Fin n) := by
      rw [← toUnits_mem_diagonalTorus_iff, map_mul, map_inv, hdσ,
        toUnits_unitaryGroup_permMatrixHom, mul_inv_cancel_right]
      exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩
    obtain ⟨z, hz⟩ := mem_unitaryTorus_iff_exists_unitaryTorusHom.mp hdiag
    exact ⟨z, σ, by rw [hz, inv_mul_cancel_right]⟩
  · rintro ⟨z, σ, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer (unitaryTorusHom_mem_unitaryTorus z))
      (unitaryGroup_permMatrixHom_mem_normalizer σ)

/-- `ℂˣ` is nontrivial, as the coordinate permutation of the general linear group requires. -/
private theorem nontrivial_units_complex : Nontrivial ℂˣ :=
  nontrivial_of_ne (-1) 1 (by rw [Ne, Units.ext_iff]; norm_num)

attribute [local instance] nontrivial_units_complex

/-- `Unitary.toUnits`, restricted to the normalizer of the diagonal torus of `U(n)`, lands in the
normalizer of the diagonal torus of `GL_n(ℂ)`. -/
private def toUnitsNormalizer :
    Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)) →*
      Subgroup.normalizer (diagonalTorus ℂ n : Set (GL (Fin n) ℂ)) :=
  (Unitary.toUnits.comp (Subgroup.normalizer _).subtype).codRestrict _ fun g =>
    mem_normalizer_unitaryTorus_iff_toUnits_mem_normalizer.mp g.2

private theorem coe_toUnitsNormalizer
    (g : Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ))) :
    (toUnitsNormalizer g : GL (Fin n) ℂ) = Unitary.toUnits (g : unitaryGroup (Fin n) ℂ) :=
  rfl

/-- The **coordinate permutation** of an element normalizing the diagonal torus of `U(n)`: the
permutation of the diagonal entries effected by conjugation
(`TauCeti.unitaryTorusNormalizer_mul_unitaryTorusHom_mul_inv`). -/
def unitaryTorusNormalizerPerm :
    Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)) →*
      Equiv.Perm (Fin n) :=
  diagonalNormalizerPerm.comp toUnitsNormalizer

private theorem unitaryTorusNormalizerPerm_apply
    (g : Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ))) :
    unitaryTorusNormalizerPerm g = diagonalNormalizerPerm (toUnitsNormalizer g) :=
  rfl

/-- A monomial factorization of an element normalizing the diagonal torus has the coordinate
permutation selected by `TauCeti.unitaryTorusNormalizerPerm`. -/
theorem unitaryTorusNormalizerPerm_eq_of_eq_unitaryTorusHom_mul_permMatrixHom
    (g : Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)))
    (z : Fin n → Circle) (σ : Equiv.Perm (Fin n))
    (h : (g : unitaryGroup (Fin n) ℂ) =
      unitaryTorusHom (Fin n) z * UnitaryGroup.permMatrixHom (R := ℂ) σ) :
    unitaryTorusNormalizerPerm g = σ := by
  rw [unitaryTorusNormalizerPerm_apply]
  refine diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL _
    (fun i => Circle.toUnits (z i)) σ ?_
  rw [coe_toUnitsNormalizer, h, map_mul, toUnits_unitaryTorusHom,
    toUnits_unitaryGroup_permMatrixHom]

/-- The coordinate permutation of a permutation matrix is the original permutation. -/
@[simp]
theorem unitaryTorusNormalizerPerm_unitaryGroup_permMatrixHom (σ : Equiv.Perm (Fin n)) :
    unitaryTorusNormalizerPerm
      ⟨UnitaryGroup.permMatrixHom (R := ℂ) σ, unitaryGroup_permMatrixHom_mem_normalizer σ⟩ = σ :=
  unitaryTorusNormalizerPerm_eq_of_eq_unitaryTorusHom_mul_permMatrixHom _ 1 σ <| by
    rw [map_one, one_mul]

/-- Every permutation is the coordinate permutation of a permutation matrix. -/
theorem unitaryTorusNormalizerPerm_surjective :
    Function.Surjective (unitaryTorusNormalizerPerm (n := n)) := fun σ =>
  ⟨_, unitaryTorusNormalizerPerm_unitaryGroup_permMatrixHom σ⟩

/-- The coordinate permutation of an element normalizing the diagonal torus is trivial exactly
when the element lies in the torus. -/
@[simp]
theorem unitaryTorusNormalizerPerm_eq_one_iff
    (g : Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ))) :
    unitaryTorusNormalizerPerm g = 1 ↔ (g : unitaryGroup (Fin n) ℂ) ∈ unitaryTorus (Fin n) := by
  rw [unitaryTorusNormalizerPerm_apply, diagonalNormalizerPerm_eq_one_iff, coe_toUnitsNormalizer,
    toUnits_mem_diagonalTorus_iff]

/-- **The Weyl group acts on the diagonal torus by permuting the diagonal entries**: conjugation by
an element normalizing the diagonal torus moves the entry at `σ⁻¹ i` to position `i`, where `σ`
is its coordinate permutation. -/
@[simp]
theorem unitaryTorusNormalizer_mul_unitaryTorusHom_mul_inv
    (g : Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)))
    (z : Fin n → Circle) :
    (g : unitaryGroup (Fin n) ℂ) * unitaryTorusHom (Fin n) z * (g : unitaryGroup (Fin n) ℂ)⁻¹ =
      unitaryTorusHom (Fin n) fun i => z ((unitaryTorusNormalizerPerm g).symm i) := by
  apply Unitary.toUnits_injective
  rw [map_mul, map_mul, map_inv, toUnits_unitaryTorusHom, toUnits_unitaryTorusHom,
    unitaryTorusNormalizerPerm_apply, ← coe_toUnitsNormalizer,
    diagonalNormalizer_mul_diagGL_mul_inv]

/-- **The Weyl group of `U(n)` is the symmetric group**: the normalizer of the diagonal torus
modulo the torus is isomorphic to `Sₙ`, through the coordinate permutation. -/
def unitaryTorusNormalizerQuotientMulEquivPerm :
    (unitaryTorus (Fin n)).normalizerQuotient ≃* Equiv.Perm (Fin n) :=
  MulEquiv.ofBijective
    ((unitaryTorus (Fin n)).normalizerQuotientLift unitaryTorusNormalizerPerm fun g hg =>
      (unitaryTorusNormalizerPerm_eq_one_iff g).mpr hg)
    ⟨(Subgroup.normalizerQuotientLift_injective_iff _ _ _).mpr
        unitaryTorusNormalizerPerm_eq_one_iff,
      Subgroup.normalizerQuotientLift_surjective_of_surjective _ _ _
        unitaryTorusNormalizerPerm_surjective⟩

/-- The isomorphism of the Weyl group with `Sₙ` sends the class of a normalizer element to its
coordinate permutation. -/
@[simp]
theorem unitaryTorusNormalizerQuotientMulEquivPerm_mk
    (g : Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ))) :
    unitaryTorusNormalizerQuotientMulEquivPerm
        (g : (unitaryTorus (Fin n)).normalizerQuotient) =
      unitaryTorusNormalizerPerm g := by
  rw [unitaryTorusNormalizerQuotientMulEquivPerm]
  rfl

/-- The inverse isomorphism sends a permutation to the class of its permutation matrix. -/
@[simp]
theorem unitaryTorusNormalizerQuotientMulEquivPerm_symm_apply (σ : Equiv.Perm (Fin n)) :
    unitaryTorusNormalizerQuotientMulEquivPerm.symm σ =
      (unitaryTorus (Fin n)).normalizerQuotientMk
        ⟨UnitaryGroup.permMatrixHom (R := ℂ) σ, unitaryGroup_permMatrixHom_mem_normalizer σ⟩ := by
  apply unitaryTorusNormalizerQuotientMulEquivPerm.injective
  simp

/-- The Weyl group of `U(n)` has `n!` elements. -/
theorem natCard_normalizerQuotient_unitaryTorus :
    Nat.card (unitaryTorus (Fin n)).normalizerQuotient = n.factorial := by
  rw [Nat.card_congr unitaryTorusNormalizerQuotientMulEquivPerm.toEquiv, Nat.card_perm,
    Nat.card_fin]

end

end TauCeti
