/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Centralizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

/-!
# The symplectic diagonal normalizer acts faithfully modulo the torus

Over a field with a unit different from its inverse, the normalizer of the paired diagonal
torus consists exactly of the symplectic monomial matrices. Its permutation action on the
`2m` coordinate lines has kernel the diagonal torus, and therefore induces an injective
homomorphism from the normalizer quotient to the symmetric group.

This supplies the coordinate-line action used to compare the normalizer quotient with the
type-C Weyl group. The image of the action is not computed here. The unit hypothesis separates
the two weights in each symplectic plane; it holds over infinite fields in every characteristic,
but cannot be dropped for rational points over small finite fields.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, Sections 16.1 and 26.3.
* J. S. Milne, *Algebraic Groups* (2017), Example 21.2.

The reduction to monomial matrices and the permutation construction follow
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Normalizer`, using the existing
general-linear normalizer API and the symplectic coordinate-separation theorem.
-/

public section

open Matrix

namespace TauCeti.GLSymplecticFin

noncomputable section

variable {m : ℕ} {k : Type*}

/-- A symplectic matrix that normalizes the full diagonal torus also normalizes the paired
diagonal torus. -/
theorem mem_normalizer_diagonalTorus_of_coe_mem [CommRing k] {g : GLSymplecticFin m k}
    (hg : (g : GL (Fin (m + m)) k) ∈
      Subgroup.normalizer (TauCeti.diagonalTorus k (m + m) : Set (GL (Fin (m + m)) k))) :
    g ∈ Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simpa only [mem_diagonalTorus_iff, TauCeti.mem_diagonalTorus_iff,
    Subgroup.coe_mul, Subgroup.coe_inv] using
    Subgroup.mem_normalizer_iff.mp hg (h : GL (Fin (m + m)) k)

variable [Field k] (u : kˣ) (hu : u ≠ u⁻¹)

include u hu

/-- If a unit differs from its inverse, normalizing the symplectic diagonal torus is equivalent
to normalizing the full diagonal torus in the ambient general linear group. -/
theorem mem_normalizer_diagonalTorus_iff_coe_mem {g : GLSymplecticFin m k} :
    g ∈ Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k)) ↔
      (g : GL (Fin (m + m)) k) ∈
        Subgroup.normalizer (TauCeti.diagonalTorus k (m + m) : Set (GL (Fin (m + m)) k)) := by
  refine ⟨fun hg => ?_, mem_normalizer_diagonalTorus_of_coe_mem⟩
  obtain ⟨d, σ, hfactor⟩ := exists_eq_diagGL_mul_permutationGL_of_forall_ne
    (g := (g : GL (Fin (m + m)) k)) fun i j hij => by
      obtain ⟨t, ht⟩ := exists_diagonalCoordinates_ne u hu hij
      refine ⟨diagonalCoordinates t, ?_, ht⟩
      have hconj := (Subgroup.mem_normalizer_iff.mp hg (diagonal t)).mp
        (mem_diagonalTorus_iff_exists_diagonal.mpr ⟨t, rfl⟩)
      simpa only [mem_diagonalTorus_iff, TauCeti.mem_diagonalTorus_iff,
        Subgroup.coe_mul, Subgroup.coe_inv, coe_diagonal] using hconj
  rw [hfactor]
  exact (Subgroup.normalizer _).mul_mem
    (Subgroup.le_normalizer (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩))
    (permutationGL_mem_normalizer σ)

/-- The normalizer of the paired diagonal torus consists exactly of symplectic monomial
matrices. The diagonal and permutation factors are taken in the ambient general linear group;
they need not separately be symplectic. -/
theorem mem_normalizer_diagonalTorus_iff_exists {g : GLSymplecticFin m k} :
    g ∈ Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k)) ↔
      ∃ d : Fin (m + m) → kˣ, ∃ σ : Equiv.Perm (Fin (m + m)),
        (g : GL (Fin (m + m)) k) = diagGL d * permutationGL (k := k) σ := by
  let : Nontrivial kˣ := nontrivial_of_ne u u⁻¹ hu
  rw [mem_normalizer_diagonalTorus_iff_coe_mem u hu,
    TauCeti.mem_normalizer_diagonalTorus_iff_exists]

/-- The inclusion of the symplectic diagonal normalizer into the ambient diagonal normalizer. -/
private def diagonalNormalizerToGL :
    Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k)) →*
      Subgroup.normalizer (TauCeti.diagonalTorus k (m + m) : Set (GL (Fin (m + m)) k)) :=
  ((GLSymplecticFin m k).subtype.comp (Subgroup.normalizer _).subtype).codRestrict _ fun g =>
    (mem_normalizer_diagonalTorus_iff_coe_mem u hu).mp g.property

private theorem coe_diagonalNormalizerToGL
    (g : Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k))) :
    (diagonalNormalizerToGL u hu g : GL (Fin (m + m)) k) =
      ((g : GLSymplecticFin m k) : GL (Fin (m + m)) k) :=
  (rfl)

/-- The permutation of the `2m` coordinate lines induced by a symplectic matrix normalizing
the paired diagonal torus. -/
def diagonalNormalizerPerm :
    Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k)) →*
      Equiv.Perm (Fin (m + m)) :=
  let : Nontrivial kˣ := nontrivial_of_ne u u⁻¹ hu
  TauCeti.diagonalNormalizerPerm.comp (diagonalNormalizerToGL u hu)

/-- Any monomial factorization reads off the permutation of a symplectic normalizer element. -/
theorem diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL
    (g : Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k)))
    (d : Fin (m + m) → kˣ) (σ : Equiv.Perm (Fin (m + m)))
    (h : ((g : GLSymplecticFin m k) : GL (Fin (m + m)) k) =
      diagGL d * permutationGL (k := k) σ) :
    diagonalNormalizerPerm u hu g = σ := by
  let : Nontrivial kˣ := nontrivial_of_ne u u⁻¹ hu
  apply TauCeti.diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL
    (diagonalNormalizerToGL u hu g) d σ
  simpa only [coe_diagonalNormalizerToGL] using h

/-- The coordinate permutation is independent of the unit used to separate coordinates. -/
theorem diagonalNormalizerPerm_eq (v : kˣ) (hv : v ≠ v⁻¹) :
    diagonalNormalizerPerm (m := m) u hu = diagonalNormalizerPerm v hv := by
  apply MonoidHom.ext
  intro g
  obtain ⟨d, σ, h⟩ := (mem_normalizer_diagonalTorus_iff_exists u hu).mp g.property
  exact (diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL u hu g d σ h).trans
    (diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL v hv g d σ h).symm

/-- A normalizer element acts trivially on coordinate lines exactly when it lies in the
paired diagonal torus. -/
@[simp]
theorem diagonalNormalizerPerm_eq_one_iff
    (g : Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k))) :
    diagonalNormalizerPerm u hu g = 1 ↔ (g : GLSymplecticFin m k) ∈ diagonalTorus k m := by
  let : Nontrivial kˣ := nontrivial_of_ne u u⁻¹ hu
  simpa only [diagonalNormalizerPerm, MonoidHom.comp_apply, coe_diagonalNormalizerToGL,
    mem_diagonalTorus_iff, TauCeti.mem_diagonalTorus_iff] using
    TauCeti.diagonalNormalizerPerm_eq_one_iff (diagonalNormalizerToGL u hu g)

/-- Conjugation by a symplectic normalizer element permutes the paired diagonal entries by
the inverse of its coordinate permutation. -/
theorem coe_diagonalNormalizer_mul_diagonal_mul_inv
    (g : Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k)))
    (t : Fin m → kˣ) :
    (((g : GLSymplecticFin m k) * diagonal t * (g : GLSymplecticFin m k)⁻¹ :
        GLSymplecticFin m k) : GL (Fin (m + m)) k) =
      diagGL (fun i => diagonalCoordinates t ((diagonalNormalizerPerm u hu g).symm i)) := by
  let : Nontrivial kˣ := nontrivial_of_ne u u⁻¹ hu
  simpa only [diagonalNormalizerPerm, MonoidHom.comp_apply, coe_diagonalNormalizerToGL,
    Subgroup.coe_mul, Subgroup.coe_inv, coe_diagonal] using
    TauCeti.diagonalNormalizer_mul_diagGL_mul_inv
      (diagonalNormalizerToGL u hu g) (diagonalCoordinates t)

/-- The action of the symplectic diagonal normalizer quotient on coordinate lines. -/
def diagonalNormalizerQuotientPerm :
    Subgroup.normalizerQuotient (diagonalTorus k m) →* Equiv.Perm (Fin (m + m)) :=
  Subgroup.normalizerQuotientLift (diagonalTorus k m) (diagonalNormalizerPerm u hu)
    (fun g hg => (diagonalNormalizerPerm_eq_one_iff u hu g).mpr hg)

/-- On a quotient representative, the induced action is its coordinate permutation. -/
@[simp]
theorem diagonalNormalizerQuotientPerm_mk
    (g : Subgroup.normalizer (diagonalTorus k m : Set (GLSymplecticFin m k))) :
    diagonalNormalizerQuotientPerm u hu
        (g : Subgroup.normalizerQuotient (diagonalTorus k m)) = diagonalNormalizerPerm u hu g := by
  unfold diagonalNormalizerQuotientPerm
  exact Subgroup.normalizerQuotientLift_mk _ _ _ g

/-- The symplectic diagonal normalizer quotient acts faithfully on the coordinate lines. -/
theorem diagonalNormalizerQuotientPerm_injective :
    Function.Injective (diagonalNormalizerQuotientPerm (m := m) u hu) := by
  rw [diagonalNormalizerQuotientPerm, Subgroup.normalizerQuotientLift_injective_iff]
  exact diagonalNormalizerPerm_eq_one_iff u hu

end

end TauCeti.GLSymplecticFin
