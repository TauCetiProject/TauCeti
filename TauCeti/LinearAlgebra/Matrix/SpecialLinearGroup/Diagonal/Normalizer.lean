/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic

/-!
# The normalizer of the diagonal torus of the special linear group

Over a commutative ring with cancellation by nonzero elements, the diagonal torus of `SL_n(k)`
is the group of determinant-one diagonal matrices, the preimage of the diagonal torus of
`GL_n(k)`. When this torus separates every pair of coordinates, its normalizer in `SL_n(k)`
consists of the determinant-one monomial matrices, and the normalizer quotient is the symmetric
group on the coordinate lines, exactly as for `GL_n(k)`. In dimensions zero and one, the quotient
is trivial over any commutative ring, without cancellation or separation assumptions.

The separation hypothesis cannot simply be dropped. Over `𝔽₃` the torus of `SL₂` is the central
subgroup `{±1}`, so its normalizer is all of `SL₂(𝔽₃)` and the normalizer quotient has order
twelve rather than two; over `𝔽₂` the torus is trivial. In dimensions at least three, however,
the determinant-one torus over `𝔽₃` does separate coordinates, so the natural separation
hypothesis retains that valid case.

This is the group-of-points computation of the Weyl group of the standard split maximal torus of
`SL_n`. It reduces to the `GL_n` computation of
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer`: a normalizer element in
`SL_n(k)` normalizes the diagonal torus of `GL_n(k)`, and its coordinate permutation is read off
there.

## Main declarations

* `Matrix.SpecialLinearGroup.mem_normalizer_diagonalTorus_iff_toGL_mem`: an element of `SL_n(k)`
  normalizes its diagonal torus exactly when it normalizes the diagonal torus of `GL_n(k)`.
* `Matrix.SpecialLinearGroup.diagonalNormalizerPerm`: the coordinate permutation of a normalizer
  element.
* `Matrix.SpecialLinearGroup.diagonalNormalizerPerm_eq_one_iff`: its kernel is the torus.
* `Matrix.SpecialLinearGroup.diagonalNormalizerPerm_surjective`: every permutation arises.
* `Matrix.SpecialLinearGroup.diagonalNormalizerQuotientMulEquivPerm`: the normalizer quotient is
  the symmetric group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 21.2 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 26.3.
-/

public section

open Matrix TauCeti

namespace Matrix.SpecialLinearGroup

universe u

noncomputable section

variable {k : Type u} {n : ℕ}

section CommRing

variable [CommRing k]

/-- In dimensions zero and one, the determinant-one diagonal normalizer quotient is trivial
over any commutative ring. -/
instance [Subsingleton (Fin n)] :
    Subsingleton (Subgroup.normalizerQuotient (diagonalTorus k n)) := by
  apply QuotientGroup.subsingleton_iff.mpr
  apply top_unique
  intro g _
  exact mem_diagonalTorus_iff.mpr (Matrix.isDiag_of_subsingleton _)

/-- An element of `SL_n(k)` normalizing the diagonal torus of `GL_n(k)` normalizes the diagonal
torus of `SL_n(k)`. -/
theorem mem_normalizer_diagonalTorus_of_toGL_mem {g : SpecialLinearGroup (Fin n) k}
    (hg : toGL g ∈ Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) :
    g ∈ Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [mem_diagonalTorus_iff_toGL_mem, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp hg (toGL h)

/-- Conjugation by a normalizer element of the diagonal torus of `SL_n(k)` keeps a diagonal
matrix separating any two given coordinates diagonal. -/
private theorem exists_conj_mem_diagonalTorus_apply_ne
    (hsep : DiagonalTorusSeparatesCoordinates k n)
    {g : SpecialLinearGroup (Fin n) k}
    (hg : g ∈ Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)))
    {i j : Fin n} (hij : i ≠ j) :
    ∃ t : Fin n → kˣ,
      toGL g * diagGL t * (toGL g)⁻¹ ∈ TauCeti.diagonalTorus k n ∧ t i ≠ t j := by
  obtain ⟨t, htprod, htne⟩ := diagonalTorusSeparatesCoordinates_iff.mp hsep i j hij
  let d : SpecialLinearGroup (Fin n) k :=
    ⟨(diagGL t : Matrix (Fin n) (Fin n) k), by
      simpa only [diagGL_coe, det_diagonal] using htprod⟩
  have hd : toGL d = diagGL t := Units.ext rfl
  have hs : d ∈ diagonalTorus k n := by
    rw [mem_diagonalTorus_iff_toGL_mem, hd]
    exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨t, rfl⟩
  have hconj := (Subgroup.mem_normalizer_iff.mp hg _).mp hs
  rw [mem_diagonalTorus_iff_toGL_mem, map_mul, map_mul, map_inv, hd] at hconj
  exact ⟨t, hconj, htne⟩

end CommRing

section IsCancelMulZero

variable [CommRing k] [IsCancelMulZero k]

/-- When the determinant-one diagonal torus separates coordinates, an element of `SL_n(k)`
normalizes it exactly when it normalizes the diagonal torus of `GL_n(k)`, that is, exactly when
it is a monomial matrix. -/
theorem mem_normalizer_diagonalTorus_iff_toGL_mem
    (hsep : DiagonalTorusSeparatesCoordinates k n)
    {g : SpecialLinearGroup (Fin n) k} :
    g ∈ Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) ↔
      toGL g ∈ Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k)) := by
  refine ⟨fun hg ↦ ?_, mem_normalizer_diagonalTorus_of_toGL_mem⟩
  obtain ⟨d, σ, hdσ⟩ := exists_eq_diagGL_mul_permutationGL_of_forall_ne fun i j hij ↦
    exists_conj_mem_diagonalTorus_apply_ne hsep hg hij
  rw [hdσ]
  exact (Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))).mul_mem
    (Subgroup.le_normalizer (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩))
    (permutationGL_mem_normalizer σ)

/-- The homomorphism from the normalizer of the diagonal torus of `SL_n(k)` to the normalizer of
the diagonal torus of `GL_n(k)`. -/
private def diagonalNormalizerToGL (hsep : DiagonalTorusSeparatesCoordinates k n) :
    Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) →*
      Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k)) :=
  (toGL.comp (Subgroup.normalizer _).subtype).codRestrict _ fun g ↦
    (mem_normalizer_diagonalTorus_iff_toGL_mem hsep).mp g.property

/-- The permutation of coordinate lines induced by an element of `SL_n(k)` normalizing its
diagonal torus. It is the coordinate permutation of the same matrix in `GL_n(k)`. -/
def diagonalNormalizerPerm (hsep : DiagonalTorusSeparatesCoordinates k n) :
    Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) →*
      Equiv.Perm (Fin n) := by
  classical
  by_cases hn : Subsingleton (Fin n)
  · exact 1
  · let _ := hsep.nontrivial_of_not_subsingleton hn
    exact TauCeti.diagonalNormalizerPerm.comp (diagonalNormalizerToGL hsep)

/-- The coordinate permutation of a normalizer element of `SL_n(k)` is the coordinate permutation
of the same matrix in `GL_n(k)`. -/
theorem diagonalNormalizerPerm_apply (hsep : DiagonalTorusSeparatesCoordinates k n)
    (hn : ¬ Subsingleton (Fin n))
    (g : Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k))) :
    diagonalNormalizerPerm hsep g =
      let _ := hsep.nontrivial_of_not_subsingleton hn
      TauCeti.diagonalNormalizerPerm
        ⟨toGL (g : SpecialLinearGroup (Fin n) k),
          (mem_normalizer_diagonalTorus_iff_toGL_mem hsep).mp g.property⟩ := by
  classical
  rw [diagonalNormalizerPerm]
  split
  · contradiction
  · rfl

/-- There is only the trivial coordinate permutation when the coordinate type is a
subsingleton. -/
@[simp]
theorem diagonalNormalizerPerm_apply_of_subsingleton
    (hsep : DiagonalTorusSeparatesCoordinates k n) [Subsingleton (Fin n)]
    (g : Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k))) :
    diagonalNormalizerPerm hsep g = 1 :=
  Subsingleton.elim _ _

/-- The coordinate permutation of a normalizer element of the diagonal torus of `SL_n(k)` is
trivial exactly for elements of the torus. -/
@[simp]
theorem diagonalNormalizerPerm_eq_one_iff (hsep : DiagonalTorusSeparatesCoordinates k n)
    (g : Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k))) :
    diagonalNormalizerPerm hsep g = 1 ↔
      (g : SpecialLinearGroup (Fin n) k) ∈ diagonalTorus k n := by
  classical
  by_cases hn : Subsingleton (Fin n)
  · let _ := hn
    constructor
    · intro _
      rw [mem_diagonalTorus_iff_toGL_mem, TauCeti.mem_diagonalTorus_iff]
      exact Matrix.isDiag_of_subsingleton _
    · intro _
      exact diagonalNormalizerPerm_apply_of_subsingleton hsep g
  · let _ := hsep.nontrivial_of_not_subsingleton hn
    rw [diagonalNormalizerPerm_apply hsep hn,
      TauCeti.diagonalNormalizerPerm_eq_one_iff, mem_diagonalTorus_iff_toGL_mem]

/-- Every permutation of the coordinate lines is induced by an element of `SL_n(k)` normalizing
the diagonal torus: a permutation matrix with a diagonal correction of its determinant. -/
theorem diagonalNormalizerPerm_surjective (hsep : DiagonalTorusSeparatesCoordinates k n) :
    Function.Surjective (diagonalNormalizerPerm (k := k) (n := n) hsep) := by
  classical
  by_cases hn : Subsingleton (Fin n)
  · let _ := hn
    intro σ
    refine ⟨1, ?_⟩
    rw [map_one, Subsingleton.elim σ 1]
  · let _ := hsep.nontrivial_of_not_subsingleton hn
    intro σ
    obtain ⟨g, d, hg⟩ := GeneralLinearGroup.exists_toGL_mul_eq
      ((permutationGL (k := k) σ)⁻¹)
    have hg' : toGL g⁻¹ = diagGL d * permutationGL (k := k) σ := by
      rw [map_inv, inv_eq_iff_mul_eq_one, ← mul_assoc, hg, inv_mul_cancel]
    have hgN : g⁻¹ ∈ Subgroup.normalizer
        (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) :=
      mem_normalizer_diagonalTorus_of_toGL_mem
        ((mem_normalizer_diagonalTorus_iff_exists (k := k)).mpr ⟨d, σ, hg'⟩)
    refine ⟨⟨g⁻¹, hgN⟩, ?_⟩
    rw [diagonalNormalizerPerm_apply hsep hn]
    exact diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL _ d σ hg'

/-- **The Weyl group of the diagonal torus of `SL_n(k)`**: when the determinant-one diagonal
torus separates coordinates, its normalizer modulo the torus is canonically the symmetric group
on the coordinate lines. -/
def diagonalNormalizerQuotientMulEquivPerm
    (hsep : DiagonalTorusSeparatesCoordinates k n) :
    Subgroup.normalizerQuotient (diagonalTorus k n) ≃* Equiv.Perm (Fin n) := by
  let φ := diagonalNormalizerPerm (k := k) (n := n) hsep
  have hkill : ∀ g : Subgroup.normalizer
      (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)),
      (g : SpecialLinearGroup (Fin n) k) ∈ diagonalTorus k n → φ g = 1 :=
    fun g hg ↦ (diagonalNormalizerPerm_eq_one_iff hsep g).mpr hg
  apply MulEquiv.ofBijective (Subgroup.normalizerQuotientLift (diagonalTorus k n) φ hkill)
  constructor
  · exact (Subgroup.normalizerQuotientLift_injective_iff
      (diagonalTorus k n) φ hkill).mpr (diagonalNormalizerPerm_eq_one_iff hsep)
  · exact Subgroup.normalizerQuotientLift_surjective_of_surjective
      (diagonalTorus k n) φ hkill (diagonalNormalizerPerm_surjective hsep)

/-- The quotient equivalence sends the class of a normalizer element to its coordinate
permutation. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivPerm_mk
    (hsep : DiagonalTorusSeparatesCoordinates k n)
    (g : Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k))) :
    diagonalNormalizerQuotientMulEquivPerm hsep
        (g : Subgroup.normalizerQuotient (diagonalTorus k n)) =
      diagonalNormalizerPerm hsep g :=
  (rfl)

end IsCancelMulZero

end

end Matrix.SpecialLinearGroup
