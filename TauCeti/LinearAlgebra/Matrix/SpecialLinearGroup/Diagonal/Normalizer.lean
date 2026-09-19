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

The diagonal torus of `SL_n(k)` is the group of determinant-one diagonal matrices, the preimage
of the diagonal torus of `GL_n(k)`. When this torus separates every pair of coordinates, its
normalizer in `SL_n(k)` consists of the determinant-one monomial matrices, and the normalizer
quotient is the symmetric group on the coordinate lines, exactly as for `GL_n(k)`.

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

* `Matrix.SpecialLinearGroup.diagonalTorus`: the diagonal torus of `SL_n(k)`.
* `Matrix.SpecialLinearGroup.DiagonalTorusSeparatesCoordinates`: the coordinate-separation
  hypothesis used by the normalizer computation.
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

/-- An element of `SL_n(k)` normalizing the diagonal torus of `GL_n(k)` normalizes the diagonal
torus of `SL_n(k)`. -/
theorem mem_normalizer_diagonalTorus_of_toGL_mem {g : SpecialLinearGroup (Fin n) k}
    (hg : toGL g ∈ Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) :
    g ∈ Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [mem_diagonalTorus_iff_toGL_mem, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp hg (toGL h)

end CommRing

section Field

variable [Field k]

/-- The determinant-one diagonal torus separates coordinates if the unit group is nontrivial and
each pair of distinct coordinates receives different values under some diagonal element of
determinant one. The nontriviality component supplies the hypothesis needed by the corresponding
`GL_n` coordinate-permutation API. -/
def DiagonalTorusSeparatesCoordinates (k : Type u) [Field k] (n : ℕ) : Prop :=
  Nontrivial kˣ ∧
    ∀ i j : Fin n, i ≠ j → ∃ t : Fin n → kˣ, ∏ r, (t r : k) = 1 ∧ t i ≠ t j

/-- A unit whose square is not one makes the determinant-one diagonal torus separate
coordinates. -/
theorem diagonalTorusSeparatesCoordinates_of_exists_sq_ne_one
    (hk : ∃ a : kˣ, a ^ 2 ≠ 1) : DiagonalTorusSeparatesCoordinates k n := by
  obtain ⟨a, ha⟩ := hk
  refine ⟨nontrivial_of_ne a 1 fun h ↦ ha (by rw [h, one_pow]), ?_⟩
  intro i j hij
  let t : Fin n → kˣ := fun r ↦ if r = i then a else if r = j then a⁻¹ else 1
  refine ⟨t, ?_, ?_⟩
  · have ht (r : Fin n) : (t r : k) =
        if r = i then (a : k) else if r = j then ((a⁻¹ : kˣ) : k) else 1 := by
      simp only [t]
      split_ifs <;> rfl
    have ht' : (fun r ↦ (t r : k)) = fun r ↦
        if r = i then (a : k) else if r = j then ((a⁻¹ : kˣ) : k) else 1 := funext ht
    rw [ht']
    simpa only [diag2nUnit_coe, det_diagonal] using (diag2nUnit hij a).property
  · intro h
    have h' : a = a⁻¹ := by simpa [t, Ne.symm hij] using h
    apply ha
    rw [sq]
    nth_rw 2 [h']
    exact mul_inv_cancel a

/-- Conjugation by a normalizer element of the diagonal torus of `SL_n(k)` keeps a diagonal
matrix separating any two given coordinates diagonal. -/
private theorem exists_conj_mem_diagonalTorus_apply_ne
    (hsep : DiagonalTorusSeparatesCoordinates k n)
    {g : SpecialLinearGroup (Fin n) k}
    (hg : g ∈ Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)))
    {i j : Fin n} (hij : i ≠ j) :
    ∃ t : Fin n → kˣ,
      toGL g * diagGL t * (toGL g)⁻¹ ∈ TauCeti.diagonalTorus k n ∧ t i ≠ t j := by
  obtain ⟨t, htprod, htne⟩ := hsep.2 i j hij
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

/-- Coordinate separation includes nontriviality of the unit group. -/
theorem DiagonalTorusSeparatesCoordinates.nontrivial
    (hsep : DiagonalTorusSeparatesCoordinates k n) : Nontrivial kˣ := by
  exact hsep.1

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
      Equiv.Perm (Fin n) :=
  letI := hsep.nontrivial
  TauCeti.diagonalNormalizerPerm.comp (diagonalNormalizerToGL hsep)

/-- The coordinate permutation of a normalizer element of `SL_n(k)` is the coordinate permutation
of the same matrix in `GL_n(k)`. -/
@[simp]
theorem diagonalNormalizerPerm_apply (hsep : DiagonalTorusSeparatesCoordinates k n)
    (g : Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k))) :
    diagonalNormalizerPerm hsep g =
      let _ := hsep.nontrivial
      TauCeti.diagonalNormalizerPerm
        ⟨toGL (g : SpecialLinearGroup (Fin n) k),
          (mem_normalizer_diagonalTorus_iff_toGL_mem hsep).mp g.property⟩ :=
  by
    let _ := hsep.nontrivial
    rfl

/-- The coordinate permutation of a normalizer element of the diagonal torus of `SL_n(k)` is
trivial exactly for elements of the torus. -/
@[simp]
theorem diagonalNormalizerPerm_eq_one_iff (hsep : DiagonalTorusSeparatesCoordinates k n)
    (g : Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k))) :
    diagonalNormalizerPerm hsep g = 1 ↔
      (g : SpecialLinearGroup (Fin n) k) ∈ diagonalTorus k n := by
  let _ := hsep.nontrivial
  rw [diagonalNormalizerPerm_apply, TauCeti.diagonalNormalizerPerm_eq_one_iff,
    mem_diagonalTorus_iff_toGL_mem]

/-- A permutation matrix corrected by a sign in one diagonal position has determinant one. -/
private theorem exists_toGL_eq_diagGL_mul_permutationGL (σ : Equiv.Perm (Fin n)) :
    ∃ (g : SpecialLinearGroup (Fin n) k) (d : Fin n → kˣ),
      toGL g = diagGL d * permutationGL (k := k) σ := by
  rcases n with _ | n
  · refine ⟨1, 1, ?_⟩
    rw [Subsingleton.elim σ 1, map_one, map_one, map_one, one_mul]
  · let s : kˣ := Units.map (Int.castRingHom k).toMonoidHom (Equiv.Perm.sign σ)
    let d : Fin (n + 1) → kˣ := Pi.mulSingle 0 s
    have hdet : ((diagGL d * permutationGL (k := k) σ : GL (Fin (n + 1)) k) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1 := by
      have hprod : ∏ i, (d i : k) = s := by
        rw [Fintype.prod_eq_single 0 fun i hi ↦ by simp [d, Pi.mulSingle_eq_of_ne hi]]
        simp [d]
      rw [Units.val_mul, det_mul, diagGL_coe, det_diagonal, hprod, permutationGL_coe,
        det_permutation, Equiv.Perm.sign_inv]
      simp only [s, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
        eq_intCast]
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    exact ⟨⟨_, hdet⟩, d, Units.ext (coe_GL_coe_matrix _)⟩

/-- Every permutation of the coordinate lines is induced by an element of `SL_n(k)` normalizing
the diagonal torus: a permutation matrix with a sign correcting its determinant. -/
theorem diagonalNormalizerPerm_surjective (hsep : DiagonalTorusSeparatesCoordinates k n) :
    Function.Surjective (diagonalNormalizerPerm (k := k) (n := n) hsep) := by
  let _ := hsep.nontrivial
  intro σ
  obtain ⟨g, d, hg⟩ := exists_toGL_eq_diagGL_mul_permutationGL (k := k) σ
  have hgN : g ∈ Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) :=
    mem_normalizer_diagonalTorus_of_toGL_mem
      ((mem_normalizer_diagonalTorus_iff_exists (k := k)).mpr ⟨d, σ, hg⟩)
  refine ⟨⟨g, hgN⟩, ?_⟩
  rw [diagonalNormalizerPerm_apply]
  exact diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL _ d σ hg

/-- **The Weyl group of the diagonal torus of `SL_n(k)`**: when the determinant-one diagonal
torus separates coordinates, its normalizer modulo the torus is canonically the symmetric group
on the coordinate lines. -/
def diagonalNormalizerQuotientMulEquivPerm
    (hsep : DiagonalTorusSeparatesCoordinates k n) :
    TauCeti.Subgroup.normalizerQuotient (diagonalTorus k n) ≃* Equiv.Perm (Fin n) := by
  let φ := diagonalNormalizerPerm (k := k) (n := n) hsep
  have hkill : ∀ g : Subgroup.normalizer
      (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)),
      (g : SpecialLinearGroup (Fin n) k) ∈ diagonalTorus k n → φ g = 1 :=
    fun g hg ↦ (diagonalNormalizerPerm_eq_one_iff hsep g).mpr hg
  apply MulEquiv.ofBijective (TauCeti.Subgroup.normalizerQuotientLift (diagonalTorus k n) φ hkill)
  constructor
  · exact (TauCeti.Subgroup.normalizerQuotientLift_injective_iff
      (diagonalTorus k n) φ hkill).mpr (diagonalNormalizerPerm_eq_one_iff hsep)
  · exact TauCeti.Subgroup.normalizerQuotientLift_surjective_of_surjective
      (diagonalTorus k n) φ hkill (diagonalNormalizerPerm_surjective hsep)

/-- The quotient equivalence sends the class of a normalizer element to its coordinate
permutation. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivPerm_mk
    (hsep : DiagonalTorusSeparatesCoordinates k n)
    (g : Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k))) :
    diagonalNormalizerQuotientMulEquivPerm hsep
        (g : TauCeti.Subgroup.normalizerQuotient (diagonalTorus k n)) =
      diagonalNormalizerPerm hsep g :=
  (rfl)

end Field

end

end Matrix.SpecialLinearGroup
