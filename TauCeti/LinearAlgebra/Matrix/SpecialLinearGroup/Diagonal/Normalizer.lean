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
of the diagonal torus of `GL_n(k)`. Over a field with a unit `a` satisfying `a ^ 2 ≠ 1`, the
torus of `SL_n(k)` separates the coordinates: `diag(…, a, …, a⁻¹, …)` takes different values at
the two chosen positions. Its normalizer in `SL_n(k)` then consists of the determinant-one
monomial matrices, and the normalizer quotient is the symmetric group on the coordinate lines,
exactly as for `GL_n(k)`.

The separation hypothesis cannot simply be dropped. Over `𝔽₃` the torus of `SL₂` is the central
subgroup `{±1}`, so its normalizer is all of `SL₂(𝔽₃)` and the normalizer quotient has order
twelve rather than two; over `𝔽₂` the torus is trivial.

This is the group-of-points computation of the Weyl group of the standard split maximal torus of
`SL_n`. It reduces to the `GL_n` computation of
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer`: a normalizer element in
`SL_n(k)` normalizes the diagonal torus of `GL_n(k)`, and its coordinate permutation is read off
there.

## Main declarations

* `Matrix.SpecialLinearGroup.diagonalTorus`: the diagonal torus of `SL_n(k)`.
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

variable (k n) in
/-- The diagonal torus of `SL_n(k)`: the determinant-one invertible diagonal matrices, that is,
the preimage of the diagonal torus of `GL_n(k)`. -/
def diagonalTorus : Subgroup (SpecialLinearGroup (Fin n) k) :=
  (TauCeti.diagonalTorus k n).comap toGL

/-- An element of `SL_n(k)` lies in its diagonal torus exactly when it lies in the diagonal torus
of `GL_n(k)`. -/
theorem mem_diagonalTorus_iff_toGL_mem {g : SpecialLinearGroup (Fin n) k} :
    g ∈ diagonalTorus k n ↔ toGL g ∈ TauCeti.diagonalTorus k n :=
  Subgroup.mem_comap

/-- An element of `SL_n(k)` lies in its diagonal torus exactly when it is a diagonal matrix. -/
@[simp]
theorem mem_diagonalTorus_iff {g : SpecialLinearGroup (Fin n) k} :
    g ∈ diagonalTorus k n ↔ (g : Matrix (Fin n) (Fin n) k).IsDiag := by
  rw [mem_diagonalTorus_iff_toGL_mem, TauCeti.mem_diagonalTorus_iff, coe_GL_coe_matrix]

/-- An element of `SL_n(k)` normalizing the diagonal torus of `GL_n(k)` normalizes the diagonal
torus of `SL_n(k)`. -/
theorem mem_normalizer_diagonalTorus_of_toGL_mem {g : SpecialLinearGroup (Fin n) k}
    (hg : toGL g ∈ Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) :
    g ∈ Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [mem_diagonalTorus_iff_toGL_mem, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp hg (toGL h)

/-- The diagonal matrix `diag2nUnit hij a`, viewed in `GL_n(k)`, is `diagGL` of its diagonal
entries. -/
theorem toGL_diag2nUnit {i j : Fin n} (hij : i ≠ j) (a : kˣ) :
    toGL (diag2nUnit hij a) =
      diagGL (fun r ↦ if r = i then a else if r = j then a⁻¹ else 1) := by
  apply Units.ext
  rw [coe_GL_coe_matrix, diag2nUnit_coe, diagGL_coe]
  congr 1
  funext r
  split_ifs <;> simp

end CommRing

section Field

variable [Field k]

/-- Conjugation by a normalizer element of the diagonal torus of `SL_n(k)` keeps a diagonal
matrix separating any two given coordinates diagonal. -/
private theorem exists_conj_mem_diagonalTorus_apply_ne (hk : ∃ a : kˣ, a ^ 2 ≠ 1)
    {g : SpecialLinearGroup (Fin n) k}
    (hg : g ∈ Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)))
    {i j : Fin n} (hij : i ≠ j) :
    ∃ t : Fin n → kˣ,
      toGL g * diagGL t * (toGL g)⁻¹ ∈ TauCeti.diagonalTorus k n ∧ t i ≠ t j := by
  obtain ⟨a, ha⟩ := hk
  have hs : diag2nUnit hij a ∈ diagonalTorus k n := by
    rw [mem_diagonalTorus_iff, diag2nUnit_coe]
    exact isDiag_diagonal _
  have hconj := (Subgroup.mem_normalizer_iff.mp hg _).mp hs
  rw [mem_diagonalTorus_iff_toGL_mem, map_mul, map_mul, map_inv, toGL_diag2nUnit] at hconj
  refine ⟨_, hconj, ?_⟩
  intro h
  have h' : a = a⁻¹ := by simpa [Ne.symm hij] using h
  apply ha
  rw [sq]
  nth_rw 2 [h']
  exact mul_inv_cancel a

/-- Over a field with a unit whose square is not `1`, an element of `SL_n(k)` normalizes its
diagonal torus exactly when it normalizes the diagonal torus of `GL_n(k)`, that is, exactly when
it is a monomial matrix. -/
theorem mem_normalizer_diagonalTorus_iff_toGL_mem (hk : ∃ a : kˣ, a ^ 2 ≠ 1)
    {g : SpecialLinearGroup (Fin n) k} :
    g ∈ Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) ↔
      toGL g ∈ Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k)) := by
  refine ⟨fun hg ↦ ?_, mem_normalizer_diagonalTorus_of_toGL_mem⟩
  obtain ⟨d, σ, hdσ⟩ := exists_eq_diagGL_mul_permutationGL_of_forall_ne fun i j hij ↦
    exists_conj_mem_diagonalTorus_apply_ne hk hg hij
  rw [hdσ]
  exact (Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))).mul_mem
    (Subgroup.le_normalizer (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩))
    (permutationGL_mem_normalizer σ)

/-- A unit whose square is not `1` makes the unit group nontrivial. -/
private theorem nontrivial_units_of_exists_sq_ne_one (hk : ∃ a : kˣ, a ^ 2 ≠ 1) :
    Nontrivial kˣ := by
  obtain ⟨a, ha⟩ := hk
  exact nontrivial_of_ne a 1 fun h ↦ ha (by rw [h, one_pow])

/-- The homomorphism from the normalizer of the diagonal torus of `SL_n(k)` to the normalizer of
the diagonal torus of `GL_n(k)`. -/
private def diagonalNormalizerToGL (hk : ∃ a : kˣ, a ^ 2 ≠ 1) :
    Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) →*
      Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k)) :=
  (toGL.comp (Subgroup.normalizer _).subtype).codRestrict _ fun g ↦
    (mem_normalizer_diagonalTorus_iff_toGL_mem hk).mp g.property

/-- The permutation of coordinate lines induced by an element of `SL_n(k)` normalizing its
diagonal torus. It is the coordinate permutation of the same matrix in `GL_n(k)`. -/
def diagonalNormalizerPerm (hk : ∃ a : kˣ, a ^ 2 ≠ 1) :
    Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) →*
      Equiv.Perm (Fin n) :=
  haveI := nontrivial_units_of_exists_sq_ne_one hk
  TauCeti.diagonalNormalizerPerm.comp (diagonalNormalizerToGL hk)

/-- The coordinate permutation of a normalizer element of `SL_n(k)` is the coordinate permutation
of the same matrix in `GL_n(k)`. -/
theorem diagonalNormalizerPerm_apply [Nontrivial kˣ] (hk : ∃ a : kˣ, a ^ 2 ≠ 1)
    (g : Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k))) :
    diagonalNormalizerPerm hk g = TauCeti.diagonalNormalizerPerm
      ⟨toGL (g : SpecialLinearGroup (Fin n) k),
        (mem_normalizer_diagonalTorus_iff_toGL_mem hk).mp g.property⟩ :=
  (rfl)

/-- Conjugation by a normalizer element of the diagonal torus of `SL_n(k)` relabels the diagonal
entries by its coordinate permutation: the entry at `i` becomes the original entry at the inverse
image of `i`. -/
theorem diagonalNormalizer_toGL_mul_diagGL_mul_inv (hk : ∃ a : kˣ, a ^ 2 ≠ 1)
    (g : Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)))
    (t : Fin n → kˣ) :
    toGL (g : SpecialLinearGroup (Fin n) k) * diagGL t *
        (toGL (g : SpecialLinearGroup (Fin n) k))⁻¹ =
      diagGL (fun i ↦ t ((diagonalNormalizerPerm hk g).symm i)) := by
  have := nontrivial_units_of_exists_sq_ne_one hk
  rw [diagonalNormalizerPerm_apply]
  exact diagonalNormalizer_mul_diagGL_mul_inv
    ⟨toGL (g : SpecialLinearGroup (Fin n) k),
      (mem_normalizer_diagonalTorus_iff_toGL_mem hk).mp g.property⟩ t

/-- The coordinate permutation of a normalizer element of the diagonal torus of `SL_n(k)` is
trivial exactly for elements of the torus. -/
@[simp]
theorem diagonalNormalizerPerm_eq_one_iff (hk : ∃ a : kˣ, a ^ 2 ≠ 1)
    (g : Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k))) :
    diagonalNormalizerPerm hk g = 1 ↔ (g : SpecialLinearGroup (Fin n) k) ∈ diagonalTorus k n := by
  have := nontrivial_units_of_exists_sq_ne_one hk
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
theorem diagonalNormalizerPerm_surjective (hk : ∃ a : kˣ, a ^ 2 ≠ 1) :
    Function.Surjective (diagonalNormalizerPerm (k := k) (n := n) hk) := by
  have := nontrivial_units_of_exists_sq_ne_one hk
  intro σ
  obtain ⟨g, d, hg⟩ := exists_toGL_eq_diagGL_mul_permutationGL (k := k) σ
  have hgN : g ∈ Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)) :=
    mem_normalizer_diagonalTorus_of_toGL_mem
      ((mem_normalizer_diagonalTorus_iff_exists (k := k)).mpr ⟨d, σ, hg⟩)
  refine ⟨⟨g, hgN⟩, ?_⟩
  rw [diagonalNormalizerPerm_apply]
  exact diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL _ d σ hg

/-- **The Weyl group of the diagonal torus of `SL_n(k)`**: over a field with a unit whose square
is not `1`, the normalizer of the diagonal torus modulo the torus is canonically the symmetric
group on the coordinate lines. -/
def diagonalNormalizerQuotientMulEquivPerm (hk : ∃ a : kˣ, a ^ 2 ≠ 1) :
    TauCeti.Subgroup.normalizerQuotient (diagonalTorus k n) ≃* Equiv.Perm (Fin n) := by
  let φ := diagonalNormalizerPerm (k := k) (n := n) hk
  have hkill : ∀ g : Subgroup.normalizer
      (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)),
      (g : SpecialLinearGroup (Fin n) k) ∈ diagonalTorus k n → φ g = 1 :=
    fun g hg ↦ (diagonalNormalizerPerm_eq_one_iff hk g).mpr hg
  apply MulEquiv.ofBijective (TauCeti.Subgroup.normalizerQuotientLift (diagonalTorus k n) φ hkill)
  constructor
  · exact (TauCeti.Subgroup.normalizerQuotientLift_injective_iff
      (diagonalTorus k n) φ hkill).mpr (diagonalNormalizerPerm_eq_one_iff hk)
  · exact TauCeti.Subgroup.normalizerQuotientLift_surjective_of_surjective
      (diagonalTorus k n) φ hkill (diagonalNormalizerPerm_surjective hk)

/-- The quotient equivalence sends the class of a normalizer element to its coordinate
permutation. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivPerm_mk (hk : ∃ a : kˣ, a ^ 2 ≠ 1)
    (g : Subgroup.normalizer (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k))) :
    diagonalNormalizerQuotientMulEquivPerm hk
        (g : TauCeti.Subgroup.normalizerQuotient (diagonalTorus k n)) =
      diagonalNormalizerPerm hk g :=
  (rfl)

end Field

end

end Matrix.SpecialLinearGroup
