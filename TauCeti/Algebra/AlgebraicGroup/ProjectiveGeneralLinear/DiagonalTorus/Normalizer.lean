/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.DiagonalTorus.Maximal
public import TauCeti.Algebra.Group.NormalizerQuotient.Surjective
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.InnerAut

/-!
# The projective diagonal torus normalizer

The diagonal torus of `PGLₙ` is the image of the diagonal torus of `GLₙ` in the
automorphism group of the matrix algebra. Its full inverse image in `GLₙ` is
the diagonal torus: the scalar kernel of conjugation is already diagonal.
Over a local ring, every matrix-algebra automorphism is inner, so conjugation
induces an isomorphism between the two normalizer quotients.

Over a field with at least two units, the projective normalizer therefore
consists exactly of conjugations by monomial matrices, and its quotient by
the diagonal torus is the symmetric group. The equivalence sends the class
of a permutation-matrix conjugation to that permutation. In particular this
computes the geometric torus normalizer quotient in every characteristic.
The nontrivial-units hypothesis matters for rational points: over `𝔽₂` the
rational diagonal torus is trivial.

The calculation reuses `Matrix.GeneralLinearGroup.innerAut_surjective`, the
general-linear diagonal normalizer calculation, and
`Subgroup.normalizerQuotientEquivOfComapEq`. The point-membership theorem connects
the automorphism-group model to the closed torus in Hopf coordinates.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §§16.1 and 26.3.
-/

public section

open Matrix

namespace TauCeti.ProjectiveGeneralLinear

universe u v w

noncomputable section

variable (n : ℕ) (R : Type u) [CommRing R]

/-- Diagonal conjugations in the matrix-algebra model of `PGLₙ`. -/
def diagonalAutSubgroup : Subgroup (Matrix (Fin n) (Fin n) R ≃ₐ[R]
    Matrix (Fin n) (Fin n) R) :=
  (TauCeti.diagonalTorus R n).map Matrix.GeneralLinearGroup.innerAut

/-- An automorphism is in the projective diagonal torus exactly when it is
conjugation by an invertible diagonal matrix. -/
theorem mem_diagonalAutSubgroup_iff
    (f : Matrix (Fin n) (Fin n) R ≃ₐ[R] Matrix (Fin n) (Fin n) R) :
    f ∈ diagonalAutSubgroup n R ↔
      ∃ d : Fin n → Rˣ, Matrix.GeneralLinearGroup.innerAut (diagGL d) = f := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨d, rfl⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hg
    exact ⟨d, rfl⟩
  · rintro ⟨d, rfl⟩
    exact ⟨diagGL d, mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩, rfl⟩

/-- The full inverse image of the projective diagonal torus is the diagonal
torus of `GLₙ`, over every commutative ring. -/
@[simp]
theorem comap_diagonalAutSubgroup_innerAut :
    (diagonalAutSubgroup n R).comap Matrix.GeneralLinearGroup.innerAut =
      TauCeti.diagonalTorus R n := by
  apply Subgroup.comap_map_eq_self
  rw [Matrix.GeneralLinearGroup.ker_innerAut]
  intro g hg
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hg
  rw [mem_diagonalTorus_iff, ← ha]
  exact Matrix.isDiag_diagonal _

/-- Under the matrix-algebra point equivalence, the closed normalized diagonal
torus is precisely the subgroup of diagonal conjugations. This also holds for
nonreduced value algebras. -/
theorem mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff_mem_diagonalAutSubgroup
    (r : ℕ) (A : CommAlgCat.{w} R)
    (q : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra (r + 1) R) A) :
    q ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra (r + 1) R)
        (diagonalTorusDefiningIdeal r R) A ↔
      pointsMulEquiv (r + 1) R A q ∈ diagonalAutSubgroup (r + 1) A := by
  rw [mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff,
    mem_diagonalAutSubgroup_iff]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨Fin.lastCases 1 (fun i ↦ s (ULift.up i)), hs.symm⟩
  · rintro ⟨d, hd⟩
    exact ⟨fun i ↦ d i.down.castSucc / d (Fin.last r),
      hd.symm.trans (Matrix.GeneralLinearGroup.innerAut_diagGL_normalize r d)⟩

/-- A conjugation normalizes the projective diagonal torus
exactly when its matrix normalizes the ordinary diagonal torus. -/
theorem innerAut_mem_normalizer_diagonalAutSubgroup_iff (g : GL (Fin n) R) :
    Matrix.GeneralLinearGroup.innerAut g ∈
        Subgroup.normalizer (diagonalAutSubgroup n R :
        Set (Matrix (Fin n) (Fin n) R ≃ₐ[R] Matrix (Fin n) (Fin n) R)) ↔
      g ∈ Subgroup.normalizer (TauCeti.diagonalTorus R n : Set (GL (Fin n) R)) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (H := diagonalAutSubgroup n R)
    (f := Matrix.GeneralLinearGroup.innerAut) (fun _ ⟨g, _, hg⟩ ↦ ⟨g, hg⟩)
  rw [comap_diagonalAutSubgroup_innerAut] at h
  exact SetLike.ext_iff.mp h g

/-- Conjugation maps the ordinary diagonal normalizer to the projective one. -/
def diagonalNormalizerHom :
    Subgroup.normalizer (TauCeti.diagonalTorus R n : Set (GL (Fin n) R)) →*
      Subgroup.normalizer (diagonalAutSubgroup n R :
        Set (Matrix (Fin n) (Fin n) R ≃ₐ[R] Matrix (Fin n) (Fin n) R)) :=
  (Matrix.GeneralLinearGroup.innerAut.comp
    (Subgroup.normalizer (TauCeti.diagonalTorus R n : Set (GL (Fin n) R))).subtype).codRestrict
      (Subgroup.normalizer (diagonalAutSubgroup n R :
        Set (Matrix (Fin n) (Fin n) R ≃ₐ[R] Matrix (Fin n) (Fin n) R))) fun g ↦
        (innerAut_mem_normalizer_diagonalAutSubgroup_iff n R (g : GL (Fin n) R)).mpr g.property

/-- The normalizer homomorphism sends a matrix to its inner automorphism. -/
@[simp]
theorem coe_diagonalNormalizerHom
    (g : Subgroup.normalizer (TauCeti.diagonalTorus R n : Set (GL (Fin n) R))) :
    (diagonalNormalizerHom n R g : Matrix (Fin n) (Fin n) R ≃ₐ[R]
      Matrix (Fin n) (Fin n) R) = Matrix.GeneralLinearGroup.innerAut (g : GL (Fin n) R) :=
  (rfl)

section LocalRing

variable [IsLocalRing R]

/-- Conjugation induces an isomorphism between the ordinary and projective
diagonal normalizer quotients over a local ring. -/
def diagonalNormalizerQuotientEquiv :
    Subgroup.normalizerQuotient (TauCeti.diagonalTorus R n) ≃*
      Subgroup.normalizerQuotient (diagonalAutSubgroup n R) :=
  (TauCeti.diagonalTorus R n).normalizerQuotientEquivOfComapEq
    (diagonalAutSubgroup n R) Matrix.GeneralLinearGroup.innerAut
    (Matrix.GeneralLinearGroup.innerAut_surjective R)
    (comap_diagonalAutSubgroup_innerAut n R)

/-- The comparison of normalizer quotients sends a matrix class to the class
of its inner automorphism. -/
@[simp]
theorem diagonalNormalizerQuotientEquiv_mk
    (g : Subgroup.normalizer (TauCeti.diagonalTorus R n : Set (GL (Fin n) R))) :
    diagonalNormalizerQuotientEquiv n R
        (g : Subgroup.normalizerQuotient (TauCeti.diagonalTorus R n)) =
      (diagonalNormalizerHom n R g :
        Subgroup.normalizerQuotient (diagonalAutSubgroup n R)) := by
  rw [diagonalNormalizerQuotientEquiv, Subgroup.normalizerQuotientEquivOfComapEq_mk]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_normalizerHomOfComapEq, coe_diagonalNormalizerHom]

end LocalRing

section Field

variable (k : Type v) [Field k] [Nontrivial kˣ]

/-- The projective diagonal normalizer consists of the conjugations by
monomial matrices. -/
theorem mem_normalizer_diagonalAutSubgroup_iff_exists
    (f : Matrix (Fin n) (Fin n) k ≃ₐ[k] Matrix (Fin n) (Fin n) k) :
    f ∈ Subgroup.normalizer (diagonalAutSubgroup n k :
        Set (Matrix (Fin n) (Fin n) k ≃ₐ[k] Matrix (Fin n) (Fin n) k)) ↔
      ∃ d : Fin n → kˣ, ∃ σ : Equiv.Perm (Fin n),
        f = Matrix.GeneralLinearGroup.innerAut (diagGL d * permutationGL σ) := by
  constructor
  · intro hf
    obtain ⟨g, rfl⟩ := Matrix.GeneralLinearGroup.innerAut_surjective k f
    obtain ⟨d, σ, rfl⟩ := mem_normalizer_diagonalTorus_iff_exists.mp
      ((innerAut_mem_normalizer_diagonalAutSubgroup_iff n k g).mp hf)
    exact ⟨d, σ, rfl⟩
  · rintro ⟨d, σ, rfl⟩
    exact (innerAut_mem_normalizer_diagonalAutSubgroup_iff n k _).mpr
      (mem_normalizer_diagonalTorus_iff_exists.mpr ⟨d, σ, rfl⟩)

/-- The projective diagonal normalizer quotient is the symmetric group on
the coordinate lines. In particular this computes the geometric quotient
over every algebraically closed field. -/
def diagonalNormalizerQuotientMulEquivPerm :
    Subgroup.normalizerQuotient (diagonalAutSubgroup n k) ≃* Equiv.Perm (Fin n) :=
  (diagonalNormalizerQuotientEquiv n k).symm.trans
    (TauCeti.diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n))

/-- The projective quotient sends a lifted normalizer class to the coordinate
permutation of the lifting matrix. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivPerm_mk
    (g : Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) :
    diagonalNormalizerQuotientMulEquivPerm n k
        (diagonalNormalizerHom n k g :
          Subgroup.normalizerQuotient (diagonalAutSubgroup n k)) =
      diagonalNormalizerPerm g := by
  rw [← diagonalNormalizerQuotientEquiv_mk, diagonalNormalizerQuotientMulEquivPerm,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact TauCeti.diagonalNormalizerQuotientMulEquivPerm_mk g

/-- The inverse quotient equivalence sends a permutation to the class of
conjugation by its permutation matrix. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivPerm_symm_apply (σ : Equiv.Perm (Fin n)) :
    (diagonalNormalizerQuotientMulEquivPerm n k).symm σ =
      (diagonalNormalizerHom n k ⟨permutationGL σ, permutationGL_mem_normalizer σ⟩ :
        Subgroup.normalizerQuotient (diagonalAutSubgroup n k)) := by
  apply (diagonalNormalizerQuotientMulEquivPerm n k).injective
  simp

end Field

end

end TauCeti.ProjectiveGeneralLinear
