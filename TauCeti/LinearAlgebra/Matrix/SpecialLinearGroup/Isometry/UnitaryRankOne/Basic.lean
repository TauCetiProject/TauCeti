/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Normalizer

/-!
# The diagonal torus and Weyl representative of the rank-one unitary group

For an involution `σ` of a commutative ring, consider the determinant-one isometries of
`Q = !![0, 0, 1; 0, -1, 0; 1, 0, 0]`. The diagonal torus is parametrized by units `t` as
`diag(t, σ(t)/t, 1/σ(t))`. The signed reversal matrix itself is a determinant-one isometry,
is an involution, and conjugates the torus parameter to `1/σ(t)`.

The parametrization exhausts all diagonal determinant-one isometries over any commutative ring.
These formulas supply the torus and a fixed representative of the nontrivial relative Weyl element
of `SU₃`.
They work in characteristic two as well as odd characteristic. The diagonal subgroup and its
normalization by the signed reversal are defined for any ring endomorphism `σ`; involutivity is
needed only for the unit parametrization and its exhaustion theorem.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), Chapter 13.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 11.
-/

public section

open Matrix

namespace TauCeti.UnitaryRankOne

variable (R : Type*) [CommRing R] (σ : R →+* R)

/-- The determinant-one isometries of the signed reversal form in dimension three. -/
protected abbrev Group :=
  ↥((typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ)

private theorem mem_group_iff (g : SpecialLinearGroup (Fin 3) R) :
    g ∈ (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ ↔
      typeAGraphAutomorphism 2 R
        (Matrix.GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL g)) =
          Matrix.SpecialLinearGroup.toGL g := by
  rw [mem_specialIsometryGroup_iff,
    typeAGraphAutomorphism_eq_iff_transpose_mul_conjugator_mul_eq]
  simp [Matrix.GeneralLinearGroup.map, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

private def torusDiag : Rˣ →* (Fin 3 → Rˣ) where
  toFun t := ![t, Units.map σ.toMonoidHom t * t⁻¹, Units.map σ.toMonoidHom t⁻¹]
  map_one' := by ext i; fin_cases i <;> simp
  map_mul' s t := by
    ext i
    fin_cases i <;> simp [map_mul, mul_mul_mul_comm, mul_comm]

private def torusSL : Rˣ →* SpecialLinearGroup (Fin 3) R :=
  Matrix.SpecialLinearGroup.toGLKerEquiv.symm.toMonoidHom.comp
    ((diagGL.comp (torusDiag R σ)).codRestrict _ fun t => by
      simp [MonoidHom.mem_ker, det_diagGL, torusDiag, Fin.prod_univ_three, mul_comm])

private theorem toGL_torusSL (t : Rˣ) :
    Matrix.SpecialLinearGroup.toGL (torusSL R σ t) = diagGL (torusDiag R σ t) := by
  rw [← Matrix.SpecialLinearGroup.toGLKerEquiv_apply_coe]
  simp [torusSL]

/-- The diagonal torus parametrization `t ↦ diag(t, σ(t)/t, 1/σ(t))`. -/
def torusHom (hσ : Function.Involutive σ) : Rˣ →* UnitaryRankOne.Group R σ :=
  (torusSL R σ).codRestrict _ fun t => by
    apply (mem_group_iff R σ _).mpr
    rw [toGL_torusSL, map_diagGL, typeAGraphAutomorphism_diagGL]
    congr 1
    funext i
    apply Units.ext
    fin_cases i <;> simp [torusDiag, hσ (t : R), hσ (↑t⁻¹ : R), -map_inv]

/-- The underlying matrix of a torus element. -/
@[simp]
theorem coe_torusHom (hσ : Function.Involutive σ) (t : Rˣ) :
    ((torusHom R σ hσ t : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      diagonal ![(t : R), σ (t : R) * ↑t⁻¹, σ (↑t⁻¹ : R)] := by
  simp only [torusHom, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
  rw [← Matrix.SpecialLinearGroup.coe_GL_coe_matrix, toGL_torusSL, diagGL_coe]
  congr 1
  funext i
  fin_cases i <;> simp [torusDiag]

private theorem toGL_torusHom (hσ : Function.Involutive σ) (t : Rˣ) :
    Matrix.SpecialLinearGroup.toGL (torusHom R σ hσ t : SpecialLinearGroup (Fin 3) R) =
      diagGL (torusDiag R σ t) := by
  simpa only [torusHom, MonoidHom.codRestrict_apply, Subgroup.coe_mk] using
    toGL_torusSL R σ t

/-- The diagonal torus parametrization is injective. -/
theorem torusHom_injective (hσ : Function.Involutive σ) :
    Function.Injective (torusHom R σ hσ) := by
  intro s t h
  apply Units.ext
  simpa using congrArg (fun g : UnitaryRankOne.Group R σ =>
    ((g : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 0) h

/-- The diagonal torus, as a subgroup of the rank-one unitary group. -/
def torus : Subgroup (UnitaryRankOne.Group R σ) :=
  (Matrix.SpecialLinearGroup.diagonalTorus R 3).comap
    ((typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ).subtype

/-- The torus consists of all diagonal determinant-one isometries. No involutivity or field
hypothesis is needed. -/
@[simp]
theorem mem_torus_iff (g : UnitaryRankOne.Group R σ) :
    g ∈ torus R σ ↔
      ((g : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).IsDiag := by
  simp only [torus, Subgroup.mem_comap, Subgroup.subtype_apply,
    Matrix.SpecialLinearGroup.mem_diagonalTorus_iff]

/-- Every value of the parametrization belongs to the torus. -/
theorem torusHom_mem_torus (hσ : Function.Involutive σ) (t : Rˣ) :
    torusHom R σ hσ t ∈ torus R σ := by
  rw [mem_torus_iff, coe_torusHom]
  exact isDiag_diagonal _

instance : IsMulCommutative (torus R σ) :=
  (Matrix.SpecialLinearGroup.diagonalTorus R 3).comap_injective_isMulCommutative
    ((typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ).subtype_injective

/-- The signed reversal matrix is a unitary Weyl representative of determinant one. -/
def weyl : UnitaryRankOne.Group R σ :=
  ⟨⟨(typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R), by
    simp [Matrix.det_fin_three, typeAGraphConjugator_apply]⟩, by
    apply mem_specialIsometryGroup_iff.mpr
    rw [map_coe_typeAGraphConjugator, transpose_typeAGraphConjugator]
    simpa only [neg_one_sq, one_smul, Units.val_mul, Units.val_one, one_mul] using
      congrArg (fun g : GL (Fin 3) R =>
        (g : Matrix (Fin 3) (Fin 3) R) * (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R))
        (typeAGraphConjugator_two_mul_self (A := R))⟩

/-- The Weyl representative is the signed reversal matrix. -/
@[simp]
theorem coe_weyl :
    ((weyl R σ : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R) := by rfl

private theorem toGL_weyl :
    Matrix.SpecialLinearGroup.toGL (weyl R σ : SpecialLinearGroup (Fin 3) R) =
      typeAGraphConjugator 2 R := by
  apply Units.ext
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_weyl]

/-- The Weyl representative squares to one, including in characteristic two. -/
@[simp]
theorem weyl_mul_self : weyl R σ * weyl R σ = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_mul,
    coe_weyl, Matrix.SpecialLinearGroup.coe_one, Units.val_mul,
    Units.val_one] using congrArg Units.val (typeAGraphConjugator_two_mul_self (A := R))

/-- The Weyl representative is its own inverse. -/
@[simp]
theorem weyl_inv : (weyl R σ)⁻¹ = weyl R σ :=
  inv_eq_of_mul_eq_one_right (weyl_mul_self R σ)

/-- Weyl conjugation maps the torus parameter `t` to `σ(t)⁻¹`. -/
@[simp]
theorem weyl_mul_torusHom_mul_weyl (hσ : Function.Involutive σ) (t : Rˣ) :
    weyl R σ * torusHom R σ hσ t * weyl R σ =
      torusHom R σ hσ ((Units.map (σ : R →* R) t)⁻¹) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.toGL_injective
  simp only [Subgroup.coe_mul, map_mul]
  have hdiag := typeAGraphConjugator_mul_diagGL_mul_inv (A := R) 2 (torusDiag R σ t)
  rw [typeAGraphConjugator_two_inv] at hdiag
  rw [toGL_weyl, toGL_torusHom, toGL_torusHom, hdiag]
  congr 1
  funext i
  apply Units.ext
  fin_cases i <;> simp [torusDiag, hσ (t : R), hσ (↑t⁻¹ : R), mul_comm, -map_inv]

/-- The torus is the range of its unit parametrization when the ring endomorphism is
involutive. Invertibility makes each diagonal entry a unit, even without a field hypothesis. -/
theorem torus_eq_range_torusHom (hσ : Function.Involutive σ) :
    torus R σ = (torusHom R σ hσ).range := by
  apply le_antisymm
  · intro g hg
    simp only [torus, Subgroup.mem_comap, Subgroup.subtype_apply,
      Matrix.SpecialLinearGroup.mem_diagonalTorus_iff_toGL_mem] at hg
    obtain ⟨d, hd⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hg
    have hdet := Matrix.SpecialLinearGroup.coeToGL_det (g : SpecialLinearGroup (Fin 3) R)
    rw [← hd, det_diagGL, Fin.prod_univ_three] at hdet
    have hfixed := (mem_group_iff R σ g.val).mp g.property
    rw [← hd, map_diagGL, typeAGraphAutomorphism_diagGL] at hfixed
    have h2 : d 2 = (Units.map σ.toMonoidHom (d 0))⁻¹ :=
      (congrFun (diagGL_injective hfixed) 2).symm
    have h1 : d 1 = Units.map σ.toMonoidHom (d 0) * (d 0)⁻¹ := by
      calc
        d 1 = (d 0)⁻¹ * (d 0 * d 1 * d 2) * (d 2)⁻¹ := by group
        _ = Units.map σ.toMonoidHom (d 0) * (d 0)⁻¹ := by rw [hdet, h2]; simp [mul_comm]
    refine ⟨d 0, ?_⟩
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [← hd, toGL_torusHom]
    congr 1
    funext i
    fin_cases i <;> simp [torusDiag, h1, h2]
  · rintro _ ⟨t, rfl⟩
    exact torusHom_mem_torus R σ hσ t

/-- Membership in the torus is existence of a unit parameter when the endomorphism is
involutive. -/
theorem mem_torus_iff_exists_torusHom (hσ : Function.Involutive σ) (g : UnitaryRankOne.Group R σ) :
    g ∈ torus R σ ↔ ∃ t, torusHom R σ hσ t = g := by
  rw [torus_eq_range_torusHom, MonoidHom.mem_range]

/-- The fixed Weyl representative normalizes the diagonal torus. -/
theorem weyl_mem_normalizer_torus :
    weyl R σ ∈ Subgroup.normalizer (torus R σ : Set (UnitaryRankOne.Group R σ)) := by
  apply Subgroup.le_normalizer_comap
    ((typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ).subtype
  apply Matrix.SpecialLinearGroup.mem_normalizer_diagonalTorus_of_toGL_mem
  rw [Subgroup.subtype_apply, toGL_weyl]
  exact typeAGraphConjugator_mem_normalizer_diagonalTorus 2

/-- The Weyl representative is not diagonal over a nontrivial ring, so it lies outside the
torus even in the smallest characteristic. -/
theorem weyl_notMem_torus [Nontrivial R] :
    weyl R σ ∉ torus R σ := by
  intro h
  have := (mem_torus_iff R σ _).mp h (show (0 : Fin 3) ≠ 2 by decide)
  simp at this

end TauCeti.UnitaryRankOne
