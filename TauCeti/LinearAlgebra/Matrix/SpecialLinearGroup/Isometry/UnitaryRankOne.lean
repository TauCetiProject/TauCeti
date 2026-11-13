/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic

/-!
# The diagonal torus and Weyl representative of the rank-one unitary group

For an involution `σ` of a commutative ring, consider the determinant-one isometries of
`Q = !![0, 0, 1; 0, -1, 0; 1, 0, 0]`. The diagonal torus is parametrized by units `t` as
`diag(t, σ(t)/t, 1/σ(t))`. The signed reversal matrix itself is a determinant-one isometry,
is an involution, and conjugates the torus parameter to `1/σ(t)`.

The parametrization exhausts all diagonal isometries over any commutative ring. These formulas
supply the torus and a fixed representative of the nontrivial relative Weyl element of `SU₃`.
They work in characteristic two as well as odd characteristic.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), Chapter 13.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 11.
-/

public section

open Matrix

namespace TauCeti.UnitaryRankOne

variable (R : Type*) [CommRing R] (σ : R →+* R)

/-- The determinant-one isometries of the signed reversal form in dimension three. -/
abbrev Group :=
  ↥((typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ)

private def torusMatrix (t : Rˣ) : Matrix (Fin 3) (Fin 3) R :=
  diagonal ![(t : R), σ (t : R) * ↑t⁻¹, σ (↑t⁻¹ : R)]

private theorem det_torusMatrix (t : Rˣ) : (torusMatrix R σ t).det = 1 := by
  simp [torusMatrix, det_diagonal, Fin.prod_univ_succ, ← map_mul,
    mul_left_comm, mul_comm]

private def torusSL (t : Rˣ) : SpecialLinearGroup (Fin 3) R :=
  ⟨torusMatrix R σ t, det_torusMatrix R σ t⟩

private theorem coe_torusSL (t : Rˣ) :
    (torusSL R σ t : Matrix (Fin 3) (Fin 3) R) = torusMatrix R σ t := rfl

/-- The diagonal torus parametrization `t ↦ diag(t, σ(t)/t, 1/σ(t))`. -/
def torusHom (hσ : Function.Involutive σ) : Rˣ →* Group R σ where
  toFun t := ⟨torusSL R σ t, by
    apply mem_specialIsometryGroup_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_torusSL, torusMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
        typeAGraphConjugator_apply, hσ (t : R), hσ (↑t⁻¹ : R),
        ← map_mul, mul_assoc, mul_comm]⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_torusSL, torusMatrix, Matrix.SpecialLinearGroup.coe_one]
  map_mul' s t := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [coe_torusSL, torusMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
        map_mul, mul_assoc, mul_left_comm, mul_comm]

/-- The underlying matrix of a torus element. -/
@[simp]
theorem coe_torusHom (hσ : Function.Involutive σ) (t : Rˣ) :
    ((torusHom R σ hσ t : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      diagonal ![(t : R), σ (t : R) * ↑t⁻¹, σ (↑t⁻¹ : R)] := by rfl

/-- The diagonal torus parametrization is injective. -/
theorem torusHom_injective (hσ : Function.Involutive σ) :
    Function.Injective (torusHom R σ hσ) := by
  intro s t h
  apply Units.ext
  simpa using congrArg (fun g : Group R σ =>
    ((g : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 0) h

/-- The diagonal torus, as a subgroup of the rank-one unitary group. -/
def torus (hσ : Function.Involutive σ) : Subgroup (Group R σ) :=
  (torusHom R σ hσ).range

/-- The torus is the range of its unit parametrization. -/
theorem torus_def (hσ : Function.Involutive σ) :
    torus R σ hσ = (torusHom R σ hσ).range := by rfl

/-- Every value of the parametrization belongs to the torus. -/
theorem torusHom_mem_torus (hσ : Function.Involutive σ) (t : Rˣ) :
    torusHom R σ hσ t ∈ torus R σ hσ := ⟨t, rfl⟩

instance (hσ : Function.Involutive σ) : IsMulCommutative (torus R σ hσ) :=
  Subgroup.range_isMulCommutative _

/-- Membership in the torus is existence of a unit parameter. -/
theorem mem_torus_iff (hσ : Function.Involutive σ) (g : Group R σ) :
    g ∈ torus R σ hσ ↔ ∃ t, torusHom R σ hσ t = g := Iff.rfl

/-- The signed reversal matrix is a unitary Weyl representative of determinant one. -/
def weyl : Group R σ :=
  ⟨⟨(typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R), by
    simp [Matrix.det_fin_three, typeAGraphConjugator_apply]⟩, by
    apply mem_specialIsometryGroup_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply,
        typeAGraphConjugator_apply]⟩

/-- The Weyl representative is the signed reversal matrix. -/
@[simp]
theorem coe_weyl :
    ((weyl R σ : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R) := by rfl

/-- The Weyl representative squares to one, including in characteristic two. -/
@[simp]
theorem weyl_mul_self : weyl R σ * weyl R σ = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_mul,
    coe_weyl, Matrix.SpecialLinearGroup.coe_one, Units.val_mul, neg_one_sq, map_one,
    Units.val_one] using congrArg Units.val (typeAGraphConjugator_mul_self (A := R) 2)

/-- The Weyl representative is its own inverse. -/
@[simp]
theorem weyl_inv : (weyl R σ)⁻¹ = weyl R σ :=
  inv_eq_of_mul_eq_one_right (weyl_mul_self R σ)

/-- Weyl conjugation maps the torus parameter `t` to `σ(t)⁻¹`. -/
theorem weyl_mul_torusHom_mul_weyl (hσ : Function.Involutive σ) (t : Rˣ) :
    weyl R σ * torusHom R σ hσ t * weyl R σ =
      torusHom R σ hσ ((Units.map σ.toMonoidHom t)⁻¹) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ,
      typeAGraphConjugator_apply, hσ (t : R), hσ (↑t⁻¹ : R),
      mul_assoc, mul_comm, -map_inv]

/-- The torus consists of all diagonal determinant-one isometries. No field hypothesis is
needed: invertibility already makes each diagonal entry a unit. -/
@[simp]
theorem mem_torus_iff_isDiag (hσ : Function.Involutive σ) (g : Group R σ) :
    g ∈ torus R σ hσ ↔
      ((g : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).IsDiag := by
  refine ⟨?_, fun hg => ?_⟩
  · rintro ⟨t, rfl⟩
    rw [coe_torusHom]
    exact isDiag_diagonal _
  · obtain ⟨d, hd⟩ := mem_diagonalTorus_iff_exists_diagGL.mp
      (Matrix.SpecialLinearGroup.mem_diagonalTorus_iff_toGL_mem.mp
        (Matrix.SpecialLinearGroup.mem_diagonalTorus_iff.mpr hg))
    have hmat : ((g : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
        diagonal (fun i => (d i : R)) := by
      simpa only [diagGL_coe, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using
        (congrArg Units.val hd).symm
    have hdet : d 0 * d 1 * d 2 = 1 := by
      apply Units.ext
      have := (g : SpecialLinearGroup (Fin 3) R).property
      simpa [hmat, det_diagonal, Fin.prod_univ_succ, mul_assoc] using this
    have hpair : Units.map σ.toMonoidHom (d 0) * d 2 = 1 := by
      apply Units.ext
      have := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 2)
        (mem_specialIsometryGroup_iff.mp g.property)
      simpa [hmat, Matrix.mul_apply, Fin.sum_univ_succ,
        typeAGraphConjugator_apply] using this
    have h2 : d 2 = (Units.map σ.toMonoidHom (d 0))⁻¹ :=
      eq_inv_of_mul_eq_one_right hpair
    have h1 : d 1 = Units.map σ.toMonoidHom (d 0) * (d 0)⁻¹ := by
      calc
        d 1 = (d 0)⁻¹ * (d 0 * d 1 * d 2) * (d 2)⁻¹ := by group
        _ = Units.map σ.toMonoidHom (d 0) * (d 0)⁻¹ := by rw [hdet, h2]; simp [mul_comm]
    refine ⟨d 0, ?_⟩
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_torusHom, hmat]
    fin_cases i <;> fin_cases j <;> simp [h1, h2, -map_inv]

/-- The fixed Weyl representative normalizes the diagonal torus. -/
theorem weyl_mem_normalizer_torus (hσ : Function.Involutive σ) :
    weyl R σ ∈ Subgroup.normalizer (torus R σ hσ : Set (Group R σ)) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · rintro ⟨t, rfl⟩
    rw [weyl_inv, weyl_mul_torusHom_mul_weyl]
    exact ⟨_, rfl⟩
  · rintro ⟨t, ht⟩
    have heq : g = weyl R σ * torusHom R σ hσ t * weyl R σ := by
      calc
        g = (weyl R σ)⁻¹ * (weyl R σ * g * (weyl R σ)⁻¹) * weyl R σ := by group
        _ = weyl R σ * torusHom R σ hσ t * weyl R σ := by rw [← ht, weyl_inv]
    rw [heq, weyl_mul_torusHom_mul_weyl]
    exact ⟨_, rfl⟩

/-- The Weyl representative is not diagonal over a nontrivial ring, so it lies outside the
torus even in the smallest characteristic. -/
theorem weyl_notMem_torus [Nontrivial R] (hσ : Function.Involutive σ) :
    weyl R σ ∉ torus R σ hσ := by
  intro h
  have := (mem_torus_iff_isDiag R σ hσ _).mp h (show (0 : Fin 3) ≠ 2 by decide)
  simp at this

end TauCeti.UnitaryRankOne
