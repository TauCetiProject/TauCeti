/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Binary.NormForm
public import TauCeti.NumberTheory.BinaryQuadraticForm.Reflection
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.GroupTheory.GroupAction.Defs
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Oriented proper classes of binary lattices

The basis matrix of an oriented integral change has determinant one. Its inverse acts on the
binary norm form through the existing left `SL₂(ℤ)` action. Primitive normalization commutes
with that action, so the proper class `binaryProperClass` depends only on the lattice and its
fixed orientation. The characteristic lemma computes it using any carrier basis of that
orientation.

Reversing the second basis vector realizes the determinant-minus-one substitution
`(x, y) ↦ (x, -y)`. It negates the middle coefficient of both the norm form and its primitive
part. A basis with the opposite orientation gives a properly equivalent representative of that
reflected form.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, Section 2.
-/

public section

open Module Matrix
open scoped MatrixGroups

namespace TauCeti.IntegralLattice
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (L : IntegralLattice V) (b b' : Basis (Fin 2) ℤ L)

/-- A determinant-one basis matrix acts on the norm form through the inverse, matching the existing
left action. -/
theorem binaryNormForm_eq_inv_smul (γ : SL(2, ℤ))
    (h : b.toMatrix b' = (γ : Matrix (Fin 2) (Fin 2) ℤ)) :
    L.binaryNormForm b' = γ⁻¹ • L.binaryNormForm b := by
  have hg : L.gramMatrix b' = (b.toMatrix b')ᵀ * L.gramMatrix b * b.toMatrix b' := by
    simpa only [gramMatrix_eq_toMatrix] using
      (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b b' L.integralForm).symm
  rw [h] at hg
  have hs := L.isSymm_integralForm.eq (b 1) (b 0)
  ext <;> simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c,
    BinaryQuadraticForm.smul_a, BinaryQuadraticForm.smul_b, BinaryQuadraticForm.smul_c, hg]
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, hs]
    ring

/-- Bases with the same orientation give properly equivalent norm forms. -/
theorem exists_binaryNormForm_eq_smul_of_orientation_eq (h : b.orientation = b'.orientation) :
    ∃ γ : SL(2, ℤ), L.binaryNormForm b' = γ • L.binaryNormForm b := by
  have hp := (Basis.orientation_eq_iff_det_pos b b').mp h
  have hd : b.det b' = 1 := (Int.isUnit_iff.mp (b.isUnit_det b')).resolve_right
    (fun hn ↦ by rw [hn] at hp; norm_num at hp)
  let γ : SL(2, ℤ) := ⟨b.toMatrix b', by rwa [← Basis.det_apply]⟩
  exact ⟨γ⁻¹, L.binaryNormForm_eq_inv_smul b b' γ rfl⟩

/-- Primitive parts in equally oriented bases are properly equivalent. -/
theorem exists_primPart_eq_smul_of_orientation_eq (h : b.orientation = b'.orientation) :
    ∃ γ : SL(2, ℤ),
      (L.binaryNormForm b').primPart = γ • (L.binaryNormForm b).primPart := by
  obtain ⟨γ, hγ⟩ := L.exists_binaryNormForm_eq_smul_of_orientation_eq b b' h
  exact ⟨γ, by rw [hγ, BinaryQuadraticForm.primPart_smul]⟩

/-- Equally oriented bases give the same proper class of the primitive norm form. -/
theorem binaryProperClass_eq_of_orientation_eq (h : b.orientation = b'.orientation) :
    (Quotient.mk'' (L.binaryNormForm b').primPart :
      MulAction.orbitRel.Quotient SL(2, ℤ) (BinaryQuadraticForm ℤ)) =
      Quotient.mk'' (L.binaryNormForm b).primPart := by
  apply Quotient.sound
  obtain ⟨γ, hγ⟩ := L.exists_primPart_eq_smul_of_orientation_eq b b' h
  exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨γ, hγ.symm⟩)

/-- The proper class of the primitive norm form for a rank-two lattice with a fixed orientation. -/
noncomputable def binaryProperClass (hV : Module.finrank ℚ V = 2)
    (o : Orientation ℤ L (Fin 2)) :
    MulAction.orbitRel.Quotient SL(2, ℤ) (BinaryQuadraticForm ℤ) :=
  Quotient.mk'' (L.binaryNormForm
    ((Module.finBasisOfFinrankEq ℤ L
      (L.finrank_carrier.trans hV)).adjustToOrientation o)).primPart

/-- Any carrier basis giving the chosen orientation represents the intrinsic proper class. -/
theorem binaryProperClass_eq_mk (hV : Module.finrank ℚ V = 2)
    (o : Orientation ℤ L (Fin 2)) (hb : b.orientation = o) :
    L.binaryProperClass hV o = Quotient.mk'' (L.binaryNormForm b).primPart := by
  let b₀ := (Module.finBasisOfFinrankEq ℤ L
    (L.finrank_carrier.trans hV)).adjustToOrientation o
  exact L.binaryProperClass_eq_of_orientation_eq b b₀
    (hb.trans (Basis.orientation_adjustToOrientation _ o).symm)

/-- Reversing the second basis vector negates precisely the middle coefficient of the norm form. -/
@[simp] theorem binaryNormForm_unitsSMul_neg :
    L.binaryNormForm (b.unitsSMul (Function.update 1 (1 : Fin 2) (-1))) =
      (L.binaryNormForm b).reflected := by
  ext <;> simp [gramMatrix_apply, Basis.unitsSMul_apply, Units.smul_def]

/-- Reversing the second basis vector also negates precisely the primitive middle coefficient. -/
@[simp↓] theorem primPart_binaryNormForm_unitsSMul_neg :
    (L.binaryNormForm (b.unitsSMul (Function.update 1 (1 : Fin 2) (-1)))).primPart =
      (L.binaryNormForm b).primPart.reflected := by
  rw [binaryNormForm_unitsSMul_neg, BinaryQuadraticForm.primPart_reflected]

/-- Changing orientation gives a form properly equivalent to the reflection of the original
primitive form. The reflection is the determinant-minus-one substitution `(x, y) ↦ (x, -y)`. -/
theorem exists_primPart_eq_smul_of_orientation_neg
    (h : b'.orientation = -b.orientation) :
    ∃ γ : SL(2, ℤ), (L.binaryNormForm b').primPart =
      γ • (L.binaryNormForm b).primPart.reflected := by
  let bRev := b.unitsSMul (Function.update 1 (1 : Fin 2) (-1))
  have ho : bRev.orientation = b'.orientation :=
    (b.orientation_neg_single 1).trans h.symm
  obtain ⟨γ, hγ⟩ := L.exists_primPart_eq_smul_of_orientation_eq bRev b' ho
  exact ⟨γ, hγ.trans (congrArg (γ • ·) (L.primPart_binaryNormForm_unitsSMul_neg b))⟩

end TauCeti.IntegralLattice
