/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Binary.Isometry
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Reflection
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Finite
import TauCeti.NumberTheory.IntegralLattice.Binary.Determinant23
import TauCeti.NumberTheory.NumberField.QuadraticAlgebra

/-!
# Improper automorphisms of binary lattices and ambiguous ideal classes

Let `L` be an integral lattice of rank two whose primitive discriminant `Δ` is not a square, and
let `f` be the primitive part of its norm form in a carrier basis. The special orthogonal group
`SO(L)` has index two in `O(L)` exactly when `f` is properly equivalent to its opposite form
(`index_specialOrthogonalGroup_eq_two_iff_reflected`). The opposite form has the inverse ideal
class, so this happens exactly when the class of `f` has order dividing two:

* for positive `Δ`, in the narrow Picard group of the quadratic order of discriminant `Δ`
  (`index_specialOrthogonalGroup_eq_two_iff_narrowPicClass_sq_eq_one`);
* for positive definite `L`, where `Δ < 0`, in its Picard group
  (`IsPosDef.index_specialOrthogonalGroup_eq_two_iff_picClass_sq_eq_one`).

The statements are made in a fixed carrier basis; changing the orientation of the basis replaces
`f` by an improperly equivalent form, whose class is the inverse one, so the condition that the
square of the class is trivial does not depend on the basis. A negative definite lattice has the
same isometry groups as its negation, which is positive definite.

The lattice `!![4, 1; 1, 6]` of determinant `23` has `O(L) = SO(L) = {±1}`, so the Picard class of
its primitive norm form `2x² + xy + 3y²` does not have order dividing two
(`picClass_two_one_three_sq_ne_one`).

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §3 and §7.
-/

public section

open Module
open scoped MatrixGroups

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable {L : IntegralLattice V} (b : Basis (Fin 2) ℤ L) (hV : Module.finrank ℚ V = 2)

/-- **Improper automorphisms at positive discriminant.** For a rank-two lattice whose primitive
discriminant is positive and not a square, `SO(L)` has index two in `O(L)` exactly when the
oriented narrow class of the primitive norm form has order dividing two. -/
theorem index_specialOrthogonalGroup_eq_two_iff_narrowPicClass_sq_eq_one
    [Fact (¬ IsSquare (L.binaryDiscriminant hV))] (hpos : 0 < L.binaryDiscriminant hV) :
    (specialOrthogonalGroup L).index = 2 ↔
      (L.binaryNormForm b).primPart.narrowPicClass (L.binaryDiscriminant hV)
        (L.binaryDiscriminant_eq_discrim_primPart b hV).symm
        (L.isPrimitive_binaryNormForm_primPart b
          (L.form_ne_zero_of_binaryDiscriminant_ne_zero hV hpos.ne')) ^ 2 = 1 :=
  (index_specialOrthogonalGroup_eq_two_iff_reflected b).trans
    (BinaryQuadraticForm.exists_eq_smul_reflected_iff_narrowPicClass_sq_eq_one hpos _ _)

/-- The primitive norm form of a positive definite rank-two lattice has positive leading
coefficient. -/
private theorem IsPosDef.primPart_binaryNormForm_a_pos (hL : L.IsPosDef) :
    0 < (L.binaryNormForm b).primPart.a := by
  have ha : 0 < (L.binaryNormForm b).a := by
    rw [binaryNormForm_a, gramMatrix_apply, ← integralNorm_apply]
    exact hL.posDef_integralNorm (b 0) (b.ne_zero 0)
  rw [BinaryQuadraticForm.primPart_a]
  exact Int.ediv_pos_of_pos_of_dvd ha (Int.natCast_nonneg _)
    (L.binaryNormForm b).content_dvd_a

/-- **Improper automorphisms of positive definite binary lattices.** For a positive definite
rank-two lattice, whose primitive discriminant is negative, `SO(L)` has index two in `O(L)` exactly
when the Picard class of the primitive norm form has order dividing two. -/
theorem IsPosDef.index_specialOrthogonalGroup_eq_two_iff_picClass_sq_eq_one (hL : L.IsPosDef)
    [Fact (¬ IsSquare (L.binaryDiscriminant hV))] :
    (specialOrthogonalGroup L).index = 2 ↔
      BinaryQuadraticForm.picClass (L.binaryDiscriminant hV)
        (L.binaryDiscriminant_emod_four_eq_zero_or_one hV)
        ⟨(L.binaryNormForm b).primPart, (BinaryQuadraticForm.mem_primitiveForms _ _).mpr
          ⟨(L.binaryDiscriminant_eq_discrim_primPart b hV).symm,
            L.isPrimitive_binaryNormForm_primPart b
              (L.form_ne_zero_of_binaryDiscriminant_ne_zero hV
                (L.binaryDiscriminant_neg_of_isPosDef hV hL).ne)⟩⟩ ^ 2 = 1 :=
  (index_specialOrthogonalGroup_eq_two_iff_reflected b).trans
    (BinaryQuadraticForm.exists_eq_smul_reflected_iff_picClass_sq_eq_one _
      (L.binaryDiscriminant_neg_of_isPosDef hV hL)
      (L.binaryDiscriminant_eq_discrim_primPart b hV).symm
      (L.isPrimitive_binaryNormForm_primPart b (L.form_ne_zero_of_binaryDiscriminant_ne_zero hV
        (L.binaryDiscriminant_neg_of_isPosDef hV hL).ne))
      (hL.primPart_binaryNormForm_a_pos b))

/-- **The form `2x² + xy + 3y²` is not ambiguous.** Its Picard class in `Pic(O_{-23})` does not
have order dividing two: it is the primitive norm form of the lattice `!![4, 1; 1, 6]`, all of
whose automorphisms are proper. -/
theorem picClass_two_one_three_sq_ne_one :
    BinaryQuadraticForm.picClass (-(23 : ℕ) : ℤ) (by decide)
      ⟨⟨2, 1, 3⟩, (BinaryQuadraticForm.mem_primitiveForms _ _).mpr
        ⟨by norm_num [BinaryQuadraticForm.discrim_def, discrim],
          by norm_num [BinaryQuadraticForm.isPrimitive_iff, BinaryQuadraticForm.content_def]⟩⟩ ^ 2
      ≠ 1 := by
  have h : ¬ ∃ γ : SL(2, ℤ), (⟨2, 1, 3⟩ : BinaryQuadraticForm ℤ) =
      γ • (⟨2, 1, 3⟩ : BinaryQuadraticForm ℤ).reflected := by
    rw [← binaryDeterminant23_primPart, ← index_specialOrthogonalGroup_eq_two_iff_reflected,
      index_specialOrthogonalGroup_binaryDeterminant23]
    norm_num
  rwa [BinaryQuadraticForm.exists_eq_smul_reflected_iff_picClass_sq_eq_one
    (D := (-(23 : ℕ) : ℤ)) (by decide)
    (by norm_num) (by norm_num [BinaryQuadraticForm.discrim_def, discrim])
    (by norm_num [BinaryQuadraticForm.isPrimitive_iff, BinaryQuadraticForm.content_def])
    (by norm_num)] at h

end TauCeti.IntegralLattice
