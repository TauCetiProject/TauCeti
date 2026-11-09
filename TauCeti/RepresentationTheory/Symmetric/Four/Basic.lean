/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinFour.Matching
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.SymmetricFour.Basic
public import TauCeti.RepresentationTheory.CharacterTwist
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
public import TauCeti.RepresentationTheory.Symmetric.Standard
import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.RepresentationTheory.Induction.Permutation

/-!
# The irreducible representations of `S₄` and the rows of its character table

The two-dimensional irreducible representation `E` of `S₄ = Equiv.Perm (Fin 4)` is the standard
representation `V₃` of `S₃` pulled back along the action `q : S₄ →* S₃` on the three perfect
matchings `01|23`, `03|12`, `02|13` of `Fin 4`. Since `q` is surjective, `E` is irreducible
whenever `V₃` is, and since `V₃` is faithful, the kernel of `E` is the kernel of `q`, the Klein
four-group.

With `E` in hand, the five rows of `TauCeti.symmetricGroupFourCharacterTable` are pinned to five
concrete representations: in its row order they are the characters of the trivial
representation, the sign representation, `E`, the standard representation `V₄` on the sum-zero
vectors of `k[Fin 4]`, and the sign twist of `V₄`, evaluated at the class representatives
`1, (01), (01)(23), (012), (0123)` of `TauCeti.symmetricGroupFourClassData`.

## Main definitions

* `TauCeti.symmetricGroupFourTwoDimensionalRepresentation`: the representation `E = q^* V₃`.

## Main results

* `TauCeti.isIrreducible_symmetricGroupFourTwoDimensionalRepresentation`: `E` is irreducible when
  `3 ≠ 0`.
* `TauCeti.ker_symmetricGroupFourTwoDimensionalRepresentation`: the kernel of `E` is the kernel of
  `q`, the Klein four-group.
* `TauCeti.symmetricGroupFourCharacterTable_eq_character`: the rows of the character table of `S₄`
  are the characters of the trivial, sign, two-dimensional, standard and sign-twisted standard
  representations.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  §2.3.
* G. James and M. Liebeck, *Representations and Characters of Groups*, Chapter 18.
-/

public section

namespace TauCeti

open Equiv

section Defn

variable (k : Type*) [CommRing k]

/-- **The two-dimensional representation `E` of `S₄`**: the standard representation of `S₃` on
the sum-zero vectors of `k[Fin 3]`, pulled back along the action
`TauCeti.symmetricGroupFourMatchingHom` of `S₄` on the three perfect matchings of `Fin 4`. -/
noncomputable def symmetricGroupFourTwoDimensionalRepresentation :
    Representation k (Perm (Fin 4))
      (augmentationSubrepresentation k (Perm (Fin 3)) (Fin 3)).toSubmodule :=
  (standardRepresentation k (Fin 3)).comp symmetricGroupFourMatchingHom

/-- A permutation acts on `E` as its image under `q` acts on the standard representation of
`S₃`. -/
@[simp]
theorem symmetricGroupFourTwoDimensionalRepresentation_apply (σ : Perm (Fin 4)) :
    symmetricGroupFourTwoDimensionalRepresentation k σ =
      standardRepresentation k (Fin 3) (symmetricGroupFourMatchingHom σ) :=
  (rfl)

/-- **The kernel of `E` is the kernel of `q`**, the Klein four-group
(`TauCeti.ker_symmetricGroupFourMatchingHom`), because the standard representation of `S₃` is
faithful. -/
theorem ker_symmetricGroupFourTwoDimensionalRepresentation [Nontrivial k] :
    (symmetricGroupFourTwoDimensionalRepresentation k).ker = symmetricGroupFourMatchingHom.ker :=
  MonoidHom.ker_comp_of_injective _ _ (standardRepresentation_injective (by simp))

end Defn

section Field

variable {k : Type*} [Field k]

/-- **`E` is irreducible** over a field in which `3 ≠ 0`, since `q` is surjective and the standard
representation of `S₃` is irreducible there. In characteristic `3` the invariant line of
`k[Fin 3]` lies in the standard representation, and `E` is reducible. -/
theorem isIrreducible_symmetricGroupFourTwoDimensionalRepresentation (h : (3 : k) ≠ 0) :
    (symmetricGroupFourTwoDimensionalRepresentation k).IsIrreducible :=
  (symmetricGroupFourMatchingHom.isIrreducible_comp_surjective_iff
    symmetricGroupFourMatchingHom_surjective _).mpr
    (isIrreducible_standardRepresentation_fin_three h)

/-- The character of `E` at `σ` is the character of the standard representation of `S₃` at
`q σ`. -/
@[simp]
theorem char_symmetricGroupFourTwoDimensionalRepresentation (σ : Perm (Fin 4)) :
    (symmetricGroupFourTwoDimensionalRepresentation k).character σ =
      (standardRepresentation k (Fin 3)).character (symmetricGroupFourMatchingHom σ) :=
  (rfl)

/-- The sign character at the class representatives `1, (01), (01)(23), (012), (0123)`. -/
theorem coe_signLinearCharacter_symmetricGroupFourClassData_rep (j : SymmetricGroupFourClassIndex) :
    (signLinearCharacter k (Fin 4) (symmetricGroupFourClassData.rep j) : k) =
      (![1, -1, 1, 1, -1] : Fin 5 → k) (j.cast numClasses_symmetricGroupFourClassData) := by
  have hc : (Perm.sign (symmetricGroupFourClassData.rep j) : ℤ) =
      (![1, -1, 1, 1, -1] : Fin 5 → ℤ) (j.cast numClasses_symmetricGroupFourClassData) := by
    fin_cases j <;> decide
  rw [coe_signLinearCharacter_apply, hc]
  fin_cases j <;> norm_num [Fin.cast, Matrix.cons_val]

/-- **The standard character of `S₄`**, `(3, 1, -1, 0, -1)` at the class representatives
`1, (01), (01)(23), (012), (0123)`: one less than the number of fixed points. -/
theorem char_standardRepresentation_symmetricGroupFourClassData_rep
    (j : SymmetricGroupFourClassIndex) :
    (standardRepresentation k (Fin 4)).character (symmetricGroupFourClassData.rep j) =
      (![3, 1, -1, 0, -1] : Fin 5 → k) (j.cast numClasses_symmetricGroupFourClassData) := by
  have hc : Nat.card {x : Fin 4 // symmetricGroupFourClassData.rep j • x = x} =
      (![4, 2, 0, 1, 0] : Fin 5 → ℕ) (j.cast numClasses_symmetricGroupFourClassData) := by
    rw [Nat.card_eq_fintype_card]
    fin_cases j <;> decide
  rw [char_standardRepresentation, char_ofMulAction, hc]
  fin_cases j <;> norm_num [Fin.cast, Matrix.cons_val]

/-- **The character of `E`**, `(2, 0, 2, -1, 0)` at the class representatives
`1, (01), (01)(23), (012), (0123)`. -/
theorem char_symmetricGroupFourTwoDimensionalRepresentation_symmetricGroupFourClassData_rep
    (j : SymmetricGroupFourClassIndex) :
    (symmetricGroupFourTwoDimensionalRepresentation k).character
        (symmetricGroupFourClassData.rep j) =
      (![2, 0, 2, -1, 0] : Fin 5 → k) (j.cast numClasses_symmetricGroupFourClassData) := by
  have hq : symmetricGroupFourMatchingHom (symmetricGroupFourClassData.rep j) =
      (![1, swap 1 2, 1, [0, 1, 2].formPerm, swap 0 1] : Fin 5 → Perm (Fin 3))
        (j.cast numClasses_symmetricGroupFourClassData) := by
    rw [rep_symmetricGroupFourClassData]
    generalize j.cast numClasses_symmetricGroupFourClassData = j'
    fin_cases j' <;>
      simp only [Fin.reduceFinMk, Matrix.cons_val, map_one,
        symmetricGroupFourMatchingHom_swap_zero_one,
        symmetricGroupFourMatchingHom_swap_zero_one_mul_swap_two_three,
        symmetricGroupFourMatchingHom_formPerm_zero_one_two,
        symmetricGroupFourMatchingHom_formPerm_zero_one_two_three]
  have hc : Nat.card {x : Fin 3 //
        (![1, swap 1 2, 1, [0, 1, 2].formPerm, swap 0 1] : Fin 5 → Perm (Fin 3))
          (j.cast numClasses_symmetricGroupFourClassData) • x = x} =
      (![3, 1, 3, 0, 1] : Fin 5 → ℕ) (j.cast numClasses_symmetricGroupFourClassData) := by
    rw [Nat.card_eq_fintype_card]
    fin_cases j <;> decide
  rw [char_symmetricGroupFourTwoDimensionalRepresentation, hq, char_standardRepresentation,
    char_ofMulAction, hc]
  fin_cases j <;> norm_num [Fin.cast, Matrix.cons_val]

/-- **The rows of the character table of `S₄`**, in the order of
`TauCeti.symmetricGroupFourCharacterTable`, are the characters of the trivial representation, the
sign representation, the two-dimensional representation `E`, the standard representation and its
sign twist, evaluated at the class representatives of `TauCeti.symmetricGroupFourClassData`. This
holds over every field, the entries being read in `k` along `ℤ → k`. -/
theorem symmetricGroupFourCharacterTable_eq_character (i j : SymmetricGroupFourClassIndex) :
    (symmetricGroupFourCharacterTable i j : k) =
      (![(Representation.trivial k (Perm (Fin 4)) k).character,
        (Representation.ofLinearCharacter (signLinearCharacter k (Fin 4))).character,
        (symmetricGroupFourTwoDimensionalRepresentation k).character,
        (standardRepresentation k (Fin 4)).character,
        (Representation.charTwist (signLinearCharacter k (Fin 4))
          (standardRepresentation k (Fin 4))).character] : Fin 5 → Perm (Fin 4) → k)
        (i.cast numClasses_symmetricGroupFourClassData) (symmetricGroupFourClassData.rep j) := by
  have ht : symmetricGroupFourCharacterTable i j =
      (!![1,  1,  1,  1,  1;
          1, -1,  1,  1, -1;
          2,  0,  2, -1,  0;
          3,  1, -1,  0, -1;
          3, -1, -1,  0,  1] : Matrix (Fin 5) (Fin 5) ℤ)
        (i.cast numClasses_symmetricGroupFourClassData)
        (j.cast numClasses_symmetricGroupFourClassData) := by
    rw [symmetricGroupFourCharacterTable_apply]
    fin_cases i <;> fin_cases j <;> decide
  rw [ht]
  generalize i.cast numClasses_symmetricGroupFourClassData = i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val, Representation.char_trivial,
      Representation.char_ofLinearCharacter, Representation.char_charTwist,
      coe_signLinearCharacter_symmetricGroupFourClassData_rep,
      char_standardRepresentation_symmetricGroupFourClassData_rep,
      char_symmetricGroupFourTwoDimensionalRepresentation_symmetricGroupFourClassData_rep] <;>
    generalize j.cast numClasses_symmetricGroupFourClassData = j <;>
    fin_cases j <;> norm_num

end Field

end TauCeti
