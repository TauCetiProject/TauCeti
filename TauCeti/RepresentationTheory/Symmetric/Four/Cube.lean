/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinFour.Cube
public import TauCeti.RepresentationTheory.CharacterTable.Determined
public import TauCeti.RepresentationTheory.Symmetric.Four.Basic
import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Character
import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.RepresentationTheory.Induction.Permutation

/-!
# The permutation representations of `S₄` on the vertices and edges of the cube

The rotation group of the cube is `S₄`, through its permutation of the four body diagonals
(`TauCeti.cubeRotationEquiv`). Transporting the actions of the rotation group on the eight vertices
`X = {-1, 1}³` and on the twelve edges `Y` through the inverse of this isomorphism makes `k[X]` and
`k[Y]` representations of `S₄ = Equiv.Perm (Fin 4)`.

Their characters are the fixed-point counts of the corresponding rotations. At the class
representatives `1, (01), (01)(23), (012), (0123)` of `TauCeti.symmetricGroupFourClassData` these
are `(8, 0, 0, 2, 0)` and `(12, 2, 0, 0, 0)`: a transposition is a half-turn about the axis through
two opposite edge midpoints, fixing those two edges and no vertex; a double transposition is a
half-turn about a face axis; a `3`-cycle is a third-turn about a body diagonal, fixing its two
endpoints; a `4`-cycle is a quarter-turn about a face axis. Compared with the rows of the character
table of `S₄` this gives, over every field,

`χ_{k[X]} = 1 + sgn + χ_{V₄} + χ_{sgn ⊗ V₄}` and `χ_{k[Y]} = 1 + χ_E + 2 χ_{V₄} + χ_{sgn ⊗ V₄}`,

where `V₄` is the standard representation on the sum-zero vectors of `k[Fin 4]` and `E` is the
two-dimensional representation pulled back from the standard representation of `S₃`
(`TauCeti.symmetricGroupFourTwoDimensionalRepresentation`). These constituents are irreducible in
characteristic zero, though not in every characteristic. Since a representation in characteristic
zero is determined by its character, `k[X] ≃ 1 ⊕ sgn ⊕ V₄ ⊕ (sgn ⊗ V₄)` and
`k[Y] ≃ 1 ⊕ E ⊕ V₄ ⊕ V₄ ⊕ (sgn ⊗ V₄)` as representations there.

## Main definitions

* `TauCeti.cubeVertexRepresentation`: the permutation representation `k[X]` of `S₄`.
* `TauCeti.cubeEdgeRepresentation`: the permutation representation `k[Y]` of `S₄`.

## Main results

* `TauCeti.char_cubeVertexRepresentation_symmetricGroupFourClassData_rep`,
  `TauCeti.char_cubeEdgeRepresentation_symmetricGroupFourClassData_rep`: the two characters at the
  class representatives.
* `TauCeti.char_cubeVertexRepresentation`, `TauCeti.char_cubeEdgeRepresentation`: the two
  characters as sums of the characters of the trivial, sign, two-dimensional, standard and
  sign-twisted standard representations, over every field.
* `TauCeti.nonempty_equiv_cubeVertexRepresentation`,
  `TauCeti.nonempty_equiv_cubeEdgeRepresentation`: the two decompositions into these
  representations, irreducible in characteristic zero.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  §2.3.
* G. James and M. Liebeck, *Representations and Characters of Groups*, Chapter 18.
-/

public section

namespace TauCeti

open Equiv

variable (k : Type*)

section CommSemiring

variable [CommSemiring k]

/-- **The permutation representation of `S₄` on the vertices of the cube**: `k[X]` for
`X = {-1, 1}³`, with `σ` acting as the rotation `TauCeti.cubeRotationEquiv.symm σ` that permutes
the body diagonals by `σ`. -/
noncomputable def cubeVertexRepresentation :
    Representation k (Perm (Fin 4)) (MonoidAlgebra k (Fin 3 → ℤˣ)) :=
  (Representation.ofMulAction k cubeRotationGroup (Fin 3 → ℤˣ)).comp
    cubeRotationEquiv.symm.toMonoidHom

/-- **The permutation representation of `S₄` on the edges of the cube**: `k[Y]` for the twelve
edges `Y`, with `σ` acting as the rotation `TauCeti.cubeRotationEquiv.symm σ`. -/
noncomputable def cubeEdgeRepresentation :
    Representation k (Perm (Fin 4)) (MonoidAlgebra k cubeEdgeSet) :=
  (Representation.ofMulAction k cubeRotationGroup cubeEdgeSet).comp
    cubeRotationEquiv.symm.toMonoidHom

/-- `σ` acts on `k[X]` as the rotation permuting the body diagonals by `σ`. -/
theorem cubeVertexRepresentation_apply (σ : Perm (Fin 4)) :
    cubeVertexRepresentation k σ =
      Representation.ofMulAction k cubeRotationGroup (Fin 3 → ℤˣ) (cubeRotationEquiv.symm σ) :=
  (rfl)

/-- `σ` acts on `k[Y]` as the rotation permuting the body diagonals by `σ`. -/
theorem cubeEdgeRepresentation_apply (σ : Perm (Fin 4)) :
    cubeEdgeRepresentation k σ =
      Representation.ofMulAction k cubeRotationGroup cubeEdgeSet (cubeRotationEquiv.symm σ) :=
  (rfl)

end CommSemiring

section Field

variable [Field k]

/-- The character of `k[X]` at `σ` is the number of vertices fixed by the rotation inducing `σ`. -/
theorem char_cubeVertexRepresentation_apply (σ : Perm (Fin 4)) :
    (cubeVertexRepresentation k).character σ =
      Nat.card {v : Fin 3 → ℤˣ // cubeRotationEquiv.symm σ • v = v} :=
  char_ofMulAction k (Fin 3 → ℤˣ) (cubeRotationEquiv.symm σ)

/-- The character of `k[Y]` at `σ` is the number of edges fixed by the rotation inducing `σ`. -/
theorem char_cubeEdgeRepresentation_apply (σ : Perm (Fin 4)) :
    (cubeEdgeRepresentation k).character σ =
      Nat.card {e : cubeEdgeSet // cubeRotationEquiv.symm σ • e = e} :=
  char_ofMulAction k cubeEdgeSet (cubeRotationEquiv.symm σ)

/-- **The vertex character**, `(8, 0, 0, 2, 0)` at the class representatives
`1, (01), (01)(23), (012), (0123)`. -/
theorem char_cubeVertexRepresentation_symmetricGroupFourClassData_rep
    (j : SymmetricGroupFourClassIndex) :
    (cubeVertexRepresentation k).character (symmetricGroupFourClassData.rep j) =
      (![8, 0, 0, 2, 0] : Fin 5 → k) (j.cast numClasses_symmetricGroupFourClassData) := by
  rw [char_cubeVertexRepresentation_apply, rep_symmetricGroupFourClassData]
  generalize j.cast numClasses_symmetricGroupFourClassData = j
  fin_cases j <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val, map_one, one_smul,
      cubeRotationEquiv_symm_swap_zero_one,
      cubeRotationEquiv_symm_swap_zero_one_mul_swap_two_three,
      cubeRotationEquiv_symm_formPerm_zero_one_two,
      cubeRotationEquiv_symm_formPerm_zero_one_two_three, natCard_fixed_cubeVertex_cubeEdgeHalfTurn,
      natCard_fixed_cubeVertex_cubeFaceHalfTurn, natCard_fixed_cubeVertex_cubeDiagonalThirdTurn,
      natCard_fixed_cubeVertex_cubeFaceQuarterTurn, Nat.card_subtype_true] <;>
    norm_num

/-- **The edge character**, `(12, 2, 0, 0, 0)` at the class representatives
`1, (01), (01)(23), (012), (0123)`. -/
theorem char_cubeEdgeRepresentation_symmetricGroupFourClassData_rep
    (j : SymmetricGroupFourClassIndex) :
    (cubeEdgeRepresentation k).character (symmetricGroupFourClassData.rep j) =
      (![12, 2, 0, 0, 0] : Fin 5 → k) (j.cast numClasses_symmetricGroupFourClassData) := by
  rw [char_cubeEdgeRepresentation_apply, rep_symmetricGroupFourClassData]
  generalize j.cast numClasses_symmetricGroupFourClassData = j
  fin_cases j <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val, map_one, one_smul,
      cubeRotationEquiv_symm_swap_zero_one,
      cubeRotationEquiv_symm_swap_zero_one_mul_swap_two_three,
      cubeRotationEquiv_symm_formPerm_zero_one_two,
      cubeRotationEquiv_symm_formPerm_zero_one_two_three,
      natCard_fixed_cubeEdgeSet_cubeEdgeHalfTurn,
      natCard_fixed_cubeEdgeSet_cubeFaceHalfTurn, natCard_fixed_cubeEdgeSet_cubeDiagonalThirdTurn,
      natCard_fixed_cubeEdgeSet_cubeFaceQuarterTurn, Nat.card_subtype_true, natCard_cubeEdgeSet] <;>
    norm_num

/-- **The vertex character decomposes** as `1 + sgn + χ_{V₄} + χ_{sgn ⊗ V₄}`, over every field. -/
theorem char_cubeVertexRepresentation :
    (cubeVertexRepresentation k).character =
      ((Representation.trivial k (Perm (Fin 4)) k).prod
        ((Representation.ofLinearCharacter (signLinearCharacter k (Fin 4))).prod
          ((standardRepresentation k (Fin 4)).prod
            (Representation.charTwist (signLinearCharacter k (Fin 4))
              (standardRepresentation k (Fin 4)))))).character := by
  refine symmetricGroupFourClassData.character_eq_of_rep fun j ↦ ?_
  simp only [Representation.char_prod, Representation.char_trivial,
    Representation.char_ofLinearCharacter, Representation.char_charTwist,
    coe_signLinearCharacter_symmetricGroupFourClassData_rep,
    char_standardRepresentation_symmetricGroupFourClassData_rep,
    char_cubeVertexRepresentation_symmetricGroupFourClassData_rep, Module.finrank_self]
  generalize j.cast numClasses_symmetricGroupFourClassData = j
  fin_cases j <;> norm_num

/-- **The edge character decomposes** as `1 + χ_E + 2 χ_{V₄} + χ_{sgn ⊗ V₄}`, over every field. -/
theorem char_cubeEdgeRepresentation :
    (cubeEdgeRepresentation k).character =
      ((Representation.trivial k (Perm (Fin 4)) k).prod
        ((symmetricGroupFourTwoDimensionalRepresentation k).prod
          ((standardRepresentation k (Fin 4)).prod
            ((standardRepresentation k (Fin 4)).prod
              (Representation.charTwist (signLinearCharacter k (Fin 4))
                (standardRepresentation k (Fin 4))))))).character := by
  refine symmetricGroupFourClassData.character_eq_of_rep fun j ↦ ?_
  simp only [Representation.char_prod, Representation.char_trivial,
    Representation.char_charTwist, coe_signLinearCharacter_symmetricGroupFourClassData_rep,
    char_standardRepresentation_symmetricGroupFourClassData_rep,
    char_symmetricGroupFourTwoDimensionalRepresentation_symmetricGroupFourClassData_rep,
    char_cubeEdgeRepresentation_symmetricGroupFourClassData_rep, Module.finrank_self]
  generalize j.cast numClasses_symmetricGroupFourClassData = j
  fin_cases j <;> norm_num

/-- **`k[X] ≃ 1 ⊕ sgn ⊕ V₄ ⊕ (sgn ⊗ V₄)`** in characteristic zero: the vertex representation
contains each of the trivial, sign, standard and sign-twisted standard representations once. -/
theorem nonempty_equiv_cubeVertexRepresentation [CharZero k] :
    Nonempty ((cubeVertexRepresentation k).Equiv
      ((Representation.trivial k (Perm (Fin 4)) k).prod
        ((Representation.ofLinearCharacter (signLinearCharacter k (Fin 4))).prod
          ((standardRepresentation k (Fin 4)).prod
            (Representation.charTwist (signLinearCharacter k (Fin 4))
              (standardRepresentation k (Fin 4))))))) :=
  Representation.nonempty_equiv_of_character_eq _ _ (char_cubeVertexRepresentation k)

/-- **`k[Y] ≃ 1 ⊕ E ⊕ V₄ ⊕ V₄ ⊕ (sgn ⊗ V₄)`** in characteristic zero: the edge representation
contains the standard representation twice and each of the trivial, two-dimensional and
sign-twisted standard representations once. -/
theorem nonempty_equiv_cubeEdgeRepresentation [CharZero k] :
    Nonempty ((cubeEdgeRepresentation k).Equiv
      ((Representation.trivial k (Perm (Fin 4)) k).prod
        ((symmetricGroupFourTwoDimensionalRepresentation k).prod
          ((standardRepresentation k (Fin 4)).prod
            ((standardRepresentation k (Fin 4)).prod
              (Representation.charTwist (signLinearCharacter k (Fin 4))
                (standardRepresentation k (Fin 4)))))))) :=
  Representation.nonempty_equiv_of_character_eq _ _ (char_cubeEdgeRepresentation k)

end Field

end TauCeti
