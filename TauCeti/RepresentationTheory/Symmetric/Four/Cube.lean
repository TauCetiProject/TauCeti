/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinFour.Cube
public import TauCeti.RepresentationTheory.CharacterTable.Determined
public import TauCeti.RepresentationTheory.Symmetric.Four.Basic
public import Mathlib.RingTheory.SimpleModule.Isotypic
import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Character
import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.RepresentationTheory.Induction.Permutation
import TauCeti.RingTheory.Semisimple.Multiplicity

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

Pairing these characters with the rows of the table gives the multiplicities, as dimensions of
spaces of intertwiners: `1, 1, 0, 1, 1` in `k[X]` and `1, 0, 1, 2, 1` in `k[Y]`, in the row
order trivial, sign, `E`, `V₄`, `sgn ⊗ V₄`. The pairings fix the multiplicities, not the copies:
the two copies of `V₄` in `k[Y]` are only determined by a basis of the two-dimensional space of
intertwiners `V₄ → k[Y]`. Over an algebraically closed field such a basis splits the
`V₄`-isotypic component of `k[Y]`, which is six-dimensional, as `V₄ ⊕ V₄` through
`Module.Basis.isotypicComponentEquiv`.

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
* `TauCeti.finrank_intertwiningMap_cubeVertexRepresentation`,
  `TauCeti.finrank_intertwiningMap_cubeEdgeRepresentation`: the multiplicities of the five
  irreducible representations of `S₄` in `k[X]` and `k[Y]`.
* `TauCeti.finrank_intertwiningMap_standardRepresentation_cubeEdgeRepresentation`,
  `TauCeti.finrank_linearMap_standardRepresentation_cubeEdgeRepresentation`: the multiplicity
  space of `V₄` in `k[Y]` is two-dimensional.
* `TauCeti.finrank_isotypicComponent_cubeEdgeRepresentation_standardRepresentation`: the
  `V₄`-isotypic component of `k[Y]` is six-dimensional.

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

section Multiplicity

variable {k} [Field k]

/-- A character with values `c` at the class representatives `1, (01), (01)(23), (012), (0123)`
takes at each element the value of `c` at its class. -/
private theorem character_eq_of_rep_eq {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (Perm (Fin 4)) V} (c : Fin 5 → ℤ)
    (h : ∀ j, ρ.character (symmetricGroupFourClassData.rep j) =
      (c (j.cast numClasses_symmetricGroupFourClassData) : k))
    (g : Perm (Fin 4)) :
    ρ.character g = (c ((symmetricGroupFourClassData.index g).cast
      numClasses_symmetricGroupFourClassData) : k) := by
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (symmetricGroupFourClassData.isConj_rep_index g)
  conv_lhs => rw [← hτ]
  rw [Representation.char_conj, h]

variable [CharZero k]

/-- The Hom-dimension between two representations of `S₄` whose characters take the integer
values `a` and `b` at the class representatives, read off from the pairing of `a` and `b`. -/
private theorem finrank_intertwiningMap_of_rep_eq {V W : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {ρ : Representation k (Perm (Fin 4)) V} {σ : Representation k (Perm (Fin 4)) W}
    (a b : Fin 5 → ℤ) (n : ℕ)
    (hρ : ∀ j, ρ.character (symmetricGroupFourClassData.rep j) =
      (a (j.cast numClasses_symmetricGroupFourClassData) : k))
    (hσ : ∀ j, σ.character (symmetricGroupFourClassData.rep j) =
      (b (j.cast numClasses_symmetricGroupFourClassData) : k))
    (hab : ∑ g : Perm (Fin 4),
      b ((symmetricGroupFourClassData.index g).cast numClasses_symmetricGroupFourClassData) *
        a ((symmetricGroupFourClassData.index g⁻¹).cast numClasses_symmetricGroupFourClassData) =
      24 * n) :
    Module.finrank k (ρ.IntertwiningMap σ) = n := by
  let : Invertible (Nat.card (Perm (Fin 4)) : k) := invertibleOfNonzero (by
    rw [Nat.card_perm, Nat.card_fin]; norm_num)
  apply Nat.cast_injective (R := k)
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  simp_rw [character_eq_of_rep_eq b hσ, character_eq_of_rep_eq a hρ, ← Int.cast_mul]
  rw [← Int.cast_sum, hab, Nat.card_perm, Nat.card_fin]
  push_cast
  ring

/-- **The multiplicities in the vertex representation** `k[X] ≃ 1 ⊕ sgn ⊕ V₄ ⊕ (sgn ⊗ V₄)`: a
representation whose character is the row `i` of `TauCeti.symmetricGroupFourCharacterTable`
(trivial, sign, `E`, `V₄`, `sgn ⊗ V₄`) has a space of intertwiners into `k[X]` of dimension
`1, 1, 0, 1, 1`. -/
theorem finrank_intertwiningMap_cubeVertexRepresentation {V : Type*} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {ρ : Representation k (Perm (Fin 4)) V} (i : Fin 5)
    (hρ : ∀ j, ρ.character (symmetricGroupFourClassData.rep j) =
      (symmetricGroupFourCharacterTable (i.cast numClasses_symmetricGroupFourClassData.symm) j :
        k)) :
    Module.finrank k (ρ.IntertwiningMap (cubeVertexRepresentation k)) =
      (![1, 1, 0, 1, 1] : Fin 5 → ℕ) i := by
  refine finrank_intertwiningMap_of_rep_eq
    (fun j ↦ symmetricGroupFourCharacterTable (i.cast numClasses_symmetricGroupFourClassData.symm)
      (j.cast numClasses_symmetricGroupFourClassData.symm))
    ![8, 0, 0, 2, 0] _ (fun j ↦ by simpa using hρ j) (fun j ↦ ?_) ?_
  · rw [char_cubeVertexRepresentation_symmetricGroupFourClassData_rep]
    generalize j.cast numClasses_symmetricGroupFourClassData = j
    fin_cases j <;> simp
  · simp only [symmetricGroupFourCharacterTable_apply]
    fin_cases i <;> decide

/-- **The multiplicities in the edge representation** `k[Y] ≃ 1 ⊕ E ⊕ V₄ ⊕ V₄ ⊕ (sgn ⊗ V₄)`: a
representation whose character is the row `i` of `TauCeti.symmetricGroupFourCharacterTable`
(trivial, sign, `E`, `V₄`, `sgn ⊗ V₄`) has a space of intertwiners into `k[Y]` of dimension
`1, 0, 1, 2, 1`. -/
theorem finrank_intertwiningMap_cubeEdgeRepresentation {V : Type*} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {ρ : Representation k (Perm (Fin 4)) V} (i : Fin 5)
    (hρ : ∀ j, ρ.character (symmetricGroupFourClassData.rep j) =
      (symmetricGroupFourCharacterTable (i.cast numClasses_symmetricGroupFourClassData.symm) j :
        k)) :
    Module.finrank k (ρ.IntertwiningMap (cubeEdgeRepresentation k)) =
      (![1, 0, 1, 2, 1] : Fin 5 → ℕ) i := by
  refine finrank_intertwiningMap_of_rep_eq
    (fun j ↦ symmetricGroupFourCharacterTable (i.cast numClasses_symmetricGroupFourClassData.symm)
      (j.cast numClasses_symmetricGroupFourClassData.symm))
    ![12, 2, 0, 0, 0] _ (fun j ↦ by simpa using hρ j) (fun j ↦ ?_) ?_
  · rw [char_cubeEdgeRepresentation_symmetricGroupFourClassData_rep]
    generalize j.cast numClasses_symmetricGroupFourClassData = j
    fin_cases j <;> simp
  · simp only [symmetricGroupFourCharacterTable_apply]
    fin_cases i <;> decide

variable (k) in
/-- **The standard representation occurs twice in the edge representation**: the space of
intertwiners `V₄ → k[Y]` is two-dimensional. Character pairings give this dimension, not two
particular copies of `V₄`; a basis of this space does, through
`Module.Basis.isotypicComponentEquiv`. -/
theorem finrank_intertwiningMap_standardRepresentation_cubeEdgeRepresentation :
    Module.finrank k
      ((standardRepresentation k (Fin 4)).IntertwiningMap (cubeEdgeRepresentation k)) = 2 :=
  finrank_intertwiningMap_cubeEdgeRepresentation 3 fun j ↦ by
    rw [symmetricGroupFourCharacterTable_eq_character, Fin.cast_cast, Fin.cast_eq_self]
    simp only [Matrix.cons_val]

end Multiplicity

section Isotypic

open scoped MonoidAlgebra

variable [Field k] [CharZero k]

/-- **The multiplicity space of `V₄` in `k[Y]` is two-dimensional**, as a space of
`k[S₄]`-linear maps between the group-algebra modules. A basis `b` of it, such as
`Module.finBasisOfFinrankEq`, splits the `V₄`-isotypic component of `k[Y]` as `V₄ ⊕ V₄`,
`(v₀, v₁) ↦ b 0 v₀ + b 1 v₁`, through `Module.Basis.isotypicComponentEquiv`. -/
theorem finrank_linearMap_standardRepresentation_cubeEdgeRepresentation :
    Module.finrank k ((standardRepresentation k (Fin 4)).asModule →ₗ[k[Perm (Fin 4)]]
      (cubeEdgeRepresentation k).asModule) = 2 := by
  rw [← (Representation.IntertwiningMap.equivLinearMapAsModule _ _).finrank_eq]
  exact finrank_intertwiningMap_standardRepresentation_cubeEdgeRepresentation k

/-- **The `V₄`-isotypic component of `k[Y]` is six-dimensional**: it is the sum of the two copies
of the standard representation in the edge representation, over an algebraically closed field of
characteristic zero. -/
theorem finrank_isotypicComponent_cubeEdgeRepresentation_standardRepresentation
    [IsAlgClosed k] :
    Module.finrank k (isotypicComponent k[Perm (Fin 4)] (cubeEdgeRepresentation k).asModule
      (standardRepresentation k (Fin 4)).asModule) = 6 := by
  have := isIrreducible_standardRepresentation (k := k) (α := Fin 4) (by decide)
    (Or.inr (by norm_num))
  rw [finrank_isotypicComponent (k := k),
    finrank_linearMap_standardRepresentation_cubeEdgeRepresentation k]
  rw [(Representation.asModuleEquiv _).finrank_eq, finrank_augmentationSubrepresentation]
  simp

end Isotypic

end TauCeti
