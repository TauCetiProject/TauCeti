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
zero is determined by its character, `k[Y] ≃ 1 ⊕ E ⊕ V₄ ⊕ V₄ ⊕ (sgn ⊗ V₄)` as representations
there.

The vertex representation decomposes explicitly, over any commutative ring in which `2` is a unit.
Each vertex lies on exactly one body diagonal, and the product of its coordinates is `1` on one of
the two tetrahedra inscribed in the cube and `-1` on the other. A rotation inducing an odd
permutation of the diagonals exchanges the two tetrahedra, so splitting a function on the vertices
into its parts even and odd under the antipodal map gives
`k[X] ≃ k[Fin 4] ⊕ (sgn ⊗ k[Fin 4])`, the permutation representation of `S₄` on the diagonals and
its sign twist. Splitting the line of the sum of the diagonals off both summands gives
`k[X] ≃ 1 ⊕ sgn ⊕ V₄ ⊕ (sgn ⊗ V₄)`, with explicit components and inverse.

Pairing these characters with the rows of the table gives the multiplicities, as dimensions of
spaces of intertwiners: `1, 1, 0, 1, 1` in `k[X]` and `1, 0, 1, 2, 1` in `k[Y]`, in the row
order trivial, sign, `E`, `V₄`, `sgn ⊗ V₄`. The pairings fix the multiplicities, not the copies:
the two copies of `V₄` in `k[Y]` are only determined by a basis of the two-dimensional space of
intertwiners `V₄ → k[Y]`. The `V₄`-isotypic component of `k[Y]` is six-dimensional, and over an
algebraically closed field such a basis splits it as `V₄ ⊕ V₄` through
`Module.Basis.isotypicComponentEquiv`.

## Main definitions

* `TauCeti.cubeVertexRepresentation`: the permutation representation `k[X]` of `S₄`.
* `TauCeti.cubeEdgeRepresentation`: the permutation representation `k[Y]` of `S₄`.
* `TauCeti.cubeVertexRepresentationDiagonalEquiv`: the splitting
  `k[X] ≃ k[Fin 4] ⊕ (sgn ⊗ k[Fin 4])` into even and odd parts, when `2` is a unit.
* `TauCeti.cubeVertexRepresentationEquiv`: the decomposition
  `k[X] ≃ 1 ⊕ sgn ⊕ V₄ ⊕ (sgn ⊗ V₄)`, when `2` is a unit.

## Main results

* `TauCeti.char_cubeVertexRepresentation_symmetricGroupFourClassData_rep`,
  `TauCeti.char_cubeEdgeRepresentation_symmetricGroupFourClassData_rep`: the two characters at the
  class representatives.
* `TauCeti.char_cubeVertexRepresentation`, `TauCeti.char_cubeEdgeRepresentation`: the two
  characters as sums of the characters of the trivial, sign, two-dimensional, standard and
  sign-twisted standard representations, over every field.
* `TauCeti.nonempty_equiv_cubeEdgeRepresentation`: the decomposition of `k[Y]` into these
  representations, irreducible in characteristic zero.
* `TauCeti.cubeVertexRepresentationEquiv_single_fst` and its three companions: the four
  components of a vertex under `TauCeti.cubeVertexRepresentationEquiv`, and
  `TauCeti.cubeVertexRepresentationEquiv_symm_apply`: its inverse.
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

/-! ### The explicit decomposition of the vertex representation -/

section VertexDecomposition

open MonoidAlgebra

variable {k} [CommRing k]

/-- Sends the vertex `v` to `(e_j, ε e_j)`, where `j` labels the body diagonal through `v` and
`ε = ±1` is the product of the coordinates of `v`. -/
private noncomputable def cubeVertexSplit :
    MonoidAlgebra k (Fin 3 → ℤˣ) →ₗ[k] MonoidAlgebra k (Fin 4) × MonoidAlgebra k (Fin 4) :=
  (MonoidAlgebra.basis _ k).constr k fun v ↦
    (single (cubeBodyDiagonalIndex v) 1,
      single (cubeBodyDiagonalIndex v) (((∏ i, v i : ℤˣ) : ℤ) : k))

private theorem cubeVertexSplit_single (v : Fin 3 → ℤˣ) (c : k) :
    cubeVertexSplit (single v c) =
      (single (cubeBodyDiagonalIndex v) c,
        single (cubeBodyDiagonalIndex v) ((((∏ i, v i : ℤˣ) : ℤ) : k) * c)) := by
  rw [← mul_one c, ← smul_eq_mul, ← smul_single, map_smul, ← basis_apply, cubeVertexSplit,
    Module.Basis.constr_basis]
  simp [smul_single, mul_comm]

/-- Sends `(e_j, 0)` to `u (v + (-v))` and `(0, e_j)` to `u (v - (-v))`, for `v` the endpoint
`TauCeti.cubeBodyDiagonal j`; for `u = 1 / 2` it inverts `cubeVertexSplit`. -/
private noncomputable def cubeVertexJoin (u : k) :
    MonoidAlgebra k (Fin 4) × MonoidAlgebra k (Fin 4) →ₗ[k] MonoidAlgebra k (Fin 3 → ℤˣ) :=
  ((MonoidAlgebra.basis _ k).constr k fun i ↦
      u • (single (cubeBodyDiagonal i) 1 + single (-cubeBodyDiagonal i) 1)).coprod
    ((MonoidAlgebra.basis _ k).constr k fun i ↦
      u • (single (cubeBodyDiagonal i) 1 - single (-cubeBodyDiagonal i) 1))

private theorem cubeVertexJoin_single_single (u : k) (i : Fin 4) (c c' : k) :
    cubeVertexJoin u (single i c, single i c') =
      u • (single (cubeBodyDiagonal i) (c + c') + single (-cubeBodyDiagonal i) (c - c')) := by
  have hs {X : Type} (x : X) (r : k) : single x r = r • single x 1 := by simp [smul_single]
  rw [cubeVertexJoin, LinearMap.coprod_apply, hs i c, hs i c', map_smul, map_smul,
    ← basis_apply, Module.Basis.constr_basis, Module.Basis.constr_basis,
    hs (cubeBodyDiagonal i) (c + c'), hs (-cubeBodyDiagonal i) (c - c')]
  module

/-- The coordinate product of the antipode of a diagonal endpoint is `-1`. -/
private theorem cast_prod_neg_cubeBodyDiagonal (j : Fin 4) :
    ((((∏ i, (-cubeBodyDiagonal j) i : ℤˣ) : ℤ) : k)) = -1 := by
  simp [Finset.prod_neg]

private theorem cubeVertexJoin_comp_cubeVertexSplit {u : k} (hu : u * 2 = 1) :
    cubeVertexJoin u ∘ₗ cubeVertexSplit = LinearMap.id := by
  refine (MonoidAlgebra.basis _ k).ext fun v ↦ ?_
  rw [basis_apply, LinearMap.comp_apply, cubeVertexSplit_single, cubeVertexJoin_single_single,
    LinearMap.id_apply]
  -- Every vertex is a diagonal endpoint or its antipode.
  obtain ⟨j, rfl | rfl⟩ : ∃ j, v = cubeBodyDiagonal j ∨ v = -cubeBodyDiagonal j :=
    ⟨_, cubeBodyDiagonalIndex_eq_iff.mp rfl⟩
  · simp only [prod_cubeBodyDiagonal, Units.val_one, Int.cast_one, mul_one, sub_self,
      single_zero, add_zero, smul_single, smul_eq_mul, cubeBodyDiagonalIndex_cubeBodyDiagonal]
    rw [one_add_one_eq_two, hu]
  · simp only [cubeBodyDiagonalIndex_neg, cubeBodyDiagonalIndex_cubeBodyDiagonal,
      cast_prod_neg_cubeBodyDiagonal, neg_mul, one_mul, add_neg_cancel, single_zero, zero_add,
      sub_neg_eq_add, smul_single, smul_eq_mul]
    rw [one_add_one_eq_two, hu]

private theorem cubeVertexSplit_comp_cubeVertexJoin {u : k} (hu : u * 2 = 1) :
    cubeVertexSplit ∘ₗ cubeVertexJoin u = LinearMap.id := by
  refine LinearMap.prod_ext ((MonoidAlgebra.basis _ k).ext fun i ↦ ?_)
    ((MonoidAlgebra.basis _ k).ext fun i ↦ ?_) <;>
  · simp only [basis_apply, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
      LinearMap.id_apply]
    rw [← single_zero i, cubeVertexJoin_single_single, map_smul, map_add, cubeVertexSplit_single,
      cubeVertexSplit_single, cubeBodyDiagonalIndex_neg, cubeBodyDiagonalIndex_cubeBodyDiagonal,
      cast_prod_neg_cubeBodyDiagonal, prod_cubeBodyDiagonal]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, ← single_add,
        smul_single, smul_eq_mul, Units.val_one, Int.cast_one] <;>
      congr 1 <;> first | linear_combination hu | ring

private theorem cubeVertexSplit_comp_cubeVertexRepresentation (g : Perm (Fin 4)) :
    cubeVertexSplit ∘ₗ cubeVertexRepresentation k g =
      ((Representation.ofMulAction k (Perm (Fin 4)) (Fin 4)).prod
        (Representation.charTwist (signLinearCharacter k (Fin 4))
          (Representation.ofMulAction k (Perm (Fin 4)) (Fin 4)))) g ∘ₗ cubeVertexSplit := by
  refine (MonoidAlgebra.basis _ k).ext fun v ↦ ?_
  have hg : cubeBodyDiagonalHom (cubeRotationEquiv.symm g) = g := by
    rw [← cubeRotationEquiv_apply, MulEquiv.apply_symm_apply]
  simp only [basis_apply, LinearMap.comp_apply, cubeVertexRepresentation_apply,
    Representation.ofMulAction_single, cubeVertexSplit_single, Representation.prod_apply_apply,
    Representation.charTwist_apply, LinearMap.smul_apply, coe_signLinearCharacter_apply,
    smul_single, smul_eq_mul, prod_cubeRotationGroup_smul, hg, Perm.smul_def,
    ← cubeBodyDiagonalHom_apply_cubeBodyDiagonalIndex, Units.val_mul, Int.cast_mul, mul_one]

/-- **The vertex representation splits into an even and an odd part** whenever `2` is a unit:
`k[X] ≃ k[Fin 4] ⊕ (sgn ⊗ k[Fin 4])`, the permutation representation of `S₄` on the four body
diagonals and its twist by the sign character. The vertex `v` goes to `(e_j, ε e_j)`, where `j`
labels the body diagonal through `v` and `ε = ±1` is the product of the coordinates of `v`, which
is `1` on one inscribed tetrahedron and `-1` on the other. A rotation inducing an odd permutation
of the diagonals exchanges the two tetrahedra (`TauCeti.prod_cubeRotationGroup_smul`), which is
where the sign twist comes from. -/
noncomputable def cubeVertexRepresentationDiagonalEquiv (h : IsUnit (2 : k)) :
    (cubeVertexRepresentation k).Equiv
      ((Representation.ofMulAction k (Perm (Fin 4)) (Fin 4)).prod
        (Representation.charTwist (signLinearCharacter k (Fin 4))
          (Representation.ofMulAction k (Perm (Fin 4)) (Fin 4)))) :=
  .mk (.ofLinearMap cubeVertexSplit (cubeVertexJoin (Ring.inverse 2))
      (cubeVertexSplit_comp_cubeVertexJoin (Ring.inverse_mul_cancel _ h))
      (cubeVertexJoin_comp_cubeVertexSplit (Ring.inverse_mul_cancel _ h)))
    cubeVertexSplit_comp_cubeVertexRepresentation

/-- The splitting sends the vertex `v` to `(e_j, ε e_j)`, where `j` labels the body diagonal
through `v` and `ε` is the product of the coordinates of `v`. -/
@[simp]
theorem cubeVertexRepresentationDiagonalEquiv_single (h : IsUnit (2 : k)) (v : Fin 3 → ℤˣ)
    (c : k) :
    cubeVertexRepresentationDiagonalEquiv h (single v c) =
      (single (cubeBodyDiagonalIndex v) c,
        single (cubeBodyDiagonalIndex v) ((((∏ i, v i : ℤˣ) : ℤ) : k) * c)) :=
  cubeVertexSplit_single v c

/-- The inverse splitting sends `(c e_j, c' e_j)` to `½ ((c + c') v + (c - c') (-v))`, for `v`
the endpoint `TauCeti.cubeBodyDiagonal j` of the body diagonal `j`. -/
theorem cubeVertexRepresentationDiagonalEquiv_symm_single_single (h : IsUnit (2 : k))
    (j : Fin 4) (c c' : k) :
    (cubeVertexRepresentationDiagonalEquiv h).symm (single j c, single j c') =
      Ring.inverse (2 : k) •
        (single (cubeBodyDiagonal j) (c + c') + single (-cubeBodyDiagonal j) (c - c')) :=
  cubeVertexJoin_single_single _ j c c'

private theorem isUnit_card_fin_four (h : IsUnit (2 : k)) : IsUnit (Fintype.card (Fin 4) : k) := by
  rw [Fintype.card_fin, show ((4 : ℕ) : k) = 2 * 2 by norm_num]
  exact h.mul h

/-- **`k[X] ≃ 1 ⊕ sgn ⊕ V₄ ⊕ (sgn ⊗ V₄)`** whenever `2` is a unit, explicitly: the even part
`k[Fin 4]` of `TauCeti.cubeVertexRepresentationDiagonalEquiv` splits as the trivial line of the
sum of the diagonals plus the standard representation on the sum-zero vectors, and the odd part
`sgn ⊗ k[Fin 4]` as the sign line plus the sign-twisted standard representation, both through
`TauCeti.ofMulActionEquivProdAugmentation`. In characteristic zero these four summands are
irreducible and pairwise inequivalent. -/
noncomputable def cubeVertexRepresentationEquiv (h : IsUnit (2 : k)) :
    (cubeVertexRepresentation k).Equiv
      ((Representation.trivial k (Perm (Fin 4)) k).prod
        ((Representation.ofLinearCharacter (signLinearCharacter k (Fin 4))).prod
          ((standardRepresentation k (Fin 4)).prod
            (Representation.charTwist (signLinearCharacter k (Fin 4))
              (standardRepresentation k (Fin 4)))))) :=
  .mk ((cubeVertexRepresentationDiagonalEquiv h).toLinearEquiv ≪≫ₗ
      ((ofMulActionEquivProdAugmentation k (Perm (Fin 4)) (Fin 4)
          (isUnit_card_fin_four h)).toLinearEquiv.prodCongr
        (ofMulActionEquivProdAugmentation k (Perm (Fin 4)) (Fin 4)
          (isUnit_card_fin_four h)).toLinearEquiv) ≪≫ₗ
      LinearEquiv.prodProdProdComm k k _ k _ ≪≫ₗ LinearEquiv.prodAssoc k k k _) fun g ↦
    LinearMap.ext fun x ↦ by
      have hD := Representation.IntertwiningMap.isIntertwining _ _
        (cubeVertexRepresentationDiagonalEquiv h).toIntertwiningMap g x
      have hA := Representation.IntertwiningMap.isIntertwining _ _
        (ofMulActionEquivProdAugmentation k (Perm (Fin 4)) (Fin 4)
          (isUnit_card_fin_four h)).toIntertwiningMap g
      simp only [Representation.Equiv.coe_toIntertwiningMap] at hD hA
      simp [hD, hA]

/-- The trivial component of `c e_v` is `c / 4`. -/
@[simp]
theorem cubeVertexRepresentationEquiv_single_fst (h : IsUnit (2 : k)) (v : Fin 3 → ℤˣ) (c : k) :
    (cubeVertexRepresentationEquiv h (single v c)).1 = c * Ring.inverse 4 := by
  simp [cubeVertexRepresentationEquiv]

/-- The sign component of `c e_v` is `ε c / 4`, for `ε` the product of the coordinates of `v`. -/
@[simp]
theorem cubeVertexRepresentationEquiv_single_snd_fst (h : IsUnit (2 : k)) (v : Fin 3 → ℤˣ)
    (c : k) :
    (cubeVertexRepresentationEquiv h (single v c)).2.1 =
      (((∏ i, v i : ℤˣ) : ℤ) : k) * c * Ring.inverse 4 := by
  simp [cubeVertexRepresentationEquiv]

/-- The standard component of `c e_v` is `c (e_j - ¼ ∑ᵢ eᵢ)`, for `j` the body diagonal
through `v`. -/
@[simp]
theorem coe_cubeVertexRepresentationEquiv_single_snd_snd_fst (h : IsUnit (2 : k))
    (v : Fin 3 → ℤˣ) (c : k) :
    ((cubeVertexRepresentationEquiv h (single v c)).2.2.1 : MonoidAlgebra k (Fin 4)) =
      single (cubeBodyDiagonalIndex v) c - (c * Ring.inverse 4) • permutationSum k (Fin 4) := by
  simp [cubeVertexRepresentationEquiv]

/-- The sign-twisted standard component of `c e_v` is `ε c (e_j - ¼ ∑ᵢ eᵢ)`, for `j` the body
diagonal through `v` and `ε` the product of the coordinates of `v`. -/
@[simp]
theorem coe_cubeVertexRepresentationEquiv_single_snd_snd_snd (h : IsUnit (2 : k))
    (v : Fin 3 → ℤˣ) (c : k) :
    ((cubeVertexRepresentationEquiv h (single v c)).2.2.2 : MonoidAlgebra k (Fin 4)) =
      single (cubeBodyDiagonalIndex v) ((((∏ i, v i : ℤˣ) : ℤ) : k) * c) -
        ((((∏ i, v i : ℤˣ) : ℤ) : k) * c * Ring.inverse 4) • permutationSum k (Fin 4) := by
  simp [cubeVertexRepresentationEquiv]

/-- The inverse decomposition adds the trivial and sign components, as multiples of the sum of
the diagonals, to the two standard components, and undoes the even and odd splitting. -/
theorem cubeVertexRepresentationEquiv_symm_apply (h : IsUnit (2 : k))
    (x : k × k × (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule ×
      (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule) :
    (cubeVertexRepresentationEquiv h).symm x =
      (cubeVertexRepresentationDiagonalEquiv h).symm
        (x.1 • permutationSum k (Fin 4) + x.2.2.1, x.2.1 • permutationSum k (Fin 4) + x.2.2.2) := by
  have hx : (LinearEquiv.prodAssoc k k k _).symm x = ((x.1, x.2.1), x.2.2) :=
    (LinearEquiv.symm_apply_eq _).mpr (by simp)
  simp [cubeVertexRepresentationEquiv, Representation.Equiv.coe_invFun, hx]

end VertexDecomposition

section Multiplicity

variable {k} [Field k] [CharZero k]

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
  refine symmetricGroupFourClassData.finrank_intertwiningMap_of_character_rep
    (symmetricGroupFourCharacterTable (i.cast numClasses_symmetricGroupFourClassData.symm))
    (fun j ↦ ![8, 0, 0, 2, 0] (j.cast numClasses_symmetricGroupFourClassData)) _ hρ (fun j ↦ ?_) ?_
  · rw [char_cubeVertexRepresentation_symmetricGroupFourClassData_rep]
    generalize j.cast numClasses_symmetricGroupFourClassData = j
    fin_cases j <;> simp
  · simp only [symmetricGroupFourCharacterTable_apply, Fintype.card_perm, Fintype.card_fin]
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
  refine symmetricGroupFourClassData.finrank_intertwiningMap_of_character_rep
    (symmetricGroupFourCharacterTable (i.cast numClasses_symmetricGroupFourClassData.symm))
    (fun j ↦ ![12, 2, 0, 0, 0] (j.cast numClasses_symmetricGroupFourClassData)) _ hρ (fun j ↦ ?_) ?_
  · rw [char_cubeEdgeRepresentation_symmetricGroupFourClassData_rep]
    generalize j.cast numClasses_symmetricGroupFourClassData = j
    fin_cases j <;> simp
  · simp only [symmetricGroupFourCharacterTable_apply, Fintype.card_perm, Fintype.card_fin]
    fin_cases i <;> decide

variable (k) in
/-- **The standard representation occurs twice in the edge representation**: the space of
intertwiners `V₄ → k[Y]` is two-dimensional. Character pairings give this dimension, not two
particular copies of `V₄`. Over an algebraically closed field a basis of this space does:
transported along `Representation.IntertwiningMap.equivLinearMapAsModule` to the `k[S₄]`-linear
maps of
`TauCeti.finrank_linearMap_standardRepresentation_cubeEdgeRepresentation`, it splits the
`V₄`-isotypic component through `Module.Basis.isotypicComponentEquiv`. -/
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
`k[S₄]`-linear maps between the group-algebra modules. Over an algebraically closed field a basis
`b` of it, such as `Module.finBasisOfFinrankEq`, splits the `V₄`-isotypic component of `k[Y]` as
`V₄ ⊕ V₄`, `(v₀, v₁) ↦ b 0 v₀ + b 1 v₁`, through `Module.Basis.isotypicComponentEquiv`. -/
theorem finrank_linearMap_standardRepresentation_cubeEdgeRepresentation :
    Module.finrank k ((standardRepresentation k (Fin 4)).asModule →ₗ[k[Perm (Fin 4)]]
      (cubeEdgeRepresentation k).asModule) = 2 := by
  rw [← (Representation.IntertwiningMap.equivLinearMapAsModule _ _).finrank_eq]
  exact finrank_intertwiningMap_standardRepresentation_cubeEdgeRepresentation k

/-- **The `V₄`-isotypic component of `k[Y]` is six-dimensional**: it is the sum of the two copies
of the standard representation in the edge representation, over any field of characteristic zero.
There `V₄` is absolutely irreducible, its intertwiners being the scalars. -/
theorem finrank_isotypicComponent_cubeEdgeRepresentation_standardRepresentation :
    Module.finrank k (isotypicComponent k[Perm (Fin 4)] (cubeEdgeRepresentation k).asModule
      (standardRepresentation k (Fin 4)).asModule) = 6 := by
  have := isIrreducible_standardRepresentation (k := k) (α := Fin 4) (by decide)
    (Or.inr (by norm_num))
  have hρ (j) : (standardRepresentation k (Fin 4)).character (symmetricGroupFourClassData.rep j) =
      symmetricGroupFourCharacterTable
        ((3 : Fin 5).cast numClasses_symmetricGroupFourClassData.symm) j := by
    rw [symmetricGroupFourCharacterTable_eq_character, Fin.cast_cast, Fin.cast_eq_self]
    simp only [Matrix.cons_val]
  have hend : Module.finrank k
      (Module.End k[Perm (Fin 4)] (standardRepresentation k (Fin 4)).asModule) = 1 := by
    rw [← (Representation.IntertwiningMap.equivLinearMapAsModule _ _).finrank_eq]
    refine symmetricGroupFourClassData.finrank_intertwiningMap_of_character_rep _ _ 1 hρ hρ ?_
    simp only [symmetricGroupFourCharacterTable_apply, Fintype.card_perm, Fintype.card_fin]
    decide
  have h := finrank_isotypicComponent_mul_finrank_end (k := k) (A := k[Perm (Fin 4)])
    (M := (cubeEdgeRepresentation k).asModule) (S := (standardRepresentation k (Fin 4)).asModule)
  rw [hend, mul_one, finrank_linearMap_standardRepresentation_cubeEdgeRepresentation k,
    (Representation.asModuleEquiv _).finrank_eq, finrank_augmentationSubrepresentation] at h
  simpa using h

end Isotypic

end TauCeti
