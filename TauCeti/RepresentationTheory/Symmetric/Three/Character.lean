/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinThree.Dihedral
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.Dihedral.Three
public import TauCeti.RepresentationTheory.Symmetric.Three.SymmetricPower
import TauCeti.GroupTheory.Perm.FinThree.Basic
import TauCeti.LinearAlgebra.SymmetricPower.Coordinates

/-!
# Characters of the symmetric powers of the standard representation of `S₃`

Over every field, the standard module and its symmetric square and cube have characters
`(2, 0, -1)`, `(3, 1, 0)` and `(4, 0, 1)` in the class order identity, transposition, `3`-cycle.
The traces are computed in monomial bases built from `e₀ - e₂`, `e₁ - e₂`, so they need no
primitive cube root of unity or characteristic restriction.

## Main results

* `TauCeti.character_standardRepresentation_one`, `TauCeti.character_standardRepresentation_swap`
  and `TauCeti.character_standardRepresentation_finRotate`: the standard character values.
* `TauCeti.trace_symmetricPower_two_standardRepresentation` and
  `TauCeti.trace_symmetricPower_three_standardRepresentation`: the characters are `1 + χ` and
  `1 + sgn + χ`, where `χ` is the standard character.
* `TauCeti.dihedralGroupThreeCharacterTable_eq_character`: through the isomorphism sending
  a rotation to `finRotate 3` and a reflection to `(0 1)`, the rows of the displayed dihedral
  character table are the trivial, sign and standard characters. Its column order is identity,
  rotation, reflection, accounting for the permutation of class orders.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  §1.3 and §2.1.
-/

public section

open MonoidAlgebra Module
open scoped TensorProduct

namespace TauCeti

variable {k : Type} [Field k]

/-! ### Characters of the standard module

These values hold over every field: the character of the standard module is the number of fixed
points minus one (`TauCeti.char_standardRepresentation`). -/

section Character

/-- **`χ_{V₃}(1) = 2`.** -/
theorem character_standardRepresentation_one (K : Type*) [Field K] :
    (standardRepresentation K (Fin 3)).character 1 = 2 := by
  rw [Representation.char_one, finrank_augmentationSubrepresentation]
  norm_num

/-- **`χ_{V₃}(σ) = 0`** for the transposition `σ = (0 1)`, which fixes one point. -/
theorem character_standardRepresentation_swap (K : Type*) [Field K] :
    (standardRepresentation K (Fin 3)).character (Equiv.swap 0 1) = 0 := by
  rw [char_standardRepresentation, char_ofMulAction, Nat.card_eq_fintype_card,
    show Fintype.card {x : Fin 3 // Equiv.swap (0 : Fin 3) 1 • x = x} = 1 by decide]
  simp

/-- **`χ_{V₃}(τ) = -1`** for the cycle `τ = (0 1 2)`, which fixes no point. -/
theorem character_standardRepresentation_finRotate (K : Type*) [Field K] :
    (standardRepresentation K (Fin 3)).character (finRotate 3) = -1 := by
  rw [char_standardRepresentation, char_ofMulAction, Nat.card_eq_fintype_card,
    show Fintype.card {x : Fin 3 // finRotate 3 • x = x} = 0 by decide]
  simp

end Character

/-! ### The characters of the symmetric square and cube

The characters of `Sym² V₃` and `Sym³ V₃` are stated as traces, `LinearMap.trace` of the action:
`Representation.character` asks for an additive group structure on the carrier, and the
representation `Representation.symmetricPower` is built on the additive monoid structure of the
symmetric power.

They are computed over every field, without a cube root of unity, in the monomial bases built
from the basis `x = e₀ - e₂`, `y = e₁ - e₂` of `V₃`. There `σ = (0 1)` exchanges `x` and `y`, so
it permutes the monomials, and `τ = (0 1 2)` acts by `τ x = y - x`, `τ y = -x`, so the diagonal
coefficients of its action on a monomial are read off by expanding the product. -/

/-- The vectors `x = e₀ - e₂` and `y = e₁ - e₂` of the standard module of `S₃`. -/
private noncomputable def symmetricGroupThreeDiffVec (i : Fin 2) :
    (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule :=
  ⟨single i.castSucc 1 - single 2 1, by
    rw [toSubmodule_augmentationSubrepresentation, LinearMap.mem_ker]
    simp only [← MonoidAlgebra.basis_apply, map_sub, Basis.sumCoords_self_apply, sub_self]⟩

/-- The vectors `x` and `y` are linearly independent. -/
private theorem linearIndependent_symmetricGroupThreeDiffVec :
    LinearIndependent k (symmetricGroupThreeDiffVec (k := k)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hcoeff : ∀ j : Fin 3, ∑ i, c i * ((symmetricGroupThreeDiffVec i :
      (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule) :
        MonoidAlgebra k (Fin 3)).coeff j = 0 := fun j => by
    simpa [Finset.sum_apply'] using
      congrArg (fun v : MonoidAlgebra k (Fin 3) => v.coeff j) (congrArg Subtype.val hc)
  have h0 := hcoeff 0
  have h1 := hcoeff 1
  simp [symmetricGroupThreeDiffVec, Fin.sum_univ_two, Finsupp.single_apply] at h0 h1
  fin_cases i <;> simpa

/-- The basis `x = e₀ - e₂`, `y = e₁ - e₂` of the standard module of `S₃`, over every field. -/
private noncomputable def symmetricGroupThreeDiffBasis :
    Basis (Fin 2) k (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_symmetricGroupThreeDiffVec
    (by rw [finrank_augmentationSubrepresentation]; simp)

/-- The basis vectors are `x` and `y`. -/
private theorem symmetricGroupThreeDiffBasis_apply (i : Fin 2) :
    symmetricGroupThreeDiffBasis (k := k) i = symmetricGroupThreeDiffVec i := by
  simp [symmetricGroupThreeDiffBasis]

/-- `σ` exchanges `x` and `y`. -/
private theorem standardRepresentation_swap_symmetricGroupThreeDiffBasis (i : Fin 2) :
    standardRepresentation k (Fin 3) (Equiv.swap 0 1) (symmetricGroupThreeDiffBasis i) =
      symmetricGroupThreeDiffBasis (Equiv.swap 0 1 i) := by
  rw [symmetricGroupThreeDiffBasis_apply, symmetricGroupThreeDiffBasis_apply,
    ← toRepresentation_augmentationSubrepresentation, Subrepresentation.toRepresentation_apply_coe]
  have h0 : Equiv.swap (0 : Fin 3) 1 • (0 : Fin 3) = 1 := by decide
  have h1 : Equiv.swap (0 : Fin 3) 1 • (1 : Fin 3) = 0 := by decide
  have h2 : Equiv.swap (0 : Fin 3) 1 • (2 : Fin 3) = 2 := by decide
  fin_cases i <;>
    simp [symmetricGroupThreeDiffVec, Representation.ofMulAction_single, h0, h1, h2]

/-- `τ x = y - x` and `τ y = -x`, as the matrix of `τ` in the basis `x, y`. -/
private theorem repr_standardRepresentation_finRotate_symmetricGroupThreeDiffBasis (i j : Fin 2) :
    symmetricGroupThreeDiffBasis.repr
        (standardRepresentation k (Fin 3) (finRotate 3) (symmetricGroupThreeDiffBasis j)) i =
      !![-1, -1; 1, 0] i j := by
  have hx : standardRepresentation k (Fin 3) (finRotate 3) (symmetricGroupThreeDiffBasis 0) =
      symmetricGroupThreeDiffBasis 1 - symmetricGroupThreeDiffBasis 0 := by
    rw [symmetricGroupThreeDiffBasis_apply, symmetricGroupThreeDiffBasis_apply,
      ← toRepresentation_augmentationSubrepresentation,
      Subrepresentation.toRepresentation_apply_coe]
    have h0 : (finRotate 3) • (0 : Fin 3) = 1 := by decide
    have h2 : (finRotate 3) • (2 : Fin 3) = 0 := by decide
    simp [symmetricGroupThreeDiffVec, Representation.ofMulAction_single, h0, h2]
  have hy : standardRepresentation k (Fin 3) (finRotate 3) (symmetricGroupThreeDiffBasis 1) =
      -symmetricGroupThreeDiffBasis 0 := by
    rw [symmetricGroupThreeDiffBasis_apply, symmetricGroupThreeDiffBasis_apply,
      ← toRepresentation_augmentationSubrepresentation,
      Subrepresentation.toRepresentation_apply_coe]
    have h1 : (finRotate 3) • (1 : Fin 3) = 2 := by decide
    have h2 : (finRotate 3) • (2 : Fin 3) = 0 := by decide
    simp [symmetricGroupThreeDiffVec, Representation.ofMulAction_single, h1, h2]
  fin_cases j <;> fin_cases i <;> simp [hx, hy]

/-- The trace of `σ` on `Symⁿ V₃` counts the monomials in `x, y` fixed by exchanging `x` and `y`. -/
private theorem trace_symmetricPower_standardRepresentation_swap (n : ℕ) :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower n (Equiv.swap 0 1)) =
      (Finset.univ.filter fun s : Sym (Fin 2) n => s.map (Equiv.swap 0 1) = s).card := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k (symmetricGroupThreeDiffBasis.symmetricPower n),
    Matrix.trace, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Representation.symmetricPower_apply,
    symmetricGroupThreeDiffBasis.map_symmetricPower_apply_eq_symmetricPower_map _ _ _
      standardRepresentation_swap_symmetricGroupThreeDiffBasis, Basis.repr_self,
    Finsupp.single_apply]

/-- The diagonal coefficient of `τ` on `Symⁿ V₃` at the monomial indexed by `Sym.ofFn p` is the
sum, over the orderings `q` of `p`, of the products of the matrix coefficients of `τ` at `q, p`. -/
private theorem symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis {n : ℕ}
    (p : Fin n → Fin 2) (S : Finset (Fin n → Fin 2))
    (hS : ∀ q, q ∈ S ↔ Sym.ofFn q = Sym.ofFn p) :
    (symmetricGroupThreeDiffBasis.symmetricPower n).repr
        ((standardRepresentation k (Fin 3)).symmetricPower n (finRotate 3)
          (symmetricGroupThreeDiffBasis.symmetricPower n (Sym.ofFn p)))
        (Sym.ofFn p) =
      ∑ q ∈ S, ∏ i, !![(-1 : k), -1; 1, 0] (q i) (p i) := by
  simp_rw [Basis.symmetricPower_apply, SymmetricPower.tprodOfSym_ofFn,
    Representation.symmetricPower_apply_tprod, Basis.symmetricPower_repr_tprod_apply,
    repr_standardRepresentation_finRotate_symmetricGroupThreeDiffBasis]
  exact finsum_cond_eq_sum_of_cond_iff _ fun {q} _ => (hS q).symm

/-- Traces of the symmetric powers are invariant under conjugation. -/
private theorem trace_symmetricPower_standardRepresentation_conj (n : ℕ)
    (x h : Equiv.Perm (Fin 3)) :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower n (h * x * h⁻¹)) =
      LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower n x) := by
  rw [map_mul ((standardRepresentation k (Fin 3)).symmetricPower n),
    map_mul ((standardRepresentation k (Fin 3)).symmetricPower n), LinearMap.trace_mul_comm,
    ← mul_assoc, ← map_mul ((standardRepresentation k (Fin 3)).symmetricPower n), inv_mul_cancel,
    map_one, one_mul]

/-- **`χ_{Sym² V₃}(1) = 3`**: `Sym² V₃` has dimension `3`. -/
theorem trace_symmetricPower_two_standardRepresentation_one :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower 2 1) = 3 := by
  -- The trace of the identity is stated for an additive group, so it is applied up to the
  -- definitional agreement of the two additive monoid structures, as explained above.
  rw [map_one]
  refine (LinearMap.trace_one k
    (Sym[k]^2 (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule)).trans ?_
  rw [SymmetricPower.finrank_eq, finrank_augmentationSubrepresentation]
  simp [Nat.multichoose_eq]

/-- **`χ_{Sym² V₃}(σ) = 1`** for the transposition `σ = (0 1)`, which fixes the monomial `xy` and
exchanges `x²` and `y²`. -/
theorem trace_symmetricPower_two_standardRepresentation_swap :
    LinearMap.trace k _
      ((standardRepresentation k (Fin 3)).symmetricPower 2 (Equiv.swap 0 1)) = 1 := by
  rw [trace_symmetricPower_standardRepresentation_swap, show (Finset.univ.filter
    fun s : Sym (Fin 2) 2 => s.map (Equiv.swap 0 1) = s).card = 1 by decide, Nat.cast_one]

/-- **`χ_{Sym² V₃}(τ) = 0`** for the cycle `τ = (0 1 2)`, whose diagonal coefficients on the
monomials `x², xy, y²` are `1, -1, 0`. -/
theorem trace_symmetricPower_two_standardRepresentation_finRotate :
    LinearMap.trace k _
      ((standardRepresentation k (Fin 3)).symmetricPower 2 (finRotate 3)) = 0 := by
  have huniv : (Finset.univ : Finset (Sym (Fin 2) 2)) =
      {Sym.ofFn ![0, 0], Sym.ofFn ![0, 1], Sym.ofFn ![1, 1]} := by
    refine (Finset.eq_univ_of_forall fun s => ?_).symm
    obtain ⟨p, rfl⟩ := Sym.ofFn_surjective s
    simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, Sym.coe_ofFn]
    revert p
    decide
  rw [LinearMap.trace_eq_matrix_trace k (symmetricGroupThreeDiffBasis.symmetricPower 2),
    Matrix.trace, huniv, Finset.sum_insert ?_, Finset.sum_insert ?_, Finset.sum_singleton]
  · simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rw [symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _ {![0, 0]} ?_,
      symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _ {![0, 1], ![1, 0]} ?_,
      symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _ {![1, 1]} ?_]
    · simp [Fin.prod_univ_two]
    -- The orderings of each monomial.
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, Sym.coe_ofFn]
      decide
  -- The three monomials are distinct.
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, Sym.coe_ofFn]
    decide

/-- **The character of `Sym² V₃` is `1 + χ_{V₃}`**, the character of `1 ⊕ V₃`
(compare `TauCeti.symmetricGroupThreeSymSqEquiv`). Both sides are class functions, so it suffices
to compare them at the identity, at `σ = (0 1)` and at `τ = (0 1 2)`. This holds over every
field. -/
theorem trace_symmetricPower_two_standardRepresentation (g : Equiv.Perm (Fin 3)) :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower 2 g) =
      1 + (standardRepresentation k (Fin 3)).character g := by
  obtain ⟨h, rfl | rfl | rfl⟩ := Equiv.Perm.fin_three_conj_cases g
  · rw [trace_symmetricPower_two_standardRepresentation_one, character_standardRepresentation_one]
    norm_num
  · rw [trace_symmetricPower_standardRepresentation_conj, Representation.char_conj,
      trace_symmetricPower_two_standardRepresentation_swap, character_standardRepresentation_swap,
      add_zero]
  · rw [trace_symmetricPower_standardRepresentation_conj, Representation.char_conj,
      trace_symmetricPower_two_standardRepresentation_finRotate,
      character_standardRepresentation_finRotate, add_neg_cancel]

/-- **`χ_{Sym³ V₃}(1) = 4`**: `Sym³ V₃` has dimension `4`. -/
theorem trace_symmetricPower_three_standardRepresentation_one :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower 3 1) = 4 := by
  -- The trace of the identity is stated for an additive group, so it is applied up to the
  -- definitional agreement of the two additive monoid structures, as explained above.
  rw [map_one]
  refine (LinearMap.trace_one k
    (Sym[k]^3 (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule)).trans ?_
  rw [SymmetricPower.finrank_eq, finrank_augmentationSubrepresentation]
  simp [Nat.multichoose_eq]

/-- **`χ_{Sym³ V₃}(σ) = 0`** for the transposition `σ = (0 1)`, which permutes the monomials
`x³, x²y, xy², y³` without fixed points. -/
theorem trace_symmetricPower_three_standardRepresentation_swap :
    LinearMap.trace k _
      ((standardRepresentation k (Fin 3)).symmetricPower 3 (Equiv.swap 0 1)) = 0 := by
  rw [trace_symmetricPower_standardRepresentation_swap, show (Finset.univ.filter
    fun s : Sym (Fin 2) 3 => s.map (Equiv.swap 0 1) = s).card = 0 by decide, Nat.cast_zero]

/-- **`χ_{Sym³ V₃}(τ) = 1`** for the cycle `τ = (0 1 2)`, whose diagonal coefficients on the
monomials `x³, x²y, xy², y³` are `-1, 2, 0, 0`. -/
theorem trace_symmetricPower_three_standardRepresentation_finRotate :
    LinearMap.trace k _
      ((standardRepresentation k (Fin 3)).symmetricPower 3 (finRotate 3)) = 1 := by
  have huniv : (Finset.univ : Finset (Sym (Fin 2) 3)) = {Sym.ofFn ![0, 0, 0],
      Sym.ofFn ![0, 0, 1], Sym.ofFn ![0, 1, 1], Sym.ofFn ![1, 1, 1]} := by
    refine (Finset.eq_univ_of_forall fun s => ?_).symm
    obtain ⟨p, rfl⟩ := Sym.ofFn_surjective s
    simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, Sym.coe_ofFn]
    revert p
    decide
  rw [LinearMap.trace_eq_matrix_trace k (symmetricGroupThreeDiffBasis.symmetricPower 3),
    Matrix.trace, huniv, Finset.sum_insert ?_, Finset.sum_insert ?_, Finset.sum_insert ?_,
    Finset.sum_singleton]
  · simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rw [symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _ {![0, 0, 0]} ?_,
      symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _
        {![0, 0, 1], ![0, 1, 0], ![1, 0, 0]} ?_,
      symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _
        {![0, 1, 1], ![1, 0, 1], ![1, 1, 0]} ?_,
      symmetricPower_repr_finRotate_symmetricGroupThreeDiffBasis _ {![1, 1, 1]} ?_]
    · simp [Fin.prod_univ_three]
    -- The orderings of each monomial.
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, Sym.coe_ofFn]
      decide
  -- The four monomials are distinct.
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, ← Sym.coe_inj, Sym.coe_ofFn]
    decide

/-- **The character of `Sym³ V₃` is `1 + sgn + χ_{V₃}`**, the character of `1 ⊕ sgn ⊕ V₃`
(compare `TauCeti.symmetricGroupThreeSymCubeEquiv`). Both sides are class functions, so it
suffices to compare them at the identity, at `σ = (0 1)` and at `τ = (0 1 2)`. Unlike the
isomorphism `1 ⊕ sgn ⊕ V₃ ≃ Sym³ V₃`, this holds over every field. -/
theorem trace_symmetricPower_three_standardRepresentation (g : Equiv.Perm (Fin 3)) :
    LinearMap.trace k _ ((standardRepresentation k (Fin 3)).symmetricPower 3 g) =
      1 + (Equiv.Perm.sign g : ℤ) + (standardRepresentation k (Fin 3)).character g := by
  have hsign : ∀ x h : Equiv.Perm (Fin 3), Equiv.Perm.sign (h * x * h⁻¹) = Equiv.Perm.sign x := by
    intro x h
    rw [map_mul, map_mul, Equiv.Perm.sign_inv, mul_right_comm, Int.units_mul_self, one_mul]
  obtain ⟨h, rfl | rfl | rfl⟩ := Equiv.Perm.fin_three_conj_cases g
  · rw [trace_symmetricPower_three_standardRepresentation_one, map_one,
      character_standardRepresentation_one]
    norm_num
  · rw [trace_symmetricPower_standardRepresentation_conj, hsign, Representation.char_conj,
      trace_symmetricPower_three_standardRepresentation_swap,
      character_standardRepresentation_swap, Equiv.Perm.sign_swap (by decide)]
    norm_num
  · rw [trace_symmetricPower_standardRepresentation_conj, hsign, Representation.char_conj,
      trace_symmetricPower_three_standardRepresentation_finRotate,
      character_standardRepresentation_finRotate, sign_finRotate]
    norm_num

/-! ### Comparison with the character table of the dihedral group of order six -/

/-- **The displayed character table of the dihedral group of order six is that of `S₃`.**
Through `TauCeti.dihedralGroupThreeMulEquivPerm`, the rows of
`TauCeti.dihedralGroupThreeCharacterTable` are the characters of the trivial representation, the
sign representation and the standard representation of `S₃`, evaluated at the numbered class
representatives: the identity, a rotation (a `3`-cycle) and a reflection (a transposition). This
holds over every field. -/
theorem dihedralGroupThreeCharacterTable_eq_character {K : Type*} [Field K]
    (i j : DihedralGroupThreeClassIndex) :
    (dihedralGroupThreeCharacterTable i j : K) =
      ![(Representation.trivial K (Equiv.Perm (Fin 3)) K).character,
        (Representation.ofLinearCharacter (signLinearCharacter K (Fin 3))).character,
        (standardRepresentation K (Fin 3)).character] i
        (dihedralGroupThreeMulEquivPerm ((dihedralClassData 3).rep j)) := by
  have hrep : ∀ j, (dihedralClassData 3).rep j = ![1, .r 2, .sr 2] j := by
    intro j
    fin_cases j <;> rfl
  rw [dihedralGroupThreeCharacterTable_apply, hrep]
  revert i j
  -- The class index type `Fin (dihedralClassData 3).numClasses` is `Fin 3` by evaluation of the
  -- class data; restating the goal over `Fin 3` lets `fin_cases` produce literal indices.
  change ∀ i j : Fin 3, ((!![1, 1, 1; 1, 1, -1; 2, -1, 0] i j : ℤ) : K) =
    ![(Representation.trivial K (Equiv.Perm (Fin 3)) K).character,
      (Representation.ofLinearCharacter (signLinearCharacter K (Fin 3))).character,
      (standardRepresentation K (Fin 3)).character] i
      (dihedralGroupThreeMulEquivPerm (![1, .r 2, .sr 2] j))
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [-dihedralGroupThreeMulEquivPerm_r, -dihedralGroupThreeMulEquivPerm_sr,
      -char_standardRepresentation, -Equiv.swap_inv, dihedralGroupThreeMulEquivPerm_r_two,
      dihedralGroupThreeMulEquivPerm_sr_two,
      Representation.char_conj, Representation.char_trivial,
      Representation.char_ofLinearCharacter, coe_signLinearCharacter_apply,
      character_standardRepresentation_swap, character_standardRepresentation_finRotate,
      sign_finRotate]

end TauCeti
