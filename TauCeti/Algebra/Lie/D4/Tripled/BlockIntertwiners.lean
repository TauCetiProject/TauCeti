/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Basic
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Rational

/-!
# Triality intertwiners between the three type-D4 blocks

The tripled type-`D₄` weight table consists of three consecutive eight-dimensional blocks,
carrying the natural and two half-spin weight systems. This file restricts the order-three
coordinate permutation of triality to equivalences between the individual blocks.

The block cycle is numbered
`V(ϖ₁) → V(ϖ₃) → V(ϖ₄) → V(ϖ₁)`. Each restricted coordinate equivalence induces a linear
equivalence over every semiring. It intertwines the positive, negative, and Cartan
Chevalley-generator matrices after applying the corresponding triality permutation to the Dynkin
node. The final
`mulVec` equations express these three compatibilities directly as identities of actions on
coordinate vectors.

These restricted intertwiners isolate the representation-level content of triality from the
ambient twenty-four-dimensional direct sum. Comparing the two spin blocks with exterior
half-spin models requires a separate choice of exterior-basis signs.

## Main declarations

* `TauCeti.D4Tripled.Block`: the coordinates belonging to one of the three blocks.
* `TauCeti.D4Tripled.blockLocalIndexEquiv`: identification of each block with its eight local
  coordinates.
* `TauCeti.D4Tripled.blockIndexEquiv`: triality restricted from one block to the next.
* `TauCeti.D4Tripled.blockModuleEquiv`: the induced coordinate equivalence over any semiring.
* `TauCeti.D4Tripled.blockModuleEquiv_raising_mulVec` and its lowering and Cartan analogues:
  the three generator-action intertwining identities.
* `TauCeti.D4Tripled.d4BlockZeroToOneEquiv`, `d4BlockOneToTwoEquiv`, and
  `d4BlockTwoToZeroEquiv`: the three concrete coordinate equivalences used by the rational
  vector and half-spin comparisons.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

open scoped Matrix

public section

namespace LinearEquiv

/-- Reindexing coordinate functions along `e` intertwines multiplication by two matrices whose
entries correspond along `e`. -/
theorem piCongrLeft'_mulVec {R I J : Type*} [Semiring R] [Fintype I] [Fintype J]
    (e : I ≃ J) (M : Matrix I I R) (N : Matrix J J R)
    (h : ∀ a b, N (e a) (e b) = M a b) (v : I → R) :
    piCongrLeft' R (fun _ => R) e (M *ᵥ v) =
      N *ᵥ piCongrLeft' R (fun _ => R) e v := by
  classical
  funext a
  have hNM : N.submatrix e e = M := by
    ext x y
    exact h x y
  have hs := Matrix.submatrix_mulVec_equiv N v e e
  have ha := congrFun hs (e.symm a)
  have hcoe : piCongrLeft' R (fun _ => R) e v = v ∘ e.symm := by
    funext x
    simp
  rw [hcoe]
  simpa only [hNM, piCongrLeft'_apply, Function.comp_apply,
    Equiv.apply_symm_apply] using ha

end LinearEquiv

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

universe u

/-! ## The cyclic block equivalences -/

/-- The eight coordinates in the `j`-th block of the tripled weight table. -/
abbrev Block (j : Fin 3) := {a : Fin 24 // d4TripledSummand a = j}

/-- The position of a coordinate inside one of the three consecutive eight-coordinate blocks. -/
def blockLocalIndexEquiv (j : Fin 3) : Block j ≃ Fin 8 where
  toFun a := ⟨a.1.val % 8, Nat.mod_lt _ (by omega)⟩
  invFun i := ⟨⟨8 * j.val + i.val, by omega⟩, by
    fin_cases j <;> fin_cases i <;> decide +kernel⟩
  left_inv a := by
    apply Subtype.ext
    apply Fin.ext
    simp only
    have ha := a.2
    simp only [d4TripledSummand] at ha
    omega
  right_inv i := by
    apply Fin.ext
    simp

/-- The local coordinate of a block index is its table index modulo eight. -/
@[simp]
theorem blockLocalIndexEquiv_apply_val (j : Fin 3) (a : Block j) :
    (blockLocalIndexEquiv j a).val = a.1.val % 8 :=
  by simp [blockLocalIndexEquiv]

/-- The table index at local position `i` in block `j` is `8 * j + i`. -/
@[simp]
theorem blockLocalIndexEquiv_symm_val (j : Fin 3) (i : Fin 8) :
    ((blockLocalIndexEquiv j).symm i).1.val = 8 * j.val + i.val :=
  by simp [blockLocalIndexEquiv]

/-- Triality restricted to an equivalence from one eight-dimensional block to the next. -/
abbrev blockIndexEquiv (j : Fin 3) : Block j ≃ Block (finRotate 3 j) :=
  d4TripledTrialityPerm.subtypeEquiv fun a => by
    rw [finRotate_apply]
    exact (d4TripledSummand_d4TripledTrialityPerm_eq_iff a j).symm

/-- The underlying table index of the restricted block equivalence is the triality index. -/
@[simp]
theorem coe_blockIndexEquiv (j : Fin 3) (a : Block j) :
    (blockIndexEquiv j a).val = d4TripledTrialityPerm a.1 :=
  rfl

/-- The coordinate equivalence induced by triality from one block to the next. -/
abbrev blockModuleEquiv (R : Type u) [Semiring R] (j : Fin 3) :
    (Block j → R) ≃ₗ[R] (Block (finRotate 3 j) → R) :=
  LinearEquiv.piCongrLeft' R (fun _ => R) (blockIndexEquiv j)

/-! ## Restricted Chevalley generators -/

/-- The positive Chevalley-generator matrix restricted to one block and extended to `R`. -/
def blockRaisingMatrix (R : Type u) [Ring R] (j : Fin 3) (i : Fin 4) :
    Matrix (Block j) (Block j) R :=
  ((raisingMatrix i).map (Int.castRingHom R)).submatrix Subtype.val Subtype.val

/-- The negative Chevalley-generator matrix restricted to one block and extended to `R`. -/
def blockLoweringMatrix (R : Type u) [Ring R] (j : Fin 3) (i : Fin 4) :
    Matrix (Block j) (Block j) R :=
  ((loweringMatrix i).map (Int.castRingHom R)).submatrix Subtype.val Subtype.val

/-- The Cartan-generator matrix restricted to one block and extended to `R`. -/
def blockCartanGeneratorMatrix (R : Type u) [Ring R] (j : Fin 3) (i : Fin 4) :
    Matrix (Block j) (Block j) R :=
  ((cartanGeneratorMatrix i).map (Int.castRingHom R)).submatrix Subtype.val Subtype.val

/-- An entry of a restricted positive generator is the cast of the corresponding full-table
entry. -/
@[simp]
theorem blockRaisingMatrix_apply (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (a b : Block j) :
    blockRaisingMatrix R j i a b = (raisingMatrix i a.1 b.1 : R) := (rfl)

/-- An entry of a restricted negative generator is the cast of the corresponding full-table
entry. -/
@[simp]
theorem blockLoweringMatrix_apply (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (a b : Block j) :
    blockLoweringMatrix R j i a b = (loweringMatrix i a.1 b.1 : R) := (rfl)

/-- An entry of a restricted Cartan generator is the cast of the corresponding full-table entry. -/
@[simp]
theorem blockCartanGeneratorMatrix_apply (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (a b : Block j) :
    blockCartanGeneratorMatrix R j i a b = (cartanGeneratorMatrix i a.1 b.1 : R) := (rfl)

/-- Triality intertwines the positive generator matrices on consecutive blocks, entrywise. -/
theorem blockRaisingMatrix_triality (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (a b : Block j) :
    blockRaisingMatrix R (finRotate 3 j) (trialityPermD4 i)
        (blockIndexEquiv j a) (blockIndexEquiv j b) =
      blockRaisingMatrix R j i a b := by
  exact congrArg (Int.castRingHom R) (raisingMatrix_trialityPerm i a.1 b.1)

/-- Triality intertwines the negative generator matrices on consecutive blocks, entrywise. -/
theorem blockLoweringMatrix_triality (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (a b : Block j) :
    blockLoweringMatrix R (finRotate 3 j) (trialityPermD4 i)
        (blockIndexEquiv j a) (blockIndexEquiv j b) =
      blockLoweringMatrix R j i a b := by
  exact congrArg (Int.castRingHom R) (loweringMatrix_trialityPerm i a.1 b.1)

/-- Triality intertwines the Cartan-generator matrices on consecutive blocks, entrywise. -/
theorem blockCartanGeneratorMatrix_triality (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (a b : Block j) :
    blockCartanGeneratorMatrix R (finRotate 3 j) (trialityPermD4 i)
        (blockIndexEquiv j a) (blockIndexEquiv j b) =
      blockCartanGeneratorMatrix R j i a b := by
  exact congrArg (Int.castRingHom R) (cartanGeneratorMatrix_trialityPerm i a.1 b.1)

/-- The restricted triality equivalence intertwines every positive generator action with the
generator at the triality image of its node. -/
theorem blockModuleEquiv_raising_mulVec (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (v : Block j → R) :
    blockModuleEquiv R j (blockRaisingMatrix R j i *ᵥ v) =
      blockRaisingMatrix R (finRotate 3 j) (trialityPermD4 i) *ᵥ blockModuleEquiv R j v :=
  LinearEquiv.piCongrLeft'_mulVec (blockIndexEquiv j) _ _
    (blockRaisingMatrix_triality R j i) v

/-- The restricted triality equivalence intertwines every negative generator action with the
generator at the triality image of its node. -/
theorem blockModuleEquiv_lowering_mulVec (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (v : Block j → R) :
    blockModuleEquiv R j (blockLoweringMatrix R j i *ᵥ v) =
      blockLoweringMatrix R (finRotate 3 j) (trialityPermD4 i) *ᵥ blockModuleEquiv R j v :=
  LinearEquiv.piCongrLeft'_mulVec (blockIndexEquiv j) _ _
    (blockLoweringMatrix_triality R j i) v

/-- The restricted triality equivalence intertwines every Cartan-generator action with the
generator at the triality image of its node. -/
theorem blockModuleEquiv_cartanGenerator_mulVec (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (v : Block j → R) :
    blockModuleEquiv R j (blockCartanGeneratorMatrix R j i *ᵥ v) =
      blockCartanGeneratorMatrix R (finRotate 3 j) (trialityPermD4 i) *ᵥ
        blockModuleEquiv R j v :=
  LinearEquiv.piCongrLeft'_mulVec (blockIndexEquiv j) _ _
    (blockCartanGeneratorMatrix_triality R j i) v

/-! ## Concrete rational block cycle -/

/-- Triality from block zero to block one. The final subtype equivalence rewrites the computed
codomain `Block (finRotate 3 0)` to the propositionally equal type `Block 1`. -/
noncomputable def d4BlockZeroToOneIndexEquiv : Block 0 ≃ Block 1 :=
  (blockIndexEquiv 0).trans
    (Equiv.subtypeEquivRight fun _ => by
      rw [show finRotate 3 (0 : Fin 3) = 1 by decide])

/-- Triality from block one to block two. The final subtype equivalence rewrites the computed
codomain `Block (finRotate 3 1)` to the propositionally equal type `Block 2`. -/
noncomputable def d4BlockOneToTwoIndexEquiv : Block 1 ≃ Block 2 :=
  (blockIndexEquiv 1).trans
    (Equiv.subtypeEquivRight fun _ => by
      rw [show finRotate 3 (1 : Fin 3) = 2 by decide])

/-- Triality from block two to block zero. The final subtype equivalence rewrites the computed
codomain `Block (finRotate 3 2)` to the propositionally equal type `Block 0`. -/
noncomputable def d4BlockTwoToZeroIndexEquiv : Block 2 ≃ Block 0 :=
  (blockIndexEquiv 2).trans
    (Equiv.subtypeEquivRight fun _ => by
      rw [show finRotate 3 (2 : Fin 3) = 0 by decide])

/-- The table coordinate underlying triality from block zero to block one. -/
@[simp]
theorem coe_d4BlockZeroToOneIndexEquiv (a : Block 0) :
    (d4BlockZeroToOneIndexEquiv a).1 = d4TripledTrialityPerm a.1 := by
  simp [d4BlockZeroToOneIndexEquiv]

/-- The table coordinate underlying triality from block one to block two. -/
@[simp]
theorem coe_d4BlockOneToTwoIndexEquiv (a : Block 1) :
    (d4BlockOneToTwoIndexEquiv a).1 = d4TripledTrialityPerm a.1 := by
  simp [d4BlockOneToTwoIndexEquiv]

/-- The table coordinate underlying triality from block two to block zero. -/
@[simp]
theorem coe_d4BlockTwoToZeroIndexEquiv (a : Block 2) :
    (d4BlockTwoToZeroIndexEquiv a).1 = d4TripledTrialityPerm a.1 := by
  simp [d4BlockTwoToZeroIndexEquiv]

/-- The rational coordinate equivalence induced by triality from block zero to block one. -/
noncomputable def d4BlockZeroToOneEquiv :
    (Block 0 → ℚ) ≃ₗ[ℚ] (Block 1 → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) d4BlockZeroToOneIndexEquiv

/-- The rational coordinate equivalence induced by triality from block one to block two. -/
noncomputable def d4BlockOneToTwoEquiv :
    (Block 1 → ℚ) ≃ₗ[ℚ] (Block 2 → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) d4BlockOneToTwoIndexEquiv

/-- The rational coordinate equivalence induced by triality from block two to block zero. -/
noncomputable def d4BlockTwoToZeroEquiv :
    (Block 2 → ℚ) ≃ₗ[ℚ] (Block 0 → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) d4BlockTwoToZeroIndexEquiv

/-- Three successive concrete block intertwiners return every block-zero coordinate vector to
itself. -/
@[simp]
theorem d4BlockCycle_apply_apply_apply (v : Block 0 → ℚ) :
    d4BlockTwoToZeroEquiv (d4BlockOneToTwoEquiv (d4BlockZeroToOneEquiv v)) = v := by
  funext a
  simp [d4BlockZeroToOneEquiv, d4BlockOneToTwoEquiv, d4BlockTwoToZeroEquiv,
    d4BlockZeroToOneIndexEquiv, d4BlockOneToTwoIndexEquiv,
    d4BlockTwoToZeroIndexEquiv, LinearEquiv.piCongrLeft'_apply]

/-! ## Rational restricted matrices -/

/-- Restricting the rational positive generator to a block agrees with casting the restricted
integral generator to `ℚ`. -/
theorem blockRaisingMatrix_eq_submatrixQ (j : Fin 3) (i : Fin 4) :
    blockRaisingMatrix ℚ j i =
      (weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val := by
  ext a b
  simp only [blockRaisingMatrix_apply, Matrix.submatrix_apply,
    MinusculeWeightTable.raisingMatrixQ_apply, raisingMatrix_apply,
    weightTable_weight, weightTable_reflection]
  split_ifs <;> norm_num

/-- Restricting the rational negative generator to a block agrees with casting the restricted
integral generator to `ℚ`. -/
theorem blockLoweringMatrix_eq_submatrixQ (j : Fin 3) (i : Fin 4) :
    blockLoweringMatrix ℚ j i =
      (weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val := by
  ext a b
  simp only [blockLoweringMatrix_apply, Matrix.submatrix_apply,
    MinusculeWeightTable.loweringMatrixQ_apply, loweringMatrix_apply,
    weightTable_weight, weightTable_reflection]
  split_ifs <;> norm_num

/-- Restricting the rational Cartan generator to a block agrees with casting the restricted
integral generator to `ℚ`. -/
theorem blockCartanGeneratorMatrix_eq_submatrixQ (j : Fin 3) (i : Fin 4) :
    blockCartanGeneratorMatrix ℚ j i =
      (weightTable.cartanGeneratorMatrixQ i).submatrix Subtype.val Subtype.val := by
  ext a b
  simp only [blockCartanGeneratorMatrix_apply, Matrix.submatrix_apply,
    MinusculeWeightTable.cartanGeneratorMatrixQ_apply,
    cartanGeneratorMatrix_apply, weightTable_weight]
  split_ifs <;> norm_num

/-! ## Concrete generator transports -/

/-- Triality from block zero to block one intertwines the rational positive generators. -/
theorem d4BlockZeroToOneEquiv_raising_mulVec (i : Fin 4) (v : Block 0 → ℚ) :
    d4BlockZeroToOneEquiv
        ((weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (weightTable.raisingMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockZeroToOneEquiv v := by
  apply LinearEquiv.piCongrLeft'_mulVec d4BlockZeroToOneIndexEquiv
  intro a b
  rw [← blockRaisingMatrix_eq_submatrixQ, ← blockRaisingMatrix_eq_submatrixQ]
  simp only [blockRaisingMatrix_apply, coe_d4BlockZeroToOneIndexEquiv]
  exact congrArg (Int.castRingHom ℚ) (raisingMatrix_trialityPerm i a.1 b.1)

/-- Triality from block one to block two intertwines the rational positive generators. -/
theorem d4BlockOneToTwoEquiv_raising_mulVec (i : Fin 4) (v : Block 1 → ℚ) :
    d4BlockOneToTwoEquiv
        ((weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (weightTable.raisingMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockOneToTwoEquiv v := by
  apply LinearEquiv.piCongrLeft'_mulVec d4BlockOneToTwoIndexEquiv
  intro a b
  rw [← blockRaisingMatrix_eq_submatrixQ, ← blockRaisingMatrix_eq_submatrixQ]
  simp only [blockRaisingMatrix_apply, coe_d4BlockOneToTwoIndexEquiv]
  exact congrArg (Int.castRingHom ℚ) (raisingMatrix_trialityPerm i a.1 b.1)

/-- Triality from block two to block zero intertwines the rational positive generators. -/
theorem d4BlockTwoToZeroEquiv_raising_mulVec (i : Fin 4) (v : Block 2 → ℚ) :
    d4BlockTwoToZeroEquiv
        ((weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (weightTable.raisingMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockTwoToZeroEquiv v := by
  apply LinearEquiv.piCongrLeft'_mulVec d4BlockTwoToZeroIndexEquiv
  intro a b
  rw [← blockRaisingMatrix_eq_submatrixQ, ← blockRaisingMatrix_eq_submatrixQ]
  simp only [blockRaisingMatrix_apply, coe_d4BlockTwoToZeroIndexEquiv]
  exact congrArg (Int.castRingHom ℚ) (raisingMatrix_trialityPerm i a.1 b.1)

/-- Triality from block zero to block one intertwines the rational negative generators. -/
theorem d4BlockZeroToOneEquiv_lowering_mulVec (i : Fin 4) (v : Block 0 → ℚ) :
    d4BlockZeroToOneEquiv
        ((weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (weightTable.loweringMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockZeroToOneEquiv v := by
  apply LinearEquiv.piCongrLeft'_mulVec d4BlockZeroToOneIndexEquiv
  intro a b
  rw [← blockLoweringMatrix_eq_submatrixQ, ← blockLoweringMatrix_eq_submatrixQ]
  simp only [blockLoweringMatrix_apply, coe_d4BlockZeroToOneIndexEquiv]
  exact congrArg (Int.castRingHom ℚ) (loweringMatrix_trialityPerm i a.1 b.1)

/-- Triality from block one to block two intertwines the rational negative generators. -/
theorem d4BlockOneToTwoEquiv_lowering_mulVec (i : Fin 4) (v : Block 1 → ℚ) :
    d4BlockOneToTwoEquiv
        ((weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (weightTable.loweringMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockOneToTwoEquiv v := by
  apply LinearEquiv.piCongrLeft'_mulVec d4BlockOneToTwoIndexEquiv
  intro a b
  rw [← blockLoweringMatrix_eq_submatrixQ, ← blockLoweringMatrix_eq_submatrixQ]
  simp only [blockLoweringMatrix_apply, coe_d4BlockOneToTwoIndexEquiv]
  exact congrArg (Int.castRingHom ℚ) (loweringMatrix_trialityPerm i a.1 b.1)

/-- Triality from block two to block zero intertwines the rational negative generators. -/
theorem d4BlockTwoToZeroEquiv_lowering_mulVec (i : Fin 4) (v : Block 2 → ℚ) :
    d4BlockTwoToZeroEquiv
        ((weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (weightTable.loweringMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockTwoToZeroEquiv v := by
  apply LinearEquiv.piCongrLeft'_mulVec d4BlockTwoToZeroIndexEquiv
  intro a b
  rw [← blockLoweringMatrix_eq_submatrixQ, ← blockLoweringMatrix_eq_submatrixQ]
  simp only [blockLoweringMatrix_apply, coe_d4BlockTwoToZeroIndexEquiv]
  exact congrArg (Int.castRingHom ℚ) (loweringMatrix_trialityPerm i a.1 b.1)

/-- Triality from block zero to block one intertwines the rational Cartan generators. -/
theorem d4BlockZeroToOneEquiv_cartanGenerator_mulVec (i : Fin 4) (v : Block 0 → ℚ) :
    d4BlockZeroToOneEquiv
        ((weightTable.cartanGeneratorMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (weightTable.cartanGeneratorMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockZeroToOneEquiv v := by
  apply LinearEquiv.piCongrLeft'_mulVec d4BlockZeroToOneIndexEquiv
  intro a b
  rw [← blockCartanGeneratorMatrix_eq_submatrixQ,
    ← blockCartanGeneratorMatrix_eq_submatrixQ]
  simp only [blockCartanGeneratorMatrix_apply, coe_d4BlockZeroToOneIndexEquiv]
  exact congrArg (Int.castRingHom ℚ) (cartanGeneratorMatrix_trialityPerm i a.1 b.1)

/-- Triality from block one to block two intertwines the rational Cartan generators. -/
theorem d4BlockOneToTwoEquiv_cartanGenerator_mulVec (i : Fin 4) (v : Block 1 → ℚ) :
    d4BlockOneToTwoEquiv
        ((weightTable.cartanGeneratorMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (weightTable.cartanGeneratorMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockOneToTwoEquiv v := by
  apply LinearEquiv.piCongrLeft'_mulVec d4BlockOneToTwoIndexEquiv
  intro a b
  rw [← blockCartanGeneratorMatrix_eq_submatrixQ,
    ← blockCartanGeneratorMatrix_eq_submatrixQ]
  simp only [blockCartanGeneratorMatrix_apply, coe_d4BlockOneToTwoIndexEquiv]
  exact congrArg (Int.castRingHom ℚ) (cartanGeneratorMatrix_trialityPerm i a.1 b.1)

/-- Triality from block two to block zero intertwines the rational Cartan generators. -/
theorem d4BlockTwoToZeroEquiv_cartanGenerator_mulVec (i : Fin 4) (v : Block 2 → ℚ) :
    d4BlockTwoToZeroEquiv
        ((weightTable.cartanGeneratorMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (weightTable.cartanGeneratorMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockTwoToZeroEquiv v := by
  apply LinearEquiv.piCongrLeft'_mulVec d4BlockTwoToZeroIndexEquiv
  intro a b
  rw [← blockCartanGeneratorMatrix_eq_submatrixQ,
    ← blockCartanGeneratorMatrix_eq_submatrixQ]
  simp only [blockCartanGeneratorMatrix_apply, coe_d4BlockTwoToZeroIndexEquiv]
  exact congrArg (Int.castRingHom ℚ) (cartanGeneratorMatrix_trialityPerm i a.1 b.1)

end TauCeti.D4Tripled
