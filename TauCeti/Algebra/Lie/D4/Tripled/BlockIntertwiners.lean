/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Basic

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
* `TauCeti.D4Tripled.blockIndexEquiv`: triality restricted from one block to the next.
* `TauCeti.D4Tripled.blockModuleEquiv`: the induced coordinate equivalence over any semiring.
* `TauCeti.D4Tripled.blockModuleEquiv_raising_mulVec` and its lowering and Cartan analogues:
  the three generator-action intertwining identities.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

open scoped Matrix

public section

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

universe u

/-! ## The cyclic block equivalences -/

/-- The cycle of the natural and two half-spin blocks, numbered `0 → 1 → 2 → 0`. -/
@[expose]
def nextBlock : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv j := by fin_cases j <;> rfl
  right_inv j := by fin_cases j <;> rfl

/-- Applying the block cycle three times returns to the original block. -/
@[simp]
theorem nextBlock_apply_apply_apply (j : Fin 3) :
    nextBlock (nextBlock (nextBlock j)) = j := by
  fin_cases j <;> rfl

/-- The eight coordinates in the `j`-th block of the tripled weight table. -/
abbrev Block (j : Fin 3) := {a : Fin 24 // d4TripledSummand a = j}

/-- Triality restricted to an equivalence from one eight-dimensional block to the next. -/
@[expose]
def blockIndexEquiv (j : Fin 3) : Block j ≃ Block (nextBlock j) :=
  d4TripledTrialityPerm.subtypeEquiv fun a => by
    simp [nextBlock]

/-- The underlying table index of the restricted block equivalence is the triality index. -/
@[simp]
theorem coe_blockIndexEquiv (j : Fin 3) (a : Block j) :
    (blockIndexEquiv j a).val = d4TripledTrialityPerm a.1 :=
  rfl

/-- The coordinate equivalence induced by triality from one block to the next. -/
def blockModuleEquiv (R : Type u) [Semiring R] (j : Fin 3) :
    (Block j → R) ≃ₗ[R] (Block (nextBlock j) → R) :=
  LinearEquiv.piCongrLeft' R (fun _ => R) (blockIndexEquiv j)

/-- The block coordinate equivalence reindexes a function by inverse triality. -/
@[simp]
theorem blockModuleEquiv_apply (R : Type u) [Semiring R] (j : Fin 3) (v : Block j → R)
    (a : Block (nextBlock j)) :
    blockModuleEquiv R j v a = v ((blockIndexEquiv j).symm a) := by
  rw [blockModuleEquiv, LinearEquiv.piCongrLeft'_apply]

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

/-- Triality intertwines the positive generator matrices on consecutive blocks, entrywise. -/
theorem blockRaisingMatrix_triality (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (a b : Block j) :
    blockRaisingMatrix R (nextBlock j) (trialityPermD4 i)
        (blockIndexEquiv j a) (blockIndexEquiv j b) =
      blockRaisingMatrix R j i a b := by
  exact congrArg (Int.castRingHom R) (raisingMatrix_trialityPerm i a.1 b.1)

/-- Triality intertwines the negative generator matrices on consecutive blocks, entrywise. -/
theorem blockLoweringMatrix_triality (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (a b : Block j) :
    blockLoweringMatrix R (nextBlock j) (trialityPermD4 i)
        (blockIndexEquiv j a) (blockIndexEquiv j b) =
      blockLoweringMatrix R j i a b := by
  exact congrArg (Int.castRingHom R) (loweringMatrix_trialityPerm i a.1 b.1)

/-- Triality intertwines the Cartan-generator matrices on consecutive blocks, entrywise. -/
theorem blockCartanGeneratorMatrix_triality (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (a b : Block j) :
    blockCartanGeneratorMatrix R (nextBlock j) (trialityPermD4 i)
        (blockIndexEquiv j a) (blockIndexEquiv j b) =
      blockCartanGeneratorMatrix R j i a b := by
  exact congrArg (Int.castRingHom R) (cartanGeneratorMatrix_trialityPerm i a.1 b.1)

private theorem blockModuleEquiv_mulVec (R : Type u) [Semiring R] (j : Fin 3)
    (M : Matrix (Block j) (Block j) R)
    (N : Matrix (Block (nextBlock j)) (Block (nextBlock j)) R)
    (h : ∀ a b, N (blockIndexEquiv j a) (blockIndexEquiv j b) = M a b)
    (v : Block j → R) :
    blockModuleEquiv R j (M *ᵥ v) = N *ᵥ blockModuleEquiv R j v := by
  funext a
  rw [blockModuleEquiv_apply, Matrix.mulVec, Matrix.mulVec]
  simp only [dotProduct]
  rw [← (blockIndexEquiv j).sum_comp]
  simp only [blockModuleEquiv_apply]
  apply Finset.sum_congr rfl
  intro b _
  simpa using congrArg (fun z : R => z * v b)
    (h ((blockIndexEquiv j).symm a) b).symm

/-- The restricted triality equivalence intertwines every positive generator action with the
generator at the triality image of its node. -/
theorem blockModuleEquiv_raising_mulVec (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (v : Block j → R) :
    blockModuleEquiv R j (blockRaisingMatrix R j i *ᵥ v) =
      blockRaisingMatrix R (nextBlock j) (trialityPermD4 i) *ᵥ blockModuleEquiv R j v :=
  blockModuleEquiv_mulVec R j _ _ (blockRaisingMatrix_triality R j i) v

/-- The restricted triality equivalence intertwines every negative generator action with the
generator at the triality image of its node. -/
theorem blockModuleEquiv_lowering_mulVec (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (v : Block j → R) :
    blockModuleEquiv R j (blockLoweringMatrix R j i *ᵥ v) =
      blockLoweringMatrix R (nextBlock j) (trialityPermD4 i) *ᵥ blockModuleEquiv R j v :=
  blockModuleEquiv_mulVec R j _ _ (blockLoweringMatrix_triality R j i) v

/-- The restricted triality equivalence intertwines every Cartan-generator action with the
generator at the triality image of its node. -/
theorem blockModuleEquiv_cartanGenerator_mulVec (R : Type u) [Ring R]
    (j : Fin 3) (i : Fin 4) (v : Block j → R) :
    blockModuleEquiv R j (blockCartanGeneratorMatrix R j i *ᵥ v) =
      blockCartanGeneratorMatrix R (nextBlock j) (trialityPermD4 i) *ᵥ
        blockModuleEquiv R j v :=
  blockModuleEquiv_mulVec R j _ _ (blockCartanGeneratorMatrix_triality R j i) v

end TauCeti.D4Tripled
