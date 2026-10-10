/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Subgroup.GeneratorCover
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M22LowerBound
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Group.Subgroup.Finite
import all TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.Permutation

/-!
# The order of the M22 permutation image

A five-level Schreier cover with sizes `22, 21, 20, 16, 3` bounds the image of the
already checked M22 representation. The signed strong generators have sizes
`4, 6, 4, 6, 2`, and the terminal family is empty. All 396 generator/transversal
transitions are checked as exact permutation equalities, including inverse steps.
Only 1582 letters in the next-level generators are needed for their residual words.

The upper bound combines with `m22PermutationHom_range_natCard_ge` to give image
order 443520. This calculation makes no finiteness assertion about the presented
group and does not assume faithfulness of the representation.
-/

public section

namespace TauCeti.Sporadic.Mathieu

/-- Point images of the level-0 generators, followed by their inverses. -/
private def generatorImages0 : Vector (Vector (Fin 22) 22) 4 := #v[
  #v[10, 19, 2, 4, 18, 8, 15, 16, 6, 9, 21, 12, 0, 20, 1, 17, 3, 5, 7, 13, 14, 11],
  #v[1, 19, 7, 21, 15, 2, 5, 12, 6, 10, 20, 17, 3, 4, 9, 16, 14, 18, 8, 13, 0, 11],
  #v[12, 14, 2, 16, 3, 17, 8, 18, 5, 9, 0, 21, 11, 19, 20, 6, 7, 15, 4, 1, 13, 10],
  #v[20, 0, 5, 12, 13, 6, 8, 2, 18, 14, 9, 21, 7, 19, 16, 4, 15, 11, 17, 1, 10, 3]]

/-- Indices pairing each level-0 generator with its inverse. -/
private def inverseIndices0 : Vector (Fin 4) 4 :=
  #v[2, 3, 0, 1]

/-- Level-0 generators with kernel-checked left and right inverse tables. -/
private def generators0 (i : Fin 4) : Equiv.Perm (Fin 22) where
  toFun x := generatorImages0[i][x]
  invFun x := generatorImages0[inverseIndices0[i]][x]
  left_inv x := by
    have h : ∀ (j : Fin 4) (y : Fin 22),
        generatorImages0[inverseIndices0[j]][generatorImages0[j][y]] = y := by
      decide +kernel
    exact h i x
  right_inv x := by
    have h : ∀ (j : Fin 4) (y : Fin 22),
        generatorImages0[j][generatorImages0[inverseIndices0[j]][y]] = y := by
      decide +kernel
    exact h i x

/-- Point images of the level-0 representatives, identity first. -/
private def transversalImages0 : Vector (Vector (Fin 22) 22) 22 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
  #v[1, 19, 7, 21, 15, 2, 5, 12, 6, 10, 20, 17, 3, 4, 9, 16, 14, 18, 8, 13, 0, 11],
  #v[2, 15, 6, 4, 7, 21, 17, 11, 8, 16, 10, 12, 3, 0, 9, 18, 5, 13, 19, 20, 1, 14],
  #v[3, 9, 7, 14, 21, 18, 6, 8, 2, 10, 1, 11, 17, 13, 0, 5, 12, 16, 15, 19, 4, 20],
  #v[4, 9, 16, 1, 11, 7, 15, 6, 2, 21, 19, 12, 5, 20, 10, 8, 0, 3, 17, 13, 18, 14],
  #v[5, 10, 16, 0, 1, 3, 2, 17, 7, 21, 4, 14, 12, 13, 18, 15, 6, 8, 11, 9, 20, 19],
  #v[6, 0, 7, 8, 5, 12, 17, 3, 15, 10, 18, 1, 14, 9, 19, 2, 16, 11, 20, 4, 13, 21],
  #v[7, 16, 5, 15, 12, 11, 18, 17, 6, 14, 20, 3, 21, 1, 10, 8, 2, 4, 13, 0, 19, 9],
  #v[8, 12, 18, 5, 17, 11, 15, 16, 6, 0, 4, 14, 20, 9, 1, 2, 7, 21, 13, 3, 19, 10],
  #v[9, 1, 5, 13, 17, 18, 4, 15, 8, 14, 3, 7, 20, 10, 0, 11, 12, 6, 2, 19, 16, 21],
  #v[10, 19, 2, 4, 18, 8, 15, 16, 6, 9, 21, 12, 0, 20, 1, 17, 3, 5, 7, 13, 14, 11],
  #v[11, 20, 2, 7, 16, 15, 5, 4, 17, 9, 12, 10, 21, 1, 13, 8, 18, 6, 3, 14, 19, 0],
  #v[12, 14, 2, 16, 3, 17, 8, 18, 5, 9, 0, 21, 11, 19, 20, 6, 7, 15, 4, 1, 13, 10],
  #v[13, 12, 17, 11, 19, 8, 5, 2, 4, 20, 9, 10, 18, 1, 7, 3, 6, 21, 15, 14, 0, 16],
  #v[14, 10, 8, 0, 20, 15, 6, 2, 7, 1, 9, 11, 16, 13, 3, 18, 17, 12, 5, 19, 21, 4],
  #v[15, 10, 14, 19, 17, 12, 16, 5, 7, 11, 13, 3, 2, 0, 20, 6, 1, 21, 18, 4, 8, 9],
  #v[16, 3, 8, 17, 0, 12, 7, 5, 15, 1, 14, 4, 11, 19, 21, 6, 2, 18, 20, 10, 13, 9],
  #v[17, 0, 7, 12, 14, 16, 2, 15, 18, 10, 3, 20, 11, 19, 4, 6, 8, 5, 21, 9, 13, 1],
  #v[18, 7, 17, 6, 11, 21, 4, 15, 8, 20, 13, 16, 10, 14, 0, 5, 2, 3, 19, 12, 1, 9],
  #v[19, 13, 16, 11, 17, 2, 8, 0, 15, 21, 14, 5, 4, 18, 9, 3, 1, 7, 6, 20, 10, 12],
  #v[20, 0, 5, 12, 13, 6, 8, 2, 18, 14, 9, 21, 7, 19, 16, 4, 15, 11, 17, 1, 10, 3],
  #v[21, 13, 2, 18, 7, 6, 17, 3, 15, 9, 11, 0, 10, 14, 19, 5, 4, 8, 16, 20, 1, 12]]

/-- Level-0 representatives from their checked bijective point maps. -/
private noncomputable def transversals0 (i : Fin 22) : Equiv.Perm (Fin 22) :=
  Equiv.ofBijective (fun x ↦ transversalImages0[i][x]) (by
    have h : ∀ j : Fin 22, Function.Bijective (fun x : Fin 22 ↦ transversalImages0[j][x]) := by
      decide +kernel
    exact h i)

/-- Point images of the level-1 generators, followed by their inverses. -/
private def generatorImages1 : Vector (Vector (Fin 22) 22) 6 := #v[
  #v[0, 4, 12, 16, 6, 5, 14, 9, 2, 20, 17, 21, 19, 1, 13, 8, 11, 7, 3, 15, 10, 18],
  #v[0, 9, 15, 1, 6, 7, 16, 11, 2, 3, 13, 5, 12, 14, 10, 8, 4, 21, 18, 19, 17, 20],
  #v[0, 1, 21, 3, 2, 17, 5, 15, 11, 19, 7, 13, 9, 8, 20, 10, 14, 6, 18, 12, 16, 4],
  #v[0, 13, 8, 18, 1, 5, 4, 17, 15, 7, 20, 16, 2, 14, 6, 19, 3, 10, 21, 12, 9, 11],
  #v[0, 3, 8, 9, 16, 11, 4, 5, 15, 1, 14, 7, 12, 10, 13, 2, 6, 20, 18, 19, 21, 17],
  #v[0, 1, 4, 3, 21, 6, 17, 10, 13, 12, 15, 8, 19, 11, 16, 7, 20, 5, 18, 9, 14, 2]]

/-- Indices pairing each level-1 generator with its inverse. -/
private def inverseIndices1 : Vector (Fin 6) 6 :=
  #v[3, 4, 5, 0, 1, 2]

/-- Level-1 generators with kernel-checked left and right inverse tables. -/
private def generators1 (i : Fin 6) : Equiv.Perm (Fin 22) where
  toFun x := generatorImages1[i][x]
  invFun x := generatorImages1[inverseIndices1[i]][x]
  left_inv x := by
    have h : ∀ (j : Fin 6) (y : Fin 22),
        generatorImages1[inverseIndices1[j]][generatorImages1[j][y]] = y := by
      decide +kernel
    exact h i x
  right_inv x := by
    have h : ∀ (j : Fin 6) (y : Fin 22),
        generatorImages1[j][generatorImages1[inverseIndices1[j]][y]] = y := by
      decide +kernel
    exact h i x

/-- Point images of the level-1 representatives, identity first. -/
private def transversalImages1 : Vector (Vector (Fin 22) 22) 21 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
  #v[0, 2, 8, 12, 15, 10, 1, 5, 16, 4, 13, 7, 9, 11, 14, 3, 6, 18, 20, 17, 21, 19],
  #v[0, 3, 8, 9, 16, 11, 4, 5, 15, 1, 14, 7, 12, 10, 13, 2, 6, 20, 18, 19, 21, 17],
  #v[0, 4, 12, 16, 6, 5, 14, 9, 2, 20, 17, 21, 19, 1, 13, 8, 11, 7, 3, 15, 10, 18],
  #v[0, 5, 18, 9, 14, 8, 12, 15, 19, 13, 6, 10, 17, 16, 11, 20, 7, 4, 1, 21, 3, 2],
  #v[0, 6, 19, 11, 14, 5, 13, 20, 12, 10, 7, 18, 15, 4, 1, 2, 21, 9, 16, 8, 17, 3],
  #v[0, 7, 3, 15, 10, 6, 16, 12, 4, 11, 8, 13, 1, 9, 14, 2, 5, 17, 19, 21, 20, 18],
  #v[0, 8, 19, 2, 12, 14, 16, 13, 21, 3, 10, 7, 18, 5, 11, 17, 4, 1, 6, 20, 9, 15],
  #v[0, 9, 15, 1, 6, 7, 16, 11, 2, 3, 13, 5, 12, 14, 10, 8, 4, 21, 18, 19, 17, 20],
  #v[0, 10, 15, 18, 3, 11, 16, 20, 2, 5, 21, 6, 8, 13, 4, 19, 9, 14, 17, 12, 1, 7],
  #v[0, 11, 13, 18, 1, 6, 21, 5, 7, 10, 14, 20, 4, 16, 17, 9, 3, 15, 2, 19, 12, 8],
  #v[0, 12, 17, 1, 14, 20, 2, 11, 16, 19, 13, 4, 9, 6, 21, 8, 5, 10, 18, 3, 15, 7],
  #v[0, 13, 8, 18, 1, 5, 4, 17, 15, 7, 20, 16, 2, 14, 6, 19, 3, 10, 21, 12, 9, 11],
  #v[0, 14, 15, 21, 13, 5, 1, 10, 19, 17, 9, 3, 8, 6, 4, 12, 18, 20, 11, 2, 7, 16],
  #v[0, 15, 8, 19, 2, 9, 21, 11, 10, 16, 6, 18, 4, 7, 17, 14, 1, 5, 3, 20, 13, 12],
  #v[0, 16, 2, 20, 11, 21, 6, 5, 8, 4, 13, 9, 19, 17, 1, 12, 14, 10, 3, 15, 18, 7],
  #v[0, 17, 3, 9, 16, 13, 18, 11, 1, 20, 10, 14, 4, 7, 5, 21, 6, 15, 12, 2, 19, 8],
  #v[0, 18, 15, 7, 3, 16, 1, 5, 19, 13, 6, 17, 2, 20, 14, 8, 4, 9, 21, 12, 11, 10],
  #v[0, 19, 15, 12, 8, 7, 11, 16, 20, 3, 4, 21, 1, 17, 10, 6, 13, 5, 18, 9, 14, 2],
  #v[0, 20, 6, 15, 9, 14, 17, 7, 12, 19, 10, 5, 16, 13, 11, 18, 8, 2, 3, 4, 21, 1],
  #v[0, 21, 17, 18, 19, 11, 2, 7, 16, 4, 10, 14, 8, 13, 5, 3, 12, 6, 15, 9, 1, 20]]

/-- Level-1 representatives from their checked bijective point maps. -/
private noncomputable def transversals1 (i : Fin 21) : Equiv.Perm (Fin 22) :=
  Equiv.ofBijective (fun x ↦ transversalImages1[i][x]) (by
    have h : ∀ j : Fin 21, Function.Bijective (fun x : Fin 22 ↦ transversalImages1[j][x]) := by
      decide +kernel
    exact h i)

/-- Point images of the level-2 generators, followed by their inverses. -/
private def generatorImages2 : Vector (Vector (Fin 22) 22) 4 := #v[
  #v[0, 1, 21, 3, 2, 17, 5, 15, 11, 19, 7, 13, 9, 8, 20, 10, 14, 6, 18, 12, 16, 4],
  #v[0, 1, 17, 7, 14, 20, 3, 13, 5, 21, 9, 10, 11, 16, 18, 4, 6, 8, 19, 15, 2, 12],
  #v[0, 1, 4, 3, 21, 6, 17, 10, 13, 12, 15, 8, 19, 11, 16, 7, 20, 5, 18, 9, 14, 2],
  #v[0, 1, 20, 6, 15, 8, 16, 3, 17, 10, 11, 12, 21, 7, 4, 19, 13, 2, 14, 18, 5, 9]]

/-- Indices pairing each level-2 generator with its inverse. -/
private def inverseIndices2 : Vector (Fin 4) 4 :=
  #v[2, 3, 0, 1]

/-- Level-2 generators with kernel-checked left and right inverse tables. -/
private def generators2 (i : Fin 4) : Equiv.Perm (Fin 22) where
  toFun x := generatorImages2[i][x]
  invFun x := generatorImages2[inverseIndices2[i]][x]
  left_inv x := by
    have h : ∀ (j : Fin 4) (y : Fin 22),
        generatorImages2[inverseIndices2[j]][generatorImages2[j][y]] = y := by
      decide +kernel
    exact h i x
  right_inv x := by
    have h : ∀ (j : Fin 4) (y : Fin 22),
        generatorImages2[j][generatorImages2[inverseIndices2[j]][y]] = y := by
      decide +kernel
    exact h i x

/-- Point images of the level-2 representatives, identity first. -/
private def transversalImages2 : Vector (Vector (Fin 22) 22) 20 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
  #v[0, 1, 3, 21, 4, 17, 10, 6, 13, 16, 7, 11, 20, 18, 9, 5, 14, 15, 8, 12, 19, 2],
  #v[0, 1, 4, 3, 21, 6, 17, 10, 13, 12, 15, 8, 19, 11, 16, 7, 20, 5, 18, 9, 14, 2],
  #v[0, 1, 5, 19, 10, 14, 15, 21, 13, 9, 17, 8, 3, 11, 2, 20, 7, 4, 18, 12, 6, 16],
  #v[0, 1, 6, 15, 20, 13, 7, 19, 4, 17, 8, 3, 16, 21, 10, 12, 11, 5, 2, 18, 14, 9],
  #v[0, 1, 7, 12, 14, 9, 8, 16, 3, 13, 6, 2, 10, 21, 19, 18, 20, 5, 4, 15, 11, 17],
  #v[0, 1, 8, 13, 18, 10, 9, 21, 12, 20, 16, 7, 2, 17, 4, 15, 5, 3, 14, 19, 6, 11],
  #v[0, 1, 9, 6, 20, 3, 18, 10, 7, 8, 2, 12, 19, 14, 16, 13, 21, 5, 17, 4, 11, 15],
  #v[0, 1, 10, 5, 19, 17, 3, 8, 9, 2, 7, 20, 11, 15, 13, 21, 14, 18, 6, 12, 4, 16],
  #v[0, 1, 11, 8, 18, 21, 15, 14, 16, 9, 4, 19, 7, 5, 12, 20, 3, 17, 10, 2, 6, 13],
  #v[0, 1, 12, 17, 14, 16, 20, 11, 2, 6, 5, 21, 8, 3, 18, 15, 10, 13, 4, 19, 9, 7],
  #v[0, 1, 13, 11, 18, 9, 17, 3, 16, 7, 6, 5, 21, 10, 4, 14, 20, 2, 19, 15, 12, 8],
  #v[0, 1, 14, 12, 17, 2, 20, 16, 11, 9, 4, 13, 19, 8, 5, 6, 21, 10, 18, 3, 15, 7],
  #v[0, 1, 15, 6, 9, 4, 10, 14, 8, 5, 3, 13, 12, 18, 17, 19, 21, 7, 11, 2, 16, 20],
  #v[0, 1, 16, 19, 5, 4, 14, 20, 8, 12, 21, 11, 9, 13, 6, 17, 2, 15, 18, 3, 7, 10],
  #v[0, 1, 17, 7, 14, 20, 3, 13, 5, 21, 9, 10, 11, 16, 18, 4, 6, 8, 19, 15, 2, 12],
  #v[0, 1, 18, 11, 8, 17, 2, 6, 10, 21, 14, 16, 15, 5, 20, 3, 12, 9, 19, 7, 4, 13],
  #v[0, 1, 19, 16, 10, 13, 20, 12, 3, 9, 18, 2, 14, 21, 7, 6, 8, 17, 4, 11, 15, 5],
  #v[0, 1, 20, 6, 15, 8, 16, 3, 17, 10, 11, 12, 21, 7, 4, 19, 13, 2, 14, 18, 5, 9],
  #v[0, 1, 21, 3, 2, 17, 5, 15, 11, 19, 7, 13, 9, 8, 20, 10, 14, 6, 18, 12, 16, 4]]

/-- Level-2 representatives from their checked bijective point maps. -/
private noncomputable def transversals2 (i : Fin 20) : Equiv.Perm (Fin 22) :=
  Equiv.ofBijective (fun x ↦ transversalImages2[i][x]) (by
    have h : ∀ j : Fin 20, Function.Bijective (fun x : Fin 22 ↦ transversalImages2[j][x]) := by
      decide +kernel
    exact h i)

/-- Point images of the level-3 generators, followed by their inverses. -/
private def generatorImages3 : Vector (Vector (Fin 22) 22) 6 := #v[
  #v[0, 1, 2, 3, 4, 9, 10, 11, 12, 5, 6, 7, 8, 17, 18, 19, 20, 13, 14, 15, 16, 21],
  #v[0, 1, 2, 21, 3, 8, 10, 14, 20, 19, 13, 9, 7, 6, 12, 16, 18, 17, 15, 11, 5, 4],
  #v[0, 1, 2, 21, 3, 11, 5, 17, 15, 16, 18, 6, 12, 9, 7, 19, 13, 14, 20, 8, 10, 4],
  #v[0, 1, 2, 3, 4, 9, 10, 11, 12, 5, 6, 7, 8, 17, 18, 19, 20, 13, 14, 15, 16, 21],
  #v[0, 1, 2, 4, 21, 20, 13, 12, 5, 11, 6, 19, 14, 10, 7, 18, 15, 17, 16, 9, 8, 3],
  #v[0, 1, 2, 4, 21, 6, 11, 14, 19, 13, 20, 5, 12, 16, 17, 8, 9, 7, 10, 15, 18, 3]]

/-- Indices pairing each level-3 generator with its inverse. -/
private def inverseIndices3 : Vector (Fin 6) 6 :=
  #v[3, 4, 5, 0, 1, 2]

/-- Level-3 generators with kernel-checked left and right inverse tables. -/
private def generators3 (i : Fin 6) : Equiv.Perm (Fin 22) where
  toFun x := generatorImages3[i][x]
  invFun x := generatorImages3[inverseIndices3[i]][x]
  left_inv x := by
    have h : ∀ (j : Fin 6) (y : Fin 22),
        generatorImages3[inverseIndices3[j]][generatorImages3[j][y]] = y := by
      decide +kernel
    exact h i x
  right_inv x := by
    have h : ∀ (j : Fin 6) (y : Fin 22),
        generatorImages3[j][generatorImages3[inverseIndices3[j]][y]] = y := by
      decide +kernel
    exact h i x

/-- Point images of the level-3 representatives, identity first. -/
private def transversalImages3 : Vector (Vector (Fin 22) 22) 16 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
  #v[0, 1, 2, 4, 21, 6, 11, 14, 19, 13, 20, 5, 12, 16, 17, 8, 9, 7, 10, 15, 18, 3],
  #v[0, 1, 2, 21, 3, 7, 9, 13, 19, 20, 14, 10, 8, 5, 11, 15, 17, 18, 16, 12, 6, 4],
  #v[0, 1, 2, 21, 3, 8, 10, 14, 20, 19, 13, 9, 7, 6, 12, 16, 18, 17, 15, 11, 5, 4],
  #v[0, 1, 2, 3, 4, 9, 10, 11, 12, 5, 6, 7, 8, 17, 18, 19, 20, 13, 14, 15, 16, 21],
  #v[0, 1, 2, 3, 4, 10, 9, 12, 11, 6, 5, 8, 7, 18, 17, 20, 19, 14, 13, 16, 15, 21],
  #v[0, 1, 2, 21, 3, 11, 5, 17, 15, 16, 18, 6, 12, 9, 7, 19, 13, 14, 20, 8, 10, 4],
  #v[0, 1, 2, 4, 21, 12, 5, 20, 13, 19, 14, 11, 6, 18, 15, 10, 7, 9, 8, 17, 16, 3],
  #v[0, 1, 2, 3, 4, 13, 14, 15, 16, 17, 18, 19, 20, 5, 6, 7, 8, 9, 10, 11, 12, 21],
  #v[0, 1, 2, 3, 4, 14, 13, 16, 15, 18, 17, 20, 19, 6, 5, 8, 7, 10, 9, 12, 11, 21],
  #v[0, 1, 2, 21, 3, 15, 17, 5, 11, 12, 6, 18, 16, 13, 19, 7, 9, 10, 8, 20, 14, 4],
  #v[0, 1, 2, 4, 21, 16, 17, 8, 9, 7, 10, 15, 18, 6, 11, 14, 19, 13, 20, 5, 12, 3],
  #v[0, 1, 2, 21, 3, 17, 15, 11, 5, 6, 12, 16, 18, 19, 13, 9, 7, 8, 10, 14, 20, 4],
  #v[0, 1, 2, 21, 3, 18, 16, 12, 6, 5, 11, 15, 17, 20, 14, 10, 8, 7, 9, 13, 19, 4],
  #v[0, 1, 2, 21, 3, 19, 13, 9, 7, 8, 10, 14, 20, 17, 15, 11, 5, 6, 12, 16, 18, 4],
  #v[0, 1, 2, 4, 21, 20, 13, 12, 5, 11, 6, 19, 14, 10, 7, 18, 15, 17, 16, 9, 8, 3]]

/-- Level-3 representatives from their checked bijective point maps. -/
private noncomputable def transversals3 (i : Fin 16) : Equiv.Perm (Fin 22) :=
  Equiv.ofBijective (fun x ↦ transversalImages3[i][x]) (by
    have h : ∀ j : Fin 16, Function.Bijective (fun x : Fin 22 ↦ transversalImages3[j][x]) := by
      decide +kernel
    exact h i)

/-- Point images of the level-4 generators, followed by their inverses. -/
private def generatorImages4 : Vector (Vector (Fin 22) 22) 2 := #v[
  #v[0, 1, 2, 21, 3, 5, 11, 15, 17, 18, 16, 12, 6, 7, 9, 13, 19, 20, 14, 10, 8, 4],
  #v[0, 1, 2, 4, 21, 5, 12, 13, 20, 14, 19, 6, 11, 15, 18, 7, 10, 8, 9, 16, 17, 3]]

/-- Indices pairing each level-4 generator with its inverse. -/
private def inverseIndices4 : Vector (Fin 2) 2 :=
  #v[1, 0]

/-- Level-4 generators with kernel-checked left and right inverse tables. -/
private def generators4 (i : Fin 2) : Equiv.Perm (Fin 22) where
  toFun x := generatorImages4[i][x]
  invFun x := generatorImages4[inverseIndices4[i]][x]
  left_inv x := by
    have h : ∀ (j : Fin 2) (y : Fin 22),
        generatorImages4[inverseIndices4[j]][generatorImages4[j][y]] = y := by
      decide +kernel
    exact h i x
  right_inv x := by
    have h : ∀ (j : Fin 2) (y : Fin 22),
        generatorImages4[j][generatorImages4[inverseIndices4[j]][y]] = y := by
      decide +kernel
    exact h i x

/-- Point images of the level-4 representatives, identity first. -/
private def transversalImages4 : Vector (Vector (Fin 22) 22) 3 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
  #v[0, 1, 2, 4, 21, 5, 12, 13, 20, 14, 19, 6, 11, 15, 18, 7, 10, 8, 9, 16, 17, 3],
  #v[0, 1, 2, 21, 3, 5, 11, 15, 17, 18, 16, 12, 6, 7, 9, 13, 19, 20, 14, 10, 8, 4]]

/-- Level-4 representatives from their checked bijective point maps. -/
private noncomputable def transversals4 (i : Fin 3) : Equiv.Perm (Fin 22) :=
  Equiv.ofBijective (fun x ↦ transversalImages4[i][x]) (by
    have h : ∀ j : Fin 3, Function.Bijective (fun x : Fin 22 ↦ transversalImages4[j][x]) := by
      decide +kernel
    exact h i)

/-- The terminal generator family is empty. -/
private def generators5 (i : Fin 0) : Equiv.Perm (Fin 22) := Fin.elim0 i

/-- Targets and residual words for every signed level-0 Schreier pair. -/
private def transitions0 : Vector (Vector (Fin 22 × List (Fin 6)) 22) 4 := #v[
  #v[
    (10, []),
    (19, []),
    (2, [0, 0, 1, 5, 4, 3, 5, 1, 2, 3, 1, 0, 5, 3, 4, 5]),
    (4, []),
    (18, [5, 0, 5, 3, 1, 0, 0, 1, 3, 4, 2, 1, 0, 2, 3, 4, 5]),
    (8, [5, 1, 0]),
    (15, [5, 1, 2, 4, 2, 3, 5, 1, 2, 3]),
    (16, []),
    (6, []),
    (9, [2, 1, 1, 2, 4, 5]),
    (21, []),
    (12, []),
    (0, []),
    (20, []),
    (1, [4]),
    (17, [3, 4, 3, 3, 1, 0, 5, 5, 4, 3, 2, 3, 3]),
    (3, [0, 1, 5, 1, 5, 4]),
    (5, []),
    (7, []),
    (13, [1]),
    (14, []),
    (11, [])],
  #v[
    (1, []),
    (19, [2]),
    (7, []),
    (21, [5, 1, 5, 1, 5, 4]),
    (15, []),
    (2, [2, 1, 3, 3, 1, 0, 1, 0, 0, 5, 0, 2, 1, 0, 5, 3, 4, 5]),
    (5, [0]),
    (12, []),
    (6, [3, 1, 5, 1, 2, 4, 2, 3, 5, 1, 2, 3]),
    (10, []),
    (20, [0]),
    (17, []),
    (3, []),
    (4, [5, 1, 5, 1, 2, 3]),
    (9, [5, 1, 5]),
    (16, [3, 4, 3, 3, 1, 0, 5, 5, 4, 3, 2, 3, 3]),
    (14, [0, 1, 5, 1, 5, 4]),
    (18, [0, 1, 3, 4, 0, 5, 1, 2, 3, 1, 0, 2, 3, 4, 5]),
    (8, []),
    (13, [2, 3, 2, 1, 5, 4, 2, 1, 0, 0, 5, 0, 2]),
    (0, []),
    (11, [3, 1, 5, 1, 2, 4, 2, 3, 5, 1, 2, 3])],
  #v[
    (12, []),
    (14, [1]),
    (2, [2, 0, 1, 5, 4, 0, 5, 4, 2, 0, 1, 0, 5, 3, 4, 5]),
    (16, [5, 0, 5, 3, 1, 0, 0, 1, 3, 4, 2, 1, 0, 2, 3, 4, 5]),
    (3, []),
    (17, []),
    (8, []),
    (18, []),
    (5, [3, 4, 2]),
    (9, [1, 5, 1, 5, 4]),
    (0, []),
    (21, []),
    (11, []),
    (19, [4]),
    (20, []),
    (6, [3, 3, 1, 0, 0, 5, 4, 2, 0]),
    (7, []),
    (15, [4, 3, 1, 5, 3, 1, 0, 4, 2, 1, 0, 5, 3, 4, 5]),
    (4, [0, 1, 5, 1, 5, 4]),
    (1, []),
    (13, []),
    (10, [])],
  #v[
    (20, []),
    (0, []),
    (5, [4, 3, 3, 3, 1, 0, 5]),
    (12, []),
    (13, [2, 1, 3, 3, 1, 0, 5, 3, 2, 3, 3, 4, 2, 1, 0, 2, 3, 4, 5]),
    (6, [3]),
    (8, [5, 1, 1, 5, 4, 2, 3, 5, 1, 2, 3]),
    (2, []),
    (18, []),
    (14, [4, 5, 1, 5, 4]),
    (9, []),
    (21, [5, 1, 1, 5, 4, 2, 3, 5, 1, 2, 3]),
    (7, []),
    (19, [5, 0, 0, 2, 3, 4, 0, 5, 0, 2, 3]),
    (16, [5, 0, 5, 3, 1, 0, 0, 1, 3, 4, 2, 1, 0, 2, 3, 4, 5]),
    (4, []),
    (15, [4, 3, 1, 5, 3, 1, 0, 4, 2, 1, 0, 5, 3, 4, 5]),
    (11, []),
    (17, [1, 0, 0, 5, 1, 5, 4, 3, 2, 1, 0, 5, 3, 4, 5]),
    (1, [5]),
    (10, [3]),
    (3, [2, 1, 1, 2, 4])]]

/-- Every level-0 Schreier correction is the recorded next-generator product. -/
private theorem transitions0_valid (s : Fin 4) (t : Fin 22) :
    generators0 s * transversals0 t =
      transversals0 (transitions0[s][t]).1 *
        ((transitions0[s][t]).2.map generators1).prod := by
  have h : ∀ (i : Fin 4) (j : Fin 22) (x : Fin 22),
      (generators0 i * transversals0 j) x =
        (transversals0 (transitions0[i][j]).1 *
          ((transitions0[i][j]).2.map generators1).prod) x := by
    decide +kernel
  exact Equiv.ext (h s t)

/-- Targets and residual words for every signed level-1 Schreier pair. -/
private def transitions1 : Vector (Vector (Fin 21 × List (Fin 4)) 21) 6 := #v[
  #v[
    (3, []),
    (11, [0, 1, 0, 3, 2, 3]),
    (15, []),
    (5, []),
    (4, [0, 1, 2, 3, 0, 3, 3, 2, 3, 0, 3, 3, 2]),
    (13, []),
    (8, [0, 1, 1, 0, 1, 2, 3, 0, 3, 3, 0, 1, 1, 2, 1, 0]),
    (1, [2, 1, 0, 1, 2, 2, 3, 0, 3, 3, 2]),
    (19, [0, 0, 1, 2, 3, 0, 3, 3]),
    (16, [0, 1, 0, 1, 2]),
    (20, [2, 3, 0, 1, 2, 3, 0, 3, 3, 2]),
    (18, [2, 1]),
    (0, []),
    (12, []),
    (7, [1, 0, 0, 3, 3, 0, 3, 2, 3, 2, 3, 0, 3, 3, 2]),
    (10, [0, 1, 1, 1, 2, 1, 0]),
    (6, [0, 1, 0, 1, 2, 3, 3, 3, 0, 3, 3, 2]),
    (2, []),
    (14, []),
    (9, [1, 1, 0, 1, 1, 1, 2, 1, 0]),
    (17, [1, 0, 3, 2, 1, 1, 0, 0, 1, 1, 2, 1, 0])],
  #v[
    (8, []),
    (14, [2, 3, 0, 3, 3]),
    (0, []),
    (5, [1, 1, 1, 0, 1, 2, 3, 0, 3, 3, 0, 1, 1, 2, 1, 0]),
    (6, [0, 1, 0, 1, 2]),
    (15, [1, 0, 1, 0, 1, 2, 3, 0, 3, 3, 0, 1, 1, 2, 1, 0]),
    (10, [2, 1, 0, 3, 2, 1, 2, 3]),
    (1, [0, 1, 2, 1, 2, 1, 1, 0, 1, 1, 2, 1, 0]),
    (2, []),
    (12, []),
    (4, [2, 1, 0, 3, 2, 1, 2, 3, 0, 1, 1, 2, 1, 0]),
    (11, [1, 2, 3, 0, 3, 3]),
    (13, [3, 3, 2, 1, 2, 1, 2, 1, 1, 2, 3, 0, 3, 3, 2]),
    (9, [1, 0, 1, 0, 1, 2, 3, 0, 3, 3, 0, 1, 1, 2, 1, 0]),
    (7, [1, 0, 1, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2]),
    (3, [3, 3, 2, 2, 1, 1, 0, 3, 2]),
    (20, [2, 3, 0, 1, 2, 3, 0, 3, 3, 2]),
    (17, [3, 2, 2, 3, 0, 3, 3, 2]),
    (18, [2]),
    (16, [2, 1, 0, 1, 2]),
    (19, [2, 3, 0, 1, 2, 3, 0, 3, 3, 2])],
  #v[
    (0, [0]),
    (20, [3, 3, 3, 0, 3, 3]),
    (2, [2, 1, 2, 3, 0, 3, 3, 2]),
    (1, [1, 0, 0, 1, 2, 3, 3, 0]),
    (16, [0, 3, 0, 3, 0, 3, 2, 3, 0, 3, 3, 2]),
    (4, [0, 1, 0, 1, 2, 3, 3, 0]),
    (14, [1, 1, 2, 3, 0, 3, 3, 0, 1, 1, 2, 1, 0]),
    (10, [2, 3, 0, 1, 0, 1, 1, 2, 1, 0]),
    (18, [1, 2, 3, 0, 3, 3]),
    (6, [2, 3, 3, 2, 1, 0, 3, 3, 2]),
    (12, []),
    (8, [2]),
    (7, [2, 3, 2, 1, 1, 0, 1, 2, 1, 0]),
    (19, [3, 3, 0, 1, 2, 3, 0, 1]),
    (9, [3, 3, 3, 0, 3, 3, 0, 3, 2, 3, 0, 1, 1, 2, 1, 0]),
    (13, [1, 0, 1, 2, 1, 1, 0, 1, 2, 1, 0]),
    (5, [1, 1, 0, 3, 2]),
    (17, [0, 3, 0, 3, 3]),
    (11, [1, 2, 3, 0, 3, 3, 2]),
    (15, [2, 3, 3, 2, 3, 0, 1, 1, 2, 1, 0]),
    (3, [1, 0, 3, 3, 0, 3, 0, 1, 1, 2, 1, 0])],
  #v[
    (12, []),
    (7, [1, 1, 0, 3, 2, 2, 3, 0, 3, 3, 2]),
    (17, []),
    (0, []),
    (4, [3, 3, 2, 3, 0, 3, 3, 0, 3, 2, 3]),
    (3, []),
    (16, [0, 1, 0, 1, 2, 3, 3, 3, 0, 3, 3, 2]),
    (14, [0, 0, 3, 2, 3, 2, 3, 0, 3, 3, 2]),
    (6, [1, 1, 2, 3, 0, 3, 3]),
    (19, [3, 0, 1, 0, 3, 2, 1, 2, 3]),
    (15, [0, 3, 3, 3, 0, 3, 0, 3, 0, 1, 1, 2, 1, 0]),
    (1, [3, 2, 3, 0, 1]),
    (13, []),
    (5, []),
    (18, []),
    (2, []),
    (9, [1, 0, 1, 0, 3, 2, 3]),
    (20, [2, 1, 2, 3, 0, 1]),
    (11, [3, 0]),
    (8, [0, 0, 1, 2, 3, 0, 3, 3]),
    (10, [3, 0, 0, 1, 0, 3, 3, 0, 3])],
  #v[
    (2, []),
    (7, [0, 1, 2, 1, 2, 1, 1, 0, 1, 1, 2, 1, 0]),
    (8, []),
    (15, [0, 3, 3, 0, 3]),
    (10, [1, 0, 1, 0, 3, 2, 3, 0, 1, 1, 2, 1, 0]),
    (3, [1, 0, 3, 3, 0, 3, 0, 3, 2, 3, 0, 3, 3, 2]),
    (4, [1, 0, 1, 0, 3, 2, 3]),
    (14, [1, 0, 0, 3, 3]),
    (0, []),
    (13, [3, 3, 2, 1, 2, 1, 2, 1, 1, 2, 3, 0, 3, 3, 2]),
    (6, [2, 3, 3, 0, 3, 0, 3, 2, 3, 0, 3, 3, 2]),
    (11, [2, 1, 2, 3, 0, 3, 3, 2]),
    (9, []),
    (12, [1, 0, 1, 0, 1, 2, 3, 0, 3, 3, 0, 1, 1, 2, 1, 0]),
    (1, [1, 1, 2, 1, 0]),
    (5, [3, 3, 2, 1, 2, 1, 2, 1, 1, 2, 3, 0, 3, 3, 2]),
    (19, [2, 1, 0, 1, 2]),
    (17, [1, 0, 1, 0, 3, 2, 1, 2, 3, 2, 3, 0, 3, 3, 2]),
    (18, [0]),
    (20, [3, 0, 0, 1, 0, 3, 3, 0, 3]),
    (16, [3, 0, 0, 1, 0, 3, 3, 0, 3])],
  #v[
    (0, [2]),
    (3, [2, 3, 3, 3, 0, 3, 0, 3]),
    (2, [1, 2, 3, 0, 3, 3]),
    (20, [2, 1, 2, 1, 2, 1, 1]),
    (5, [0, 1, 1, 0, 1, 0, 3, 3, 0, 3]),
    (16, [1, 0, 1, 1, 0, 1, 2, 3, 0, 3, 3]),
    (9, [1, 2, 3, 3, 3, 0, 3, 3, 2]),
    (12, [2, 3, 0, 1, 0, 1, 1, 2, 1, 0]),
    (11, [0]),
    (14, [3, 0, 3, 0, 1, 0, 3, 3, 0, 3, 0, 1, 1, 2, 1, 0]),
    (7, [2, 3, 2, 1, 1, 0, 1, 2, 1, 0]),
    (18, [1, 2, 3, 0, 3, 3, 2]),
    (10, []),
    (15, [0, 1, 0, 3, 0, 1, 2, 3, 2, 3, 0, 3, 3, 2]),
    (6, [0, 1, 1, 1, 0, 1, 2, 3, 0, 3, 3]),
    (19, [3, 3, 2, 1, 0, 3, 0, 1, 2, 3]),
    (4, [3, 0, 1, 2, 3, 3, 0, 0, 1, 1, 2, 1, 0]),
    (17, [1, 0, 3, 0, 3, 0, 3]),
    (8, [2, 1, 2, 3, 0, 3, 3, 2]),
    (13, [3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2]),
    (1, [2, 3, 2, 2, 1, 1, 0, 3, 2, 2, 3, 0, 3, 3, 2])]]

/-- Every level-1 Schreier correction is the recorded next-generator product. -/
private theorem transitions1_valid (s : Fin 6) (t : Fin 21) :
    generators1 s * transversals1 t =
      transversals1 (transitions1[s][t]).1 *
        ((transitions1[s][t]).2.map generators2).prod := by
  have h : ∀ (i : Fin 6) (j : Fin 21) (x : Fin 22),
      (generators1 i * transversals1 j) x =
        (transversals1 (transitions1[i][j]).1 *
          ((transitions1[i][j]).2.map generators2).prod) x := by
    decide +kernel
  exact Equiv.ext (h s t)

/-- Targets and residual words for every signed level-2 Schreier pair. -/
private def transitions2 : Vector (Vector (Fin 20 × List (Fin 6)) 20) 4 := #v[
  #v[
    (19, []),
    (1, [3, 4, 3]),
    (0, []),
    (15, [5, 4, 3]),
    (3, [4, 3]),
    (13, [2, 1]),
    (9, [3, 1, 0, 1, 2]),
    (17, [1]),
    (5, [3, 5, 0, 1, 2]),
    (11, [5, 3, 2]),
    (7, [5, 3, 5, 4, 3]),
    (6, [5, 1]),
    (18, [3, 1]),
    (8, [3]),
    (12, []),
    (4, [3, 1, 0, 1, 2]),
    (16, [3, 2]),
    (10, [3, 1, 5, 4, 3]),
    (14, [4, 3]),
    (2, [])],
  #v[
    (15, []),
    (5, [5, 5, 4, 3]),
    (12, [5, 1, 5, 4, 3]),
    (18, [5, 1, 0, 1, 2]),
    (1, [1, 2]),
    (11, [3, 1, 0, 1, 2]),
    (3, [3, 5, 4, 3]),
    (19, [3, 5, 5, 4, 3]),
    (7, [1, 2]),
    (8, [5, 1]),
    (9, [4, 5, 4, 3]),
    (14, [3, 5, 0, 1, 2]),
    (16, []),
    (2, [4, 5, 4, 3]),
    (4, [4, 5, 4, 3]),
    (6, [3, 1, 0, 1, 2]),
    (17, [3, 4]),
    (13, [4, 5, 4, 3]),
    (0, []),
    (10, [3, 1])],
  #v[
    (2, []),
    (1, [2, 1, 0, 1, 2]),
    (19, []),
    (4, [3, 1]),
    (15, [3, 1, 0, 1, 2]),
    (8, [5, 1, 0, 1, 2]),
    (11, [5, 1]),
    (10, [5, 3, 5, 4, 3]),
    (13, [3]),
    (6, [3, 1, 0, 1, 2]),
    (17, [5, 0, 1, 2]),
    (9, [5, 3, 2]),
    (14, []),
    (5, [5, 1, 2]),
    (18, [3, 1]),
    (3, [0, 1, 2]),
    (16, [5, 3]),
    (7, [4]),
    (12, [4, 3]),
    (0, [])],
  #v[
    (18, []),
    (4, [5, 4]),
    (13, [4, 5, 4, 3]),
    (6, [5, 3, 2, 0, 1, 2]),
    (14, [4, 5, 4, 3]),
    (1, [5, 5, 4, 3]),
    (15, [3, 1, 0, 1, 2]),
    (8, [5, 4]),
    (9, [5, 1]),
    (10, [4, 5, 4, 3]),
    (19, [4, 3]),
    (5, [3, 1, 0, 1, 2]),
    (2, [3, 4]),
    (17, [4, 5, 4, 3]),
    (11, [5, 1, 0, 1, 2]),
    (0, []),
    (12, []),
    (16, [5, 1, 5, 4, 3]),
    (3, [3, 5, 0, 1, 2]),
    (7, [3, 5, 5, 4, 3])]]

/-- Every level-2 Schreier correction is the recorded next-generator product. -/
private theorem transitions2_valid (s : Fin 4) (t : Fin 20) :
    generators2 s * transversals2 t =
      transversals2 (transitions2[s][t]).1 *
        ((transitions2[s][t]).2.map generators3).prod := by
  have h : ∀ (i : Fin 4) (j : Fin 20) (x : Fin 22),
      (generators2 i * transversals2 j) x =
        (transversals2 (transitions2[i][j]).1 *
          ((transitions2[i][j]).2.map generators3).prod) x := by
    decide +kernel
  exact Equiv.ext (h s t)

/-- Targets and residual words for every signed level-3 Schreier pair. -/
private def transitions3 : Vector (Vector (Fin 16 × List (Fin 2)) 16) 6 := #v[
  #v[
    (4, []),
    (5, [1]),
    (6, []),
    (7, [1]),
    (0, []),
    (1, [0]),
    (2, []),
    (3, [0]),
    (12, [1]),
    (13, [1]),
    (14, []),
    (15, []),
    (8, [0]),
    (9, [0]),
    (10, []),
    (11, [])],
  #v[
    (3, []),
    (5, []),
    (9, [1]),
    (15, []),
    (14, []),
    (8, [0]),
    (4, [1]),
    (2, [1]),
    (1, [1]),
    (7, [1]),
    (11, []),
    (13, [1]),
    (12, [0]),
    (10, [0]),
    (6, [0]),
    (0, [])],
  #v[
    (6, []),
    (0, []),
    (12, [0]),
    (10, [0]),
    (11, [1]),
    (13, []),
    (1, []),
    (7, [0]),
    (4, [0]),
    (2, []),
    (14, [0]),
    (8, []),
    (9, [1]),
    (15, []),
    (3, [0]),
    (5, [])],
  #v[
    (4, []),
    (5, [1]),
    (6, []),
    (7, [1]),
    (0, []),
    (1, [0]),
    (2, []),
    (3, [0]),
    (12, [1]),
    (13, [1]),
    (14, []),
    (15, []),
    (8, [0]),
    (9, [0]),
    (10, []),
    (11, [])],
  #v[
    (15, []),
    (8, [0]),
    (7, [0]),
    (0, []),
    (6, [0]),
    (1, []),
    (14, [1]),
    (9, [0]),
    (5, [1]),
    (2, [0]),
    (13, [1]),
    (10, []),
    (12, [1]),
    (11, [0]),
    (4, []),
    (3, [])],
  #v[
    (1, []),
    (6, []),
    (9, []),
    (14, [1]),
    (8, [1]),
    (15, []),
    (0, []),
    (7, [1]),
    (11, []),
    (12, [0]),
    (3, [1]),
    (4, [0]),
    (2, [1]),
    (5, []),
    (10, [1]),
    (13, [])]]

/-- Every level-3 Schreier correction is the recorded next-generator product. -/
private theorem transitions3_valid (s : Fin 6) (t : Fin 16) :
    generators3 s * transversals3 t =
      transversals3 (transitions3[s][t]).1 *
        ((transitions3[s][t]).2.map generators4).prod := by
  have h : ∀ (i : Fin 6) (j : Fin 16) (x : Fin 22),
      (generators3 i * transversals3 j) x =
        (transversals3 (transitions3[i][j]).1 *
          ((transitions3[i][j]).2.map generators4).prod) x := by
    decide +kernel
  exact Equiv.ext (h s t)

/-- Targets and residual words for every signed level-4 Schreier pair. -/
private def transitions4 : Vector (Vector (Fin 3 × List (Fin 0)) 3) 2 := #v[
  #v[
    (2, []),
    (0, []),
    (1, [])],
  #v[
    (1, []),
    (2, []),
    (0, [])]]

/-- Every level-4 Schreier correction is the recorded next-generator product. -/
private theorem transitions4_valid (s : Fin 2) (t : Fin 3) :
    generators4 s * transversals4 t =
      transversals4 (transitions4[s][t]).1 *
        ((transitions4[s][t]).2.map generators5).prod := by
  have h : ∀ (i : Fin 2) (j : Fin 3) (x : Fin 22),
      (generators4 i * transversals4 j) x =
        (transversals4 (transitions4[i][j]).1 *
          ((transitions4[i][j]).2.map generators5).prod) x := by
    decide +kernel
  exact Equiv.ext (h s t)

/-- The checked homomorphism image is generated by its two original images. -/
private theorem range_eq_closure :
    m22PermutationHom.range = Subgroup.closure (Set.range m22GeneratorImages) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    apply PresentedGroup.generated_by m22Presentation.relatorSet
      ((Subgroup.closure (Set.range m22GeneratorImages)).comap m22PermutationHom)
    intro j
    change m22PermutationHom (PresentedGroup.of j) ∈
      Subgroup.closure (Set.range m22GeneratorImages)
    rw [m22PermutationHom_of]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨PresentedGroup.of j, m22PermutationHom_of j⟩

/-- Numbers of signed strong generators, including the empty terminal family. -/
private def generatorSize (i : Fin 6) : ℕ := (#v[4, 6, 4, 6, 2, 0])[i]

/-- Numbers of representatives in the five successive covers. -/
private def transversalSize (i : Fin 5) : ℕ := (#v[22, 21, 20, 16, 3])[i]

/-- The concrete strong-generator family at each of the six levels. -/
private def strongGenerators : (level : Fin 6) → Fin (generatorSize level) → Equiv.Perm (Fin 22)
  | 0 => fun i ↦ generators0 i
  | 1 => fun i ↦ generators1 i
  | 2 => fun i ↦ generators2 i
  | 3 => fun i ↦ generators3 i
  | 4 => fun i ↦ generators4 i
  | 5 => fun i ↦ generators5 i

/-- The concrete representatives at each nonterminal level. -/
private noncomputable def representatives : (level : Fin 5) →
    Fin (transversalSize level) → Equiv.Perm (Fin 22)
  | 0 => fun i ↦ transversals0 i
  | 1 => fun i ↦ transversals1 i
  | 2 => fun i ↦ transversals2 i
  | 3 => fun i ↦ transversals3 i
  | 4 => fun i ↦ transversals4 i

/-- The recorded target representative and next-level residual word for each step. -/
private def transitions : (level : Fin 5) → Fin (generatorSize level.castSucc) →
    Fin (transversalSize level) →
      Fin (transversalSize level) × List (Fin (generatorSize level.succ))
  | 0 => fun i j ↦ transitions0[i][j]
  | 1 => fun i j ↦ transitions1[i][j]
  | 2 => fun i j ↦ transitions2[i][j]
  | 3 => fun i j ↦ transitions3[i][j]
  | 4 => fun i j ↦ transitions4[i][j]

/-- The subgroup generated by a level of the checked certificate. -/
private def levelSubgroup (level : Fin 6) : Subgroup (Equiv.Perm (Fin 22)) :=
  Subgroup.closure (Set.range (strongGenerators level))

/-- Every recorded transition gives the required next-level correction. -/
private theorem transitions_valid (level : Fin 5)
    (s : Fin (generatorSize level.castSucc)) (t : Fin (transversalSize level)) :
    strongGenerators level.castSucc s * representatives level t =
      representatives level (transitions level s t).1 *
        ((transitions level s t).2.map (strongGenerators level.succ)).prod := by
  fin_cases level
  · exact transitions0_valid s t
  · exact transitions1_valid s t
  · exact transitions2_valid s t
  · exact transitions3_valid s t
  · exact transitions4_valid s t

/-- The signed generator family contains an inverse for each of its members. -/
private theorem inverse_generator (level : Fin 5)
    (i : Fin (generatorSize level.castSucc)) :
    ∃ j, strongGenerators level.castSucc j = (strongGenerators level.castSucc i)⁻¹ := by
  have h : ∀ (k : Fin 5) (a : Fin (generatorSize k.castSucc)),
      ∃ b, strongGenerators k.castSucc b = (strongGenerators k.castSucc a)⁻¹ := by
    decide +kernel
  exact h level i

/-- Each cover includes the identity as its first representative. -/
private theorem representative_one (level : Fin 5) :
    ∃ i, representatives level i = 1 := by
  fin_cases level <;> refine ⟨⟨0, by decide⟩, Equiv.ext ?_⟩ <;> decide +kernel

/-- Every generator step is covered modulo the next generated subgroup. -/
private theorem step (level : Fin 5) (a : Fin (generatorSize level.castSucc))
    (i : Fin (transversalSize level)) :
    ∃ j, (representatives level j)⁻¹ * strongGenerators level.castSucc a *
      representatives level i ∈ levelSubgroup level.succ := by
  refine ⟨(transitions level a i).1, ?_⟩
  rw [mul_assoc, transitions_valid, inv_mul_cancel_left]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure ⟨j, rfl⟩

/-- The generic finite-cover theorem bounds each level by the next one. -/
private theorem level_bound (level : Fin 5) :
    Nat.card (levelSubgroup level.castSucc) ≤
      transversalSize level * Nat.card (levelSubgroup level.succ) := by
  have h := Subgroup.natCard_closure_le_mul (strongGenerators level.castSucc)
    (representatives level) (levelSubgroup level.succ) (representative_one level)
    (step level) ?_
  · simpa only [levelSubgroup, Nat.card_fin] using h
  · intro a i
    obtain ⟨b, hb⟩ := inverse_generator level a
    obtain ⟨j, hj⟩ := step level b i
    exact ⟨j, by simpa only [hb] using hj⟩

/-- The empty terminal generator family generates the trivial subgroup. -/
private theorem terminal_subgroup : levelSubgroup 5 = ⊥ := by
  simp [levelSubgroup, strongGenerators, generatorSize]

/-- The first two table generators agree with the checked M22 representation. -/
private theorem original_generator (i : Fin 2) :
    m22GeneratorImages ⟨i.val, by simpa [GroupPresentation.generatorCount] using i.isLt⟩ =
      generators0 (Fin.castLE (by decide) i) := by
  have h : ∀ (j : Fin 2) (x : Fin 22),
      m22GeneratorImages
        ⟨j.val, by simpa [GroupPresentation.generatorCount] using j.isLt⟩ x =
          generators0 (Fin.castLE (by decide) j) x := by
    unfold m22GeneratorImages
    decide +kernel
  exact Equiv.ext (h i)

/-- The generated top level contains the entire image of the presentation. -/
private theorem image_le_closure : m22PermutationHom.range ≤ levelSubgroup 0 := by
  rw [range_eq_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨i, rfl⟩
  let j : Fin 2 := ⟨i.val, by simpa [GroupPresentation.generatorCount] using i.isLt⟩
  exact ⟨Fin.castLE (by decide) j, (original_generator j).symm⟩

/-- The checked Schreier cover bounds the concrete M22 permutation image by 443520. -/
theorem m22PermutationHom_range_natCard_le : Nat.card m22PermutationHom.range ≤ 443520 := by
  apply (Subgroup.card_le_of_le image_le_closure).trans
  have h0 := level_bound 0
  have h1 := level_bound 1
  have h2 := level_bound 2
  have h3 := level_bound 3
  have h4 := level_bound 4
  change Nat.card (levelSubgroup 0) ≤ 22 * Nat.card (levelSubgroup 1) at h0
  change Nat.card (levelSubgroup 1) ≤ 21 * Nat.card (levelSubgroup 2) at h1
  change Nat.card (levelSubgroup 2) ≤ 20 * Nat.card (levelSubgroup 3) at h2
  change Nat.card (levelSubgroup 3) ≤ 16 * Nat.card (levelSubgroup 4) at h3
  change Nat.card (levelSubgroup 4) ≤ 3 * Nat.card (levelSubgroup 5) at h4
  rw [terminal_subgroup, Subgroup.card_bot] at h4
  exact h0.trans (Nat.mul_le_mul_left 22
    (h1.trans (Nat.mul_le_mul_left 21
      (h2.trans (Nat.mul_le_mul_left 20
        (h3.trans (Nat.mul_le_mul_left 16 h4)))))))

/-- The image of the exact M22 presentation in the checked action has order 443520. -/
theorem m22PermutationHom_range_natCard : Nat.card m22PermutationHom.range = 443520 :=
  le_antisymm m22PermutationHom_range_natCard_le m22PermutationHom_range_natCard_ge

end TauCeti.Sporadic.Mathieu
