/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.Permutation
import Mathlib.Tactic.FinCases

/-!
# A finite-cover certificate for the M23 permutation image

The six covers have sizes 23, 22, 21, 20, 16, and 3. Their generator and
representative tables define permutations with checked inverses or bijectivity.
Each signed generator step has a target representative and a correction word in
the next generator family. Kernel computation checks all 446 transitions as
full permutation equalities; the final generator family is empty.

The `M23Cover` namespace exposes the indexed certificate and its transition
identity. `M23Order` applies the generic finite-cover bound and identifies the
initial generators with the checked degree-23 model. No membership of the
representatives in the image or stabilizer identification is assumed.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M23Cover

/-- Permutations from point images with a checked pairing of inverse rows. -/
private def tableGenerators {n : ℕ} (p : Vector (Vector (Fin 23) 23) n)
    (inverse : Vector (Fin n) n)
    (h : ∀ (i : Fin n) (x : Fin 23), p[inverse[i]][p[i][x]] = x ∧
      p[i][p[inverse[i]][x]] = x) (i : Fin n) : Equiv.Perm (Fin 23) where
  toFun x := p[i][x]
  invFun x := p[inverse[i]][x]
  left_inv x := (h i x).1
  right_inv x := (h i x).2

/-- Point images of the level-0 generators, followed by their inverses. -/
private def generatorImages0 : Vector (Vector (Fin 23) 23) 4 :=
  #v[
    #v[5, 1, 7, 20, 4, 0, 14, 2, 9, 8, 10, 17, 12, 13, 6, 15, 19, 11, 21, 16, 3, 18, 22],
    #v[7, 3, 2, 14, 11, 12, 15, 6, 8, 22, 20, 5, 4, 9, 21, 0, 16, 19, 13, 17, 10, 1, 18],
    #v[5, 1, 7, 20, 4, 0, 14, 2, 9, 8, 10, 17, 12, 13, 6, 15, 19, 11, 21, 16, 3, 18, 22],
    #v[15, 21, 2, 1, 12, 11, 7, 0, 8, 13, 20, 4, 5, 18, 3, 6, 16, 19, 22, 17, 10, 14, 9]]

/-- The signed level-0 generators with checked inverse rows. -/
private def generators0 : Fin 4 → Equiv.Perm (Fin 23) :=
  tableGenerators generatorImages0 #v[2, 3, 0, 1]
    (by decide +kernel)

/-- Point images of the 23 level-0 representatives, identity first. -/
private def transversalImages0 : Vector (Vector (Fin 23) 23) 23 :=
  #v[
    #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22],
    #v[1, 0, 15, 9, 6, 5, 4, 7, 18, 3, 10, 11, 17, 13, 14, 2, 19, 12, 8, 16, 21, 20, 22],
    #v[2, 20, 7, 6, 17, 12, 15, 14, 9, 22, 3, 0, 4, 8, 18, 5, 19, 16, 13, 11, 10, 1, 21],
    #v[3, 7, 0, 22, 15, 12, 11, 6, 13, 14, 20, 5, 19, 9, 21, 2, 17, 4, 8, 16, 1, 10, 18],
    #v[4, 14, 15, 20, 5, 6, 1, 2, 18, 8, 10, 17, 11, 22, 0, 7, 19, 12, 3, 16, 21, 9, 13],
    #v[5, 1, 7, 20, 4, 0, 14, 2, 9, 8, 10, 17, 12, 13, 6, 15, 19, 11, 21, 16, 3, 18, 22],
    #v[6, 14, 2, 21, 5, 4, 0, 15, 8, 18, 10, 12, 11, 22, 1, 7, 16, 17, 9, 19, 20, 3, 13],
    #v[7, 3, 2, 14, 11, 12, 15, 6, 8, 22, 20, 5, 4, 9, 21, 0, 16, 19, 13, 17, 10, 1, 18],
    #v[8, 2, 1, 22, 7, 11, 17, 4, 13, 6, 18, 0, 19, 20, 3, 15, 12, 14, 21, 16, 5, 10, 9],
    #v[9, 7, 1, 22, 2, 17, 11, 4, 13, 14, 21, 5, 16, 3, 20, 15, 12, 6, 18, 19, 0, 10, 8],
    #v[10, 2, 11, 9, 6, 5, 19, 3, 18, 7, 1, 15, 16, 8, 22, 0, 4, 12, 13, 17, 21, 20, 14],
    #v[11, 21, 0, 10, 12, 15, 3, 2, 13, 8, 20, 19, 5, 18, 7, 6, 17, 4, 14, 16, 1, 22, 9],
    #v[12, 3, 6, 10, 11, 7, 21, 2, 22, 8, 20, 19, 4, 9, 15, 0, 17, 5, 1, 16, 14, 13, 18],
    #v[13, 0, 21, 9, 2, 19, 4, 12, 18, 3, 14, 11, 16, 1, 10, 6, 5, 7, 22, 17, 15, 20, 8],
    #v[14, 6, 7, 18, 0, 4, 5, 15, 9, 21, 10, 12, 17, 22, 1, 2, 19, 11, 8, 16, 3, 20, 13],
    #v[15, 21, 2, 1, 12, 11, 7, 0, 8, 13, 20, 4, 5, 18, 3, 6, 16, 19, 22, 17, 10, 14, 9],
    #v[16, 22, 17, 3, 0, 14, 10, 5, 21, 13, 1, 19, 15, 6, 7, 20, 4, 12, 2, 11, 18, 8, 9],
    #v[17, 18, 5, 10, 12, 15, 20, 7, 13, 9, 3, 16, 0, 21, 2, 14, 11, 4, 6, 19, 1, 22, 8],
    #v[18, 15, 14, 13, 2, 17, 12, 5, 22, 1, 3, 4, 16, 21, 20, 7, 11, 0, 9, 19, 6, 10, 8],
    #v[19, 22, 11, 20, 5, 6, 10, 0, 18, 13, 1, 16, 15, 14, 2, 3, 4, 12, 7, 17, 21, 9, 8],
    #v[20, 2, 5, 22, 15, 12, 17, 14, 13, 6, 3, 0, 16, 8, 18, 7, 11, 4, 9, 19, 1, 10, 21],
    #v[21, 15, 6, 13, 7, 11, 12, 0, 22, 1, 20, 4, 19, 18, 3, 2, 17, 5, 8, 16, 14, 10, 9],
    #v[22, 6, 3, 18, 2, 19, 5, 11, 9, 21, 1, 12, 16, 14, 10, 0, 4, 15, 13, 17, 7, 20, 8]]

/-- Level-0 representatives from their checked bijective point maps. -/
private noncomputable def transversals0 (i : Fin 23) : Equiv.Perm (Fin 23) :=
  Equiv.ofBijective (fun x ↦ transversalImages0[i][x]) (by
    have h : ∀ j : Fin 23,
        Function.Bijective (fun x : Fin 23 ↦ transversalImages0[j][x]) := by
      decide +kernel
    exact h i)

/-- Point images of the level-1 generators, followed by their inverses. -/
private def generatorImages1 : Vector (Vector (Fin 23) 23) 4 :=
  #v[
    #v[0, 20, 11, 5, 14, 8, 15, 17, 10, 22, 3, 2, 4, 12, 13, 6, 19, 16, 18, 7, 9, 21, 1],
    #v[0, 20, 11, 2, 16, 15, 3, 10, 18, 8, 21, 6, 5, 13, 9, 19, 4, 17, 14, 12, 1, 22, 7],
    #v[0, 22, 11, 10, 12, 3, 15, 19, 5, 20, 8, 2, 13, 14, 4, 6, 17, 7, 18, 16, 1, 21, 9],
    #v[0, 20, 3, 6, 16, 12, 11, 22, 9, 14, 7, 2, 19, 13, 18, 5, 4, 17, 8, 15, 1, 10, 21]]

/-- The signed level-1 generators with checked inverse rows. -/
private def generators1 : Fin 4 → Equiv.Perm (Fin 23) :=
  tableGenerators generatorImages1 #v[2, 3, 0, 1]
    (by decide +kernel)

/-- Point images of the 22 level-1 representatives, identity first. -/
private def transversalImages1 : Vector (Vector (Fin 23) 23) 22 :=
  #v[
    #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22],
    #v[0, 2, 15, 20, 3, 11, 16, 18, 10, 8, 13, 19, 5, 21, 9, 6, 4, 22, 7, 12, 1, 17, 14],
    #v[0, 3, 5, 1, 6, 2, 4, 8, 7, 9, 13, 15, 12, 10, 14, 11, 16, 21, 22, 19, 20, 17, 18],
    #v[0, 4, 10, 20, 14, 19, 2, 12, 15, 1, 13, 11, 18, 17, 16, 3, 9, 6, 5, 7, 21, 8, 22],
    #v[0, 5, 2, 18, 14, 21, 10, 12, 11, 1, 6, 15, 20, 17, 3, 16, 8, 13, 4, 7, 19, 9, 22],
    #v[0, 6, 12, 20, 11, 3, 16, 9, 22, 14, 13, 5, 19, 7, 18, 2, 4, 10, 21, 15, 1, 17, 8],
    #v[0, 7, 6, 21, 5, 2, 19, 12, 15, 1, 18, 11, 13, 9, 16, 3, 17, 10, 14, 4, 20, 22, 8],
    #v[0, 8, 11, 18, 13, 21, 3, 4, 2, 20, 15, 6, 9, 16, 5, 19, 10, 12, 14, 17, 7, 22, 1],
    #v[0, 9, 2, 8, 13, 10, 6, 16, 3, 1, 5, 11, 14, 4, 12, 15, 7, 19, 18, 17, 22, 21, 20],
    #v[0, 10, 3, 22, 15, 11, 12, 5, 19, 20, 14, 6, 13, 8, 4, 2, 17, 21, 9, 16, 1, 7, 18],
    #v[0, 11, 19, 1, 2, 6, 4, 14, 21, 18, 13, 12, 15, 22, 8, 3, 16, 7, 10, 5, 20, 17, 9],
    #v[0, 12, 19, 22, 2, 6, 4, 13, 3, 7, 14, 11, 9, 1, 17, 21, 10, 18, 16, 5, 20, 8, 15],
    #v[0, 13, 5, 22, 12, 17, 2, 14, 15, 9, 4, 11, 18, 19, 7, 8, 1, 6, 10, 16, 21, 3, 20],
    #v[0, 14, 3, 9, 13, 7, 11, 4, 6, 20, 12, 2, 18, 16, 19, 5, 22, 15, 8, 17, 21, 10, 1],
    #v[0, 15, 5, 10, 6, 2, 4, 13, 11, 21, 8, 3, 18, 1, 17, 7, 22, 9, 16, 19, 20, 14, 12],
    #v[0, 16, 6, 21, 10, 2, 17, 14, 15, 9, 18, 11, 4, 1, 7, 8, 19, 5, 12, 13, 22, 20, 3],
    #v[0, 17, 15, 21, 8, 11, 7, 4, 6, 20, 18, 2, 12, 22, 19, 5, 16, 3, 13, 14, 9, 1, 10],
    #v[0, 18, 6, 14, 13, 22, 2, 16, 11, 1, 19, 3, 8, 4, 15, 12, 21, 5, 9, 17, 10, 7, 20],
    #v[0, 19, 15, 21, 3, 11, 16, 13, 6, 22, 18, 2, 14, 20, 17, 10, 7, 8, 4, 12, 1, 9, 5],
    #v[0, 20, 3, 6, 16, 12, 11, 22, 9, 14, 7, 2, 19, 13, 18, 5, 4, 17, 8, 15, 1, 10, 21],
    #v[0, 21, 2, 7, 19, 6, 5, 15, 12, 1, 9, 3, 13, 18, 16, 11, 17, 22, 8, 4, 20, 10, 14],
    #v[0, 22, 11, 10, 12, 3, 15, 19, 5, 20, 8, 2, 13, 14, 4, 6, 17, 7, 18, 16, 1, 21, 9]]

/-- Level-1 representatives from their checked bijective point maps. -/
private noncomputable def transversals1 (i : Fin 22) : Equiv.Perm (Fin 23) :=
  Equiv.ofBijective (fun x ↦ transversalImages1[i][x]) (by
    have h : ∀ j : Fin 22,
        Function.Bijective (fun x : Fin 23 ↦ transversalImages1[j][x]) := by
      decide +kernel
    exact h i)

/-- Point images of the level-2 generators, followed by their inverses. -/
private def generatorImages2 : Vector (Vector (Fin 23) 23) 4 :=
  #v[
    #v[0, 1, 14, 19, 18, 13, 6, 3, 8, 22, 5, 17, 11, 10, 16, 9, 2, 12, 21, 7, 20, 4, 15],
    #v[0, 1, 22, 12, 14, 21, 13, 3, 11, 20, 10, 9, 5, 2, 18, 4, 8, 6, 19, 15, 16, 7, 17],
    #v[0, 1, 16, 7, 21, 10, 6, 19, 8, 15, 13, 12, 17, 5, 2, 22, 14, 11, 4, 3, 20, 18, 9],
    #v[0, 1, 13, 7, 15, 12, 17, 21, 16, 11, 10, 8, 3, 6, 4, 19, 20, 22, 14, 18, 9, 5, 2]]

/-- The signed level-2 generators with checked inverse rows. -/
private def generators2 : Fin 4 → Equiv.Perm (Fin 23) :=
  tableGenerators generatorImages2 #v[2, 3, 0, 1]
    (by decide +kernel)

/-- Point images of the 21 level-2 representatives, identity first. -/
private def transversalImages2 : Vector (Vector (Fin 23) 23) 21 :=
  #v[
    #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22],
    #v[0, 1, 3, 14, 13, 2, 16, 4, 15, 7, 17, 20, 5, 22, 12, 21, 11, 8, 6, 19, 18, 10, 9],
    #v[0, 1, 4, 18, 14, 6, 17, 7, 16, 2, 12, 22, 8, 10, 20, 11, 13, 3, 5, 21, 9, 15, 19],
    #v[0, 1, 5, 19, 22, 17, 11, 18, 14, 12, 13, 8, 7, 6, 21, 3, 20, 9, 2, 4, 15, 10, 16],
    #v[0, 1, 6, 21, 19, 3, 22, 5, 20, 8, 10, 16, 7, 17, 15, 18, 9, 2, 4, 14, 11, 12, 13],
    #v[0, 1, 7, 8, 20, 9, 5, 21, 15, 22, 11, 14, 6, 18, 13, 16, 2, 12, 4, 17, 10, 3, 19],
    #v[0, 1, 8, 3, 7, 10, 13, 15, 11, 4, 2, 5, 6, 21, 22, 17, 18, 9, 14, 12, 16, 19, 20],
    #v[0, 1, 9, 17, 2, 18, 5, 7, 12, 20, 13, 15, 10, 16, 4, 21, 8, 6, 3, 22, 14, 19, 11],
    #v[0, 1, 10, 3, 9, 11, 12, 4, 2, 17, 5, 8, 19, 6, 18, 7, 20, 15, 16, 21, 22, 13, 14],
    #v[0, 1, 11, 22, 13, 14, 12, 21, 3, 9, 6, 19, 10, 20, 15, 5, 16, 17, 7, 2, 4, 18, 8],
    #v[0, 1, 12, 18, 2, 22, 8, 14, 4, 3, 6, 16, 21, 17, 5, 7, 9, 11, 13, 15, 19, 10, 20],
    #v[0, 1, 13, 7, 15, 12, 17, 21, 16, 11, 10, 8, 3, 6, 4, 19, 20, 22, 14, 18, 9, 5, 2],
    #v[0, 1, 14, 19, 18, 13, 6, 3, 8, 22, 5, 17, 11, 10, 16, 9, 2, 12, 21, 7, 20, 4, 15],
    #v[0, 1, 15, 11, 16, 4, 10, 19, 17, 20, 5, 22, 13, 14, 21, 18, 8, 6, 7, 9, 2, 3, 12],
    #v[0, 1, 16, 7, 21, 10, 6, 19, 8, 15, 13, 12, 17, 5, 2, 22, 14, 11, 4, 3, 20, 18, 9],
    #v[0, 1, 17, 5, 18, 7, 2, 12, 9, 16, 10, 20, 21, 22, 19, 14, 11, 13, 15, 4, 8, 3, 6],
    #v[0, 1, 18, 15, 19, 2, 13, 12, 11, 17, 21, 6, 9, 10, 8, 20, 22, 5, 7, 3, 16, 14, 4],
    #v[0, 1, 19, 8, 20, 15, 10, 18, 22, 9, 12, 2, 6, 4, 5, 14, 16, 17, 21, 11, 13, 7, 3],
    #v[0, 1, 20, 21, 5, 10, 17, 18, 16, 19, 6, 3, 22, 12, 13, 2, 4, 8, 15, 7, 9, 14, 11],
    #v[0, 1, 21, 4, 2, 6, 11, 19, 14, 16, 17, 9, 8, 13, 20, 12, 5, 7, 10, 18, 15, 22, 3],
    #v[0, 1, 22, 12, 14, 21, 13, 3, 11, 20, 10, 9, 5, 2, 18, 4, 8, 6, 19, 15, 16, 7, 17]]

/-- Level-2 representatives from their checked bijective point maps. -/
private noncomputable def transversals2 (i : Fin 21) : Equiv.Perm (Fin 23) :=
  Equiv.ofBijective (fun x ↦ transversalImages2[i][x]) (by
    have h : ∀ j : Fin 21,
        Function.Bijective (fun x : Fin 23 ↦ transversalImages2[j][x]) := by
      decide +kernel
    exact h i)

/-- Point images of the level-3 generators, followed by their inverses. -/
private def generatorImages3 : Vector (Vector (Fin 23) 23) 4 :=
  #v[
    #v[0, 1, 2, 3, 21, 12, 16, 18, 6, 13, 9, 7, 19, 10, 14, 20, 8, 15, 11, 5, 17, 22, 4],
    #v[0, 1, 2, 18, 10, 5, 3, 13, 22, 19, 14, 9, 16, 15, 4, 7, 21, 17, 6, 11, 8, 12, 20],
    #v[0, 1, 2, 3, 22, 19, 8, 11, 16, 10, 13, 18, 5, 9, 14, 17, 6, 20, 7, 12, 15, 4, 21],
    #v[0, 1, 2, 6, 14, 5, 18, 15, 20, 11, 4, 19, 21, 7, 10, 13, 12, 17, 3, 9, 22, 16, 8]]

/-- The signed level-3 generators with checked inverse rows. -/
private def generators3 : Fin 4 → Equiv.Perm (Fin 23) :=
  tableGenerators generatorImages3 #v[2, 3, 0, 1]
    (by decide +kernel)

/-- Point images of the 20 level-3 representatives, identity first. -/
private def transversalImages3 : Vector (Vector (Fin 23) 23) 20 :=
  #v[
    #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22],
    #v[0, 1, 2, 4, 22, 6, 10, 16, 20, 9, 5, 19, 15, 8, 12, 14, 18, 11, 7, 17, 13, 21, 3],
    #v[0, 1, 2, 5, 13, 4, 12, 21, 20, 17, 6, 19, 16, 3, 18, 22, 10, 9, 8, 11, 14, 15, 7],
    #v[0, 1, 2, 6, 14, 5, 18, 15, 20, 11, 4, 19, 21, 7, 10, 13, 12, 17, 3, 9, 22, 16, 8],
    #v[0, 1, 2, 7, 13, 19, 3, 9, 21, 12, 14, 10, 6, 17, 22, 11, 4, 20, 8, 18, 16, 5, 15],
    #v[0, 1, 2, 8, 14, 19, 7, 17, 15, 18, 22, 12, 4, 11, 13, 9, 5, 20, 3, 10, 21, 6, 16],
    #v[0, 1, 2, 9, 19, 16, 18, 14, 10, 5, 4, 15, 22, 8, 12, 6, 20, 7, 21, 13, 3, 11, 17],
    #v[0, 1, 2, 10, 12, 6, 7, 14, 13, 19, 22, 17, 21, 16, 5, 8, 15, 11, 4, 9, 3, 18, 20],
    #v[0, 1, 2, 11, 9, 12, 3, 10, 4, 5, 14, 13, 8, 20, 21, 18, 22, 15, 16, 7, 6, 19, 17],
    #v[0, 1, 2, 12, 10, 21, 19, 22, 17, 15, 16, 5, 8, 3, 11, 4, 9, 13, 6, 7, 14, 20, 18],
    #v[0, 1, 2, 13, 15, 11, 18, 19, 12, 16, 4, 14, 3, 17, 20, 9, 10, 8, 22, 6, 21, 5, 7],
    #v[0, 1, 2, 14, 8, 18, 4, 12, 22, 11, 5, 9, 13, 20, 21, 10, 3, 19, 15, 17, 7, 16, 6],
    #v[0, 1, 2, 15, 7, 9, 6, 11, 16, 21, 10, 4, 18, 17, 8, 19, 14, 22, 20, 3, 12, 5, 13],
    #v[0, 1, 2, 16, 14, 12, 11, 20, 17, 7, 21, 5, 22, 18, 9, 10, 19, 15, 3, 13, 4, 8, 6],
    #v[0, 1, 2, 17, 11, 10, 8, 18, 6, 4, 13, 22, 7, 20, 16, 12, 14, 21, 15, 3, 5, 19, 9],
    #v[0, 1, 2, 18, 10, 5, 3, 13, 22, 19, 14, 9, 16, 15, 4, 7, 21, 17, 6, 11, 8, 12, 20],
    #v[0, 1, 2, 19, 11, 21, 6, 4, 14, 5, 10, 7, 20, 22, 16, 3, 8, 13, 12, 15, 18, 9, 17],
    #v[0, 1, 2, 20, 10, 9, 15, 17, 13, 3, 8, 21, 14, 19, 7, 11, 5, 22, 6, 4, 16, 18, 12],
    #v[0, 1, 2, 21, 4, 16, 9, 8, 17, 13, 12, 5, 20, 6, 19, 14, 11, 7, 18, 15, 10, 22, 3],
    #v[0, 1, 2, 22, 4, 11, 13, 17, 7, 6, 20, 16, 10, 9, 15, 19, 5, 8, 18, 14, 12, 3, 21]]

/-- Level-3 representatives from their checked bijective point maps. -/
private noncomputable def transversals3 (i : Fin 20) : Equiv.Perm (Fin 23) :=
  Equiv.ofBijective (fun x ↦ transversalImages3[i][x]) (by
    have h : ∀ j : Fin 20,
        Function.Bijective (fun x : Fin 23 ↦ transversalImages3[j][x]) := by
      decide +kernel
    exact h i)

/-- Point images of the level-4 generators, followed by their inverses. -/
private def generatorImages4 : Vector (Vector (Fin 23) 23) 6 :=
  #v[
    #v[0, 1, 2, 3, 21, 15, 11, 5, 17, 10, 14, 20, 8, 13, 9, 7, 19, 12, 16, 18, 6, 22, 4],
    #v[0, 1, 2, 3, 4, 16, 15, 14, 13, 20, 19, 18, 17, 8, 7, 6, 5, 12, 11, 10, 9, 21, 22],
    #v[0, 1, 2, 3, 21, 14, 10, 8, 20, 11, 15, 17, 5, 16, 12, 6, 18, 9, 13, 19, 7, 22, 4],
    #v[0, 1, 2, 3, 22, 7, 20, 15, 12, 14, 9, 6, 17, 13, 10, 5, 18, 8, 19, 16, 11, 4, 21],
    #v[0, 1, 2, 3, 4, 16, 15, 14, 13, 20, 19, 18, 17, 8, 7, 6, 5, 12, 11, 10, 9, 21, 22],
    #v[0, 1, 2, 3, 22, 12, 15, 20, 7, 17, 6, 9, 14, 18, 5, 10, 13, 11, 16, 19, 8, 4, 21]]

/-- The signed level-4 generators with checked inverse rows. -/
private def generators4 : Fin 6 → Equiv.Perm (Fin 23) :=
  tableGenerators generatorImages4 #v[3, 4, 5, 0, 1, 2]
    (by decide +kernel)

/-- Point images of the 16 level-4 representatives, identity first. -/
private def transversalImages4 : Vector (Vector (Fin 23) 23) 16 :=
  #v[
    #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22],
    #v[0, 1, 2, 3, 21, 7, 19, 13, 9, 18, 6, 12, 16, 5, 17, 15, 11, 20, 8, 10, 14, 22, 4],
    #v[0, 1, 2, 3, 21, 8, 20, 14, 10, 17, 5, 11, 15, 6, 18, 16, 12, 19, 7, 9, 13, 22, 4],
    #v[0, 1, 2, 3, 22, 13, 10, 5, 18, 8, 19, 16, 11, 7, 20, 15, 12, 14, 9, 6, 17, 4, 21],
    #v[0, 1, 2, 3, 4, 16, 15, 14, 13, 20, 19, 18, 17, 8, 7, 6, 5, 12, 11, 10, 9, 21, 22],
    #v[0, 1, 2, 3, 21, 11, 15, 17, 5, 14, 10, 8, 20, 9, 13, 19, 7, 16, 12, 6, 18, 22, 4],
    #v[0, 1, 2, 3, 21, 12, 16, 18, 6, 13, 9, 7, 19, 10, 14, 20, 8, 15, 11, 5, 17, 22, 4],
    #v[0, 1, 2, 3, 22, 17, 6, 9, 14, 12, 15, 20, 7, 11, 16, 19, 8, 18, 5, 10, 13, 4, 21],
    #v[0, 1, 2, 3, 22, 18, 5, 10, 13, 11, 16, 19, 8, 12, 15, 20, 7, 17, 6, 9, 14, 4, 21],
    #v[0, 1, 2, 3, 21, 16, 12, 6, 18, 9, 13, 19, 7, 14, 10, 8, 20, 11, 15, 17, 5, 22, 4],
    #v[0, 1, 2, 3, 21, 13, 9, 7, 19, 12, 16, 18, 6, 15, 11, 5, 17, 10, 14, 20, 8, 22, 4],
    #v[0, 1, 2, 3, 21, 14, 10, 8, 20, 11, 15, 17, 5, 16, 12, 6, 18, 9, 13, 19, 7, 22, 4],
    #v[0, 1, 2, 3, 21, 19, 7, 9, 13, 6, 18, 16, 12, 17, 5, 11, 15, 8, 20, 14, 10, 22, 4],
    #v[0, 1, 2, 3, 22, 12, 15, 20, 7, 17, 6, 9, 14, 18, 5, 10, 13, 11, 16, 19, 8, 4, 21],
    #v[0, 1, 2, 3, 21, 17, 5, 11, 15, 8, 20, 14, 10, 19, 7, 9, 13, 6, 18, 16, 12, 22, 4],
    #v[0, 1, 2, 3, 21, 18, 6, 12, 16, 7, 19, 13, 9, 20, 8, 10, 14, 5, 17, 15, 11, 22, 4]]

/-- Level-4 representatives from their checked bijective point maps. -/
private noncomputable def transversals4 (i : Fin 16) : Equiv.Perm (Fin 23) :=
  Equiv.ofBijective (fun x ↦ transversalImages4[i][x]) (by
    have h : ∀ j : Fin 16,
        Function.Bijective (fun x : Fin 23 ↦ transversalImages4[j][x]) := by
      decide +kernel
    exact h i)

/-- Point images of the level-5 generators, followed by their inverses. -/
private def generatorImages5 : Vector (Vector (Fin 23) 23) 2 :=
  #v[
    #v[0, 1, 2, 3, 21, 15, 11, 5, 17, 10, 14, 20, 8, 13, 9, 7, 19, 12, 16, 18, 6, 22, 4],
    #v[0, 1, 2, 3, 22, 7, 20, 15, 12, 14, 9, 6, 17, 13, 10, 5, 18, 8, 19, 16, 11, 4, 21]]

/-- The signed level-5 generators with checked inverse rows. -/
private def generators5 : Fin 2 → Equiv.Perm (Fin 23) :=
  tableGenerators generatorImages5 #v[1, 0]
    (by decide +kernel)

/-- Point images of the 3 level-5 representatives, identity first. -/
private def transversalImages5 : Vector (Vector (Fin 23) 23) 3 :=
  #v[
    #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22],
    #v[0, 1, 2, 3, 21, 15, 11, 5, 17, 10, 14, 20, 8, 13, 9, 7, 19, 12, 16, 18, 6, 22, 4],
    #v[0, 1, 2, 3, 22, 7, 20, 15, 12, 14, 9, 6, 17, 13, 10, 5, 18, 8, 19, 16, 11, 4, 21]]

/-- Level-5 representatives from their checked bijective point maps. -/
private noncomputable def transversals5 (i : Fin 3) : Equiv.Perm (Fin 23) :=
  Equiv.ofBijective (fun x ↦ transversalImages5[i][x]) (by
    have h : ∀ j : Fin 3,
        Function.Bijective (fun x : Fin 23 ↦ transversalImages5[j][x]) := by
      decide +kernel
    exact h i)

/-- The generator family at the terminal level is empty. -/
private def generators6 : Fin 0 → Equiv.Perm (Fin 23) := Fin.elim0

/-- Target representatives and next-level words for every signed step at level 0. -/
private def transitions0 : Vector (Vector (Fin 23 × List (Fin 4)) 23) 4 :=
  #v[
    #v[
      (5, []),
      (1, [2, 1, 2, 3, 2, 1, 0, 1, 1, 2, 3, 2, 1, 1, 1, 0, 1, 0, 0, 3, 2, 1, 0, 1, 0, 1, 1, 0, 3,
        3, 2, 2, 2, 3, 0, 1, 2, 3, 2]),
      (7, []),
      (20, []),
      (4, [2, 1, 2, 3, 2, 1, 0, 1, 1, 2, 3, 2, 1, 1, 1, 0, 1, 0, 0, 3, 2, 1, 0, 1, 0, 1, 1, 0, 3,
        3, 2, 2, 2, 3, 0, 1, 2, 3, 2]),
      (0, []),
      (14, []),
      (2, []),
      (9, []),
      (8, []),
      (10, [2, 1, 0, 3, 2, 2, 1, 1, 0, 0, 1, 2, 2, 3, 2, 2, 3, 3, 0, 0, 3, 2, 1, 1, 0, 1, 2, 1, 0,
        3, 3, 0, 3, 2, 1, 0, 1, 0, 1, 1, 0, 3, 3, 2, 2, 2, 3, 0, 1, 2, 3, 2]),
      (17, []),
      (12, [3, 3, 2, 3, 3, 0, 1, 0, 3, 2, 3, 3, 0, 3, 2, 1, 0, 1, 1, 2, 3, 2, 1, 1, 1, 0, 0, 1, 0,
        3, 3, 2, 3, 0, 1, 2, 1, 0, 1, 1, 0, 3, 2, 1, 0, 1, 2, 3, 3]),
      (13, [2, 2, 1, 1, 2, 3, 3, 2, 1, 0, 1, 1, 2, 3, 2, 2, 3, 0, 1, 1, 2, 1, 1, 2, 1, 0, 3, 3, 2,
        3, 3, 2, 3]),
      (6, []),
      (15, [0, 3, 2, 1, 0, 3, 2, 2, 3, 0, 1, 2, 2, 3, 2, 1, 0, 1, 0, 0, 1, 2, 3, 2, 3, 3, 2, 1, 1,
        0]),
      (19, []),
      (11, []),
      (21, []),
      (16, []),
      (3, []),
      (18, []),
      (22, [0, 3, 2, 2, 1, 0, 3, 3, 2, 3, 0, 3, 2, 1, 0, 1, 1, 2, 3, 2, 2, 3, 3, 0, 1, 1, 2, 3, 0,
        3, 2, 3, 3, 0, 1, 2, 2, 1, 1, 0])],
    #v[
      (7, []),
      (3, []),
      (2, [3]),
      (14, []),
      (11, []),
      (12, []),
      (15, []),
      (6, []),
      (8, [0, 3, 2, 1, 0, 1, 2, 2, 3, 3, 3, 0, 1, 2, 2, 3, 2, 2, 3, 3, 3, 2, 3, 0, 1, 0, 3, 3, 0,
        0, 1, 2, 3, 2, 2, 3, 3, 0, 1, 0, 3, 3, 2, 3, 0, 1, 2, 1, 0, 1, 1, 0, 3, 2, 1, 0, 1, 2, 3,
        3]),
      (22, []),
      (20, []),
      (5, []),
      (4, []),
      (9, []),
      (21, []),
      (0, []),
      (16, [0]),
      (19, [2, 2, 2, 3, 2, 3, 2, 3, 3, 3, 2, 3, 3, 3, 0, 1, 2, 2, 3, 2, 2, 3, 3, 3, 0, 1, 0, 3, 3,
        2, 3, 0, 1, 2, 1, 0, 0, 3, 2, 1, 0, 1, 0, 1, 1, 0, 3, 3, 2, 2, 2, 3, 0, 1, 2, 3, 2]),
      (13, []),
      (17, []),
      (10, [0, 1, 0, 3, 2, 2, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 3, 3,
        2, 3, 3, 3, 0, 1, 0, 3, 3, 2, 3, 0, 1, 2, 1, 0, 1, 1, 0, 3, 2, 1, 0, 1, 2, 3, 3]),
      (1, []),
      (18, [])],
    #v[
      (5, []),
      (1, [2, 1, 2, 3, 2, 1, 0, 1, 1, 2, 3, 2, 1, 1, 1, 0, 1, 0, 0, 3, 2, 1, 0, 1, 0, 1, 1, 0, 3,
        3, 2, 2, 2, 3, 0, 1, 2, 3, 2]),
      (7, []),
      (20, []),
      (4, [2, 1, 2, 3, 2, 1, 0, 1, 1, 2, 3, 2, 1, 1, 1, 0, 1, 0, 0, 3, 2, 1, 0, 1, 0, 1, 1, 0, 3,
        3, 2, 2, 2, 3, 0, 1, 2, 3, 2]),
      (0, []),
      (14, []),
      (2, []),
      (9, []),
      (8, []),
      (10, [2, 1, 0, 3, 2, 2, 1, 1, 0, 0, 1, 2, 2, 3, 2, 2, 3, 3, 0, 0, 3, 2, 1, 1, 0, 1, 2, 1, 0,
        3, 3, 0, 3, 2, 1, 0, 1, 0, 1, 1, 0, 3, 3, 2, 2, 2, 3, 0, 1, 2, 3, 2]),
      (17, []),
      (12, [3, 3, 2, 3, 3, 0, 1, 0, 3, 2, 3, 3, 0, 3, 2, 1, 0, 1, 1, 2, 3, 2, 1, 1, 1, 0, 0, 1, 0,
        3, 3, 2, 3, 0, 1, 2, 1, 0, 1, 1, 0, 3, 2, 1, 0, 1, 2, 3, 3]),
      (13, [2, 2, 1, 1, 2, 3, 3, 2, 1, 0, 1, 1, 2, 3, 2, 2, 3, 0, 1, 1, 2, 1, 1, 2, 1, 0, 3, 3, 2,
        3, 3, 2, 3]),
      (6, []),
      (15, [0, 3, 2, 1, 0, 3, 2, 2, 3, 0, 1, 2, 2, 3, 2, 1, 0, 1, 0, 0, 1, 2, 3, 2, 3, 3, 2, 1, 1,
        0]),
      (19, []),
      (11, []),
      (21, []),
      (16, []),
      (3, []),
      (18, []),
      (22, [0, 3, 2, 2, 1, 0, 3, 3, 2, 3, 0, 3, 2, 1, 0, 1, 1, 2, 3, 2, 2, 3, 3, 0, 1, 1, 2, 3, 0,
        3, 2, 3, 3, 0, 1, 2, 2, 1, 1, 0])],
    #v[
      (15, []),
      (21, []),
      (2, [3, 3, 3]),
      (1, []),
      (12, []),
      (11, []),
      (7, []),
      (0, []),
      (8, [0, 1, 0, 3, 2, 3, 3, 0, 1, 0, 3, 2, 2, 3, 2, 3, 0, 1, 2, 3, 2, 1, 0, 1, 1, 2, 3, 0, 0,
        3, 0, 3, 3, 2, 1, 2, 3, 3, 2, 3]),
      (13, []),
      (20, [0, 1, 0, 3, 2, 2, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 3, 3,
        2, 3, 3, 3, 0, 1, 0, 3, 3, 2, 3, 0, 1, 2, 1, 0, 1, 1, 0, 3, 2, 1, 0, 1, 2, 3, 3]),
      (4, []),
      (5, []),
      (18, []),
      (3, []),
      (6, []),
      (16, [2]),
      (19, []),
      (22, []),
      (17, [2, 2, 2, 3, 2, 3, 2, 3, 3, 3, 2, 3, 3, 3, 0, 1, 2, 2, 3, 2, 2, 3, 3, 3, 0, 1, 0, 3, 3,
        2, 3, 0, 1, 2, 1, 0, 0, 3, 2, 1, 0, 1, 0, 1, 1, 0, 3, 3, 2, 2, 2, 3, 0, 1, 2, 3, 2]),
      (10, []),
      (14, []),
      (9, [])]]

private theorem transitions0_valid (s : Fin 4) (t : Fin 23) :
    generators0 s * transversals0 t =
      transversals0 (transitions0[s][t]).1 *
        ((transitions0[s][t]).2.map generators1).prod := by
  have h : ∀ (i : Fin 4) (j : Fin 23) (x : Fin 23),
      (generators0 i * transversals0 j) x =
        (transversals0 (transitions0[i][j]).1 *
          ((transitions0[i][j]).2.map generators1).prod) x := by
    decide +kernel
  exact Equiv.ext (h s t)

/-- Target representatives and next-level words for every signed step at level 1. -/
private def transitions1 : Vector (Vector (Fin 22 × List (Fin 4)) 22) 4 :=
  #v[
    #v[
      (19, [3, 3, 3, 2, 3, 3, 0, 0, 1, 2, 1, 2, 1, 1, 0, 3, 2, 2, 1, 0]),
      (10, [2, 3, 0, 3, 2, 1, 2, 3, 2, 3, 0, 1, 2, 3]),
      (4, [2, 2, 1, 2, 1, 0]),
      (13, []),
      (7, []),
      (14, [3, 3, 3, 2, 3, 3, 0, 0, 1, 2, 3, 2, 3, 2, 1, 0, 3, 3, 2, 3, 3, 0, 3, 3, 2, 2, 3, 0, 3,
        0]),
      (16, []),
      (9, [0, 1, 2, 1, 2, 1, 0]),
      (21, []),
      (2, []),
      (1, [1, 0, 3, 3, 2, 3, 2, 2, 1, 1, 0, 3, 3, 3, 2, 3, 2, 3]),
      (3, [3, 0, 1, 2, 1, 0, 3, 0, 3, 0, 3, 2, 3, 2, 1, 0, 3, 3, 3, 0, 3, 3, 2, 2, 3, 0, 3, 0]),
      (11, [2, 3, 0, 3, 2, 3, 3, 0, 3, 2, 3, 0, 1, 2, 3, 3, 0, 3, 3, 2, 2, 3, 0, 3, 0]),
      (12, []),
      (5, [0, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 0, 3, 3, 3, 2, 2, 3, 0, 3, 0]),
      (18, []),
      (15, []),
      (17, [0, 0, 3, 0, 1, 1, 2, 3, 2, 3, 2, 1, 0, 3, 3, 2, 3]),
      (6, []),
      (8, [0, 0, 1, 1, 2, 3, 0, 1, 0, 1, 1, 2, 1, 1, 0, 3, 2, 2, 1, 1, 2, 1, 0, 0, 1, 1, 2, 1]),
      (20, [0, 1, 0, 3, 2, 1, 2, 2, 3, 0, 0, 1, 2, 3, 3, 0, 3, 3, 2, 2, 1, 2, 1, 0, 0, 1, 1, 2,
        1]),
      (0, [])],
    #v[
      (19, [3, 3, 2, 1, 1, 0, 1, 0, 1, 2, 3, 2, 3, 3, 0, 3, 3, 3, 2, 3, 0, 3, 3, 2, 2, 3, 0, 3,
        0]),
      (10, []),
      (1, []),
      (15, [3, 3, 2, 3, 0, 3, 2, 1, 2, 1, 0, 3, 2, 1, 0, 1]),
      (14, [1, 2, 3, 2, 3, 3, 0, 3, 3, 2, 3, 2, 1, 0, 3, 3, 3, 0, 3, 3, 2, 2, 3, 0, 3, 0]),
      (2, []),
      (9, []),
      (17, []),
      (7, []),
      (20, []),
      (5, []),
      (4, [0, 3, 3, 3, 0, 1, 1, 0, 3, 3, 0, 1, 2, 3, 2, 3, 2, 1, 0, 3, 3, 2, 3, 3, 0, 3, 3, 2, 2,
        3, 0, 3, 0]),
      (12, [1, 2, 1, 1, 0, 3, 2, 1, 0, 1, 2, 3, 3, 3, 0, 3, 3, 2, 2, 3, 0, 3, 0]),
      (8, []),
      (18, []),
      (3, [0, 1, 2, 1, 0, 1, 2, 3, 3, 0, 3, 3, 2, 3, 0, 3, 3, 2, 2, 3, 0, 3, 0]),
      (16, [0, 3, 2, 3, 3, 0, 0, 3, 2, 1, 2, 1, 2, 1, 0, 1, 2, 3, 3, 2, 1, 2, 1, 0, 0, 1, 1, 2,
        1]),
      (13, []),
      (11, []),
      (0, []),
      (21, []),
      (6, [])],
    #v[
      (21, []),
      (10, [2, 2, 3, 0, 3, 2, 3, 0, 3, 0, 1, 2, 1, 0, 1, 0, 3, 3, 3, 0, 3, 3, 2, 2, 3, 0, 3, 0]),
      (9, []),
      (11, [2, 3, 0, 3, 2, 3, 3, 0, 3, 2, 3, 0, 1, 2, 3, 3, 0, 3, 3, 2, 2, 3, 0, 3, 0]),
      (2, [0, 1, 2, 1, 2, 1, 0]),
      (14, [0, 3, 3, 3, 0, 0, 1, 2, 3, 2, 1, 0, 3, 2, 1, 0, 1]),
      (18, []),
      (4, []),
      (19, [3, 3, 3, 2, 3, 3, 0, 0, 1, 2, 1, 2, 1, 1, 0, 3, 2, 2, 1, 0]),
      (7, [2, 2, 1, 2, 1, 0]),
      (1, [3, 3, 3, 2, 3, 3, 0, 0, 1, 2, 3, 2, 3, 2, 1, 0, 3, 3, 2, 3, 3, 0, 3, 3, 2, 2, 3, 0, 3,
        0]),
      (12, [3, 0, 1, 2, 1, 0, 3, 0, 3, 0, 3, 2, 3, 2, 1, 0, 3, 3, 3, 0, 3, 3, 2, 2, 3, 0, 3, 0]),
      (13, []),
      (3, []),
      (5, [2, 3, 0, 3, 2, 1, 2, 3, 2, 3, 0, 1, 2, 3]),
      (16, []),
      (6, []),
      (17, [0, 3, 2, 3, 3, 0, 0, 3, 2, 1, 2, 1, 0, 3, 2, 1, 0, 1, 2, 1, 2, 1, 0, 0, 1, 1, 2, 1]),
      (15, []),
      (0, [0, 0, 1, 1, 2, 3, 0, 1, 0, 1, 1, 2, 1, 1, 0, 3, 2, 2, 1, 1, 2, 1, 0, 0, 1, 1, 2, 1]),
      (20, [3, 3, 0, 0, 3, 2, 1, 2, 1, 2, 3, 0, 3, 3, 0, 3, 3, 2]),
      (8, [])],
    #v[
      (19, []),
      (2, []),
      (5, []),
      (15, [0, 3, 2, 3, 3, 0, 0, 3, 2, 1, 2, 1, 2, 1, 0, 1, 2, 3, 3, 2, 1, 2, 1, 0, 0, 1, 1, 2,
        1]),
      (11, [1, 2, 3, 2, 3, 3, 0, 3, 3, 2, 3, 2, 1, 0, 3, 3, 3, 0, 3, 3, 2, 2, 3, 0, 3, 0]),
      (10, []),
      (21, []),
      (8, []),
      (13, []),
      (6, []),
      (1, []),
      (18, []),
      (12, [3, 0, 3, 2, 3, 3, 0, 0, 1, 2, 3, 2, 1, 1, 2, 3, 3, 3, 3, 0, 3, 3, 3, 2, 2, 3, 0, 3,
        0]),
      (17, []),
      (4, [0, 3, 3, 3, 0, 1, 1, 0, 3, 3, 0, 1, 2, 3, 2, 3, 2, 1, 0, 3, 3, 2, 3, 3, 0, 3, 3, 2, 2,
        3, 0, 3, 0]),
      (3, [3, 2, 3, 2, 3, 2, 3, 2, 3, 0, 3, 0, 1, 2, 1, 0, 1, 0, 3, 3, 3, 0, 3, 3, 2, 2, 3, 0, 3,
        0]),
      (16, [0, 1, 2, 1, 0, 1, 2, 3, 3, 0, 3, 3, 2, 3, 0, 3, 3, 2, 2, 3, 0, 3, 0]),
      (7, []),
      (14, []),
      (0, [3, 3, 2, 1, 1, 0, 1, 0, 1, 2, 3, 2, 3, 3, 0, 3, 3, 3, 2, 3, 0, 3, 3, 2, 2, 3, 0, 3, 0]),
      (9, []),
      (20, [])]]

private theorem transitions1_valid (s : Fin 4) (t : Fin 22) :
    generators1 s * transversals1 t =
      transversals1 (transitions1[s][t]).1 *
        ((transitions1[s][t]).2.map generators2).prod := by
  have h : ∀ (i : Fin 4) (j : Fin 22) (x : Fin 23),
      (generators1 i * transversals1 j) x =
        (transversals1 (transitions1[i][j]).1 *
          ((transitions1[i][j]).2.map generators2).prod) x := by
    decide +kernel
  exact Equiv.ext (h s t)

/-- Target representatives and next-level words for every signed step at level 2. -/
private def transitions2 : Vector (Vector (Fin 21 × List (Fin 4)) 21) 4 :=
  #v[
    #v[
      (12, []),
      (17, [0, 0, 3, 0, 1, 0, 3]),
      (16, [2, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3]),
      (11, []),
      (4, [2, 3, 2, 1, 2, 1, 1, 2, 3, 0, 3, 2, 1, 0, 1, 0]),
      (1, [2, 3, 2, 1, 2, 1, 0, 3, 0, 0, 3, 2, 1, 0, 1, 0]),
      (6, [1, 0, 0, 1, 0, 3, 2, 1, 2, 3, 2, 3, 0, 1, 2, 1, 0, 3]),
      (20, []),
      (3, []),
      (15, [0, 3, 0, 1, 0, 1, 1, 2, 3, 0, 3, 2, 1, 0, 1, 0]),
      (9, [2, 2, 3, 2, 1, 2, 2, 3, 0, 1, 2, 1, 0, 3]),
      (8, []),
      (14, []),
      (7, []),
      (0, []),
      (10, [1, 2, 1, 2, 3, 0, 3, 2, 1, 0, 1, 0]),
      (19, [0, 1, 2, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 3, 0, 1, 2, 1, 0, 3]),
      (5, []),
      (18, [0, 3, 3, 2, 3, 2, 1, 2, 1, 0]),
      (2, []),
      (13, [])],
    #v[
      (20, []),
      (10, []),
      (12, []),
      (19, [3, 2, 3, 3, 0, 3, 0, 1, 0, 1, 2]),
      (11, []),
      (1, [0, 3, 3, 2, 3, 2, 1, 2, 1]),
      (9, [0, 1, 0, 3, 2, 1, 2, 3, 2, 3, 0, 1, 2, 1, 0, 3]),
      (18, [2, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 3, 0, 1, 2, 1, 0, 3]),
      (8, [3, 3, 2, 3, 2, 1, 2, 2, 3, 0, 1, 2, 1, 0, 3]),
      (7, []),
      (3, []),
      (0, []),
      (16, []),
      (2, [3, 2, 3, 2]),
      (6, []),
      (4, []),
      (17, [0, 1, 0, 1]),
      (13, []),
      (14, []),
      (5, [0, 1, 2, 1, 0, 3, 0, 0, 3, 2, 1, 0, 1, 0]),
      (15, [])],
    #v[
      (14, []),
      (5, [0, 0, 3, 0, 1, 0, 3]),
      (19, []),
      (8, []),
      (4, [3, 2, 1, 2, 1, 0, 3, 0, 1, 0, 3]),
      (17, []),
      (6, [2, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 3, 0, 1, 2, 1, 0, 3]),
      (13, []),
      (11, []),
      (10, [0, 3, 3, 2, 3, 2, 1, 2, 1, 0]),
      (15, [3, 0, 1, 1, 2, 3, 0, 3, 2, 1, 0, 1]),
      (3, []),
      (0, []),
      (20, []),
      (12, []),
      (9, [3, 0, 3, 3, 2, 3, 2, 1, 2, 1, 1, 2, 3, 0, 3, 2, 1, 0, 1, 0]),
      (2, [0, 1, 2, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 3, 0, 1, 2, 1, 0, 3]),
      (1, [2, 3, 2, 1, 2, 1, 0, 3, 0, 0, 3, 2, 1, 0, 1, 0]),
      (18, [2, 2, 3, 2, 1, 2, 2, 3, 0, 1, 2, 1, 0, 3]),
      (16, [2, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3]),
      (7, [])],
    #v[
      (11, []),
      (5, [2, 3, 2, 1, 2, 2, 3, 0, 1, 2, 1, 0, 3]),
      (13, [0, 1, 0, 1]),
      (10, []),
      (15, []),
      (19, [1, 0, 1, 2, 3, 2, 3, 0, 1, 2, 1, 0, 3]),
      (14, []),
      (9, []),
      (8, [3, 2, 1, 1, 2, 1, 2, 3, 0, 1, 1, 2, 3, 0, 3, 2, 1, 0, 1, 0]),
      (6, [2, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 3, 0, 1, 2, 1, 0, 3]),
      (1, []),
      (4, []),
      (2, []),
      (17, []),
      (18, []),
      (20, []),
      (12, []),
      (16, [3, 2, 3, 2]),
      (7, [0, 1, 0, 3, 2, 1, 2, 3, 2, 3, 0, 1, 2, 1, 0, 3]),
      (3, [3, 2, 3, 3, 0, 3, 0, 1, 0, 1, 2]),
      (0, [])]]

private theorem transitions2_valid (s : Fin 4) (t : Fin 21) :
    generators2 s * transversals2 t =
      transversals2 (transitions2[s][t]).1 *
        ((transitions2[s][t]).2.map generators3).prod := by
  have h : ∀ (i : Fin 4) (j : Fin 21) (x : Fin 23),
      (generators2 i * transversals2 j) x =
        (transversals2 (transitions2[i][j]).1 *
          ((transitions2[i][j]).2.map generators3).prod) x := by
    decide +kernel
  exact Equiv.ext (h s t)

/-- Target representatives and next-level words for every signed step at level 3. -/
private def transitions3 : Vector (Vector (Fin 20 × List (Fin 6)) 20) 4 :=
  #v[
    #v[
      (0, [4, 3, 5]),
      (18, []),
      (9, []),
      (13, []),
      (15, []),
      (3, []),
      (10, [3, 5]),
      (6, []),
      (4, []),
      (16, [3, 5, 4]),
      (7, [2, 0]),
      (11, [3, 5, 0]),
      (17, [3, 4, 5]),
      (5, []),
      (12, []),
      (8, []),
      (2, [4, 2, 0]),
      (14, [2, 4, 0]),
      (19, [4, 5]),
      (1, [2, 4])],
    #v[
      (15, []),
      (7, [4, 3, 5, 0]),
      (2, [5, 3, 4]),
      (0, []),
      (10, []),
      (19, []),
      (16, []),
      (11, [5, 3, 4]),
      (6, []),
      (13, []),
      (12, []),
      (1, []),
      (4, []),
      (18, []),
      (14, [3, 4, 5, 0]),
      (3, []),
      (8, []),
      (5, []),
      (9, []),
      (17, [])],
    #v[
      (0, [5, 4, 5, 0]),
      (19, [4, 5]),
      (16, [3, 5, 4]),
      (5, []),
      (8, []),
      (13, []),
      (7, []),
      (10, [3, 5]),
      (15, []),
      (2, []),
      (6, [2, 0]),
      (11, [5, 3]),
      (14, []),
      (3, []),
      (17, [3, 4, 5]),
      (4, []),
      (9, [4, 2, 0]),
      (12, [2, 4, 0]),
      (1, []),
      (18, [2, 4])],
    #v[
      (3, []),
      (11, []),
      (2, [4, 3, 5, 0]),
      (15, []),
      (12, []),
      (17, []),
      (8, []),
      (1, [5, 3, 4]),
      (16, []),
      (18, []),
      (4, []),
      (7, [4, 3, 5, 0]),
      (10, []),
      (9, []),
      (14, [4, 5, 3]),
      (0, []),
      (6, []),
      (19, []),
      (13, []),
      (5, [])]]

private theorem transitions3_valid (s : Fin 4) (t : Fin 20) :
    generators3 s * transversals3 t =
      transversals3 (transitions3[s][t]).1 *
        ((transitions3[s][t]).2.map generators4).prod := by
  have h : ∀ (i : Fin 4) (j : Fin 20) (x : Fin 23),
      (generators3 i * transversals3 j) x =
        (transversals3 (transitions3[i][j]).1 *
          ((transitions3[i][j]).2.map generators4).prod) x := by
    decide +kernel
  exact Equiv.ext (h s t)

/-- Target representatives and next-level words for every signed step at level 4. -/
private def transitions4 : Vector (Vector (Fin 16 × List (Fin 2)) 16) 6 :=
  #v[
    #v[
      (0, [0]),
      (10, [0]),
      (7, []),
      (1, [1]),
      (12, []),
      (6, [0]),
      (9, [0]),
      (15, [1]),
      (4, []),
      (5, [0]),
      (3, []),
      (14, [0]),
      (8, []),
      (11, [1]),
      (13, []),
      (2, [0])],
    #v[
      (4, []),
      (11, []),
      (10, []),
      (9, [0]),
      (0, []),
      (15, []),
      (14, []),
      (13, []),
      (12, [0]),
      (3, [1]),
      (2, []),
      (1, []),
      (8, [1]),
      (7, []),
      (6, []),
      (5, [])],
    #v[
      (11, []),
      (9, [0]),
      (6, [0]),
      (4, []),
      (15, []),
      (7, []),
      (10, [0]),
      (12, [1]),
      (1, [1]),
      (8, []),
      (2, [0]),
      (13, []),
      (5, [0]),
      (0, []),
      (14, [0]),
      (3, [])],
    #v[
      (0, [1]),
      (3, [0]),
      (15, [1]),
      (10, []),
      (8, []),
      (9, [1]),
      (5, [1]),
      (2, []),
      (12, []),
      (6, [1]),
      (1, [1]),
      (13, [0]),
      (4, []),
      (14, []),
      (11, [1]),
      (7, [0])],
    #v[
      (4, []),
      (11, []),
      (10, []),
      (9, [0]),
      (0, []),
      (15, []),
      (14, []),
      (13, []),
      (12, [0]),
      (3, [1]),
      (2, []),
      (1, []),
      (8, [1]),
      (7, []),
      (6, []),
      (5, [])],
    #v[
      (13, []),
      (8, [0]),
      (10, [1]),
      (15, []),
      (3, []),
      (12, [1]),
      (2, [1]),
      (5, []),
      (9, []),
      (1, [1]),
      (6, [1]),
      (0, []),
      (7, [0]),
      (11, []),
      (14, [1]),
      (4, [])]]

private theorem transitions4_valid (s : Fin 6) (t : Fin 16) :
    generators4 s * transversals4 t =
      transversals4 (transitions4[s][t]).1 *
        ((transitions4[s][t]).2.map generators5).prod := by
  have h : ∀ (i : Fin 6) (j : Fin 16) (x : Fin 23),
      (generators4 i * transversals4 j) x =
        (transversals4 (transitions4[i][j]).1 *
          ((transitions4[i][j]).2.map generators5).prod) x := by
    decide +kernel
  exact Equiv.ext (h s t)

/-- Target representatives and next-level words for every signed step at level 5. -/
private def transitions5 : Vector (Vector (Fin 3 × List (Fin 0)) 3) 2 :=
  #v[
    #v[
      (1, []),
      (2, []),
      (0, [])],
    #v[
      (2, []),
      (0, []),
      (1, [])]]

private theorem transitions5_valid (s : Fin 2) (t : Fin 3) :
    generators5 s * transversals5 t =
      transversals5 (transitions5[s][t]).1 *
        ((transitions5[s][t]).2.map generators6).prod := by
  have h : ∀ (i : Fin 2) (j : Fin 3) (x : Fin 23),
      (generators5 i * transversals5 j) x =
        (transversals5 (transitions5[i][j]).1 *
          ((transitions5[i][j]).2.map generators6).prod) x := by
    decide +kernel
  exact Equiv.ext (h s t)

/-- Numbers of signed generators, including the empty terminal family. -/
def generatorSize (i : Fin 7) : ℕ := (#v[4, 4, 4, 4, 6, 2, 0])[i]

/-- Numbers of representatives in the six covers. -/
def transversalSize (i : Fin 6) : ℕ := (#v[23, 22, 21, 20, 16, 3])[i]

/-- The concrete generator family at each level. -/
def strongGenerators : (level : Fin 7) → Fin (generatorSize level) → Equiv.Perm (Fin 23)
  | 0 => fun i ↦ generators0 i
  | 1 => fun i ↦ generators1 i
  | 2 => fun i ↦ generators2 i
  | 3 => fun i ↦ generators3 i
  | 4 => fun i ↦ generators4 i
  | 5 => fun i ↦ generators5 i
  | 6 => fun i ↦ generators6 i

/-- The concrete representatives at each nonterminal level. -/
noncomputable def representatives : (level : Fin 6) →
    Fin (transversalSize level) → Equiv.Perm (Fin 23)
  | 0 => fun i ↦ transversals0 i
  | 1 => fun i ↦ transversals1 i
  | 2 => fun i ↦ transversals2 i
  | 3 => fun i ↦ transversals3 i
  | 4 => fun i ↦ transversals4 i
  | 5 => fun i ↦ transversals5 i

/-- The target representative and correction word of a generator step. -/
def transitions : (level : Fin 6) → Fin (generatorSize level.castSucc) →
    Fin (transversalSize level) →
      Fin (transversalSize level) × List (Fin (generatorSize level.succ))
  | 0 => fun i j ↦ transitions0[i][j]
  | 1 => fun i j ↦ transitions1[i][j]
  | 2 => fun i j ↦ transitions2[i][j]
  | 3 => fun i j ↦ transitions3[i][j]
  | 4 => fun i j ↦ transitions4[i][j]
  | 5 => fun i j ↦ transitions5[i][j]

/-- Each signed generator step is its target representative times its correction word. -/
theorem transitions_valid (level : Fin 6)
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
  · exact transitions5_valid s t

end TauCeti.Sporadic.Mathieu.M23Cover
