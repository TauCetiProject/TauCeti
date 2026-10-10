/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M24LowerBound
public import TauCeti.GroupTheory.Subgroup.GeneratorCover
import Mathlib.Tactic.FinCases
import all TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.Permutation

/-!
# The order of the M24 permutation image

Seven finite covers have sizes `24, 23, 22, 21, 20, 16, 3`. Explicit point tables
give the generators and representatives; each stored transition is checked at every
point. Its residue is a word in the next level's generators and their inverses.

For each generator, the transition targets permute the representative indices.
Taking preimages and inverting residues therefore proves every inverse step without
storing a second transition table. The empty terminal generator family closes the
cover argument. The resulting upper bound and the word witnesses in `M24LowerBound`
give image order 244823040, without a finiteness or faithfulness claim for the presentation.
-/

public section

namespace TauCeti.Sporadic.Mathieu

/-- Permutations specified by point maps with checked two-sided inverses. -/
private def tablePerms {n : ℕ} (p q : Vector (Vector (Fin 24) 24) n)
    (h : ∀ (i : Fin n) (x : Fin 24), p[i][q[i][x]] = x ∧ q[i][p[i][x]] = x)
    (i : Fin n) : Equiv.Perm (Fin 24) where
  toFun x := p[i][x]
  invFun x := q[i][x]
  left_inv x := (h i x).2
  right_inv x := (h i x).1

/-- A signed alphabet, with positive generators followed by their inverses. -/
private def signedGenerator {n : ℕ} (s : Fin n → Equiv.Perm (Fin 24))
    (i : Fin (n + n)) : Equiv.Perm (Fin 24) :=
  if h : i.val < n then s ⟨i.val, h⟩ else (s ⟨i.val - n, by omega⟩)⁻¹

/-- Evaluate a word in the signed alphabet of a level. -/
private def evalWord {n : ℕ} (s : Fin n → Equiv.Perm (Fin 24))
    (w : List (Fin (n + n))) : Equiv.Perm (Fin 24) :=
  (w.map (signedGenerator s)).prod

private theorem evalWord_mem {n : ℕ} (s : Fin n → Equiv.Perm (Fin 24))
    (w : List (Fin (n + n))) : evalWord s w ∈ Subgroup.closure (Set.range s) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  unfold signedGenerator
  split_ifs
  · exact Subgroup.subset_closure ⟨_, rfl⟩
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨_, rfl⟩)

/-- Point images of the level-0 generators. -/
private def generatorImages0 : Vector (Vector (Fin 24) 24) 2 := #v[
  #v[11, 4, 5, 10, 1, 2, 14, 17, 23, 20, 3, 0, 15, 19, 6, 12, 18, 7, 16, 13, 9, 22, 21, 8],
  #v[0, 11, 2, 16, 4, 10, 14, 7, 8, 15, 22, 21, 12, 9, 19, 13, 20, 23, 17, 6, 3, 1, 5, 18]]

/-- Inverse point images of the level-0 generators. -/
private def generatorInverseImages0 : Vector (Vector (Fin 24) 24) 2 := #v[
  #v[11, 4, 5, 10, 1, 2, 14, 17, 23, 20, 3, 0, 15, 19, 6, 12, 18, 7, 16, 13, 9, 22, 21, 8],
  #v[0, 21, 2, 20, 4, 22, 19, 7, 8, 13, 5, 1, 12, 15, 6, 9, 3, 18, 23, 14, 16, 11, 10, 17]]

/-- The level-0 generators with checked inverse tables. -/
private def generators0 : Fin 2 → Equiv.Perm (Fin 24) :=
  tablePerms generatorImages0 generatorInverseImages0 (by decide +kernel)

/-- Point images of the level-0 representatives, identity first. -/
private def transversalImages0 : Vector (Vector (Fin 24) 24) 24 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #v[1, 4, 22, 5, 21, 2, 6, 18, 17, 16, 20, 0, 9, 14, 19, 12, 23, 7, 3, 15, 13, 10, 11, 8],
  #v[2, 0, 18, 4, 11, 3, 20, 23, 9, 21, 7, 22, 14, 13, 6, 19, 17, 8, 12, 10, 15, 5, 1, 16],
  #v[3, 22, 9, 0, 11, 21, 12, 23, 10, 2, 8, 4, 6, 14, 13, 20, 17, 16, 19, 18, 15, 5, 1, 7],
  #v[4, 1, 21, 2, 22, 5, 14, 16, 7, 18, 9, 11, 20, 6, 13, 15, 8, 17, 10, 12, 19, 3, 0, 23],
  #v[5, 11, 16, 1, 0, 10, 9, 8, 20, 22, 17, 21, 6, 19, 14, 13, 7, 23, 15, 3, 12, 2, 4, 18],
  #v[6, 15, 14, 4, 11, 21, 3, 23, 10, 1, 7, 5, 12, 19, 13, 8, 22, 2, 9, 18, 17, 0, 16, 20],
  #v[7, 5, 15, 22, 2, 1, 19, 9, 4, 3, 16, 0, 6, 20, 10, 21, 23, 12, 13, 17, 14, 18, 11, 8],
  #v[8, 5, 15, 4, 3, 1, 20, 10, 0, 21, 7, 22, 13, 12, 18, 2, 23, 19, 14, 17, 6, 9, 11, 16],
  #v[9, 3, 19, 11, 4, 0, 15, 7, 2, 5, 23, 1, 13, 14, 12, 18, 16, 10, 6, 8, 20, 21, 22, 17],
  #v[10, 21, 20, 11, 0, 22, 15, 8, 3, 5, 23, 1, 14, 6, 19, 9, 7, 18, 13, 16, 12, 2, 4, 17],
  #v[11, 4, 5, 10, 1, 2, 14, 17, 23, 20, 3, 0, 15, 19, 6, 12, 18, 7, 16, 13, 9, 22, 21, 8],
  #v[12, 18, 14, 22, 1, 11, 19, 17, 5, 3, 16, 0, 20, 13, 15, 7, 9, 21, 6, 23, 10, 4, 2, 8],
  #v[13, 20, 14, 1, 4, 0, 9, 7, 2, 22, 17, 21, 15, 6, 12, 23, 3, 5, 19, 8, 16, 11, 10, 18],
  #v[14, 13, 19, 4, 21, 1, 16, 18, 22, 11, 7, 10, 12, 6, 9, 8, 5, 2, 15, 17, 23, 0, 20, 3],
  #v[15, 16, 6, 21, 4, 0, 13, 7, 2, 10, 18, 11, 9, 19, 12, 17, 20, 22, 14, 8, 3, 1, 5, 23],
  #v[16, 5, 15, 0, 21, 1, 12, 18, 22, 2, 8, 4, 14, 19, 9, 3, 23, 20, 6, 17, 13, 10, 11, 7],
  #v[17, 2, 12, 21, 5, 4, 13, 20, 1, 10, 18, 11, 14, 9, 3, 22, 8, 15, 19, 7, 6, 16, 0, 23],
  #v[18, 2, 12, 11, 22, 4, 15, 16, 21, 5, 23, 1, 6, 13, 20, 10, 8, 9, 14, 7, 19, 3, 0, 17],
  #v[19, 9, 6, 4, 1, 11, 20, 17, 5, 21, 7, 22, 12, 14, 15, 8, 10, 2, 13, 23, 18, 0, 3, 16],
  #v[20, 10, 13, 0, 1, 11, 12, 17, 5, 2, 8, 4, 19, 6, 15, 16, 18, 3, 14, 23, 9, 22, 21, 7],
  #v[21, 4, 10, 22, 11, 2, 19, 23, 18, 3, 16, 0, 13, 6, 14, 12, 17, 7, 20, 9, 15, 5, 1, 8],
  #v[22, 1, 3, 21, 0, 5, 13, 8, 16, 10, 18, 11, 19, 14, 6, 15, 7, 17, 9, 20, 12, 2, 4, 23],
  #v[23, 2, 12, 1, 10, 4, 9, 3, 11, 22, 17, 21, 19, 15, 16, 5, 8, 13, 6, 7, 14, 20, 0, 18]]

/-- The level-0 representatives from their checked bijective point maps. -/
private noncomputable def transversals0 (i : Fin 24) : Equiv.Perm (Fin 24) :=
  Equiv.ofBijective (fun x : Fin 24 ↦ transversalImages0[i][x]) (by
    have h : ∀ j : Fin 24, Function.Bijective
        (fun x : Fin 24 ↦ transversalImages0[j][x]) := by decide +kernel
    exact h i)

/-- Point images of the level-1 generators. -/
private def generatorImages1 : Vector (Vector (Fin 24) 24) 3 := #v[
  #v[0, 11, 2, 16, 4, 10, 14, 7, 8, 15, 22, 21, 12, 9, 19, 13, 20, 23, 17, 6, 3, 1, 5, 18],
  #v[0, 11, 1, 3, 5, 18, 20, 12, 8, 17, 15, 2, 21, 6, 10, 14, 16, 23, 4, 19, 13, 7, 22, 9],
  #v[0, 1, 16, 3, 9, 23, 5, 2, 20, 22, 10, 21, 15, 8, 12, 14, 7, 17, 18, 11, 13, 19, 4, 6]]

/-- Inverse point images of the level-1 generators. -/
private def generatorInverseImages1 : Vector (Vector (Fin 24) 24) 3 := #v[
  #v[0, 21, 2, 20, 4, 22, 19, 7, 8, 13, 5, 1, 12, 15, 6, 9, 3, 18, 23, 14, 16, 11, 10, 17],
  #v[0, 2, 11, 3, 18, 4, 13, 21, 8, 23, 14, 1, 7, 20, 15, 10, 16, 9, 5, 19, 6, 12, 22, 17],
  #v[0, 1, 7, 3, 22, 6, 23, 16, 13, 4, 10, 19, 14, 20, 15, 12, 2, 17, 18, 21, 8, 11, 9, 5]]

/-- The level-1 generators with checked inverse tables. -/
private def generators1 : Fin 3 → Equiv.Perm (Fin 24) :=
  tablePerms generatorImages1 generatorInverseImages1 (by decide +kernel)

/-- Point images of the level-1 representatives, identity first. -/
private def transversalImages1 : Vector (Vector (Fin 24) 24) 23 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #v[0, 2, 11, 3, 18, 4, 13, 21, 8, 23, 14, 1, 7, 20, 15, 10, 16, 9, 5, 19, 6, 12, 22, 17],
  #v[0, 3, 11, 20, 23, 13, 8, 14, 16, 19, 12, 21, 2, 15, 6, 5, 7, 10, 17, 1, 22, 9, 4, 18],
  #v[0, 4, 6, 13, 19, 22, 2, 12, 3, 8, 9, 21, 5, 16, 14, 23, 10, 20, 15, 1, 7, 11, 17, 18],
  #v[0, 5, 20, 6, 19, 22, 1, 21, 3, 8, 17, 7, 18, 16, 10, 9, 15, 13, 14, 11, 12, 2, 23, 4],
  #v[0, 6, 20, 9, 15, 4, 21, 2, 3, 8, 18, 11, 13, 19, 10, 5, 16, 17, 14, 12, 7, 1, 22, 23],
  #v[0, 7, 1, 13, 5, 22, 19, 12, 8, 6, 18, 11, 21, 14, 20, 17, 3, 4, 9, 10, 16, 2, 15, 23],
  #v[0, 8, 1, 2, 17, 12, 13, 23, 3, 15, 14, 19, 7, 4, 21, 9, 16, 6, 18, 11, 10, 20, 22, 5],
  #v[0, 9, 11, 22, 23, 4, 1, 14, 16, 15, 13, 3, 2, 5, 8, 19, 20, 17, 18, 6, 7, 21, 12, 10],
  #v[0, 10, 3, 14, 6, 5, 11, 1, 16, 8, 23, 7, 17, 20, 22, 15, 13, 9, 19, 21, 12, 2, 18, 4],
  #v[0, 11, 2, 16, 4, 10, 14, 7, 8, 15, 22, 21, 12, 9, 19, 13, 20, 23, 17, 6, 3, 1, 5, 18],
  #v[0, 12, 11, 6, 18, 22, 19, 21, 8, 20, 4, 2, 7, 10, 13, 23, 3, 5, 17, 15, 16, 1, 14, 9],
  #v[0, 13, 6, 23, 10, 18, 12, 11, 3, 8, 5, 1, 20, 19, 14, 4, 16, 9, 15, 7, 21, 2, 22, 17],
  #v[0, 14, 3, 15, 13, 4, 1, 2, 16, 8, 17, 21, 9, 6, 22, 10, 20, 23, 19, 12, 7, 11, 5, 18],
  #v[0, 15, 21, 5, 18, 4, 11, 19, 20, 13, 9, 16, 2, 10, 8, 6, 3, 23, 17, 14, 7, 1, 12, 22],
  #v[0, 16, 21, 3, 18, 9, 8, 19, 20, 6, 12, 1, 2, 13, 14, 10, 7, 22, 23, 11, 5, 15, 4, 17],
  #v[0, 17, 8, 4, 12, 10, 1, 7, 20, 15, 23, 14, 16, 11, 5, 19, 2, 18, 9, 6, 3, 21, 13, 22],
  #v[0, 18, 8, 4, 12, 5, 21, 7, 16, 9, 17, 6, 3, 1, 22, 14, 2, 23, 13, 19, 20, 11, 15, 10],
  #v[0, 19, 16, 13, 9, 4, 11, 2, 20, 8, 23, 1, 15, 14, 5, 22, 3, 18, 6, 12, 7, 21, 10, 17],
  #v[0, 20, 1, 16, 17, 15, 8, 6, 3, 14, 12, 11, 2, 9, 19, 22, 7, 5, 18, 21, 10, 13, 4, 23],
  #v[0, 21, 2, 20, 4, 22, 19, 7, 8, 13, 5, 1, 12, 15, 6, 9, 3, 18, 23, 14, 16, 11, 10, 17],
  #v[0, 22, 16, 19, 14, 10, 21, 11, 20, 8, 18, 7, 23, 3, 5, 13, 9, 15, 6, 1, 12, 2, 17, 4],
  #v[0, 23, 8, 4, 12, 22, 11, 7, 3, 13, 18, 19, 20, 21, 10, 6, 2, 17, 15, 14, 16, 1, 9, 5]]

/-- The level-1 representatives from their checked bijective point maps. -/
private noncomputable def transversals1 (i : Fin 23) : Equiv.Perm (Fin 24) :=
  Equiv.ofBijective (fun x : Fin 24 ↦ transversalImages1[i][x]) (by
    have h : ∀ j : Fin 23, Function.Bijective
        (fun x : Fin 24 ↦ transversalImages1[j][x]) := by decide +kernel
    exact h i)

/-- Point images of the level-2 generators. -/
private def generatorImages2 : Vector (Vector (Fin 24) 24) 3 := #v[
  #v[0, 1, 11, 16, 18, 14, 15, 21, 8, 10, 22, 12, 7, 23, 19, 20, 6, 17, 9, 13, 3, 2, 4, 5],
  #v[0, 1, 16, 3, 9, 23, 5, 2, 20, 22, 10, 21, 15, 8, 12, 14, 7, 17, 18, 11, 13, 19, 4, 6],
  #v[0, 1, 20, 7, 15, 22, 12, 2, 3, 19, 4, 6, 13, 5, 21, 8, 9, 14, 23, 10, 16, 11, 18, 17]]

/-- Inverse point images of the level-2 generators. -/
private def generatorInverseImages2 : Vector (Vector (Fin 24) 24) 3 := #v[
  #v[0, 1, 21, 20, 22, 23, 16, 12, 8, 18, 9, 2, 11, 19, 5, 6, 3, 17, 4, 14, 15, 7, 10, 13],
  #v[0, 1, 7, 3, 22, 6, 23, 16, 13, 4, 10, 19, 14, 20, 15, 12, 2, 17, 18, 21, 8, 11, 9, 5],
  #v[0, 1, 7, 8, 10, 13, 11, 3, 15, 16, 19, 21, 6, 12, 17, 4, 20, 23, 22, 9, 2, 14, 5, 18]]

/-- The level-2 generators with checked inverse tables. -/
private def generators2 : Fin 3 → Equiv.Perm (Fin 24) :=
  tablePerms generatorImages2 generatorInverseImages2 (by decide +kernel)

/-- Point images of the level-2 representatives, identity first. -/
private def transversalImages2 : Vector (Vector (Fin 24) 24) 22 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #v[0, 1, 3, 20, 18, 13, 23, 21, 15, 10, 9, 7, 6, 8, 11, 5, 12, 17, 4, 2, 19, 14, 22, 16],
  #v[0, 1, 4, 6, 11, 19, 21, 14, 2, 17, 5, 20, 9, 18, 3, 15, 22, 13, 12, 16, 8, 7, 10, 23],
  #v[0, 1, 5, 21, 23, 4, 15, 16, 6, 10, 3, 12, 7, 18, 19, 2, 8, 13, 9, 17, 22, 20, 14, 11],
  #v[0, 1, 6, 16, 10, 5, 14, 11, 3, 4, 22, 2, 20, 8, 7, 19, 21, 17, 9, 12, 23, 13, 18, 15],
  #v[0, 1, 7, 3, 22, 6, 23, 16, 13, 4, 10, 19, 14, 20, 15, 12, 2, 17, 18, 21, 8, 11, 9, 5],
  #v[0, 1, 8, 16, 12, 9, 14, 7, 3, 21, 22, 23, 20, 6, 11, 13, 4, 15, 5, 10, 2, 19, 18, 17],
  #v[0, 1, 9, 7, 19, 17, 22, 20, 16, 18, 4, 11, 8, 3, 13, 21, 2, 14, 23, 6, 5, 10, 15, 12],
  #v[0, 1, 10, 21, 13, 17, 4, 3, 6, 9, 18, 12, 8, 16, 23, 2, 11, 19, 5, 15, 14, 22, 20, 7],
  #v[0, 1, 11, 16, 18, 14, 15, 21, 8, 10, 22, 12, 7, 23, 19, 20, 6, 17, 9, 13, 3, 2, 4, 5],
  #v[0, 1, 12, 6, 9, 19, 20, 2, 8, 22, 4, 7, 21, 5, 13, 3, 15, 17, 10, 23, 16, 11, 18, 14],
  #v[0, 1, 13, 2, 14, 4, 15, 16, 3, 11, 9, 5, 8, 23, 19, 20, 22, 12, 6, 10, 7, 21, 18, 17],
  #v[0, 1, 14, 2, 5, 18, 20, 6, 15, 22, 16, 7, 21, 9, 13, 11, 8, 23, 10, 17, 4, 3, 19, 12],
  #v[0, 1, 15, 12, 6, 10, 11, 21, 20, 14, 22, 16, 19, 23, 7, 8, 18, 5, 13, 9, 3, 2, 4, 17],
  #v[0, 1, 16, 3, 9, 23, 5, 2, 20, 22, 10, 21, 15, 8, 12, 14, 7, 17, 18, 11, 13, 19, 4, 6],
  #v[0, 1, 17, 7, 13, 22, 2, 11, 4, 5, 20, 3, 14, 16, 12, 21, 15, 18, 19, 23, 10, 8, 9, 6],
  #v[0, 1, 18, 12, 14, 17, 10, 15, 3, 4, 22, 2, 8, 20, 19, 7, 21, 5, 13, 16, 23, 9, 6, 11],
  #v[0, 1, 19, 13, 4, 6, 7, 15, 20, 18, 22, 16, 21, 11, 23, 5, 3, 17, 9, 12, 14, 2, 10, 8],
  #v[0, 1, 20, 7, 15, 22, 12, 2, 3, 19, 4, 6, 13, 5, 21, 8, 9, 14, 23, 10, 16, 11, 18, 17],
  #v[0, 1, 21, 20, 22, 23, 16, 12, 8, 18, 9, 2, 11, 19, 5, 6, 3, 17, 4, 14, 15, 7, 10, 13],
  #v[0, 1, 22, 2, 11, 17, 4, 13, 7, 18, 9, 21, 20, 3, 8, 19, 16, 12, 6, 5, 23, 10, 14, 15],
  #v[0, 1, 23, 2, 10, 6, 15, 19, 3, 22, 9, 7, 8, 13, 16, 21, 11, 17, 4, 14, 5, 20, 18, 12]]

/-- The level-2 representatives from their checked bijective point maps. -/
private noncomputable def transversals2 (i : Fin 22) : Equiv.Perm (Fin 24) :=
  Equiv.ofBijective (fun x : Fin 24 ↦ transversalImages2[i][x]) (by
    have h : ∀ j : Fin 22, Function.Bijective
        (fun x : Fin 24 ↦ transversalImages2[j][x]) := by decide +kernel
    exact h i)

/-- Point images of the level-3 generators. -/
private def generatorImages3 : Vector (Vector (Fin 24) 24) 2 := #v[
  #v[0, 1, 2, 20, 10, 8, 21, 3, 14, 7, 11, 19, 5, 15, 17, 9, 13, 6, 4, 22, 16, 12, 23, 18],
  #v[0, 1, 2, 21, 9, 7, 19, 13, 3, 22, 18, 20, 11, 15, 12, 23, 14, 17, 4, 8, 16, 6, 10, 5]]

/-- Inverse point images of the level-3 generators. -/
private def generatorInverseImages3 : Vector (Vector (Fin 24) 24) 2 := #v[
  #v[0, 1, 2, 7, 18, 12, 17, 9, 5, 15, 4, 10, 21, 16, 8, 13, 20, 14, 23, 11, 3, 6, 19, 22],
  #v[0, 1, 2, 8, 18, 23, 21, 5, 19, 4, 22, 12, 14, 7, 16, 13, 20, 17, 10, 6, 11, 3, 9, 15]]

/-- The level-3 generators with checked inverse tables. -/
private def generators3 : Fin 2 → Equiv.Perm (Fin 24) :=
  tablePerms generatorImages3 generatorInverseImages3 (by decide +kernel)

/-- Point images of the level-3 representatives, identity first. -/
private def transversalImages3 : Vector (Vector (Fin 24) 24) 21 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #v[0, 1, 2, 4, 15, 3, 16, 13, 14, 7, 10, 18, 21, 11, 23, 20, 8, 19, 9, 22, 5, 17, 12, 6],
  #v[0, 1, 2, 5, 23, 22, 6, 12, 11, 18, 19, 21, 8, 9, 20, 16, 3, 14, 4, 17, 10, 7, 15, 13],
  #v[0, 1, 2, 6, 15, 9, 11, 16, 7, 19, 23, 3, 10, 13, 21, 22, 8, 14, 18, 5, 20, 17, 4, 12],
  #v[0, 1, 2, 7, 18, 12, 17, 9, 5, 15, 4, 10, 21, 16, 8, 13, 20, 14, 23, 11, 3, 6, 19, 22],
  #v[0, 1, 2, 8, 18, 23, 21, 5, 19, 4, 22, 12, 14, 7, 16, 13, 20, 17, 10, 6, 11, 3, 9, 15],
  #v[0, 1, 2, 9, 23, 21, 14, 15, 12, 13, 18, 4, 6, 20, 5, 16, 3, 8, 22, 10, 7, 17, 11, 19],
  #v[0, 1, 2, 10, 19, 11, 7, 5, 20, 12, 21, 17, 22, 16, 14, 18, 9, 6, 23, 15, 3, 8, 13, 4],
  #v[0, 1, 2, 11, 22, 19, 3, 8, 16, 5, 12, 6, 23, 13, 17, 4, 7, 21, 18, 9, 20, 14, 15, 10],
  #v[0, 1, 2, 12, 7, 3, 22, 15, 20, 23, 4, 16, 19, 9, 5, 18, 17, 6, 10, 14, 13, 21, 11, 8],
  #v[0, 1, 2, 13, 4, 11, 17, 22, 7, 23, 9, 18, 6, 14, 3, 15, 16, 12, 5, 20, 21, 19, 8, 10],
  #v[0, 1, 2, 14, 4, 18, 12, 8, 22, 10, 23, 5, 17, 3, 13, 15, 16, 6, 11, 21, 19, 20, 7, 9],
  #v[0, 1, 2, 15, 22, 6, 8, 13, 21, 16, 23, 18, 17, 3, 12, 20, 7, 5, 19, 4, 9, 14, 10, 11],
  #v[0, 1, 2, 16, 11, 14, 12, 20, 17, 3, 19, 22, 8, 9, 6, 7, 15, 21, 10, 23, 13, 5, 18, 4],
  #v[0, 1, 2, 17, 10, 4, 5, 14, 23, 11, 18, 8, 6, 20, 15, 9, 13, 21, 19, 12, 22, 16, 3, 7],
  #v[0, 1, 2, 18, 13, 7, 20, 16, 8, 9, 4, 23, 6, 10, 22, 3, 5, 11, 15, 19, 12, 14, 21, 17],
  #v[0, 1, 2, 19, 10, 15, 3, 23, 6, 18, 9, 14, 16, 5, 20, 7, 11, 17, 22, 21, 12, 8, 4, 13],
  #v[0, 1, 2, 20, 10, 8, 21, 3, 14, 7, 11, 19, 5, 15, 17, 9, 13, 6, 4, 22, 16, 12, 23, 18],
  #v[0, 1, 2, 21, 9, 7, 19, 13, 3, 22, 18, 20, 11, 15, 12, 23, 14, 17, 4, 8, 16, 6, 10, 5],
  #v[0, 1, 2, 22, 5, 6, 12, 23, 11, 15, 4, 9, 19, 16, 7, 14, 21, 3, 10, 18, 13, 17, 20, 8],
  #v[0, 1, 2, 23, 15, 9, 21, 14, 12, 10, 6, 3, 19, 4, 11, 20, 8, 16, 18, 17, 22, 5, 13, 7]]

/-- The level-3 representatives from their checked bijective point maps. -/
private noncomputable def transversals3 (i : Fin 21) : Equiv.Perm (Fin 24) :=
  Equiv.ofBijective (fun x : Fin 24 ↦ transversalImages3[i][x]) (by
    have h : ∀ j : Fin 21, Function.Bijective
        (fun x : Fin 24 ↦ transversalImages3[j][x]) := by decide +kernel
    exact h i)

/-- Point images of the level-4 generators. -/
private def generatorImages4 : Vector (Vector (Fin 24) 24) 2 := #v[
  #v[0, 1, 2, 3, 22, 16, 19, 11, 8, 15, 20, 12, 7, 5, 10, 18, 13, 6, 9, 17, 14, 21, 23, 4],
  #v[0, 1, 2, 3, 18, 14, 11, 23, 7, 10, 22, 13, 5, 6, 12, 16, 21, 4, 17, 19, 20, 15, 9, 8]]

/-- Inverse point images of the level-4 generators. -/
private def generatorInverseImages4 : Vector (Vector (Fin 24) 24) 2 := #v[
  #v[0, 1, 2, 3, 23, 13, 17, 12, 8, 18, 14, 7, 11, 16, 20, 9, 5, 19, 15, 6, 10, 21, 4, 22],
  #v[0, 1, 2, 3, 17, 12, 13, 8, 23, 22, 9, 6, 14, 11, 5, 21, 15, 18, 4, 19, 20, 16, 10, 7]]

/-- The level-4 generators with checked inverse tables. -/
private def generators4 : Fin 2 → Equiv.Perm (Fin 24) :=
  tablePerms generatorImages4 generatorInverseImages4 (by decide +kernel)

/-- Point images of the level-4 representatives, identity first. -/
private def transversalImages4 : Vector (Vector (Fin 24) 24) 20 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #v[0, 1, 2, 3, 5, 23, 16, 20, 9, 8, 6, 7, 4, 10, 22, 18, 13, 11, 15, 21, 17, 14, 19, 12],
  #v[0, 1, 2, 3, 6, 7, 5, 8, 4, 23, 15, 19, 10, 12, 16, 21, 18, 9, 22, 17, 14, 13, 20, 11],
  #v[0, 1, 2, 3, 7, 11, 18, 14, 23, 4, 5, 8, 6, 15, 20, 22, 12, 19, 21, 13, 9, 16, 17, 10],
  #v[0, 1, 2, 3, 8, 6, 4, 5, 7, 17, 12, 23, 13, 21, 20, 10, 14, 19, 16, 11, 22, 15, 18, 9],
  #v[0, 1, 2, 3, 9, 21, 19, 13, 7, 16, 20, 5, 23, 14, 22, 17, 6, 11, 10, 4, 12, 15, 8, 18],
  #v[0, 1, 2, 3, 10, 15, 19, 6, 23, 21, 20, 14, 8, 12, 9, 4, 11, 13, 22, 18, 5, 16, 7, 17],
  #v[0, 1, 2, 3, 11, 12, 9, 10, 4, 22, 16, 8, 19, 18, 14, 23, 7, 17, 21, 5, 15, 13, 6, 20],
  #v[0, 1, 2, 3, 12, 7, 15, 20, 22, 23, 13, 8, 17, 9, 10, 4, 11, 6, 21, 16, 18, 5, 19, 14],
  #v[0, 1, 2, 3, 13, 8, 12, 23, 17, 7, 21, 19, 9, 14, 15, 16, 4, 22, 10, 18, 5, 11, 20, 6],
  #v[0, 1, 2, 3, 14, 9, 6, 17, 22, 21, 10, 20, 8, 11, 18, 23, 7, 16, 4, 15, 13, 5, 12, 19],
  #v[0, 1, 2, 3, 15, 20, 7, 22, 12, 14, 4, 16, 13, 17, 11, 5, 21, 23, 19, 6, 10, 9, 18, 8],
  #v[0, 1, 2, 3, 16, 20, 23, 9, 5, 12, 18, 21, 6, 4, 13, 14, 15, 8, 19, 11, 22, 10, 17, 7],
  #v[0, 1, 2, 3, 17, 12, 13, 8, 23, 22, 9, 6, 14, 11, 5, 21, 15, 18, 4, 19, 20, 16, 10, 7],
  #v[0, 1, 2, 3, 18, 14, 11, 23, 7, 10, 22, 13, 5, 6, 12, 16, 21, 4, 17, 19, 20, 15, 9, 8],
  #v[0, 1, 2, 3, 19, 11, 16, 8, 22, 4, 18, 17, 20, 7, 13, 21, 9, 15, 23, 6, 10, 5, 14, 12],
  #v[0, 1, 2, 3, 20, 18, 17, 19, 4, 21, 14, 10, 8, 7, 15, 22, 12, 5, 23, 9, 16, 13, 11, 6],
  #v[0, 1, 2, 3, 21, 20, 8, 10, 14, 5, 17, 15, 11, 18, 6, 12, 16, 7, 19, 13, 9, 22, 4, 23],
  #v[0, 1, 2, 3, 22, 16, 19, 11, 8, 15, 20, 12, 7, 5, 10, 18, 13, 6, 9, 17, 14, 21, 23, 4],
  #v[0, 1, 2, 3, 23, 13, 17, 12, 8, 18, 14, 7, 11, 16, 20, 9, 5, 19, 15, 6, 10, 21, 4, 22]]

/-- The level-4 representatives from their checked bijective point maps. -/
private noncomputable def transversals4 (i : Fin 20) : Equiv.Perm (Fin 24) :=
  Equiv.ofBijective (fun x : Fin 24 ↦ transversalImages4[i][x]) (by
    have h : ∀ j : Fin 20, Function.Bijective
        (fun x : Fin 24 ↦ transversalImages4[j][x]) := by decide +kernel
    exact h i)

/-- Point images of the level-5 generators. -/
private def generatorImages5 : Vector (Vector (Fin 24) 24) 3 := #v[
  #v[0, 1, 2, 3, 4, 8, 6, 5, 7, 16, 14, 13, 15, 20, 18, 17, 19, 12, 10, 9, 11, 23, 21, 22],
  #v[0, 1, 2, 3, 4, 16, 13, 15, 14, 12, 9, 11, 10, 20, 17, 19, 18, 8, 5, 7, 6, 22, 23, 21],
  #v[0, 1, 2, 3, 4, 14, 15, 13, 16, 10, 11, 9, 12, 18, 19, 17, 20, 6, 7, 5, 8, 22, 23, 21]]

/-- Inverse point images of the level-5 generators. -/
private def generatorInverseImages5 : Vector (Vector (Fin 24) 24) 3 := #v[
  #v[0, 1, 2, 3, 4, 7, 6, 8, 5, 19, 18, 20, 17, 11, 10, 12, 9, 15, 14, 16, 13, 22, 23, 21],
  #v[0, 1, 2, 3, 4, 18, 20, 19, 17, 10, 12, 11, 9, 6, 8, 7, 5, 14, 16, 15, 13, 23, 21, 22],
  #v[0, 1, 2, 3, 4, 19, 17, 18, 20, 11, 9, 10, 12, 7, 5, 6, 8, 15, 13, 14, 16, 23, 21, 22]]

/-- The level-5 generators with checked inverse tables. -/
private def generators5 : Fin 3 → Equiv.Perm (Fin 24) :=
  tablePerms generatorImages5 generatorInverseImages5 (by decide +kernel)

/-- Point images of the level-5 representatives, identity first. -/
private def transversalImages5 : Vector (Vector (Fin 24) 24) 16 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #v[0, 1, 2, 3, 4, 6, 8, 7, 5, 14, 16, 15, 13, 18, 20, 19, 17, 10, 12, 11, 9, 23, 21, 22],
  #v[0, 1, 2, 3, 4, 7, 6, 8, 5, 19, 18, 20, 17, 11, 10, 12, 9, 15, 14, 16, 13, 22, 23, 21],
  #v[0, 1, 2, 3, 4, 8, 6, 5, 7, 16, 14, 13, 15, 20, 18, 17, 19, 12, 10, 9, 11, 23, 21, 22],
  #v[0, 1, 2, 3, 4, 9, 11, 12, 10, 17, 19, 20, 18, 13, 15, 16, 14, 5, 7, 8, 6, 23, 21, 22],
  #v[0, 1, 2, 3, 4, 10, 11, 9, 12, 14, 15, 13, 16, 6, 7, 5, 8, 18, 19, 17, 20, 22, 23, 21],
  #v[0, 1, 2, 3, 4, 11, 12, 9, 10, 7, 8, 5, 6, 19, 20, 17, 18, 15, 16, 13, 14, 21, 22, 23],
  #v[0, 1, 2, 3, 4, 12, 11, 10, 9, 8, 7, 6, 5, 20, 19, 18, 17, 16, 15, 14, 13, 21, 22, 23],
  #v[0, 1, 2, 3, 4, 13, 15, 16, 14, 5, 7, 8, 6, 9, 11, 12, 10, 17, 19, 20, 18, 23, 21, 22],
  #v[0, 1, 2, 3, 4, 14, 15, 13, 16, 10, 11, 9, 12, 18, 19, 17, 20, 6, 7, 5, 8, 22, 23, 21],
  #v[0, 1, 2, 3, 4, 15, 13, 14, 16, 7, 5, 6, 8, 11, 9, 10, 12, 19, 17, 18, 20, 23, 21, 22],
  #v[0, 1, 2, 3, 4, 16, 13, 15, 14, 12, 9, 11, 10, 20, 17, 19, 18, 8, 5, 7, 6, 22, 23, 21],
  #v[0, 1, 2, 3, 4, 17, 20, 18, 19, 5, 8, 6, 7, 13, 16, 14, 15, 9, 12, 10, 11, 22, 23, 21],
  #v[0, 1, 2, 3, 4, 18, 20, 19, 17, 10, 12, 11, 9, 6, 8, 7, 5, 14, 16, 15, 13, 23, 21, 22],
  #v[0, 1, 2, 3, 4, 19, 17, 18, 20, 11, 9, 10, 12, 7, 5, 6, 8, 15, 13, 14, 16, 23, 21, 22],
  #v[0, 1, 2, 3, 4, 20, 17, 19, 18, 8, 5, 7, 6, 16, 13, 15, 14, 12, 9, 11, 10, 22, 23, 21]]

/-- The level-5 representatives from their checked bijective point maps. -/
private noncomputable def transversals5 (i : Fin 16) : Equiv.Perm (Fin 24) :=
  Equiv.ofBijective (fun x : Fin 24 ↦ transversalImages5[i][x]) (by
    have h : ∀ j : Fin 16, Function.Bijective
        (fun x : Fin 24 ↦ transversalImages5[j][x]) := by decide +kernel
    exact h i)

/-- Point images of the level-6 generators. -/
private def generatorImages6 : Vector (Vector (Fin 24) 24) 1 := #v[
  #v[0, 1, 2, 3, 4, 5, 8, 6, 7, 17, 20, 18, 19, 9, 12, 10, 11, 13, 16, 14, 15, 22, 23, 21]]

/-- Inverse point images of the level-6 generators. -/
private def generatorInverseImages6 : Vector (Vector (Fin 24) 24) 1 := #v[
  #v[0, 1, 2, 3, 4, 5, 7, 8, 6, 13, 15, 16, 14, 17, 19, 20, 18, 9, 11, 12, 10, 23, 21, 22]]

/-- The level-6 generators with checked inverse tables. -/
private def generators6 : Fin 1 → Equiv.Perm (Fin 24) :=
  tablePerms generatorImages6 generatorInverseImages6 (by decide +kernel)

/-- Point images of the level-6 representatives, identity first. -/
private def transversalImages6 : Vector (Vector (Fin 24) 24) 3 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #v[0, 1, 2, 3, 4, 5, 7, 8, 6, 13, 15, 16, 14, 17, 19, 20, 18, 9, 11, 12, 10, 23, 21, 22],
  #v[0, 1, 2, 3, 4, 5, 8, 6, 7, 17, 20, 18, 19, 9, 12, 10, 11, 13, 16, 14, 15, 22, 23, 21]]

/-- The level-6 representatives from their checked bijective point maps. -/
private noncomputable def transversals6 (i : Fin 3) : Equiv.Perm (Fin 24) :=
  Equiv.ofBijective (fun x : Fin 24 ↦ transversalImages6[i][x]) (by
    have h : ∀ j : Fin 3, Function.Bijective
        (fun x : Fin 24 ↦ transversalImages6[j][x]) := by decide +kernel
    exact h i)

/-- The terminal generator family is empty. -/
private def generators7 (i : Fin 0) : Equiv.Perm (Fin 24) := Fin.elim0 i

/-- Target representatives and next-level signed residue words for level 0. -/
private def transitions0 :
    Vector (Vector (Fin 24 × List (Fin 6)) 24) 2 := #v[
  #v[
    (11, []),
    (4, []),
    (5, []),
    (10, []),
    (1, []),
    (2, []),
    (14, [4, 3, 5, 3, 1, 5, 3, 5, 1, 2, 3, 5, 1, 2, 0, 2, 0, 5, 3, 2, 3, 4, 0, 4, 2, 4, 2, 3, 5,
      3, 3, 5, 1, 3, 4, 2, 0, 2, 3, 1, 0, 2, 1, 2, 4, 0, 0, 2, 0, 4, 2, 1, 5, 0, 2]),
    (17, []),
    (23, []),
    (20, []),
    (3, []),
    (0, []),
    (15, []),
    (19, []),
    (6, [4, 0, 5, 0, 1, 0, 4, 4, 0, 2, 0, 1, 0, 4, 3, 3, 1, 5, 1, 5, 1, 2, 4, 5, 1, 0, 4, 2, 4,
      0, 0, 2, 0, 2, 0, 1, 0, 4, 3, 5, 3, 2, 4, 5, 1, 3, 5, 3, 3, 1, 5, 4, 5, 3, 4, 0]),
    (12, []),
    (18, []),
    (7, []),
    (16, []),
    (13, []),
    (9, []),
    (22, []),
    (21, []),
    (8, [])],
  #v[
    (0, [0]),
    (11, []),
    (2, [2]),
    (16, []),
    (4, [1]),
    (10, []),
    (14, []),
    (7, [5, 4, 3, 5, 0, 2, 0, 2, 2, 0, 1, 0, 4, 3, 4, 0, 2, 3, 2, 1, 5, 1, 2, 3, 5, 3, 3, 5, 1,
      0, 4, 3, 2, 0, 2, 0, 5, 4, 5, 3, 4, 0, 5, 3, 2, 4, 5, 1, 3, 5, 3, 3, 1, 5, 4, 5, 3, 4,
      0]),
    (8, [5, 4, 5, 3, 1, 1, 0, 4]),
    (15, []),
    (22, []),
    (21, []),
    (12, [0, 5, 3, 4, 5, 4, 0, 4, 2, 4, 5, 5, 3, 5, 4, 0, 0, 2, 0, 5, 0, 2, 0, 2, 3, 5, 3, 5, 3,
      2, 4, 5, 1, 3, 5, 3, 3, 1, 5, 4, 5, 3, 4, 0]),
    (9, []),
    (19, []),
    (13, []),
    (20, []),
    (23, []),
    (17, []),
    (6, []),
    (3, []),
    (1, []),
    (5, []),
    (18, [])]]

/-- Target representatives and next-level signed residue words for level 1. -/
private def transitions1 :
    Vector (Vector (Fin 23 × List (Fin 6)) 23) 3 := #v[
  #v[
    (10, []),
    (1, [2, 3, 1]),
    (15, []),
    (3, [5, 3, 4, 3, 2, 0, 1, 5, 4, 2, 2, 4, 5, 3, 5, 5, 0, 0, 1]),
    (9, []),
    (13, []),
    (6, [0, 5, 0, 0, 0, 2, 2, 3, 5, 0, 1, 5, 5, 1, 2, 2, 0, 5, 3, 2, 0, 2, 4, 2, 2, 3, 1]),
    (7, [4, 0, 1, 5, 4, 5, 5, 4, 0, 1, 2, 0, 0, 5, 4, 2, 3, 4, 3, 5, 5, 1, 1, 5, 1, 5, 5, 5,
      1]),
    (14, []),
    (21, []),
    (20, []),
    (11, [5, 4, 3, 2, 0, 4, 0, 5, 4, 2, 4, 4, 0, 2, 4, 2, 1, 5, 4, 3, 2, 0, 2, 4, 2, 2, 3, 1]),
    (8, [5, 4, 3, 5, 3, 5, 3, 4, 2, 0, 2, 1, 2, 4, 5, 0, 4, 3, 2, 0, 0, 2]),
    (18, []),
    (12, [0, 4, 5, 3, 2, 4, 0, 4, 2, 2, 3, 5, 0, 1, 3, 2, 3, 5, 5, 1, 1, 5, 1, 5, 5, 5, 1]),
    (19, []),
    (22, []),
    (16, []),
    (5, []),
    (2, []),
    (0, []),
    (4, []),
    (17, [])],
  #v[
    (10, [3]),
    (0, []),
    (2, [3, 5, 0, 1, 0, 1, 2, 4, 5, 4, 2, 4, 4, 5, 0, 4, 3, 2, 0, 0, 2, 4, 3, 2, 0, 2, 4, 2, 2,
      3, 1]),
    (4, []),
    (17, [3, 2, 1, 5, 1, 0, 4, 2, 1, 5, 4, 0, 0, 2, 4, 0, 2, 4, 2, 1, 5, 5, 5, 1, 1, 5, 1, 5, 5,
      5, 1]),
    (19, [3, 4, 3, 2, 0, 0, 1, 0, 4, 3, 2, 4, 3, 4, 5, 0, 4, 3, 2, 0, 0, 2]),
    (11, []),
    (7, [4, 0, 1, 5, 1, 2, 3, 1, 3, 4, 3, 5, 1, 3, 4, 5, 3, 2, 0, 2, 4, 2, 2, 3, 1]),
    (16, [1, 3, 4, 3, 2, 4, 4, 3, 3, 3, 4, 5, 3, 5, 3, 4, 3, 3, 5, 4, 4, 5, 3, 5, 3, 5, 5, 1, 1,
      5, 1, 5, 5, 5, 1]),
    (14, [1, 1, 5, 5, 3, 5, 4, 0, 1, 0, 5, 0, 1, 3, 2, 2, 4, 5, 1, 1, 5, 1, 5, 5, 5, 1]),
    (1, [0]),
    (20, []),
    (5, []),
    (9, []),
    (13, [2, 4, 3, 2, 0, 4, 5, 5, 4, 0, 4, 3, 3, 5, 4, 4, 5, 3, 5, 3, 5, 5, 1, 1, 5, 1, 5, 5, 5,
      1]),
    (15, [1, 3, 1, 2, 2, 1, 5, 0, 1, 3, 2, 2, 4, 2]),
    (22, [4, 3, 5, 3, 5, 3, 1, 2, 2, 1, 5, 0, 1, 3, 2, 2, 4, 2, 4, 3, 2, 0, 2, 4, 2, 2, 3, 1]),
    (3, [2, 3, 5, 3, 5, 3, 4, 3, 3, 2, 1, 0, 4, 3, 3, 5, 4, 4, 5, 3, 5, 3]),
    (18, [4, 3, 2, 0, 4, 0, 5, 4, 2, 4, 4, 0, 2, 4, 2, 1, 5, 4, 3, 2, 0, 2, 4, 2, 2, 3, 1]),
    (12, [4, 4, 0, 0, 2, 3, 4, 3, 5, 1, 3, 4, 5, 1, 5, 5, 1, 1, 5, 1, 5, 5, 5, 1]),
    (6, []),
    (21, [5, 5, 1, 2, 2, 0, 0, 5, 4, 2, 3, 4, 3, 4, 3, 2, 0, 2, 4, 2, 2, 3, 1]),
    (8, [5, 3, 5, 0, 4, 5, 3, 1, 5, 4, 2, 2, 3, 4, 3, 5, 1, 3, 4, 5, 1])],
  #v[
    (0, [1]),
    (15, []),
    (2, [0, 4, 3, 5, 3, 5, 1, 0, 5, 1, 2, 2, 4]),
    (8, [1, 0, 0, 0, 1, 3, 4, 3, 3, 2, 1, 0, 5, 5, 1, 2, 0, 5, 1, 2, 2, 4, 4, 3, 2, 0, 2, 4, 2,
      2, 3, 1]),
    (22, [2, 3, 2, 0, 5, 3, 5, 4, 5, 1, 3, 4, 5, 3, 2, 0, 2, 4, 2, 2, 3, 1]),
    (4, [5, 5, 3, 2, 2, 3, 1, 1, 2, 0, 0, 5, 4, 2, 3, 4, 3]),
    (1, [4, 3]),
    (19, []),
    (21, [0, 1, 1, 5, 4, 2, 2, 3, 5, 0, 1, 2, 4, 5, 1, 5, 3, 3, 2, 0, 2, 4, 2, 2, 3, 1]),
    (9, [1, 5, 0, 1, 2, 3, 1, 5, 3, 2, 3, 4, 3, 2, 0, 2, 4, 2, 2, 3, 1]),
    (20, [2]),
    (14, []),
    (7, [4, 0, 1, 2, 4, 2, 2, 0, 2, 3, 4, 3, 3, 2, 1, 0, 4, 0, 2, 4, 2, 1, 5, 4, 3, 2, 0, 2, 4,
      2, 2, 3, 1]),
    (11, [1, 2, 4, 2, 4, 3, 1, 2, 2, 1, 3, 2, 3, 4, 3, 2, 0, 2, 4, 2, 2, 3, 1]),
    (13, [3, 2, 1, 3, 4, 3, 2, 4, 4, 2, 1, 2, 3, 2, 3, 2, 3, 4, 3, 2, 0, 2, 4, 2, 2, 3, 1]),
    (6, [0, 1]),
    (16, [4, 2, 4, 5, 3, 2, 4, 0, 5, 3, 5, 4, 0, 1, 0, 5, 5, 1, 2, 2, 0, 5, 3, 2, 0, 2, 4, 2, 2,
      3, 1]),
    (17, [2, 1, 5, 1, 5, 1, 5, 1, 2, 3, 1, 5, 0, 1, 3, 2, 2, 4, 2]),
    (10, [5]),
    (12, [0, 5, 0, 4, 5, 3, 3, 4, 3, 3, 2, 1, 0, 2, 4, 5, 1, 5, 3, 1]),
    (18, []),
    (3, [0, 4, 5, 3, 3, 4, 2, 0, 2, 1, 2]),
    (5, [])]]

/-- Target representatives and next-level signed residue words for level 2. -/
private def transitions2 :
    Vector (Vector (Fin 22 × List (Fin 4)) 22) 3 := #v[
  #v[
    (9, []),
    (14, []),
    (16, [2, 1, 0, 3, 0, 1, 0, 3, 3, 2, 2]),
    (12, []),
    (13, [3, 2, 2, 3, 2, 2, 3, 2, 3, 2, 2, 1, 0, 0, 3, 0, 3, 2, 2, 2, 1, 0, 3, 0, 0, 1, 2, 2, 2,
      3, 3, 0]),
    (19, [1, 1, 2, 2, 1, 0, 0, 0, 0, 1, 1, 2, 3, 2, 2, 3, 2]),
    (6, [1, 1, 2, 3, 0, 0, 0, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 0, 3, 0, 0, 1, 2, 2, 2, 3, 3,
      0]),
    (8, []),
    (20, [1, 0, 3, 0, 0, 1, 1, 2, 3, 2, 2, 3, 2, 2, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 3, 3]),
    (10, []),
    (5, [0, 3, 3, 0, 1, 1, 2, 3, 0, 0, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2]),
    (21, [0, 0, 3, 0, 1, 1, 2, 3, 3, 0, 3]),
    (17, [1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 2, 3, 0, 1]),
    (18, []),
    (4, []),
    (15, [2, 2, 2, 3, 0, 1, 1, 2, 2, 1, 0, 3, 0, 0, 3, 3, 2, 1, 1, 2, 2, 1, 0]),
    (7, []),
    (11, [1, 2, 3, 3, 2, 2, 1, 0, 3, 3, 3, 2, 3, 2, 1, 2, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 3,
      3]),
    (1, [2, 1, 0, 3, 0, 1, 0, 3, 3, 2, 2]),
    (0, []),
    (2, [3, 2, 2, 1, 2, 3, 0, 1, 0, 0, 1, 0, 3, 3, 2, 2, 2, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 3,
      3]),
    (3, [3, 3, 2, 1, 1, 2, 3, 2, 3, 2, 3, 0, 3, 3, 0, 0, 1, 2, 2, 2, 3, 3, 0])],
  #v[
    (14, []),
    (1, [3, 2, 3, 3, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 2, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 3,
      3]),
    (7, [0, 3, 2, 3, 3, 3, 3, 0, 3, 2, 2, 1, 0, 3, 0, 0, 1, 2, 2, 2, 3, 3, 0]),
    (21, [1, 2, 3]),
    (3, [3, 3, 3, 3, 0, 3]),
    (0, []),
    (18, []),
    (20, []),
    (8, [2, 1, 0, 1, 1, 2, 2, 3, 0, 3, 2, 3, 0, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 3, 3]),
    (19, [1]),
    (13, [1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 0, 3, 0, 0, 1, 2, 2, 2, 3, 3, 0]),
    (6, []),
    (10, [0, 1, 2, 3, 0, 3, 2, 1, 0, 1, 0, 3, 3, 0]),
    (12, [3, 3, 0, 1, 1, 2, 3, 0, 0, 3, 3, 2, 1, 0, 1, 0, 3, 3, 0]),
    (5, []),
    (15, [1, 1, 0, 1, 2, 3, 2, 3, 3, 0, 3, 2, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 3, 3]),
    (16, [2, 1, 0, 3, 2, 3, 2, 2, 1, 0, 0, 3, 0, 3, 2, 2, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 3,
      3]),
    (9, [3]),
    (11, []),
    (17, []),
    (2, [3, 3, 0, 1, 2, 3, 0, 3, 3, 2, 2, 2, 1, 0, 3, 2, 2, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 3,
      3]),
    (4, [])],
  #v[
    (18, []),
    (5, [2, 2, 3, 0, 0, 3, 2, 1, 0, 3, 3, 0, 0, 3, 2, 2, 1]),
    (13, []),
    (20, [3, 2, 2, 1, 0, 3, 2, 3, 2, 1, 0, 3, 3, 0, 0, 3, 2, 2, 1, 2, 2, 1, 0, 3, 0, 0, 1, 2, 2,
      2, 3, 3, 0]),
    (10, [3, 2, 2, 3, 2, 2, 3, 2, 3, 2, 2, 1, 0, 0, 3, 0, 3, 2, 2, 2, 1, 0, 3, 0, 0, 1, 2, 2, 2,
      3, 3, 0]),
    (0, [2]),
    (1, [2, 3, 0, 3, 3, 2, 1, 2, 2, 3, 0, 3, 2, 3, 0, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 3, 3]),
    (17, [0, 1, 1, 2, 3, 0, 0, 0, 1, 2, 1, 2, 2, 3, 0, 0, 1, 2, 2, 1, 0, 3, 0, 0, 1, 2, 2, 2, 3,
      3, 0]),
    (2, [3, 2, 2, 3, 2, 2, 2, 3, 3, 2, 3, 3, 2, 1, 0]),
    (4, [3, 3, 2, 2, 3, 0, 0, 0, 0, 3, 3, 0, 1, 0, 1, 1, 1, 2, 3, 0, 1, 2, 3, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 0, 3, 3]),
    (11, [2, 2, 1, 2, 3, 0, 0, 0, 0, 0, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 0, 3, 0, 0, 1, 2, 2, 2,
      3, 3, 0]),
    (3, [1, 0, 1, 2, 3, 0, 0, 0, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 0, 3, 0, 0, 1, 2, 2, 2, 3, 3,
      0]),
    (19, []),
    (6, [2, 2, 2, 3, 0, 1, 1, 0, 1, 0, 3, 3, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 3, 3]),
    (7, []),
    (12, []),
    (21, [1, 1, 0, 3, 3, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 3, 3]),
    (8, [3, 3, 2, 2, 1, 2, 2, 2, 2, 1, 0, 0, 1, 0, 3, 3, 2, 2, 2, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0,
      0, 3, 3]),
    (14, [2, 3, 0, 1, 1, 0, 0, 1, 1, 2, 3, 2, 2]),
    (9, [3, 3, 2, 1, 0, 1, 0, 3, 3, 0]),
    (16, [1, 2, 3, 0, 1, 1, 1, 2, 3, 0, 1]),
    (15, [2, 3, 3, 0, 0, 0, 0, 1, 0, 3, 3, 2, 2, 2, 2, 1, 0, 3, 0, 0, 1, 2, 2, 2, 3, 3, 0])]]

/-- Target representatives and next-level signed residue words for level 3. -/
private def transitions3 :
    Vector (Vector (Fin 21 × List (Fin 4)) 21) 2 := #v[
  #v[
    (17, []),
    (7, [1, 2, 1, 0, 3, 0, 1, 2]),
    (5, []),
    (18, []),
    (0, []),
    (11, []),
    (4, []),
    (8, []),
    (16, [3, 2, 2, 1, 2, 1, 0, 3, 3, 0, 1, 2, 1, 0, 1, 0, 3, 0, 3]),
    (2, [1, 2, 1, 0, 1, 2, 1, 0, 3, 2, 1, 0, 1, 0, 3, 0, 3, 3, 2, 1, 0]),
    (12, [0, 0, 1, 2, 1, 0, 3, 2, 1, 0, 1, 0, 3, 0, 3, 3, 2, 1, 0]),
    (14, []),
    (6, []),
    (10, [3, 2, 1, 1, 0, 1, 2, 3, 2, 3, 0, 1, 2, 1, 0, 1, 0, 3, 0, 3]),
    (3, [1, 0, 1, 2, 1, 2, 3, 0, 1, 2, 1, 0, 1, 0, 3, 0, 3]),
    (1, []),
    (19, [1, 2, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 3, 0, 3, 3, 2, 1, 0]),
    (13, []),
    (9, []),
    (20, [1, 2, 1, 2, 1, 0, 3, 2, 3, 2, 2, 3, 0, 1, 2, 1, 0, 1, 0, 3, 0, 3]),
    (15, [0, 1, 1, 0, 3, 2, 3, 0, 3, 2, 1, 2, 2, 1, 0, 1, 0, 3, 0, 3, 3, 2, 1, 0])],
  #v[
    (18, []),
    (6, []),
    (4, [1, 2, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 3, 0, 3, 3, 2, 1, 0]),
    (16, [3, 2, 2, 1, 2, 1, 0, 3, 3, 0, 1, 2, 1, 0, 1, 0, 3, 0, 3]),
    (10, []),
    (0, []),
    (19, []),
    (15, [1, 2]),
    (17, []),
    (8, [3, 0, 3, 3, 0, 1, 0, 3, 2, 1, 2, 1, 0, 1, 0, 3, 0, 3, 3, 2, 1, 0]),
    (12, [0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 0, 1, 0, 3, 0, 3, 3, 2, 1, 0]),
    (9, [3, 0, 3, 2, 3, 0, 1, 2, 1, 0, 1, 0, 3, 0, 3, 3, 2, 1, 0]),
    (20, [0, 1, 2, 1, 2, 1, 0, 3, 0]),
    (11, [3, 2, 1, 1, 0, 1, 2, 3, 2, 3, 0, 1, 2, 1, 0, 1, 0, 3, 0, 3]),
    (14, [0, 1, 0, 3, 0, 3, 3, 2, 1, 0]),
    (1, [3, 0, 1, 2, 3, 2, 1]),
    (5, []),
    (13, [3, 0, 1]),
    (3, [2, 1, 2, 1, 0, 3, 2, 3, 2, 2, 3, 0, 1, 2, 1, 0, 1, 0, 3, 0, 3]),
    (7, [0, 3, 3, 0, 1, 0, 3, 2, 1]),
    (2, [])]]

/-- Target representatives and next-level signed residue words for level 4. -/
private def transitions4 :
    Vector (Vector (Fin 20 × List (Fin 6)) 20) 2 := #v[
  #v[
    (18, []),
    (12, [5, 4, 5, 3, 4]),
    (15, []),
    (7, []),
    (4, [4, 0]),
    (11, [1]),
    (16, []),
    (8, []),
    (3, []),
    (1, [3, 1]),
    (6, []),
    (14, []),
    (9, [5, 4]),
    (2, []),
    (5, [4]),
    (13, []),
    (10, []),
    (17, [0]),
    (19, []),
    (0, [])],
  #v[
    (14, []),
    (10, [4, 3, 2]),
    (7, [4, 5]),
    (19, []),
    (3, []),
    (6, []),
    (18, []),
    (9, [5, 5, 1]),
    (1, []),
    (2, []),
    (8, [2, 3, 5, 1]),
    (12, []),
    (17, []),
    (0, []),
    (13, []),
    (15, [2]),
    (16, [5, 4, 5, 5, 3, 4]),
    (11, []),
    (5, []),
    (4, [])]]

/-- Target representatives and next-level signed residue words for level 5. -/
private def transitions5 :
    Vector (Vector (Fin 16 × List (Fin 2)) 16) 3 := #v[
  #v[
    (3, []),
    (1, [1]),
    (0, []),
    (2, []),
    (11, []),
    (9, [1]),
    (8, []),
    (10, []),
    (15, []),
    (13, [0]),
    (12, []),
    (14, [0]),
    (7, []),
    (5, []),
    (4, [1]),
    (6, [])],
  #v[
    (11, []),
    (8, [0]),
    (10, []),
    (9, [1]),
    (7, []),
    (4, []),
    (6, [0]),
    (5, []),
    (15, [1]),
    (12, [0]),
    (14, [0]),
    (13, []),
    (3, []),
    (0, []),
    (2, [1]),
    (1, [])],
  #v[
    (9, []),
    (10, [0]),
    (8, []),
    (11, [1]),
    (5, [1]),
    (6, [1]),
    (4, [1]),
    (7, [0]),
    (13, [0]),
    (14, []),
    (12, [1]),
    (15, [0]),
    (1, []),
    (2, [1]),
    (0, []),
    (3, [])]]

/-- Target representatives and next-level signed residue words for level 6. -/
private def transitions6 :
    Vector (Vector (Fin 3 × List (Fin 0)) 3) 1 := #v[
  #v[
    (2, []),
    (0, []),
    (1, [])]]

/-- Generator counts, including the empty terminal family. -/
private def generatorSize (i : Fin 8) : ℕ := (#v[2, 3, 3, 2, 2, 3, 1, 0])[i]

/-- Representative counts for the seven successive covers. -/
private def transversalSize (i : Fin 7) : ℕ := (#v[24, 23, 22, 21, 20, 16, 3])[i]

/-- The generator family at each level of the cover. -/
private def strongGenerators : (level : Fin 8) →
    Fin (generatorSize level) → Equiv.Perm (Fin 24)
  | 0 => generators0
  | 1 => generators1
  | 2 => generators2
  | 3 => generators3
  | 4 => generators4
  | 5 => generators5
  | 6 => generators6
  | 7 => generators7

/-- Representatives at each nonterminal level. -/
private noncomputable def representatives : (level : Fin 7) →
    Fin (transversalSize level) → Equiv.Perm (Fin 24)
  | 0 => transversals0
  | 1 => transversals1
  | 2 => transversals2
  | 3 => transversals3
  | 4 => transversals4
  | 5 => transversals5
  | 6 => transversals6

/-- The checked target and residue data, indexed by their level. -/
private def transitions : (level : Fin 7) → Fin (generatorSize level.castSucc) →
    Fin (transversalSize level) → Fin (transversalSize level) ×
      List (Fin (generatorSize level.succ + generatorSize level.succ))
  | 0 => fun a j ↦ transitions0[a][j]
  | 1 => fun a j ↦ transitions1[a][j]
  | 2 => fun a j ↦ transitions2[a][j]
  | 3 => fun a j ↦ transitions3[a][j]
  | 4 => fun a j ↦ transitions4[a][j]
  | 5 => fun a j ↦ transitions5[a][j]
  | 6 => fun a j ↦ transitions6[a][j]

/-- The subgroup generated by a level's concrete permutations. -/
private def levelSubgroup (level : Fin 8) : Subgroup (Equiv.Perm (Fin 24)) :=
  Subgroup.closure (Set.range (strongGenerators level))

private theorem transitions_valid0 : ∀ (a : Fin 2) (i : Fin 24) (x : Fin 24),
    (generators0 a * transversals0 i) x =
      (transversals0 (transitions0[a][i]).1 *
        evalWord generators1 (transitions0[a][i]).2) x := by
  decide +kernel

private theorem transitions_valid1 : ∀ (a : Fin 3) (i : Fin 23) (x : Fin 24),
    (generators1 a * transversals1 i) x =
      (transversals1 (transitions1[a][i]).1 *
        evalWord generators2 (transitions1[a][i]).2) x := by
  decide +kernel

private theorem transitions_valid2 : ∀ (a : Fin 3) (i : Fin 22) (x : Fin 24),
    (generators2 a * transversals2 i) x =
      (transversals2 (transitions2[a][i]).1 *
        evalWord generators3 (transitions2[a][i]).2) x := by
  decide +kernel

private theorem transitions_valid3 : ∀ (a : Fin 2) (i : Fin 21) (x : Fin 24),
    (generators3 a * transversals3 i) x =
      (transversals3 (transitions3[a][i]).1 *
        evalWord generators4 (transitions3[a][i]).2) x := by
  decide +kernel

private theorem transitions_valid4 : ∀ (a : Fin 2) (i : Fin 20) (x : Fin 24),
    (generators4 a * transversals4 i) x =
      (transversals4 (transitions4[a][i]).1 *
        evalWord generators5 (transitions4[a][i]).2) x := by
  decide +kernel

private theorem transitions_valid5 : ∀ (a : Fin 3) (i : Fin 16) (x : Fin 24),
    (generators5 a * transversals5 i) x =
      (transversals5 (transitions5[a][i]).1 *
        evalWord generators6 (transitions5[a][i]).2) x := by
  decide +kernel

private theorem transitions_valid6 : ∀ (a : Fin 1) (i : Fin 3) (x : Fin 24),
    (generators6 a * transversals6 i) x =
      (transversals6 (transitions6[a][i]).1 *
        evalWord generators7 (transitions6[a][i]).2) x := by
  decide +kernel

private theorem transitions_valid (level : Fin 7)
    (a : Fin (generatorSize level.castSucc)) (i : Fin (transversalSize level)) :
    strongGenerators level.castSucc a * representatives level i =
      representatives level (transitions level a i).1 *
        evalWord (strongGenerators level.succ) (transitions level a i).2 := by
  apply Equiv.ext
  fin_cases level
  · exact transitions_valid0 a i
  · exact transitions_valid1 a i
  · exact transitions_valid2 a i
  · exact transitions_valid3 a i
  · exact transitions_valid4 a i
  · exact transitions_valid5 a i
  · exact transitions_valid6 a i

private theorem targets_surjective (level : Fin 7) (a : Fin (generatorSize level.castSucc)) :
    Function.Surjective (fun i ↦ (transitions level a i).1) := by
  have h : ∀ (k : Fin 7) (b : Fin (generatorSize k.castSucc)),
      Function.Surjective (fun j ↦ (transitions k b j).1) := by
    intro k
    fin_cases k <;> decide +kernel
  exact h level a

private theorem representative_one (level : Fin 7) :
    ∃ i, representatives level i = 1 := by
  fin_cases level <;> refine ⟨⟨0, by decide⟩, Equiv.ext ?_⟩ <;> decide +kernel

private theorem step (level : Fin 7) (a : Fin (generatorSize level.castSucc))
    (i : Fin (transversalSize level)) :
    (representatives level (transitions level a i).1)⁻¹ *
      strongGenerators level.castSucc a * representatives level i ∈ levelSubgroup level.succ := by
  rw [mul_assoc, transitions_valid, inv_mul_cancel_left]
  exact evalWord_mem _ _

private theorem inverse_step (level : Fin 7) (a : Fin (generatorSize level.castSucc))
    (i : Fin (transversalSize level)) :
    ∃ j, (representatives level j)⁻¹ * (strongGenerators level.castSucc a)⁻¹ *
      representatives level i ∈ levelSubgroup level.succ := by
  obtain ⟨j, hj⟩ := targets_surjective level a i
  have h := (levelSubgroup level.succ).inv_mem (step level a j)
  change (transitions level a j).1 = i at hj
  rw [hj] at h
  exact ⟨j, by simpa only [mul_inv_rev, inv_inv, mul_assoc] using h⟩

private theorem level_bound (level : Fin 7) :
    Nat.card (levelSubgroup level.castSucc) ≤
      transversalSize level * Nat.card (levelSubgroup level.succ) := by
  have h := Subgroup.natCard_closure_le_mul (strongGenerators level.castSucc)
    (representatives level) (levelSubgroup level.succ) (representative_one level)
    (fun a i ↦ ⟨_, step level a i⟩) (inverse_step level)
  simpa only [levelSubgroup, Nat.card_fin] using h

private theorem terminal_subgroup : levelSubgroup 7 = ⊥ := by
  simp [levelSubgroup, strongGenerators, generatorSize]

private theorem original_generator (i : Fin 2) :
    m24GeneratorImages ⟨i.val, by simpa [GroupPresentation.generatorCount] using i.isLt⟩ =
      generators0 i := by
  have h : ∀ (j : Fin 2) (x : Fin 24),
      m24GeneratorImages
        ⟨j.val, by simpa [GroupPresentation.generatorCount] using j.isLt⟩ x =
          generators0 j x := by
    unfold m24GeneratorImages
    decide +kernel
  exact Equiv.ext (h i)

private theorem image_le_closure : m24PermutationHom.range ≤ levelSubgroup 0 := by
  rintro _ ⟨g, rfl⟩
  apply PresentedGroup.generated_by m24Presentation.relatorSet
    ((levelSubgroup 0).comap m24PermutationHom)
  intro i
  change m24PermutationHom (PresentedGroup.of i) ∈ levelSubgroup 0
  rw [m24PermutationHom_of]
  let j : Fin 2 := ⟨i.val, by simpa [GroupPresentation.generatorCount] using i.isLt⟩
  exact Subgroup.subset_closure ⟨j, (original_generator j).symm⟩

/-- The seven checked covers bound the concrete M24 permutation image by 244823040. -/
theorem m24PermutationHom_range_natCard_le :
    Nat.card m24PermutationHom.range ≤ 244823040 := by
  apply (Subgroup.card_le_of_le image_le_closure).trans
  have h0 := level_bound 0
  change Nat.card (levelSubgroup 0) ≤ 24 * Nat.card (levelSubgroup 1) at h0
  have h1 := level_bound 1
  change Nat.card (levelSubgroup 1) ≤ 23 * Nat.card (levelSubgroup 2) at h1
  have h2 := level_bound 2
  change Nat.card (levelSubgroup 2) ≤ 22 * Nat.card (levelSubgroup 3) at h2
  have h3 := level_bound 3
  change Nat.card (levelSubgroup 3) ≤ 21 * Nat.card (levelSubgroup 4) at h3
  have h4 := level_bound 4
  change Nat.card (levelSubgroup 4) ≤ 20 * Nat.card (levelSubgroup 5) at h4
  have h5 := level_bound 5
  change Nat.card (levelSubgroup 5) ≤ 16 * Nat.card (levelSubgroup 6) at h5
  have h6 := level_bound 6
  change Nat.card (levelSubgroup 6) ≤ 3 * Nat.card (levelSubgroup 7) at h6
  rw [terminal_subgroup, Subgroup.card_bot] at h6
  omega

/-- The image of the exact M24 presentation in its checked action has order 244823040. -/
theorem m24PermutationHom_range_natCard : Nat.card m24PermutationHom.range = 244823040 :=
  le_antisymm m24PermutationHom_range_natCard_le m24PermutationHom_range_natCard_ge

end TauCeti.Sporadic.Mathieu
