/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.PolyTime.Writer
public import TauCeti.GroupTheory.Perm.Certificates.Families
public import TauCeti.GroupTheory.Perm.Certificates.Tables.Basic

/-!
# Uniform polynomial-time tables for the successful families

These algorithms enumerate points, ordered pairs, and ordered triples. They
never enumerate the symmetric group. First-occurrence table searches agree
with the bounded indices used by the mathematical certificate construction.
-/

@[expose] public section

namespace TauCeti.FamilyTables

open Equiv Computability BitEncoding Turing PermutationTables

/-- The transposition table, defined on all natural inputs. -/
def swapTable (n a b : ℕ) : Table :=
  (List.range n).map fun x => bif decide (x = a) then b
    else bif decide (x = b) then a else x

/-- The forward table of the ordered three-cycle. -/
def tripleTable (n a b c : ℕ) : Table :=
  PermutationTables.mul n (swapTable n a b) (swapTable n b c)

/-- Optionally exclude the fixed point zero. -/
def permitted (fixZero : Bool) (x : ℕ) : Bool := !fixZero || !decide (x = 0)

/-- Enumerate transpositions on the permitted ordered pairs. -/
def swaps (n : ℕ) (fixZero : Bool) : List Table :=
  (List.range n).flatMap fun a =>
    ((List.range n).filter fun b =>
      permitted fixZero a && permitted fixZero b && !decide (a = b)).map
        fun b => swapTable n a b

/-- Enumerate three-cycles on the permitted ordered triples. -/
def triples (n : ℕ) (fixZero : Bool) : List Table :=
  (List.range n).flatMap fun a =>
    (List.range n).flatMap fun b =>
      ((List.range n).filter fun c =>
        permitted fixZero a && permitted fixZero b && permitted fixZero c &&
          !decide (a = b) && !decide (a = c) && !decide (b = c)).map
            fun c => tripleTable n a b c

/-- Find the first occurrence of a table; use zero when it is absent. -/
def tableIndex (gs : List Table) (g : Table) : ℕ :=
  ((List.range gs.length).find? fun i => decide (gs[i]?.getD [] = g)).getD 0

/-- One-letter ambient words representing the explicitly listed subgroup tables. -/
def wordsFor (gs hs : List Table) : List PermutationTables.Word :=
  hs.map fun h => [(tableIndex gs h, false)]

@[fun_prop] theorem polyTime_swapTable :
    PolyTime (fun p : ℕ × ℕ × ℕ => swapTable p.1 p.2.1 p.2.2) := by
  unfold swapTable
  fun_prop

@[fun_prop] theorem polyTime_tripleTable :
    PolyTime (fun p : ℕ × ℕ × ℕ × ℕ => tripleTable p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold tripleTable
  fun_prop

@[fun_prop] theorem polyTime_permitted :
    PolyTime (fun p : Bool × ℕ => permitted p.1 p.2) := by
  unfold permitted
  fun_prop

@[fun_prop] theorem polyTime_swaps :
    PolyTime (fun p : ℕ × Bool => swaps p.1 p.2) := by
  unfold swaps
  fun_prop

@[fun_prop] theorem polyTime_triples :
    PolyTime (fun p : ℕ × Bool => triples p.1 p.2) := by
  unfold triples
  fun_prop

@[fun_prop] theorem polyTime_tableIndex :
    PolyTime (fun p : List Table × Table => tableIndex p.1 p.2) := by
  unfold tableIndex
  fun_prop

@[fun_prop] theorem polyTime_wordsFor :
    PolyTime (fun p : List Table × List Table => wordsFor p.1 p.2) := by
  unfold wordsFor
  fun_prop

theorem swapTable_ofFin {n : ℕ} (a b : Fin n) :
    swapTable n a.val b.val = ofPerm (Equiv.swap a b) := by
  rw [swapTable, range_eq_ofFn, List.map_ofFn, ofPerm]
  congr 1
  funext x
  simp only [Function.comp_apply, Equiv.swap_apply_def, Fin.ext_iff, Bool.cond_decide]
  split_ifs <;> rfl

theorem tripleTable_ofFin {n : ℕ} (a b c : Fin n) :
    tripleTable n a.val b.val c.val = ofPerm (Equiv.swap a b * Equiv.swap b c) := by
  rw [tripleTable, swapTable_ofFin, swapTable_ofFin, mul_ofPerm]

theorem swaps_eq (n : ℕ) (fixZero : Bool) :
    swaps n fixZero =
      (SuccessfulFamilies.swaps n (fun x => permitted fixZero x.val)).map ofPerm := by
  simp only [swaps, SuccessfulFamilies.swaps, ← List.map_coe_finRange_eq_range,
    List.flatMap_map, List.filter_map, List.map_flatMap, List.map_map, Fin.ext_iff,
    decide_not, Function.comp_def, swapTable_ofFin]

theorem triples_eq (n : ℕ) (fixZero : Bool) :
    triples n fixZero =
      (SuccessfulFamilies.triples n (fun x => permitted fixZero x.val)).map ofPerm := by
  simp only [triples, SuccessfulFamilies.triples, ← List.map_coe_finRange_eq_range,
    List.flatMap_map, List.filter_map, List.map_flatMap, List.map_map, Fin.ext_iff,
    decide_not, Function.comp_def, tripleTable_ofFin]

theorem swaps_all_eq (n : ℕ) :
    swaps n false = (SuccessfulFamilies.swaps n (fun _ => true)).map ofPerm := by
  simpa only [permitted, Bool.not_false, Bool.true_or] using swaps_eq n false

theorem swaps_fixed_eq (n : ℕ) :
    swaps n true = (SuccessfulFamilies.swaps n SuccessfulFamilies.allowed).map ofPerm := by
  change swaps n true =
    (SuccessfulFamilies.swaps n (fun x => !decide (x.val = 0))).map ofPerm
  simpa only [permitted, Bool.not_true, Bool.false_or] using swaps_eq n true

theorem triples_all_eq (n : ℕ) :
    triples n false = (SuccessfulFamilies.triples n (fun _ => true)).map ofPerm := by
  simpa only [permitted, Bool.not_false, Bool.true_or] using triples_eq n false

theorem triples_fixed_eq (n : ℕ) :
    triples n true = (SuccessfulFamilies.triples n SuccessfulFamilies.allowed).map ofPerm := by
  change triples n true =
    (SuccessfulFamilies.triples n (fun x => !decide (x.val = 0))).map ofPerm
  simpa only [permitted, Bool.not_true, Bool.false_or] using triples_eq n true

theorem ofPerm_injective {n : ℕ} :
    Function.Injective (ofPerm : Perm (Fin n) → Table) := by
  intro g h he
  apply Equiv.ext
  intro x
  apply Fin.ext
  simpa only [lookup_ofPerm] using congrArg (fun t => lookup n t x.val) he

/-- The ordinary table scan finds the same first index as the bounded scan. -/
theorem tableIndex_ofPerm {n : ℕ} (gs : List (Perm (Fin n))) (g : Perm (Fin n))
    (hg : g ∈ gs) :
    tableIndex (gs.map ofPerm) (ofPerm g) =
      (CertificateConstruction.indexOfMem gs g hg).val := by
  have hp : ∀ i : Fin gs.length, (gs.map ofPerm)[i.val]?.getD [] = ofPerm (gs.get i) := by
    intro i
    simp [i.isLt, List.get_eq_getElem]
  have hf : ((List.range gs.length).find? fun i =>
      decide ((gs.map ofPerm)[i]?.getD [] = ofPerm g)) =
        some (CertificateConstruction.indexOfMem gs g hg).val := by
    rw [range_eq_ofFn, List.find?_ofFn_eq_some_of_injective Fin.val_injective]
    constructor
    · change decide ((gs.map ofPerm)[(CertificateConstruction.indexOfMem gs g hg).val]?.getD [] =
        ofPerm g) = true
      rw [hp, CertificateConstruction.indexOfMem_spec]
      simp only [decide_true]
    · intro j hj he
      have he' : gs.get j = g := ofPerm_injective (by simpa only [hp, decide_eq_true_eq] using he)
      exact Fin.find_min (p := fun i => gs.get i = g) (List.mem_iff_get.mp hg) hj he'
  simp only [tableIndex, List.length_map, hf, Option.getD_some]

theorem wordsFor_ofPerm {n : ℕ} (gs hs : List (Perm (Fin n)))
    (hmem : ∀ h ∈ hs, h ∈ gs) :
    wordsFor (gs.map ofPerm) (hs.map ofPerm) =
      (CertificateConstruction.wordsFor gs hs hmem).map eraseWord := by
  rw [wordsFor, CertificateConstruction.wordsFor, List.map_map, List.map_ofFn]
  conv_lhs => rw [← List.ofFn_get hs, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply, eraseWord, List.map_cons, List.map_nil]
  rw [tableIndex_ofPerm gs (hs.get i) (hmem _ (hs.get_mem i))]

end TauCeti.FamilyTables
