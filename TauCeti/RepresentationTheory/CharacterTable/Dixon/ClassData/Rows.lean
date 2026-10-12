/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.FinEnum
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.EigenvectorSearch
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.List.OfFn

/-!
# Enumerating the modular central-character rows

`TauCeti.ClassData.centralCharacterRows` lists the output of the certified common-eigenspace
search without enumerating the ambient space of row vectors. It sorts only the surviving rows,
lexicographically by the coordinate ranks supplied by `FinEnum`.

Both the rational and cyclotomic Dixon solvers need an executable numbering of these rows.
The list has no duplicates, its finite-set image is exactly `centralCharacterSearch`, and its
ordering is given by `pairwise_centralCharacterRows`. No good-prime or splitting assumption is
needed.

The comparison constructs coordinate lists of length the number of conjugacy classes. It does
not use the `FinEnum` instance on the row type, which itself enumerates all possible rows.

## References

* J. D. Dixon, *High speed computation of group characters*, Numer. Math. **10** (1967),
  446–450.
-/

public section

namespace TauCeti.ClassData

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable (d : ClassData G) {F : Type*} [Field F] [Fintype F] [DecidableEq F] [FinEnum F]

@[instance_reducible]
private def centralCharacterRowOrder : LinearOrder (Fin d.numClasses → F) :=
  LinearOrder.lift' (fun row ↦ List.ofFn fun i ↦ FinEnum.equiv (row i))
    (fun _ _ h ↦ funext fun i ↦ FinEnum.equiv.injective
      (congrFun (List.ofFn_injective h) i))

omit [Fintype G] [DecidableEq G] [Field F] [Fintype F] [DecidableEq F] in
private theorem centralCharacterRowOrder_le (a b : Fin d.numClasses → F) :
    @LE.le _ (d.centralCharacterRowOrder (F := F)).toLE a b ↔
      List.ofFn (fun i ↦ FinEnum.equiv (a i)) ≤
        List.ofFn (fun i ↦ FinEnum.equiv (b i)) := Iff.rfl

/-- The modular central-character search output, sorted lexicographically by coordinate ranks.
Only the surviving common-eigenvalue tuples are sorted. -/
def centralCharacterRows : List (Fin d.numClasses → F) :=
  letI := d.centralCharacterRowOrder (F := F)
  d.centralCharacterSearch.sort

/-- The row list enumerates exactly the modular central-character search. -/
@[simp]
theorem centralCharacterRows_toFinset :
    (d.centralCharacterRows (F := F)).toFinset = d.centralCharacterSearch := by
  unfold centralCharacterRows
  exact Finset.sort_toFinset _ _

/-- Membership in the row list is membership in the certified search output. -/
@[simp]
theorem mem_centralCharacterRows {row : Fin d.numClasses → F} :
    row ∈ d.centralCharacterRows ↔ row ∈ d.centralCharacterSearch := by
  rw [← List.mem_toFinset, centralCharacterRows_toFinset]

/-- Each modular central-character row occurs once in the enumeration. -/
@[simp]
theorem nodup_centralCharacterRows : (d.centralCharacterRows (F := F)).Nodup := by
  unfold centralCharacterRows
  exact Finset.sort_nodup _ _

/-- The enumeration orders rows lexicographically by their coordinate ranks. -/
@[simp]
theorem pairwise_centralCharacterRows :
    (d.centralCharacterRows (F := F)).Pairwise
      (fun a b ↦ List.ofFn (fun i ↦ FinEnum.equiv (a i)) ≤
        List.ofFn (fun i ↦ FinEnum.equiv (b i))) := by
  let := d.centralCharacterRowOrder (F := F)
  unfold centralCharacterRows
  simpa only [centralCharacterRowOrder_le] using
    (d.centralCharacterSearch (F := F)).pairwise_sort (· ≤ ·)

end TauCeti.ClassData
