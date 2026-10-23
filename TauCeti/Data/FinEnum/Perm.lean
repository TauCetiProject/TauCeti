/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Perm

/-!
# Executable enumeration of permutations

A finitely enumerable type has a finitely enumerable permutation group. The enumeration uses
Mathlib's `permsOfList` on the enumeration of the carrier, generating only permutations
instead of filtering all endofunctions. This is useful when a search needs independent
permutations of a finite set, such as aligning modular central-character rows at conjugate roots.
-/

public section

namespace FinEnum

variable {α : Type*} [FinEnum α]

/-- Enumerate the permutation group by permuting the enumeration of its carrier.
Mathlib's `permsOfList` generates each permutation once. -/
instance perm : FinEnum (Equiv.Perm α) :=
  ofNodupList (permsOfList (toList α))
    (fun _ ↦ mem_permsOfList_of_mem fun _ _ ↦ mem_toList _)
    (nodup_permsOfList nodup_toList)

end FinEnum
