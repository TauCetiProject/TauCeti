/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Substructures
import Mathlib.Data.Fintype.Order

/-!
# Substructures

Additions to Mathlib's `Mathlib.ModelTheory.Substructures`.

## Main results

* `FirstOrder.Language.Substructure.exists_forall_mem_of_directed`: a finitely indexed family of
  elements of a directed union of substructures lies in one of them.
-/

public section

namespace FirstOrder

namespace Language

namespace Substructure

variable {L : Language} {M : Type*} [L.Structure M]

/-- **A finite tuple of a directed union lies in one member.** For a nonempty directed family of
substructures, finitely many elements of their union all lie in a single member. -/
theorem exists_forall_mem_of_directed {ι κ : Type*} [Nonempty ι] [Finite κ]
    {S : ι → L.Substructure M} (hdir : Directed (· ≤ ·) S) (a : κ → ↥(⨆ i, S i)) :
    ∃ k, ∀ j, (a j : M) ∈ S k := by
  choose ks hks using fun j => (mem_iSup_of_directed hdir).1 (a j).2
  obtain ⟨k, hk⟩ := hdir.finite_le ks
  exact ⟨k, fun j => hk j (hks j)⟩

end Substructure

end Language

end FirstOrder
