/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.RibbonGraph.Classification

/-!
# Euler characteristic of a bipartite ribbon graph

The Euler characteristic agrees with that of any edge-numbered permutation triple. This
comparison gives its parity and the connected upper bound.
-/

public section

namespace TauCeti

universe u

namespace BipartiteRibbonGraph

variable (Γ : BipartiteRibbonGraph.{u})

/-- The Euler characteristic of a ribbon graph agrees with that of its permutation triple for
any numbering of the edges. -/
@[simp] theorem eulerChar_toPermutationTriple {n : ℕ} (ν : Γ.E ≃ Fin n) :
    (Γ.toPermutationTriple ν).eulerChar = Γ.eulerChar := by
  exact (PermutationTriple.eulerChar_ribbonGraph _).symm.trans
    (Γ.isoRibbonGraph ν).eulerChar_eq.symm

/-- The Euler characteristic of a finite bipartite ribbon graph is even. -/
theorem even_eulerChar : Even Γ.eulerChar := by
  let ν := Fintype.equivFin Γ.E
  rw [← Γ.eulerChar_toPermutationTriple ν]
  exact PermutationTriple.even_eulerChar _

/-- A connected bipartite ribbon graph has Euler characteristic at most two. -/
theorem IsConnected.eulerChar_le_two (hΓ : Γ.IsConnected) : Γ.eulerChar ≤ 2 := by
  let ν := Fintype.equivFin Γ.E
  rw [← Γ.eulerChar_toPermutationTriple ν]
  exact (Γ.isConnected_toPermutationTriple ν).mpr hΓ |>.eulerChar_le_two

end BipartiteRibbonGraph

end TauCeti
