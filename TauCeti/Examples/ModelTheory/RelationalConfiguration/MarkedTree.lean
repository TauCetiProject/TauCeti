/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.MarkedTree

/-!
# Checks for the cover graph of a coded order

The cover graph of the chain `(ℕ, ≤)` with its least element marked is a ray with its end marked:
`u` and `v` are adjacent exactly when they differ by one, and `0` is the only marked vertex.
-/

public section

open FirstOrder FirstOrder.Language TauCeti TauCeti.RelationalConfiguration

namespace TauCeti.Examples.MarkedTree

/-- The code of the chain `(ℕ, ≤)`. -/
noncomputable abbrev chain : RelationalConfiguration Language.order ℕ :=
  @ofStructure Language.order ℕ (orderStructure ℕ)

private theorem covers_chain (u v : ℕ) : Covers (codeRel leSymb chain) u v ↔ u + 1 = v := by
  simp only [covers_iff, chain, codeRel_leSymb_ofStructure_orderStructure, not_le]
  refine ⟨fun ⟨⟨_, _⟩, hw⟩ => ?_, fun h => ⟨⟨by omega, by omega⟩, fun w => by omega⟩⟩
  by_contra hne
  exact hw (u + 1) ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- In the cover graph of `(ℕ, ≤)`, two vertices are adjacent exactly when they differ by one. -/
example (u v : ℕ) : codeRel adjSymb (coverGraphCode chain) u v ↔ u + 1 = v ∨ v + 1 = u := by
  rw [codeRel_coverGraphCode, covers_chain, covers_chain]

/-- In the cover graph of `(ℕ, ≤)`, the only marked vertex is `0`. -/
example (v : ℕ) : IsMarked (coverGraphCode chain) v ↔ v = 0 := by
  simp only [isMarked_coverGraphCode, chain, codeRel_leSymb_ofStructure_orderStructure]
  exact ⟨fun h => Nat.le_zero.1 (h 0), fun h w => h ▸ Nat.zero_le w⟩

end TauCeti.Examples.MarkedTree
