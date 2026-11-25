/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Defect

/-!
# The defect of the block of `k[C_p]`

For a prime `p` and a field `k`, the identity `1` of `k[C_p]` has the whole group `C_p` as its
defect group at `p`, so its defect `TauCeti.blockDefect p 1` is `1`, the exponent of `|C_p| = p`,
and not `|C_p|` itself. When `k` has characteristic `p`, `1` is the single block of `k[C_p]`.
-/

public section

namespace TauCeti.Examples.BlockDefectCyclic

open MonoidAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k]

/-- The whole group `C_p` is a defect group of `1 ∈ k[C_p]` at `p`: it is a `p`-group, and
`Br_{C_p}(1) = 1 ≠ 0`. -/
theorem isDefectGroup_top :
    IsDefectGroup k p (1 : MonoidAlgebra k (Multiplicative (ZMod p))) ⊤ := by
  refine isDefectGroup_iff.2 ⟨IsPGroup.of_card (n := 1) ?_, ?_, fun Q _ _ hQ =>
    top_le_iff.1 hQ⟩
  · simp [Nat.card_eq_fintype_card]
  · rw [brauerProjection_one]
    exact one_ne_zero

/-- **The defect of `C_p` at `p` is `1`.** The defect of `1 ∈ k[C_p]` is the exponent `1` of
`|C_p| = p ^ 1`, not the order `p` of its defect group. -/
theorem blockDefect_one : blockDefect p (1 : MonoidAlgebra k (Multiplicative (ZMod p))) = 1 := by
  refine blockDefect_eq_of_forall_card (isDefectGroup_top p k) fun D hD => ?_
  rw [(isDefectGroup_iff.1 hD).2.2 ⊤ (isDefectGroup_top p k).isPGroup
    (isDefectGroup_top p k).brauerProjection_ne_zero le_top |>.symm, Subgroup.card_top]
  simp [Nat.card_eq_fintype_card]

end TauCeti.Examples.BlockDefectCyclic
