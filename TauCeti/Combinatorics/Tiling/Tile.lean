/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Tiling.Tile

/-!
# Free actions on placed tiles

The group `G` acts freely on the placed tiles of a protoset exactly when every prototile has
trivial symmetries: a symmetry `s` of the prototile `i` fixes the placed tile of index `i` at `1`,
and conversely `g` fixes the placed tile of index `i` at `h` only when `h⁻¹ * g * h` is a symmetry
of the prototile `i`.

## Main results

* `DiscreteTiling.PlacedTile.isCancelSMul_iff`: `G` acts freely on `PlacedTile ps` if and only if
  every prototile of `ps` has trivial symmetries.
-/

public section

namespace DiscreteTiling.PlacedTile

variable {G X ιₚ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}

/-- `G` acts freely on the placed tiles of `ps` exactly when every prototile of `ps` has trivial
symmetries. -/
theorem isCancelSMul_iff : IsCancelSMul G (PlacedTile ps) ↔ ∀ i, (ps i).symmetries = ⊥ := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  refine ⟨fun h i => (Subgroup.eq_bot_iff_forall _).2 fun s hs => ?_, fun h g pt hg => ?_⟩
  · refine Subtype.ext (h (s : G) ⟨i, (1 : G)⟩ ?_)
    rw [smul_mk_coe, mul_one, PlacedTile.mk.injEq, heq_iff_eq, QuotientGroup.eq]
    simpa using hs
  · induction pt using PlacedTile.induction_on with
    | h i x =>
      rw [smul_mk_coe, PlacedTile.mk.injEq, heq_iff_eq, QuotientGroup.eq, h] at hg
      simpa [mul_assoc, inv_mul_eq_one] using hg.2

end DiscreteTiling.PlacedTile
