/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.CoverMultiplicity

/-!
# A cover multiplicity equal to the order of the level

Let `J` be a subgroup of a group `G`, and take `S = G`, `A = ⊥` and for `T` the single coset `J`.
The translates `r • T` through the coset `J` are those by `r ∈ J`, and modulo `S ∩ A = ⊥` these are
`|J|` distinct classes, so the cover multiplicity of `J` is the order of `J`
(`Subgroup.coverMultiplicity_eq_relIndex`). In particular cover multiplicities take every value,
and the multiplicity is `0` exactly when `J` is infinite.
-/

public section

open MulAction

namespace TauCeti.Examples.CoverMultiplicity

/-- For `S = G`, `A = ⊥` and `T = {J}`, the cover multiplicity of the coset `J` is the order of
`J`. -/
theorem coverMultiplicity_top_bot_singleton_one {G : Type*} [Group G] (J : Subgroup G) :
    (⊤ : Subgroup G).coverMultiplicity ⊥ {((1 : G) : G ⧸ J)} ((1 : G) : G ⧸ J) = Nat.card J := by
  rw [Subgroup.coverMultiplicity_eq_relIndex ⟨_, rfl, mem_orbit_self _⟩
    fun x hx ↦ Set.mem_singleton_iff.1 hx.1 ▸ mem_orbit_self _, top_inf_eq, stabilizer_quotient,
    Subgroup.relIndex_bot_left]

end TauCeti.Examples.CoverMultiplicity
