/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow

/-!
# Elements carrying a coset of an iterated quotient to the base coset

Let `C` be a normal subgroup of a group `G` and `D` a subgroup of `G ⧸ C`, so that `G` acts on the
cosets `(G ⧸ C) ⧸ D` through `G ⧸ C`. The elements of `G` carrying a given coset to the base coset
form a translate of the preimage of `D` in `G`, so there are `|C| |D|` of them.

## Main results

* `QuotientGroup.natCard_inv_smul_eq_mk_one`: the number of `g` with `g⁻¹ • x` the base coset is
  `|C| |D|`.
-/

public section

namespace QuotientGroup

variable {G : Type*} [Group G] (C : Subgroup G) [C.Normal] (D : Subgroup (G ⧸ C))

/-- The elements of `G` carrying a coset `x` of `D` in `G ⧸ C` to the base coset are counted by
`|C| |D|`. -/
theorem natCard_inv_smul_eq_mk_one (x : (G ⧸ C) ⧸ D) :
    Nat.card {g : G // (mk' C g)⁻¹ • x = (mk 1 : (G ⧸ C) ⧸ D)} = Nat.card C * Nat.card D := by
  obtain ⟨y, rfl⟩ := mk_surjective x
  obtain ⟨h, rfl⟩ := mk_surjective y
  -- The translation `g ↦ g⁻¹ * h` carries these elements onto the preimage of `D`.
  have hmem (g : G) : (mk' C g)⁻¹ • (mk (mk h : G ⧸ C) : (G ⧸ C) ⧸ D) = mk 1 ↔
      (mk (g⁻¹ * h) : G ⧸ C) ∈ (D : Set (G ⧸ C)) := by
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, mul_one, inv_mem_iff, mk'_apply, smul_eq_mul,
      mk_mul, mk_inv, SetLike.mem_coe]
  rw [← SetLike.coe_sort_coe D, ← card_preimage_mk C (D : Set (G ⧸ C))]
  exact Nat.card_congr (((Equiv.inv G).trans (Equiv.mulRight h)).subtypeEquiv hmem)

end QuotientGroup
