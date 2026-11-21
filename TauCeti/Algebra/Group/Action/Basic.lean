/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Action.Basic

/-!
# Pointwise cancellation for group actions

Trivial stabilizer at a point `x` (`∀ g : G, g • x = x → g = 1`) implies orbit cancellation
(`g • x = h • x ↔ g = h`), recorded for left actions and right (`Gᵐᵒᵖ`) actions.
-/

public section

namespace TauCeti

/-- Pointwise cancellation: trivial stabilizer at `x` implies `g • x = h • x ↔ g = h`. -/
@[to_additive /-- Pointwise additive cancellation: trivial stabilizer at `x` implies
`g +ᵥ x = h +ᵥ x ↔ g = h`. -/]
theorem smul_eq_smul_iff_of_smul_eq_self_imp {G α : Type*} [Group G] [MulAction G α] {x : α}
    (hfree : ∀ g : G, g • x = x → g = 1) {g h : G} : g • x = h • x ↔ g = h := by
  refine ⟨fun hgh ↦ ?_, fun hgh ↦ hgh ▸ rfl⟩
  rw [smul_eq_iff_eq_inv_smul, eq_comm, ← mul_smul] at hgh
  exact inv_mul_eq_one.1 (hfree (g⁻¹ * h) hgh)

/-- Right-action (`MulAction Gᵐᵒᵖ α`) pointwise cancellation: trivial stabilizer at `x` implies
`op g • x = op h • x ↔ g = h`. -/
@[to_additive /-- Right additive-action (`AddAction Gᵃᵒᵖ α`) pointwise cancellation: trivial
stabilizer at `x` implies `op g +ᵥ x = op h +ᵥ x ↔ g = h`. -/]
theorem op_smul_eq_op_smul_iff_of_op_smul_eq_self_imp {G α : Type*} [Group G] [MulAction Gᵐᵒᵖ α]
    {x : α} (hfree : ∀ g : G, MulOpposite.op g • x = x → g = 1) {g h : G} :
    MulOpposite.op g • x = MulOpposite.op h • x ↔ g = h :=
  (smul_eq_smul_iff_of_smul_eq_self_imp (G := Gᵐᵒᵖ) fun k hk ↦ MulOpposite.unop_injective
    ((hfree k.unop (k.op_unop.symm ▸ hk)).trans MulOpposite.unop_one.symm)).trans
    MulOpposite.op_injective.eq_iff

end TauCeti
