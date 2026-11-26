/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Equivariance of the orbit-stabilizer equivalence

Mathlib's `MulAction.orbitEquivQuotientStabilizer G b : orbit G b ≃ G ⧸ stabilizer G b` is defined
as the inverse of the equivariant bijection induced by `MulAction.ofQuotientStabilizer`. This file
records that `orbitEquivQuotientStabilizer` (and its additive counterpart) intertwines the
`G`-action on `orbit G b` with left translation on `G ⧸ stabilizer G b`.

## Main results

* `TauCeti.orbitEquivQuotientStabilizer_smul`, `TauCeti.orbitEquivQuotientStabilizer_vadd`:
  `orbitEquivQuotientStabilizer` commutes with the group action.
-/

public section

namespace TauCeti

/-- `MulAction.orbitEquivQuotientStabilizer` intertwines the `G`-action on `orbit G b` with left
translation on `G ⧸ stabilizer G b`. -/
@[to_additive (attr := simp)
  /-- `AddAction.orbitEquivQuotientStabilizer` intertwines the additive `G`-action on `orbit G b`
  with translation on `G ⧸ stabilizer G b`. -/]
theorem orbitEquivQuotientStabilizer_smul {G X : Type*} [Group G] [MulAction G X] (b : X)
    (g : G) (u : MulAction.orbit G b) :
    MulAction.orbitEquivQuotientStabilizer G b (g • u) =
      g • MulAction.orbitEquivQuotientStabilizer G b u := by
  let e := MulAction.orbitEquivQuotientStabilizer G b
  apply e.symm.injective
  obtain ⟨q, rfl⟩ := e.symm.surjective u
  rw [e.symm_apply_apply, e.apply_symm_apply]
  induction q using QuotientGroup.induction_on with
  | H x =>
    ext
    simp [e, smul_eq_mul, mul_smul]

end TauCeti
