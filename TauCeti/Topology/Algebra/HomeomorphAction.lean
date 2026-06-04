/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# The tautological action of the homeomorphism group

For a topological space `E`, the homeomorphism group `E ≃ₜ E` acts on `E` by evaluation:
`φ • e = φ e`. This file records that action, that it is faithful, and that it is continuous
in the point, mirroring `Equiv.Perm.applyMulAction` and the construction in Kim Morrison's
mathlib4#40135.

## Main definitions

* `TauCeti.Homeomorph.applyMulAction`: the `MulAction (E ≃ₜ E) E` with `φ • e = φ e`.
* `TauCeti.Homeomorph.smul_def`: the defining simp lemma `φ • e = φ e`.
* `TauCeti.Homeomorph.applyFaithfulSMul`: the action is faithful.
* `TauCeti.Homeomorph.applyContinuousConstSMul`: each homeomorphism acts continuously.
-/

namespace TauCeti

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]

/-- The tautological action of the homeomorphism group `E ≃ₜ E` on `E` by evaluation. -/
instance applyMulAction : MulAction (E ≃ₜ E) E where
  smul φ e := φ e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological action of `E ≃ₜ E` on `E` is given by evaluation. -/
@[simp]
lemma smul_def (φ : E ≃ₜ E) (e : E) : φ • e = φ e := rfl

/-- The tautological action of `E ≃ₜ E` on `E` is faithful. -/
instance applyFaithfulSMul : FaithfulSMul (E ≃ₜ E) E :=
  ⟨fun h => Homeomorph.ext h⟩

/-- The tautological action of `E ≃ₜ E` on `E` is continuous in the point. -/
instance applyContinuousConstSMul : ContinuousConstSMul (E ≃ₜ E) E :=
  ⟨fun φ => φ.continuous⟩

-- Faithfulness for a `Subgroup (E ≃ₜ E)` is already supplied by Mathlib's generic subgroup
-- action transfer (`Mathlib.Algebra.Group.Subgroup.Actions`) from the ambient `applyFaithfulSMul`,
-- so we do not restate it. Continuity in the point, however, has no such subgroup transfer:

/-- A subgroup of the homeomorphism group acts continuously on `E` in the point, reusing
continuity of the ambient action. Mathlib transfers `MulAction` and `FaithfulSMul` to a
subgroup but not `ContinuousConstSMul`, so we record it here. -/
instance applySubgroupContinuousConstSMul (H : Subgroup (E ≃ₜ E)) : ContinuousConstSMul H E :=
  ⟨fun φ => continuous_const_smul (φ : E ≃ₜ E)⟩

end Homeomorph

end TauCeti
