/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

/-!
# The invariant σ-algebra of a group action

For a group `G` acting on a measurable space `X`, the σ-algebra
`⨅ g : G, MeasurableSpace.invariants (g • ·)` consists of the measurable sets that are fixed
blocks of the action (`TauCeti.measurableSet_iInf_invariants_iff`).
-/

public section

open MeasureTheory Set
open scoped Pointwise

namespace TauCeti

/-- **The invariant σ-algebra of a group action.** A set is measurable for
`⨅ g, MeasurableSpace.invariants (g • ·)` exactly when it is measurable and a fixed block of the
action. -/
theorem measurableSet_iInf_invariants_iff {G X : Type*} [Group G] [MeasurableSpace X]
    [MulAction G X] {B : Set X} :
    MeasurableSet[⨅ g : G, MeasurableSpace.invariants (fun x : X => g • x)] B ↔
      MeasurableSet B ∧ MulAction.IsFixedBlock G B := by
  simp only [MeasurableSpace.measurableSet_iInf, MeasurableSpace.measurableSet_invariants,
    preimage_smul, forall_and, forall_const]
  exact and_congr_right fun _ => (inv_surjective.forall (p := fun g : G => g • B = B)).symm

end TauCeti
