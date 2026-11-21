/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Topology.Semicontinuity.Sequences
import TauCeti.Logic.Equiv.Set

/-!
# Weak lower semicontinuity

This module characterizes weak lower semicontinuity and sequential weak lower semicontinuity on a
subset `S : Set V` in terms of relative weak closedness
(`TauCeti.lowerSemicontinuousOn_toWeakSpace_iff_isClosed_subtype`) and relative sequential weak
closedness (`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_subtype`) of the
sublevels `{u ∈ S | E u ≤ b}` in `toWeakSpace 𝕜 V '' S`.
-/

public section

open Set

namespace TauCeti

variable {𝕜 V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]

/-- Weak lower semicontinuity of `E` on `S` is equivalent to relative weak closedness of each
sublevel `{u ∈ S | E u ≤ b}` in `toWeakSpace 𝕜 V '' S`. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_isClosed_subtype {β : Type*} [LinearOrder β]
    {E : V → β} {S : Set V} :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, IsClosed (((↑) : toWeakSpace 𝕜 V '' S → WeakSpace 𝕜 V) ⁻¹'
        (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b})) := by
  rw [← lowerSemicontinuous_restrict_iff, lowerSemicontinuous_iff_isClosed_preimage]
  refine forall_congr' fun b ↦ ?_
  have heq : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      toWeakSpace 𝕜 V '' S ∩
        (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ⁻¹' Iic b :=
    (toWeakSpace 𝕜 V).toEquiv.image_inter_preimage S E (Iic b)
  rw [heq, Subtype.preimage_coe_self_inter]
  rfl

/-- Sequential weak lower semicontinuity of `E` on `S` is equivalent to relative sequential weak
closedness of each sublevel `{u ∈ S | E u ≤ b}` in `toWeakSpace 𝕜 V '' S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_subtype {β : Type*} [LinearOrder β]
    {E : V → β} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, IsSeqClosed (((↑) : toWeakSpace 𝕜 V '' S → WeakSpace 𝕜 V) ⁻¹'
        (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b})) := by
  rw [seqLowerSemicontinuousOn_iff_isSeqClosed_subtype]
  refine forall_congr' fun b ↦ ?_
  have heq : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      toWeakSpace 𝕜 V '' S ∩
        (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ⁻¹' Iic b :=
    (toWeakSpace 𝕜 V).toEquiv.image_inter_preimage S E (Iic b)
  rw [heq, Subtype.preimage_coe_self_inter]

end TauCeti
