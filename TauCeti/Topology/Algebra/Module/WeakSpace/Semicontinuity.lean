/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.WeakSpace.Basic
public import TauCeti.Topology.Semicontinuity.Sequences

/-!
# Sequential weak lower semicontinuity

This module unpacks sequential lower semicontinuity on `WeakSpace 𝕜 V` in terms of weakly
convergent sequences in `V` (`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff`), together with the
`EReal` lower-limit form (`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf_ereal`) and
the finite-limit form for real-valued energies bounded below
(`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_forall_le_of_tendsto`).
-/

public section

open Filter Set Topology

namespace TauCeti

variable {𝕜 V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]

/-- Sequential weak lower semicontinuity of `E` on `S` unpacked in terms of weakly convergent
sequences in `V`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff {β : Type*} [Preorder β] {E : V → β} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        ∀ b < E v, ∀ᶠ n in atTop, b < E (u n) :=
  (toWeakSpace 𝕜 V).toEquiv.seqLowerSemicontinuousOn_image_iff

/-- Sequential weak lower semicontinuity of a real-valued energy on `S`, expressed via the
`EReal` lower limit along weakly convergent sequences in `S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf_ereal {E : V → ℝ} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_coe_ereal_iff,
    seqLowerSemicontinuousOn_toWeakSpace_iff (E := fun x ↦ (E x : EReal))]
  refine forall₂_congr fun u v ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦
    imp_congr_right fun _ ↦ ?_
  exact (le_liminf_iff (u := fun n ↦ (E (u n) : EReal)) (f := atTop)).symm

/-- For a real-valued energy bounded below on `S`, sequential weak lower semicontinuity on `S`
is equivalent to the finite-limit inequality `E v ≤ r` whenever `u n ⇀ v` in `S` and
`E (u n) → r`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_forall_le_of_tendsto {E : V → ℝ} {S : Set V}
    (hb : BddBelow (E '' S)) :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ (u : ℕ → V) (v : V) (r : ℝ), (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        Tendsto (E ∘ u) atTop (𝓝 r) → E v ≤ r :=
  (toWeakSpace 𝕜 V).toEquiv.seqLowerSemicontinuousOn_image_iff_forall_le_of_tendsto hb

end TauCeti
