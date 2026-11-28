/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.GroupTheory.GroupAction.IterateAct
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

/-!
# The invariant σ-algebra of an action on a measure space

For an action of `M` on a measurable space `X` with a measure `μ`, the *invariant σ-algebra*
`TauCeti.aeSMulInvariants M μ` consists of the measurable sets `s` that are invariant up to null
sets under every parameter: `(m • ·) ⁻¹' s =ᵐ[μ] s` for all `m : M`. The additive version is
`TauCeti.aeVAddInvariants M μ`. Neither invariance nor finiteness of `μ` is assumed.

## Main definitions

* `TauCeti.aeSMulInvariants M μ`, `TauCeti.aeVAddInvariants M μ`: the invariant σ-algebra.

## Main results

* `TauCeti.aeSMulInvariants_le`: it is a sub-σ-algebra of the ambient one.
* `TauCeti.measurable_aeSMulInvariants_dom`: functions measurable for the invariant σ-algebra.
* `TauCeti.ergodicSMul_iff_aeSMulInvariants`: an invariant measure is ergodic exactly when every
  invariant set is null or conull.
* `TauCeti.comap_aeSMulInvariants_le`: pullback along a measurable map that is nonsingular and
  intertwines every parameter almost everywhere (for instance a factor map) sends invariant sets
  to invariant sets.
* `TauCeti.invariants_le_aeSMulInvariants_iterateMulAct`: for a single map `T`, Mathlib's
  σ-algebra `MeasurableSpace.invariants T` of strictly invariant sets lies in the invariant
  σ-algebra of the `ℕ`-action of its iterates.
-/

public section

namespace TauCeti

open MeasureTheory Filter Set

variable (M : Type*) {X Y Z : Type*} [SMul M X] [mX : MeasurableSpace X]

/-- The invariant σ-algebra of an action: the measurable sets `s` with
`(m • ·) ⁻¹' s =ᵐ[μ] s` for every `m : M`. -/
@[instance_reducible, to_additive /-- The invariant σ-algebra of an additive action: the
measurable sets `s` with `(m +ᵥ ·) ⁻¹' s =ᵐ[μ] s` for every `m : M`. -/]
def aeSMulInvariants (μ : Measure X) : MeasurableSpace X where
  MeasurableSet' s := MeasurableSet s ∧ ∀ m : M, (m • ·) ⁻¹' s =ᵐ[μ] s
  measurableSet_empty := ⟨.empty, fun _ ↦ by rw [preimage_empty]⟩
  measurableSet_compl s hs := ⟨hs.1.compl, fun m ↦ by rw [preimage_compl]; exact (hs.2 m).compl⟩
  measurableSet_iUnion f hf := ⟨.iUnion fun i ↦ (hf i).1, fun m ↦ by
    rw [preimage_iUnion]; exact EventuallyEqSet.countable_iUnion fun i ↦ (hf i).2 m⟩

variable {M} {μ : Measure X}

/-- A set is measurable for the invariant σ-algebra exactly when it is measurable and invariant up
to null sets under every parameter. -/
@[to_additive /-- A set is measurable for the invariant σ-algebra exactly when it is measurable
and invariant up to null sets under every parameter. -/]
theorem measurableSet_aeSMulInvariants {s : Set X} :
    MeasurableSet[aeSMulInvariants M μ] s ↔
      MeasurableSet s ∧ ∀ m : M, (m • ·) ⁻¹' s =ᵐ[μ] s :=
  .rfl

/-- A function is measurable for the invariant σ-algebra exactly when it is measurable and the
preimage of every measurable set is invariant up to null sets under every parameter. -/
@[to_additive /-- A function is measurable for the invariant σ-algebra exactly when it is
measurable and the preimage of every measurable set is invariant up to null sets under every
parameter. -/]
theorem measurable_aeSMulInvariants_dom [MeasurableSpace Z] {g : X → Z} :
    Measurable[aeSMulInvariants M μ] g ↔
      Measurable g ∧ ∀ m : M, ∀ t, MeasurableSet t → (g ∘ (m • ·)) ⁻¹' t =ᵐ[μ] g ⁻¹' t := by
  simp only [Measurable, measurableSet_aeSMulInvariants, imp_and, forall_and]
  exact and_congr_right' ⟨fun h m t ht ↦ h t ht m, fun h t ht m ↦ h m t ht⟩

/-- The invariant σ-algebra is a sub-σ-algebra of the ambient one. -/
@[to_additive /-- The invariant σ-algebra is a sub-σ-algebra of the ambient one. -/]
theorem aeSMulInvariants_le : aeSMulInvariants M μ ≤ mX := fun _ hs ↦ hs.1

/-- A measurable set invariant under every parameter is in the invariant σ-algebra. -/
@[to_additive /-- A measurable set invariant under every parameter is in the invariant
σ-algebra. -/]
theorem measurableSet_aeSMulInvariants_of_preimage_eq {s : Set X} (hs : MeasurableSet s)
    (h : ∀ m : M, (m • ·) ⁻¹' s = s) : MeasurableSet[aeSMulInvariants M μ] s :=
  ⟨hs, fun m ↦ by rw [h m]⟩

/-- **Ergodicity through the invariant σ-algebra.** An invariant measure is ergodic exactly when
every set of the invariant σ-algebra is null or conull. -/
@[to_additive /-- **Ergodicity through the invariant σ-algebra.** An invariant measure is ergodic
exactly when every set of the invariant σ-algebra is null or conull. -/]
theorem ergodicSMul_iff_aeSMulInvariants [SMulInvariantMeasure M X μ] :
    ErgodicSMul M X μ ↔
      ∀ s, MeasurableSet[aeSMulInvariants M μ] s → EventuallyEmptyOrUniv s (ae μ) :=
  ⟨fun _ _ hs ↦ aeconst_of_forall_preimage_smul_ae_eq M hs.1.nullMeasurableSet hs.2,
    fun h ↦ ⟨fun hs hinv ↦ h _ ⟨hs, hinv⟩⟩⟩

variable [SMul M Y] [MeasurableSpace Y] {ν : Measure Y}

/-- **Pullback of invariant sets.** If `π : X → Y` is measurable, nonsingular from `μ` to `ν` and
intertwines every parameter almost everywhere, then the preimage of an invariant set is
invariant: `comap π (aeSMulInvariants M ν) ≤ aeSMulInvariants M μ`. This applies to factor maps. -/
@[to_additive /-- **Pullback of invariant sets.** If `π : X → Y` is measurable, nonsingular from
`μ` to `ν` and intertwines every parameter almost everywhere, then the preimage of an invariant set
is invariant: `comap π (aeVAddInvariants M ν) ≤ aeVAddInvariants M μ`. -/]
theorem comap_aeSMulInvariants_le {π : X → Y} (hπm : Measurable π)
    (hπ : QuasiMeasurePreserving π μ ν)
    (h : ∀ m : M, π ∘ (m • ·) =ᵐ[μ] (m • ·) ∘ π) :
    (aeSMulInvariants M ν).comap π ≤ aeSMulInvariants M μ := by
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨hs.1.preimage hπm, fun m ↦
    ((h m).preimage s).trans (hπ.preimage_ae_eq (hs.2 m))⟩

/-- For a single map `T`, a set measurable for Mathlib's σ-algebra of strictly invariant sets
`MeasurableSpace.invariants T` is in the invariant σ-algebra of the `ℕ`-action of the iterates of
`T`. -/
@[to_additive /-- For a single map `T`, a set measurable for Mathlib's σ-algebra of strictly
invariant sets `MeasurableSpace.invariants T` is in the invariant σ-algebra of the additive
`ℕ`-action of the iterates of `T`. -/]
theorem invariants_le_aeSMulInvariants_iterateMulAct (T : X → X) :
    MeasurableSpace.invariants T ≤ aeSMulInvariants (IterateMulAct T) μ := by
  intro s hs
  rw [MeasurableSpace.measurableSet_invariants] at hs
  refine measurableSet_aeSMulInvariants_of_preimage_eq hs.1 fun ⟨n⟩ ↦ ?_
  simpa only [IterateMulAct.mk_smul] using (Function.IsFixedPt.preimage_iterate hs.2 n).eq

end TauCeti
