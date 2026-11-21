/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.WeakSpace
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
        ∀ b < E v, ∀ᶠ n in atTop, b < E (u n) := by
  simp only [seqLowerSemicontinuousOn_iff, seqLowerSemicontinuousWithinAt_iff]
  constructor
  · intro hE u v hu hv hlim b hb
    have h := hE (toWeakSpace 𝕜 V v) (mem_image_of_mem _ hv)
      (fun n ↦ mem_image_of_mem _ (hu n)) hlim b
      (by simpa only [LinearEquiv.symm_apply_apply] using hb)
    simpa only [LinearEquiv.symm_apply_apply] using h
  · intro hE w hw u hu hlim b hb
    have hu' : ∀ n, (toWeakSpace 𝕜 V).symm (u n) ∈ S := fun n ↦ by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hu n
    have hw' : (toWeakSpace 𝕜 V).symm w ∈ S := by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hw
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm (u n))) atTop
        (𝓝 (toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm w))) := by
      simpa only [LinearEquiv.apply_symm_apply] using hlim
    exact hE _ _ hu' hw' hlim' b hb

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
        Tendsto (E ∘ u) atTop (𝓝 r) → E v ≤ r := by
  have hb' : BddBelow ((fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ''
      (toWeakSpace 𝕜 V '' S)) := by
    simpa only [image_image, LinearEquiv.symm_apply_apply] using hb
  rw [seqLowerSemicontinuousOn_iff_forall_le_of_tendsto hb']
  constructor
  · intro hE u v r hu hv hlim hEr
    have h := hE (fun n ↦ toWeakSpace 𝕜 V (u n)) (toWeakSpace 𝕜 V v) r
      (fun n ↦ mem_image_of_mem _ (hu n)) (mem_image_of_mem _ hv) hlim
      (by simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using hEr)
    simpa only [LinearEquiv.symm_apply_apply] using h
  · intro hE u w r hu hw hlim hEr
    have hu' : ∀ n, (toWeakSpace 𝕜 V).symm (u n) ∈ S := fun n ↦ by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hu n
    have hw' : (toWeakSpace 𝕜 V).symm w ∈ S := by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hw
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm (u n))) atTop
        (𝓝 (toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm w))) := by
      simpa only [LinearEquiv.apply_symm_apply] using hlim
    exact hE _ _ r hu' hw' hlim' hEr

end TauCeti
