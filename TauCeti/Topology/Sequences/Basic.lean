/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sequences
import TauCeti.Logic.Equiv.Set

/-!
# Sequential closedness under equivalences and sequential compactness

For any bijection `e : X ≃ Y` into a topological space `Y`, sequential closedness of an image
`e '' s` translates directly to closure of `s` under sequences whose images under `e` converge
(`Equiv.isSeqClosed_image_iff`), without requiring a topology on `X`. In a Hausdorff space, every
sequentially compact set is sequentially closed (`IsSeqCompact.isSeqClosed`).
-/

public section

open Filter Set Topology

/-- Sequential closedness of `e '' s` under an equivalence `e : X ≃ Y` into a topological space
`Y` is equivalent to closure of `s` under limits of sequences whose images under `e` converge. -/
theorem Equiv.isSeqClosed_image_iff {X Y : Type*} [TopologicalSpace Y] (e : X ≃ Y) {s : Set X} :
    IsSeqClosed (e '' s) ↔
      ∀ ⦃u : ℕ → X⦄ ⦃v : X⦄, (∀ n, u n ∈ s) →
        Tendsto (fun n ↦ e (u n)) atTop (𝓝 (e v)) → v ∈ s := by
  have h := e.forall_mem_image_fun_iff (ι := ℕ) s univ
    (fun y u ↦ Tendsto u atTop (𝓝 y) → y ∈ e '' s)
  simp only [image_univ, EquivLike.range_eq_univ, mem_univ, forall_true_left,
    e.injective.mem_set_image] at h
  exact ⟨fun hs u v hu hlim ↦ h.1 (fun y u hu hlim ↦ hs hu hlim) u v hu hlim,
    fun hs u y hu hlim ↦ h.2 (fun u v hu hlim ↦ hs hu hlim) y hu hlim⟩

/-- In a Hausdorff space, every sequentially compact set is sequentially closed. -/
protected theorem IsSeqCompact.isSeqClosed {X : Type*} [TopologicalSpace X] [T2Space X]
    {s : Set X} (hs : IsSeqCompact s) : IsSeqClosed s := fun _ _ hu hlim ↦ by
  obtain ⟨w, hw, σ, hσ, hlim'⟩ := hs hu
  exact tendsto_nhds_unique (hlim.comp hσ.tendsto_atTop) hlim' ▸ hw
