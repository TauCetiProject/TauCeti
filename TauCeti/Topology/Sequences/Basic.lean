/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sequences

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
  refine ⟨fun hs u v hu hlim ↦ ?_, fun hs x p hx hlim ↦ ?_⟩
  · obtain ⟨w, hw, hwv⟩ := hs (fun n ↦ mem_image_of_mem e (hu n)) hlim
    rwa [← e.injective hwv]
  · choose u hu hux using hx
    refine ⟨e.symm p, hs hu ?_, e.apply_symm_apply p⟩
    simpa only [hux, Equiv.apply_symm_apply] using hlim

/-- In a Hausdorff space, every sequentially compact set is sequentially closed. -/
protected theorem IsSeqCompact.isSeqClosed {X : Type*} [TopologicalSpace X] [T2Space X]
    {s : Set X} (hs : IsSeqCompact s) : IsSeqClosed s := fun _ _ hu hlim ↦ by
  obtain ⟨w, hw, σ, hσ, hlim'⟩ := hs hu
  exact tendsto_nhds_unique (hlim.comp hσ.tendsto_atTop) hlim' ▸ hw
