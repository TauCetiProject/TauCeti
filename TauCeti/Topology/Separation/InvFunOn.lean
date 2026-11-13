/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuity of inverses of maps out of compact sets

A continuous injection from a compact space to a Hausdorff space is a closed embedding. This file
records the version of that fact needed for the characteristic maps of cells: let `f` be continuous
on a compact set `K`, with values in a Hausdorff space, injective on a subset `U ⊆ K`, and assume no
point of `K \ U` has the same image as a point of `U`. Then the inverse `Function.invFunOn f U` is
continuous on `f '' U` (`ContinuousOn.continuousOn_invFunOn_image_of_isCompact`). For a cell, `K`
is the closed unit ball, `U` the open unit ball, and the boundary sphere is mapped outside the open
cell.

The proof is the closed map argument: the preimage under the inverse of a closed set `C` is the
trace on `f '' U` of the compact, hence closed, set `f '' (C ∩ K)`.

As an application, let `f` be continuous on `K` and injective on `K` away from the fibre over a
point `y`, and let `k` be continuous and injective on `f '' K`, equal to the identity on `f '' K`
near `y`, and mapping `f '' K` into `f '' (K ∩ U)` for a set `U` containing the fibre. Then there
is a map `g`, continuous and injective on `K`, which maps `K` into `K ∩ U`, lifts `k` through `f`
on `K`, and fixes every point of `K` at whose image `k` is the identity
(`ContinuousOn.exists_continuousOn_injOn_mapsTo_of_mapsTo_image`). This is the shrinking step in
M. Brown's proof that the only inverse set of a map of a cell is cellular.
-/

public section

open Function Set Filter Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- **Inverses of maps out of compact sets are continuous.** If `f` is continuous on a compact set
`K` with values in a Hausdorff space, injective on `U ⊆ K`, and no point of `K \ U` has the same
image as a point of `U`, then the inverse `invFunOn f U` of `f` on `U` is continuous on `f '' U`.
-/
theorem ContinuousOn.continuousOn_invFunOn_image_of_isCompact [Nonempty α] [T2Space β]
    {f : α → β} {K U : Set α} (hf : ContinuousOn f K) (hK : IsCompact K) (hUK : U ⊆ K)
    (hinj : InjOn f U) (hdisj : Disjoint (f '' (K \ U)) (f '' U)) :
    ContinuousOn (invFunOn f U) (f '' U) := by
  refine continuousOn_iff_isClosed.2 fun C hC ↦
    ⟨f '' (C ∩ K), ((hK.inter_left hC).image_of_continuousOn (hf.mono inter_subset_right)).isClosed,
      ?_⟩
  ext y
  simp only [mem_inter_iff, mem_preimage]
  refine ⟨fun ⟨hyC, hy⟩ ↦ ⟨?_, hy⟩, fun ⟨⟨k, ⟨hkC, hkK⟩, hky⟩, hy⟩ ↦ ⟨?_, hy⟩⟩
  · exact ⟨invFunOn f U y, ⟨hyC, hUK (invFunOn_mem hy)⟩, invFunOn_eq hy⟩
  · -- A point of `K` with image in `f '' U` lies in `U`, so it is the chosen preimage.
    have hkU : k ∈ U := by
      by_contra hkU
      exact disjoint_left.1 hdisj ⟨k, ⟨hkK, hkU⟩, hky⟩ hy
    rwa [← hky, hinj.leftInvOn_invFunOn hkU]

/-- **Lifting a map of the target through a map injective off one fibre.** Let `f` be continuous
on a compact set `K` with values in a Hausdorff space, and injective on `K` away from the fibre
`K ∩ f ⁻¹' {y}`. Let `k` be continuous and injective on `f '' K`, equal to the identity on `f '' K`
near `y`, and mapping `f '' K` into `f '' (K ∩ U)` for a set `U` containing the fibre. Then there
is a map `g`, continuous and injective on `K`, which maps `K` into `K ∩ U`, satisfies
`f (g x) = k (f x)` on `K`, and fixes every point `x` of `K` with `k (f x) = f x`. -/
theorem ContinuousOn.exists_continuousOn_injOn_mapsTo_of_mapsTo_image [T2Space β] {f : α → β}
    {K : Set α} {y : β} (hf : ContinuousOn f K) (hK : IsCompact K)
    (hinj : InjOn f (K \ f ⁻¹' {y})) {U : Set α} (hXU : K ∩ f ⁻¹' {y} ⊆ U) {k : β → β}
    (hkc : ContinuousOn k (f '' K)) (hki : InjOn k (f '' K)) (hkid : k =ᶠ[𝓝[f '' K] y] id)
    (hkN : MapsTo k (f '' K) (f '' (K ∩ U))) :
    ∃ g : α → α, ContinuousOn g K ∧ InjOn g K ∧ MapsTo g K (K ∩ U) ∧
      (∀ x ∈ K, f (g x) = k (f x)) ∧ ∀ x ∈ K, k (f x) = f x → g x = x := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨id, fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x,
      fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x⟩
  set P := K \ f ⁻¹' {y}
  have heq {x x' : α} (hx : x ∈ K) (hx' : x' ∈ K) (h : f x = f x') (hy : f x ≠ y) : x = x' :=
    hinj ⟨hx, hy⟩ ⟨hx', fun h' ↦ hy (h.trans h')⟩ h
  -- `k` fixes `y` as soon as `y` is a value of `f` on `K`.
  have hky {x : α} (hx : x ∈ K) (hxy : f x = y) : k y = y :=
    hkid.eq_of_nhdsWithin ⟨x, hx, hxy⟩
  have hkP {x : α} (hx : x ∈ P) : k (f x) ∈ f '' P := by
    obtain ⟨x', hx', hx'k⟩ := hkN (mem_image_of_mem f hx.1)
    refine ⟨x', ⟨hx'.1, fun h ↦ hx.2 ?_⟩, hx'k⟩
    have hfx' : f x' = y := mem_singleton_iff.1 h
    exact hki (mem_image_of_mem f hx.1) (hfx' ▸ mem_image_of_mem f hx'.1)
      (hx'k.symm.trans hfx' ▸ (hky hx'.1 hfx').symm)
  set g : α → α := fun x ↦ if f x = y then x else invFunOn f P (k (f x))
  have hg {x : α} (hx : f x ≠ y) : g x = invFunOn f P (k (f x)) := by simp [g, hx]
  have hgP {x : α} (hx : x ∈ P) : g x ∈ P ∧ f (g x) = k (f x) := by
    rw [hg hx.2]
    exact ⟨invFunOn_mem (hkP hx), invFunOn_eq (hkP hx)⟩
  have hfg {x : α} (hx : x ∈ K) : f (g x) = k (f x) := by
    by_cases hxy : f x = y
    · simp [g, hxy, hky hx hxy]
    · exact (hgP ⟨hx, hxy⟩).2
  have hfix {x : α} (hx : x ∈ K) (hkx : k (f x) = f x) : g x = x := by
    by_cases hxy : f x = y
    · simp [g, hxy]
    have hfgx : f (g x) = f x := (hfg hx).trans hkx
    exact heq (hgP ⟨hx, hxy⟩).1.1 hx hfgx (by rwa [hfgx])
  refine ⟨g, fun x hx ↦ ?_, fun x hx x' hx' h ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ hfg hx,
    fun x hx ↦ hfix hx⟩
  · -- Near a point mapped close to `y`, `g` is the identity; elsewhere it is `f⁻¹ ∘ k ∘ f`.
    obtain ⟨W, hW, hyW, hWk⟩ := mem_nhdsWithin.1 hkid
    by_cases hxW : f x ∈ W
    · have hid : g =ᶠ[𝓝[K] x] id := by
        filter_upwards [self_mem_nhdsWithin,
          (hf x hx).preimage_mem_nhdsWithin (hW.mem_nhds hxW)] with x' hx' hx'W
        exact hfix hx' (hWk ⟨hx'W, mem_image_of_mem f hx'⟩)
      exact continuousWithinAt_id.congr_of_eventuallyEq hid (hid.eq_of_nhdsWithin hx)
    have hxP : x ∈ P := ⟨hx, fun h ↦ hxW (mem_singleton_iff.1 h ▸ hyW)⟩
    -- The inverse of `f` on `P` is continuous, since `K` is compact.
    have hinv : ContinuousOn (invFunOn f P) (f '' P) :=
      hf.continuousOn_invFunOn_image_of_isCompact hK sdiff_subset hinj
        (disjoint_left.2 fun _ ⟨a, ha, haz⟩ ⟨b, hb, hbz⟩ ↦
          hb.2 (hbz.trans (haz.symm.trans (not_not.1 fun h ↦ ha.2 ⟨ha.1, h⟩))))
    have hkf : ContinuousWithinAt (fun x' ↦ k (f x')) P x :=
      (hkc _ (mem_image_of_mem f hx)).comp ((hf x hx).mono sdiff_subset)
        fun x' hx' ↦ mem_image_of_mem f hx'.1
    have hgx : ContinuousWithinAt g P x :=
      ((hinv _ (hkP hxP)).comp (f := fun x' ↦ k (f x')) hkf fun x' hx' ↦ hkP hx').congr
        (fun x' hx' ↦ hg hx'.2) (hg hxP.2)
    exact hgx.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
      ((hf x hx).preimage_mem_nhdsWithin (isOpen_compl_singleton.mem_nhds hxP.2)))
  · have hfx : f x = f x' := hki (mem_image_of_mem f hx) (mem_image_of_mem f hx')
      (by rw [← hfg hx, ← hfg hx', h])
    by_cases hxy : f x = y
    · simpa [g, hxy, ← hfx] using h
    · exact heq hx hx' hfx hxy
  · by_cases hxy : f x = y
    · simpa [g, hxy] using ⟨hx, hXU ⟨hx, hxy⟩⟩
    obtain ⟨hgx, hfgx⟩ := hgP ⟨hx, hxy⟩
    obtain ⟨x', hx', hx'k⟩ := hkN (mem_image_of_mem f hx)
    rw [heq hgx.1 hx'.1 (hfgx.trans hx'k.symm) hgx.2]
    exact hx'

end
