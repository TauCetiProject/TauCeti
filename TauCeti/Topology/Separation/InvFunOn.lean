/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuous inverses of maps out of compact sets, and lifts through them

A continuous injection from a compact space to a Hausdorff space is a closed embedding. This file
records the version of that fact needed for the characteristic maps of cells: let `f` be continuous
on a compact set `K`, with values in a Hausdorff space, injective on a subset `U ⊆ K`, and assume no
point of `K \ U` has the same image as a point of `U`. Then the inverse `Function.invFunOn f U` is
continuous on `f '' U` (`ContinuousOn.continuousOn_invFunOn_image_of_isCompact`). For a cell, `K`
is the closed unit ball, `U` the open unit ball, and the boundary sphere is mapped outside the open
cell.

The proof is the closed map argument: the preimage under the inverse of a closed set `C` is the
trace on `f '' U` of the compact, hence closed, set `f '' (C ∩ K)`.

Such an inverse lifts maps of the target through `f`, as in M. Brown's proof of the generalized
Schoenflies theorem. Let `f` be continuous on `Q`, with values in a `T₁` space, and injective on
`P` with inverse continuous on `f '' P`. Let `k` be continuous on `f '' Q` and the identity near
`y` within `f '' Q`, and suppose that `k ∘ f` maps `Q \ f⁻¹(y)` into `f '' P` and that every point
of `Q \ f⁻¹(y)` mapped into `f '' P` lies in `P`. Then there is a lift `g` of `k` through `f`,
continuous on `Q` and fixing `Q ∩ f⁻¹(y)` pointwise, which is injective on every `R ⊆ Q` such that
`k` is injective on `f '' R` and `f` is injective on `R \ f⁻¹(y)`
(`ContinuousOn.exists_continuousOn_injOn_lift`).

For instance, let `f` be continuous on a compact set `K`, with values in a Hausdorff space, and
injective on `K` away from the fibre over a point `y`, and let `k` be continuous and injective on
`f '' K`, equal to the identity on `f '' K` near `y`, and mapping `f '' K` into `f '' (K ∩ U)` for
a set `U` containing the fibre. Then the lift is continuous and injective on `K`, maps `K` into
`K ∩ U`, and fixes every point of `K` at whose image `k` is the identity
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
  · obtain ⟨hU, hfy⟩ := invFunOn_pos hy
    exact ⟨invFunOn f U y, ⟨hyC, hUK hU⟩, hfy⟩
  · -- A point of `K` with image in `f '' U` lies in `U`, so it is the chosen preimage.
    have hkU : k ∈ U := of_not_not fun hkU ↦ disjoint_left.1 hdisj ⟨k, ⟨hkK, hkU⟩, hky⟩ hy
    rwa [← hky, hinj.leftInvOn_invFunOn hkU]

/-- **Lifting a map which is the identity near a point.** Let `f` be continuous on `Q`, with
values in a `T₁` space, and injective on `P` with inverse continuous on `f '' P`. Let `k` be
continuous on `f '' Q` and the identity near `y` within `f '' Q`. Suppose that `k ∘ f` maps
`Q \ f⁻¹(y)` into `f '' P`, and that every point of `Q \ f⁻¹(y)` mapped into `f '' P` lies in
`P`. Then there is a map `g`, continuous on `Q`, with `f ∘ g = k ∘ f` on `Q`, which fixes
`Q ∩ f⁻¹(y)` pointwise, maps `Q \ f⁻¹(y)` into `P`, and is injective on every `R ⊆ Q` such that
`k` is injective on `f '' R` and `f` is injective on `R \ f⁻¹(y)`. -/
theorem ContinuousOn.exists_continuousOn_injOn_lift [Nonempty α] [T1Space β] {f : α → β}
    {Q P : Set α} {y : β} {k : β → β} (hf : ContinuousOn f Q)
    (hinv : ContinuousOn (invFunOn f P) (f '' P)) (hinj : InjOn f P)
    (hQP : ∀ x ∈ Q, f x ≠ y → f x ∈ f '' P → x ∈ P) (hkc : ContinuousOn k (f '' Q))
    (hkid : k =ᶠ[𝓝[f '' Q] y] id) (hkP : ∀ x ∈ Q, f x ≠ y → k (f x) ∈ f '' P) :
    ∃ g : α → α, ContinuousOn g Q ∧ (∀ x ∈ Q, f (g x) = k (f x)) ∧
      (∀ x ∈ Q, f x = y → g x = x) ∧ (∀ x ∈ Q, f x ≠ y → g x ∈ P) ∧
      ∀ R ⊆ Q, InjOn k (f '' R) → InjOn f (R \ f ⁻¹' {y}) → InjOn g R := by
  classical
  -- The identity on the fibre `f⁻¹(y)` and `f⁻¹ ∘ k ∘ f` elsewhere.
  set g : α → α := fun x ↦ if f x = y then x else invFunOn f P (k (f x))
  have hgy {x : α} (hx : f x = y) : g x = x := by simp [g, hx]
  have hg {x : α} (hx : f x ≠ y) : g x = invFunOn f P (k (f x)) := by simp [g, hx]
  have hgP {x : α} (hx : x ∈ Q) (hxy : f x ≠ y) : g x ∈ P ∧ f (g x) = k (f x) := by
    rw [hg hxy]
    exact invFunOn_pos (hkP x hx hxy)
  have hfg {x : α} (hx : x ∈ Q) : f (g x) = k (f x) := by
    by_cases hxy : f x = y
    · rw [hgy hxy, hxy]
      exact (hkid.eq_of_nhdsWithin ⟨x, hx, hxy⟩).symm
    · exact (hgP hx hxy).2
  refine ⟨g, fun x hx ↦ ?_, fun x hx ↦ hfg hx, fun x _ ↦ hgy, fun x hx hxy ↦ (hgP hx hxy).1,
    fun R hRQ hki hfR x hx x' hx' h ↦ ?_⟩
  · by_cases hxy : f x = y
    · -- Near the fibre `k` is the identity, so `g` is the identity.
      have hid : g =ᶠ[𝓝[Q] x] id := by
        filter_upwards [self_mem_nhdsWithin, (hf x hx).tendsto_nhdsWithin_image.eventually
          (p := fun z ↦ k z = z) (by rw [hxy]; exact hkid)] with x' hx' hk
        by_cases hx'y : f x' = y
        · exact hgy hx'y
        · rw [hg hx'y, hk, id]
          exact hinj.leftInvOn_invFunOn (hQP x' hx' hx'y (hk ▸ hkP x' hx' hx'y))
      exact continuousWithinAt_id.congr_of_eventuallyEq_of_mem hid hx
    · -- Off the fibre, `g` is `f⁻¹ ∘ k ∘ f` near `x`, a composite of maps continuous there.
      have hne : ∀ᶠ x' in 𝓝[Q] x, f x' ≠ y := (hf x hx).tendsto.eventually_ne hxy
      have hkf : ContinuousWithinAt (k ∘ f) Q x :=
        (hkc (f x) (mem_image_of_mem f hx)).comp (hf x hx) (mapsTo_image f Q)
      exact ((hinv _ (hkP x hx hxy)).comp_of_preimage_mem_nhdsWithin (f := k ∘ f) hkf <|
        mem_of_superset (inter_mem self_mem_nhdsWithin hne) fun x' hx' ↦ hkP x' hx'.1 hx'.2)
        |>.congr_of_eventuallyEq_of_mem (mem_of_superset hne fun _ ↦ hg) hx
  · -- `k` is injective on `f '' R`, so `x` and `x'` have the same image under `f`.
    have hfx : f x = f x' := hki (mem_image_of_mem f hx) (mem_image_of_mem f hx')
      (by rw [← hfg (hRQ hx), ← hfg (hRQ hx'), h])
    by_cases hxy : f x = y
    · rwa [hgy hxy, hgy (hfx ▸ hxy)] at h
    · exact hfR ⟨hx, hxy⟩ ⟨hx', fun h ↦ hxy (hfx.trans h)⟩ hfx

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
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨id, fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x,
      fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x⟩
  set P := K \ f ⁻¹' {y}
  have hUP : (K ∩ U) \ f ⁻¹' {y} ⊆ P := Set.sdiff_subset_sdiff_left inter_subset_left
  -- Off the fibre, `k ∘ f` avoids `y`, since `k` fixes `y` and is injective on `f '' K`.
  have hkP (x : α) (hx : x ∈ K) (hxy : f x ≠ y) : k (f x) ∈ f '' ((K ∩ U) \ f ⁻¹' {y}) := by
    rw [image_sdiff_preimage, Set.mem_sdiff, mem_singleton_iff]
    refine ⟨hkN (mem_image_of_mem f hx), fun h ↦ hxy ?_⟩
    have hyK : y ∈ f '' K := image_mono inter_subset_left (h ▸ hkN (mem_image_of_mem f hx))
    exact hki (mem_image_of_mem f hx) hyK (h.trans (hkid.eq_of_nhdsWithin hyK).symm)
  -- The inverse of `f` on `P` is continuous, since `K` is compact.
  have hinv : ContinuousOn (invFunOn f P) (f '' P) :=
    hf.continuousOn_invFunOn_image_of_isCompact hK sdiff_subset hinj <| by
      -- The image of the fibre is in `{y}`, which the image of `P` avoids.
      rw [Set.sdiff_sdiff_right_self, image_inter_preimage, image_sdiff_preimage]
      exact disjoint_sdiff_inter.symm
  obtain ⟨g, hgc, hfg, hgy, hgP, hgi⟩ := hf.exists_continuousOn_injOn_lift hinv hinj
    (fun x hx hxy _ ↦ ⟨hx, hxy⟩) hkc hkid fun x hx hxy ↦ image_mono hUP (hkP x hx hxy)
  refine ⟨g, hgc, hgi K subset_rfl hki hinj, fun x hx ↦ ?_, hfg, fun x hx hkx ↦ ?_⟩
  · by_cases hxy : f x = y
    · rw [hgy x hx hxy]
      exact ⟨hx, hXU ⟨hx, hxy⟩⟩
    exact (hinj.mem_of_mem_image hUP (hgP x hx hxy) (hfg x hx ▸ hkP x hx hxy)).1
  · by_cases hxy : f x = y
    · exact hgy x hx hxy
    · exact hinj (hgP x hx hxy) ⟨hx, hxy⟩ ((hfg x hx).trans hkx)

end
