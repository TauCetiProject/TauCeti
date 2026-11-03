/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Separation.Hausdorff
import TauCeti.Topology.Separation.InvFunOn

/-!
# Compactness utilities

General lemmas about compact and σ-compact subsets of topological spaces.
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X]

/-- Compactness of `U ∩ S` for a compact set `U` may be checked on open pieces of `U` around
each of its points. -/
theorem _root_.IsCompact.inter_of_forall_exists {U S : Set X} (hU : IsCompact U)
    (h : ∀ x ∈ U, ∃ U' ⊆ U, IsOpen U' ∧ x ∈ U' ∧ IsCompact (U' ∩ S)) : IsCompact (U ∩ S) := by
  choose! W hWU hWo hxW hWc using h
  obtain ⟨t, htU, htf, ht⟩ :=
    hU.elim_finite_subcover_image hWo fun x hx ↦ mem_biUnion hx (hxW x hx)
  have heq : U ∩ S = ⋃ x ∈ t, W x ∩ S := by
    rw [← iUnion₂_inter]
    exact subset_antisymm (inter_subset_inter_left S ht)
      (inter_subset_inter_left S (iUnion₂_subset fun x hx ↦ hWU x (htU hx)))
  rw [heq]
  exact htf.isCompact_biUnion fun x hx ↦ hWc x (htU hx)

/-- **A continuous injection on a compact set maps components onto components.** If `f` is
continuous and injective on a compact set `K` with values in a Hausdorff space, and `A ⊆ K`, then
`f` maps the connected component of `A` at a point `x ∈ K` onto the connected component of
`f '' A` at `f x`. Both sides are empty when `x ∉ A`. -/
theorem _root_.IsCompact.image_connectedComponentIn {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {K A : Set X} {f : X → Y} (hK : IsCompact K) (hf : ContinuousOn f K) (hinj : InjOn f K)
    (hA : A ⊆ K) {x : X} (hx : x ∈ K) :
    f '' connectedComponentIn A x = connectedComponentIn (f '' A) (f x) := by
  have : Nonempty X := ⟨x⟩
  by_cases hxA : x ∈ A
  · refine ((hf.mono hA).image_connectedComponentIn_subset hxA).antisymm fun v hv => ?_
    -- The inverse is continuous on `f '' K`, so it maps the component at `f x` back into the
    -- component at `x`.
    have hgf : LeftInvOn (Function.invFunOn f K) f K := hinj.leftInvOn_invFunOn
    have hg := ((hf.continuousOn_invFunOn_image_of_isCompact hK subset_rfl hinj (by simp)).mono
      (image_mono hA)).image_connectedComponentIn_subset (mem_image_of_mem f hxA)
    rw [hgf.image_image' hA, hgf hx] at hg
    obtain ⟨w, hwA, rfl⟩ := connectedComponentIn_subset _ _ hv
    refine ⟨w, ?_, rfl⟩
    simpa only [hgf (hA hwA)] using hg (mem_image_of_mem _ hv)
  · have hfx : f x ∉ f '' A := fun ⟨w, hwA, hw⟩ => hxA (hinj (hA hwA) hx hw ▸ hwA)
    rw [connectedComponentIn_eq_empty hxA, connectedComponentIn_eq_empty hfx, image_empty]

/-- The union of two σ-compact sets is σ-compact. -/
theorem _root_.IsSigmaCompact.union {s t : Set X} (hs : IsSigmaCompact s)
    (ht : IsSigmaCompact t) : IsSigmaCompact (s ∪ t) := by
  rw [union_eq_iUnion]
  exact isSigmaCompact_iUnion _ (Bool.forall_bool.2 ⟨ht, hs⟩)

/-- **Slices of a map proper on `s ×ˢ I` are proper**: if `(s ×ˢ I) ∩ H ⁻¹' K` is compact for
every compact `K ⊆ U`, then so is `s ∩ H (·, t) ⁻¹' K` for every `t ∈ I`. -/
theorem isCompact_inter_preimage_comp_prodMk_left {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] [T1Space Z] {s : Set X} {I : Set Z} {H : X × Z → Y}
    {U : Set Y} (hHp : ∀ K : Set Y, IsCompact K → K ⊆ U → IsCompact ((s ×ˢ I) ∩ H ⁻¹' K))
    {t : Z} (ht : t ∈ I) (K : Set Y) (hK : IsCompact K) (hKU : K ⊆ U) :
    IsCompact (s ∩ (fun x ↦ H (x, t)) ⁻¹' K) := by
  have h : s ∩ (fun x ↦ H (x, t)) ⁻¹' K =
      Prod.fst '' ((s ×ˢ I) ∩ H ⁻¹' K ∩ Prod.snd ⁻¹' {t}) := by
    ext x
    constructor
    · rintro ⟨hx, hxK⟩
      exact ⟨(x, t), ⟨⟨⟨hx, ht⟩, hxK⟩, rfl⟩, rfl⟩
    · rintro ⟨⟨y, t'⟩, ⟨⟨⟨hy, -⟩, hyK⟩, rfl : t' = t⟩, rfl⟩
      exact ⟨hy, hyK⟩
  rw [h]
  exact ((hHp K hK hKU).inter_right (isClosed_singleton.preimage continuous_snd)).image
    continuous_fst

end TauCeti

end
