/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Reading neighbourhoods and limits through an inducing restriction

If the restriction of a map `f` to a set `K` is inducing, then neighbourhoods of a point of `K`
within `K` (`Topology.IsInducing.exists_mem_nhds_inter_preimage_subset`) and convergence to a point
of `K` of a family eventually in `K` (`Topology.IsInducing.tendsto_nhds_of_tendsto_comp`) can be
read through `f`. If moreover `f '' K` is closed, then so can limits of maps: let the values at each
point of a set `Ω` of maps `x i` eventually lie in `K` along a nontrivial filter. A limit `g`,
continuous on `Ω`, of the maps `f ∘ x i` pointwise on `Ω` is `f ∘ y` on `Ω` for a map `y`
continuous on `Ω`, and the `x i` converge to `y` pointwise on `Ω`
(`Topology.IsInducing.exists_tendsto_of_tendsto_comp`). This is how a limit in a manifold without
a metric is constructed from a limit measured through an embedding into a normed space.

A continuous injection on a compact set with values in a Hausdorff space restricts to a closed
embedding, so all of this applies to it; see `TauCeti.Topology.Compactness.Compact`.
-/

public section

open Filter Set Topology

namespace Topology.IsInducing

variable {X : Type*} [TopologicalSpace X]

/-- **Neighbourhoods in a set are read through a map inducing its topology.** Let the restriction
of `f` to a set `K` be inducing. For `x ∈ K` and a neighbourhood `s` of `x` within `K`, there is
a neighbourhood `t` of `f x` such that every point of `K` that `f` maps into `t` lies in `s`. -/
theorem exists_mem_nhds_inter_preimage_subset {Y : Type*} [TopologicalSpace Y] {K : Set X}
    {f : X → Y} (hf : IsInducing (K.domRestrict f)) {x : X} (hx : x ∈ K) {s : Set X}
    (hs : s ∈ 𝓝[K] x) : ∃ t ∈ 𝓝 (f x), K ∩ f ⁻¹' t ⊆ s := by
  -- Inside `K`, the neighbourhoods of `x` are read through `f`.
  rw [nhdsWithin_eq_map_subtypeVal hx, mem_map, hf.nhds_eq_comap, mem_comap] at hs
  obtain ⟨t, ht, hts⟩ := hs
  refine ⟨t, ht, fun p ⟨hpK, hpt⟩ ↦ hts (a := ⟨p, hpK⟩) ?_⟩
  rwa [mem_preimage, domRestrict_apply]

/-- **Convergence in a set is read through a map inducing its topology.** Let the restriction of
`f` to a set `K` be inducing, and let `g` eventually take values in `K`. If `f ∘ g` tends to `f x`
for some `x ∈ K`, then `g` tends to `x`. -/
theorem tendsto_nhds_of_tendsto_comp {Y ι : Type*} [TopologicalSpace Y] {K : Set X}
    {f : X → Y} (hf : IsInducing (K.domRestrict f)) {l : Filter ι} {g : ι → X}
    (hg : ∀ᶠ i in l, g i ∈ K) {x : X} (hx : x ∈ K) (h : Tendsto (f ∘ g) l (𝓝 (f x))) :
    Tendsto g l (𝓝 x) := by
  intro s hs
  obtain ⟨t, ht, hts⟩ :=
    hf.exists_mem_nhds_inter_preimage_subset hx (mem_nhdsWithin_of_mem_nhds hs)
  exact (hg.and (h.eventually_mem ht)).mono fun i hi ↦ hts hi

/-- **Limits read back through a map inducing the topology of a set.** Let the restriction of `f`
to a set `K` be inducing, with `f '' K` closed, and let `x i` be maps from a space `T` whose values
at each point of a set `Ω ⊆ T` eventually lie in `K` along a nontrivial filter `l`. If the maps
`f ∘ x i` converge along `l` pointwise on `Ω` to a map `g` continuous on `Ω`, then `g = f ∘ y` on
`Ω` for a map `y` that is continuous on `Ω` and maps `Ω` into `K`, and the `x i` converge along `l`
pointwise on `Ω` to `y`. -/
theorem exists_tendsto_of_tendsto_comp {Y : Type*} [TopologicalSpace Y] {K : Set X}
    {f : X → Y} (hf : IsInducing (K.domRestrict f)) (hfK : IsClosed (f '' K)) {T : Type*}
    [TopologicalSpace T] {Ω : Set T} {ι : Type*} {l : Filter ι} [l.NeBot] {x : ι → T → X}
    (hxK : ∀ t ∈ Ω, ∀ᶠ i in l, x i t ∈ K) {g : T → Y} (hg : ContinuousOn g Ω)
    (hlim : ∀ t ∈ Ω, Tendsto (fun i ↦ f (x i t)) l (𝓝 (g t))) :
    ∃ y : T → X, ContinuousOn y Ω ∧ MapsTo y Ω K ∧ EqOn (f ∘ y) g Ω ∧
      ∀ t ∈ Ω, Tendsto (fun i ↦ x i t) l (𝓝 (y t)) := by
  obtain ⟨i⟩ := l.nonempty_of_neBot
  rcases isEmpty_or_nonempty X with hX | hX
  · -- Then `T` is empty too, as the map `x i : T → X` shows.
    have := Function.isEmpty (x i)
    exact ⟨x i, fun t ↦ isEmptyElim t, fun t ↦ isEmptyElim t, fun t ↦ isEmptyElim t,
      fun t ↦ isEmptyElim t⟩
  -- The limit takes values in the closed set `f(K)`, so it lifts to `K`.
  have hgK : MapsTo g Ω (f '' K) := fun t ht ↦
    hfK.mem_of_tendsto (hlim t ht) ((hxK t ht).mono fun i ↦ mem_image_of_mem f)
  set y := Function.invFunOn f K ∘ g
  have hy (t : T) (ht : t ∈ Ω) : y t ∈ K ∧ f (y t) = g t := Function.invFunOn_pos (hgK ht)
  -- Both the continuity of `y` and the convergence to it are read in `K` through `f`.
  refine ⟨y, fun t ht ↦ hf.tendsto_nhds_of_tendsto_comp
      (eventually_nhdsWithin_of_forall fun t' ht' ↦ (hy t' ht').1) (hy t ht).1 ?_,
    fun t ht ↦ (hy t ht).1, fun t ht ↦ (hy t ht).2,
    fun t ht ↦ hf.tendsto_nhds_of_tendsto_comp (hxK t ht) (hy t ht).1 ?_⟩
  · rw [(hy t ht).2]
    exact tendsto_nhdsWithin_congr (fun t' ht' ↦ (hy t' ht').2.symm) (hg t ht)
  · rw [(hy t ht).2]
    exact hlim t ht

end Topology.IsInducing
