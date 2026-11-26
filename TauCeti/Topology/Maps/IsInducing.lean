/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Reading neighbourhoods and limits through an inducing restriction

If the restriction of a map `f` to a set `K` is inducing, then at every point `x ∈ K` the
within-neighbourhood filter `𝓝[K] x` is the pullback `comap f (𝓝 (f x)) ⊓ 𝓟 K`
(`Topology.IsInducing.nhdsWithin_eq_comap_inf_principal_of_domRestrict`), generalizing
`OpenPartialHomeomorph.nhds_eq_comap_inf_principal` to arbitrary subsets without openness. Hence
within-neighbourhoods of `x ∈ K` (`Topology.IsInducing.mem_nhdsWithin_iff_of_domRestrict`,
`Topology.IsInducing.exists_mem_nhds_inter_preimage_subset`) and convergence to `𝓝[K] x` or `𝓝 x`
for families eventually in `K` (`Topology.IsInducing.tendsto_nhdsWithin_iff_of_domRestrict`,
`Topology.IsInducing.tendsto_nhds_iff_of_domRestrict`,
`Topology.IsInducing.tendsto_nhds_of_tendsto_comp`) can be read through `f`. So can limits of maps:
let the values at each point of a set `Ω` of maps `x i`
eventually lie in `K` along a nontrivial filter. A limit `g`, continuous on `Ω` and with values in
`f '' K` on `Ω`, of the maps `f ∘ x i` pointwise on `Ω` is `f ∘ y` on `Ω` for a map `y` continuous
on `Ω`, and the `x i` converge to `y` pointwise on `Ω`
(`Topology.IsInducing.exists_tendsto_of_tendsto_comp`). If `f '' K` is closed, the limit `g` takes
values in it automatically. This is how a limit in a manifold without
a metric is constructed from a limit measured through an embedding into a normed space.

A continuous injection on a compact set with values in a Hausdorff space restricts to a closed
embedding, so all of this applies to it; see `TauCeti.Topology.Compactness.Compact`.
-/

public section

open Filter Set Topology

namespace Topology.IsInducing

variable {X : Type*} [TopologicalSpace X]

/-- If `f` restricts to a topologically inducing map on `s`, then at every `x ∈ s` the
within-neighbourhood filter `𝓝[s] x` is the pullback along `f` of `𝓝 (f x)` restricted to `s`. -/
theorem nhdsWithin_eq_comap_inf_principal_of_domRestrict {Y : Type*} [TopologicalSpace Y]
    {s : Set X} {f : X → Y} (hf : IsInducing (s.domRestrict f)) {x : X} (hx : x ∈ s) :
    𝓝[s] x = comap f (𝓝 (f x)) ⊓ 𝓟 s := by
  rw [nhdsWithin_eq_map_subtypeVal hx, hf.nhds_eq_comap, domRestrict_eq, Function.comp_apply,
    ← comap_comap, map_comap_setCoe_val]

/-- If `f` restricts to a topologically inducing map on `s`, then at `x ∈ s` the
within-neighbourhoods `W ∈ 𝓝[s] x` are precisely the sets containing `{y ∈ s | f y ∈ V}` for some
`V ∈ 𝓝 (f x)`. -/
theorem mem_nhdsWithin_iff_of_domRestrict {Y : Type*} [TopologicalSpace Y] {s : Set X}
    {f : X → Y} (hf : IsInducing (s.domRestrict f)) {x : X} (hx : x ∈ s) {W : Set X} :
    W ∈ 𝓝[s] x ↔ ∃ V ∈ 𝓝 (f x), ∀ y ∈ s, f y ∈ V → y ∈ W := by
  rw [hf.nhdsWithin_eq_comap_inf_principal_of_domRestrict hx, mem_inf_principal, mem_comap]
  exact ⟨fun ⟨V, hV, hVW⟩ ↦ ⟨V, hV, fun _ hys hfy ↦ hVW hfy hys⟩,
    fun ⟨V, hV, hVW⟩ ↦ ⟨V, hV, fun _ hfy hys ↦ hVW _ hys hfy⟩⟩

/-- If `f` restricts to a topologically inducing map on `s`, then convergence to `𝓝[s] x` at
`x ∈ s` is equivalent to convergence of `f ∘ g` to `𝓝 (f x)` together with eventual membership in
`s`. -/
theorem tendsto_nhdsWithin_iff_of_domRestrict {Y ι : Type*} [TopologicalSpace Y] {s : Set X}
    {f : X → Y} {g : ι → X} {l : Filter ι} (hf : IsInducing (s.domRestrict f)) {x : X}
    (hx : x ∈ s) :
    Tendsto g l (𝓝[s] x) ↔ Tendsto (f ∘ g) l (𝓝 (f x)) ∧ ∀ᶠ i in l, g i ∈ s := by
  rw [hf.nhdsWithin_eq_comap_inf_principal_of_domRestrict hx, tendsto_inf, tendsto_comap_iff,
    tendsto_principal]

/-- If `f` restricts to a topologically inducing map on `s`, `x ∈ s`, and `g` eventually takes
values in `s`, then `g` tends to `x` if and only if `f ∘ g` tends to `f x`. -/
theorem tendsto_nhds_iff_of_domRestrict {Y ι : Type*} [TopologicalSpace Y] {s : Set X}
    {f : X → Y} {g : ι → X} {l : Filter ι} (hf : IsInducing (s.domRestrict f)) {x : X}
    (hx : x ∈ s) (hg : ∀ᶠ i in l, g i ∈ s) :
    Tendsto g l (𝓝 x) ↔ Tendsto (f ∘ g) l (𝓝 (f x)) :=
  (and_iff_left hg).symm.trans <| tendsto_nhdsWithin_iff.symm.trans <|
    (hf.tendsto_nhdsWithin_iff_of_domRestrict hx).trans (and_iff_left hg)

/-- **Neighbourhoods in a set are read through a map inducing its topology.** Let the restriction
of `f` to a set `K` be inducing. For `x ∈ K` and a neighbourhood `s` of `x` within `K`, there is
a neighbourhood `t` of `f x` such that every point of `K` that `f` maps into `t` lies in `s`. -/
theorem exists_mem_nhds_inter_preimage_subset {Y : Type*} [TopologicalSpace Y] {K : Set X}
    {f : X → Y} (hf : IsInducing (K.domRestrict f)) {x : X} (hx : x ∈ K) {s : Set X}
    (hs : s ∈ 𝓝[K] x) : ∃ t ∈ 𝓝 (f x), K ∩ f ⁻¹' t ⊆ s :=
  ((hf.mem_nhdsWithin_iff_of_domRestrict hx).1 hs).imp fun _ ⟨ht, hts⟩ ↦
    ⟨ht, fun _ ⟨hpK, hpt⟩ ↦ hts _ hpK hpt⟩

/-- **Convergence in a set is read through a map inducing its topology.** Let the restriction of
`f` to a set `K` be inducing, and let `g` eventually take values in `K`. If `f ∘ g` tends to `f x`
for some `x ∈ K`, then `g` tends to `x`. -/
theorem tendsto_nhds_of_tendsto_comp {Y ι : Type*} [TopologicalSpace Y] {K : Set X}
    {f : X → Y} (hf : IsInducing (K.domRestrict f)) {l : Filter ι} {g : ι → X}
    (hg : ∀ᶠ i in l, g i ∈ K) {x : X} (hx : x ∈ K) (h : Tendsto (f ∘ g) l (𝓝 (f x))) :
    Tendsto g l (𝓝 x) :=
  (hf.tendsto_nhds_iff_of_domRestrict hx hg).2 h

/-- **Limits read back through a map inducing the topology of a set.** Let the restriction of `f`
to a set `K` be inducing, and let `x i` be maps from a space `T` whose values at each point of a set
`Ω ⊆ T` eventually lie in `K` along a nontrivial filter `l`. If the maps `f ∘ x i` converge along
`l` pointwise on `Ω` to a map `g` continuous on `Ω` with values in `f '' K` on `Ω`, then `g = f ∘ y`
on `Ω` for a map `y` that is continuous on `Ω` and maps `Ω` into `K`, and the `x i` converge along
`l` pointwise on `Ω` to `y`. -/
theorem exists_tendsto_of_tendsto_comp {Y : Type*} [TopologicalSpace Y] {K : Set X}
    {f : X → Y} (hf : IsInducing (K.domRestrict f)) {T : Type*} [TopologicalSpace T] {Ω : Set T}
    {ι : Type*} {l : Filter ι} [l.NeBot] {x : ι → T → X} (hxK : ∀ t ∈ Ω, ∀ᶠ i in l, x i t ∈ K)
    {g : T → Y} (hg : ContinuousOn g Ω) (hgK : MapsTo g Ω (f '' K))
    (hlim : ∀ t ∈ Ω, Tendsto (fun i ↦ f (x i t)) l (𝓝 (g t))) :
    ∃ y : T → X, ContinuousOn y Ω ∧ MapsTo y Ω K ∧ EqOn (f ∘ y) g Ω ∧
      ∀ t ∈ Ω, Tendsto (fun i ↦ x i t) l (𝓝 (y t)) := by
  -- Lift `g` to `K` on `Ω`, and extend the lift to `T` by one of the maps `x i`.
  choose z hzK hfz using fun t : Ω ↦ hgK t.property
  obtain ⟨i⟩ := l.nonempty_of_neBot
  set y := Function.extend ((↑) : Ω → T) z (x i)
  have hy (t : T) (ht : t ∈ Ω) : y t ∈ K ∧ f (y t) = g t := by
    rw [show y t = z ⟨t, ht⟩ from Subtype.val_injective.extend_apply z (x i) ⟨t, ht⟩]
    exact ⟨hzK _, hfz _⟩
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
