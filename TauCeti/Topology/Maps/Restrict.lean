/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.NhdsWithin

/-!
# Neighbourhoods and convergence under inducing restrictions

If the restriction `s.domRestrict f : s → Y` of a map `f : X → Y` to a subset `s ⊆ X` is
topologically inducing, then at every point `x ∈ s` the within-neighbourhood filter `𝓝[s] x` is
pulled back from `𝓝 (f x)` along `f`:

* `Topology.IsInducing.nhdsWithin_eq_comap_inf_principal_of_domRestrict`:
  `𝓝[s] x = comap f (𝓝 (f x)) ⊓ 𝓟 s`, generalizing
  `OpenPartialHomeomorph.nhds_eq_comap_inf_principal` to arbitrary subsets without openness.
* `Topology.IsInducing.mem_nhdsWithin_iff_of_domRestrict`: `W ∈ 𝓝[s] x` if and only if
  `{y ∈ s | f y ∈ V} ⊆ W` for some `V ∈ 𝓝 (f x)`.
* `Topology.IsInducing.tendsto_nhdsWithin_iff_of_domRestrict`: convergence of `g` to `𝓝[s] x` at
  `x ∈ s` is equivalent to convergence of `f ∘ g` to `f x` together with eventual membership in `s`;
  `Topology.IsInducing.tendsto_nhds_iff_of_domRestrict` deduces that when `g` eventually lies in
  `s`, convergence of `g` to `x` is equivalent to convergence of `f ∘ g` to `f x`.
-/

public section

open Filter Set Topology

namespace Topology.IsInducing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s : Set X} {f : X → Y}

/-- If `f` restricts to a topologically inducing map on `s`, then at every `x ∈ s` the
within-neighbourhood filter `𝓝[s] x` is the pullback along `f` of `𝓝 (f x)` restricted to `s`. -/
theorem nhdsWithin_eq_comap_inf_principal_of_domRestrict (hf : IsInducing (s.domRestrict f))
    {x : X} (hx : x ∈ s) :
    𝓝[s] x = comap f (𝓝 (f x)) ⊓ 𝓟 s := by
  rw [nhdsWithin_eq_map_subtype_coe hx, hf.nhds_eq_comap, domRestrict_eq, ← comap_comap,
    map_comap_setCoe_val]
  rfl

/-- If `f` restricts to a topologically inducing map on `s`, then at `x ∈ s` the
within-neighbourhoods `W ∈ 𝓝[s] x` are precisely the sets containing `{y ∈ s | f y ∈ V}` for some
`V ∈ 𝓝 (f x)`. -/
theorem mem_nhdsWithin_iff_of_domRestrict (hf : IsInducing (s.domRestrict f)) {x : X} (hx : x ∈ s)
    {W : Set X} :
    W ∈ 𝓝[s] x ↔ ∃ V ∈ 𝓝 (f x), ∀ y ∈ s, f y ∈ V → y ∈ W := by
  rw [hf.nhdsWithin_eq_comap_inf_principal_of_domRestrict hx, mem_inf_principal, mem_comap]
  exact ⟨fun ⟨V, hV, hVW⟩ ↦ ⟨V, hV, fun _ hys hfy ↦ hVW hfy hys⟩,
    fun ⟨V, hV, hVW⟩ ↦ ⟨V, hV, fun _ hfy hys ↦ hVW _ hys hfy⟩⟩

/-- If `f` restricts to a topologically inducing map on `s`, then convergence to `𝓝[s] x` at
`x ∈ s` is equivalent to convergence of `f ∘ g` to `𝓝 (f x)` together with eventual membership in
`s`. -/
theorem tendsto_nhdsWithin_iff_of_domRestrict {ι : Type*} {g : ι → X} {l : Filter ι}
    (hf : IsInducing (s.domRestrict f)) {x : X} (hx : x ∈ s) :
    Tendsto g l (𝓝[s] x) ↔ Tendsto (f ∘ g) l (𝓝 (f x)) ∧ ∀ᶠ i in l, g i ∈ s := by
  rw [hf.nhdsWithin_eq_comap_inf_principal_of_domRestrict hx, tendsto_inf, tendsto_comap_iff,
    tendsto_principal]

/-- If `f` restricts to a topologically inducing map on `s`, `x ∈ s`, and `g` eventually takes
values in `s`, then `g` tends to `x` if and only if `f ∘ g` tends to `f x`. -/
theorem tendsto_nhds_iff_of_domRestrict {ι : Type*} {g : ι → X} {l : Filter ι}
    (hf : IsInducing (s.domRestrict f)) {x : X} (hx : x ∈ s) (hg : ∀ᶠ i in l, g i ∈ s) :
    Tendsto g l (𝓝 x) ↔ Tendsto (f ∘ g) l (𝓝 (f x)) :=
  (and_iff_left hg).symm.trans <| tendsto_nhdsWithin_iff.symm.trans <|
    (hf.tendsto_nhdsWithin_iff_of_domRestrict hx).trans (and_iff_left hg)

end Topology.IsInducing
