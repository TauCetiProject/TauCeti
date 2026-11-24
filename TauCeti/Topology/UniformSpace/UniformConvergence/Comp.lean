/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Composing uniformly convergent families with continuous maps

Mathlib composes a uniformly convergent family with a uniformly continuous map
(`UniformContinuous.comp_tendstoUniformlyOn`). A map that is only continuous at the points of the
set of values of the limit suffices, provided that set is compact: by the Heine–Cantor argument
(`IsCompact.uniformContinuousAt_of_continuousAt`) the map is uniformly continuous at that compact
set, so it sends points close to it close to their images.

This applies, for instance, to families of paths converging uniformly on a compact interval to a
continuous limit, composed with a continuous integrand. To compose with a map that also depends on
the point `a` itself, as a time-dependent integrand does, first pass to the graphs
`a ↦ (a, F i a)`, which converge uniformly to the graph of the limit
(`TendstoUniformlyOn.graph`).

For coefficients `P (x, y)` that depend on both the point `x` and the value `y`, continuity on a
compact product `s ×ˢ t` suffices when all the values lie in `t`
(`IsCompact.tendstoUniformlyOn_comp_prodMk`): `P` is then uniformly continuous there. This is the
form in which the coefficients `J(z, u(z))` of a nonlinear equation converge along a sequence of
maps `u` converging uniformly on a compact set. When the space of values is weakly locally compact,
a jointly continuous `P` and a limit continuous on `s` suffice
(`IsCompact.tendstoUniformlyOn_comp_prodMk_of_continuous`): a compact neighborhood of the values
of the limit then serves as `t`.

When the inner maps vary too, a uniformly convergent family `G i → g` can be composed with a
uniformly convergent family `F i → f`, provided `g` is uniformly continuous on a set containing all
the values (`TendstoUniformlyOn.comp_tendstoUniformlyOn`). This is the form needed to compare
maps read at moving base points, such as `z ↦ G i (x i + z)` with `x i → x`.

Uniform convergence to a limit mapping `s` into a compact set with a neighborhood `W` puts the
values of the family on `s` eventually inside `W` (`TendstoUniformlyOn.eventually_mapsTo`); in
particular this holds for an open set `W` containing the values on a compact set `s` of a limit
continuous on `s` (`TendstoUniformlyOn.eventually_mapsTo_of_isOpen`).

The file also records that a constant family converges uniformly
(`TauCeti.tendstoUniformlyOn_const`), that uniform convergence along a mapped filter `map g l` is
uniform convergence of the reindexed family `F ∘ g` along `l`
(`TauCeti.tendstoUniformlyOn_map_iff`), and that two families converging uniformly along the same
filter converge jointly (`TendstoUniformlyOn.prodMk_same`), which is the form needed to compose
with maps of several variables, and that multiplying by a constant scalar preserves uniform
convergence (`TendstoUniformlyOn.const_smul`).
-/

public section

open Filter Set Topology

variable {α β γ ι : Type*} [UniformSpace β] [UniformSpace γ]
  {F : ι → α → β} {f : α → β} {s : Set α} {g : β → γ} {p : Filter ι}

/-- Composing a family converging uniformly on `s` with a map continuous at every value of the
limit on `s` preserves uniform convergence on `s`, provided the values of the limit on `s` form a
compact set. -/
theorem IsCompact.comp_tendstoUniformlyOn (hf : IsCompact (f '' s))
    (hg : ∀ y ∈ f '' s, ContinuousAt g y) (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i x ↦ g (F i x)) (fun x ↦ g (f x)) p s := fun _ hu ↦ by
  filter_upwards [h _ (hf.uniformContinuousAt_of_continuousAt g hg hu)] with i hi x hx
  exact hi x hx (mem_image_of_mem f hx)

/-- Let `G i → g` uniformly on `t`, with `g` uniformly continuous on `t`, and let `F i → f`
uniformly on `s`, where `f` and eventually every `F i` map `s` into `t`. Then `G i ∘ F i → g ∘ f`
uniformly on `s`. Mathlib's `UniformContinuousOn.comp_tendstoUniformlyOn_eventually` is the case of
a constant outer family. -/
theorem TendstoUniformlyOn.comp_tendstoUniformlyOn {t : Set β} {G : ι → β → γ}
    (hG : TendstoUniformlyOn G g p t) (hg : UniformContinuousOn g t)
    (h : TendstoUniformlyOn F f p s) (hF : ∀ᶠ i in p, MapsTo (F i) s t) (hf : MapsTo f s t) :
    TendstoUniformlyOn (fun i x ↦ G i (F i x)) (fun x ↦ g (f x)) p s := fun u hu ↦ by
  obtain ⟨v, hv, hvu⟩ := comp_mem_uniformity_sets hu
  filter_upwards [hG v hv, hg.comp_tendstoUniformlyOn_eventually
    (hF.mono fun _ hFi _ hx ↦ hFi hx) hf h v hv, hF] with i hGi hgi hFi x hx
  exact hvu (SetRel.prodMk_mem_comp (hgi x hx) (hGi _ (hFi hx)))

/-- If `Fᵢ → f` uniformly on `s` and `f` maps `s` into a compact set `K` with a neighborhood `W`,
then eventually every `Fᵢ` maps `s` into `W`. -/
theorem TendstoUniformlyOn.eventually_mapsTo {K W : Set β} (h : TendstoUniformlyOn F f p s)
    (hf : MapsTo f s K) (hK : IsCompact K) (hW : W ∈ 𝓝ˢ K) :
    ∀ᶠ i in p, MapsTo (F i) s W := by
  obtain ⟨V, hV, hVW⟩ := (hK.nhdsSet_basis_uniformity (uniformity β).basis_sets).mem_iff.1 hW
  filter_upwards [h _ (tendsto_swap_uniformity hV)] with i hi x hx
  exact hVW (mem_biUnion (hf hx) (hi x hx))

/-- If `Fᵢ → f` uniformly on a compact set `s`, and `f` is continuous on `s` with values in an open
set `W`, then eventually every `Fᵢ` maps `s` into `W`. -/
theorem TendstoUniformlyOn.eventually_mapsTo_of_isOpen [TopologicalSpace α] {W : Set β}
    (h : TendstoUniformlyOn F f p s) (hs : IsCompact s) (hf : ContinuousOn f s) (hW : IsOpen W)
    (hfW : MapsTo f s W) : ∀ᶠ i in p, MapsTo (F i) s W :=
  h.eventually_mapsTo (mapsTo_image f s) (hs.image_of_continuousOn hf)
    (hW.mem_nhdsSet.2 (image_subset_iff.2 hfW))

namespace TauCeti

/-- A constant family converges uniformly to its value. -/
theorem tendstoUniformlyOn_const (f : α → β) (p : Filter ι) (s : Set α) :
    TendstoUniformlyOn (fun _ ↦ f) f p s :=
  fun _ hu ↦ .of_forall fun _ _ _ ↦ refl_mem_uniformity hu

/-- A family converges uniformly along a mapped filter `map g l` exactly when the reindexed family
`F ∘ g` converges uniformly along `l`. -/
theorem tendstoUniformlyOn_map_iff {κ : Type*} {g : κ → ι} {l : Filter κ} :
    TendstoUniformlyOn F f (map g l) s ↔ TendstoUniformlyOn (fun k ↦ F (g k)) f l s :=
  forall₂_congr fun _ _ ↦ eventually_map

end TauCeti

/-- Two families converging uniformly on `s` along the same filter converge jointly. Mathlib's
`TendstoUniformlyOn.prodMk` gives the joint convergence along the product filter `p ×ˢ p`. -/
theorem TendstoUniformlyOn.prodMk_same {F' : ι → α → γ} {f' : α → γ}
    (h : TendstoUniformlyOn F f p s) (h' : TendstoUniformlyOn F' f' p s) :
    TendstoUniformlyOn (fun i x ↦ (F i x, F' i x)) (fun x ↦ (f x, f' x)) p s :=
  fun _ hu ↦ Filter.tendsto_diag.eventually (h.prodMk h' _ hu)

/-- The graphs `a ↦ (a, F i a)` of a family converging uniformly on `s` converge uniformly on `s`
to the graph of the limit. -/
theorem TendstoUniformlyOn.graph [UniformSpace α] (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i a ↦ (a, F i a)) (fun a ↦ (a, f a)) p s := by
  rw [tendstoUniformlyOn_iff_tendsto] at h ⊢
  rw [uniformity_prod, tendsto_inf, tendsto_comap_iff, tendsto_comap_iff]
  refine ⟨?_, h⟩
  exact (tendsto_principal.2 (.of_forall fun _ ↦ SetRel.mem_id.2 rfl)).mono_right
    refl_le_uniformity

/-- Let `Fᵢ → f` uniformly on a compact set `s`, with all values on `s` in a compact set `t`. Then
`P (x, Fᵢ x) → P (x, f x)` uniformly on `s`, for every `P` continuous on `s ×ˢ t`. -/
theorem IsCompact.tendstoUniformlyOn_comp_prodMk [UniformSpace α] {t : Set β} {P : α × β → γ}
    (hs : IsCompact s) (ht : IsCompact t) (hP : ContinuousOn P (s ×ˢ t))
    (hF : ∀ᶠ i in p, MapsTo (F i) s t) (hf : MapsTo f s t) (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i x ↦ P (x, F i x)) (fun x ↦ P (x, f x)) p s :=
  ((hs.prod ht).uniformContinuousOn_of_continuous hP).comp_tendstoUniformlyOn_eventually
    (hF.mono fun _ hFi _ hx ↦ mk_mem_prod hx (hFi hx)) (fun _ hx ↦ mk_mem_prod hx (hf hx))
    h.graph

/-- Let `Fᵢ → f` uniformly on a compact set `s`, with `f` continuous on `s` and values in a weakly
locally compact space. Then `P (x, Fᵢ x) → P (x, f x)` uniformly on `s`, for every continuous `P`.
-/
theorem IsCompact.tendstoUniformlyOn_comp_prodMk_of_continuous [UniformSpace α]
    [WeaklyLocallyCompactSpace β] {P : α × β → γ} (hs : IsCompact s) (hP : Continuous P)
    (hf : ContinuousOn f s) (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i x ↦ P (x, F i x)) (fun x ↦ P (x, f x)) p s := by
  have hfs := hs.image_of_continuousOn hf
  obtain ⟨t, ht, hft⟩ := exists_compact_superset hfs
  exact hs.tendstoUniformlyOn_comp_prodMk ht hP.continuousOn
    (h.eventually_mapsTo (mapsTo_image f s) hfs (subset_interior_iff_mem_nhdsSet.1 hft))
    (fun _ hx ↦ interior_subset (hft (mem_image_of_mem f hx))) h

/-- Multiplying a family converging uniformly on `s` by a constant scalar preserves uniform
convergence on `s`. -/
theorem TendstoUniformlyOn.const_smul {M : Type*} [SMul M β] [UniformContinuousConstSMul M β]
    (h : TendstoUniformlyOn F f p s) (c : M) : TendstoUniformlyOn (c • F) (c • f) p s :=
  (uniformContinuous_const_smul c).comp_tendstoUniformlyOn h
