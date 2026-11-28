/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Equicontinuity of a sequence from equicontinuity of a tail

Equicontinuity at a point is insensitive to finitely many members of a family, provided each of
them is continuous there (`equicontinuousAt_finite`). For a sequence `F : ℕ → X → α` this means
that equicontinuity at `x₀` of a tail `n ↦ F (n + N)` and continuity at `x₀` of the first `N`
members give equicontinuity at `x₀` of the whole sequence
(`TauCeti.equicontinuousAt_of_equicontinuousAt_add`). Local arguments often control a sequence
only from some index on, with the index depending on the point; this lemma assembles such local
control into equicontinuity of the original sequence.

Equicontinuity within a neighbourhood of `x₀` is equicontinuity at `x₀`
(`EquicontinuousWithinAt.equicontinuousAt`), as for continuity.

Finally, equicontinuity within `s` at `x ∈ closure s` (even restricted to a filter member `S ∈ l`)
extends pointwise convergence on `s` to `x` whenever the limit has a within-set limit at `x`
(`EquicontinuousWithinAt.tendsto_of_mem_closure`,
`TauCeti.tendsto_of_mem_closure_of_equicontinuousWithinAt`), and uniform equicontinuity on a
totally bounded set `s` (again on a filter member `S ∈ l`) upgrades pointwise convergence on `s` to
uniform convergence on `s` (`TauCeti.tendstoUniformlyOn_of_uniformEquicontinuousOn`).
-/

public section

open Filter Set Topology

open scoped Uniformity

variable {ι X α : Type*} [TopologicalSpace X] [UniformSpace α]

/-- A family equicontinuous at `x₀` within a neighbourhood of `x₀` is equicontinuous at `x₀`. -/
theorem EquicontinuousWithinAt.equicontinuousAt {F : ι → X → α} {S : Set X} {x₀ : X}
    (hF : EquicontinuousWithinAt F S x₀) (hS : S ∈ 𝓝 x₀) : EquicontinuousAt F x₀ := by
  rwa [EquicontinuousWithinAt, nhdsWithin_eq_nhds.2 hS] at hF

/-- If `F : ι → X → α` is equicontinuous at `x` within `s`, converges pointwise to `f` on `s`,
and `f` tends to `z` along `𝓝[s] x` at a point `x ∈ closure s`, then `F · x` tends to `z` along
`l`. -/
theorem EquicontinuousWithinAt.tendsto_of_mem_closure {l : Filter ι} {F : ι → X → α}
    {f : X → α} {s : Set X} {x : X} {z : α} (hF : EquicontinuousWithinAt F s x)
    (hf : Tendsto f (𝓝[s] x) (𝓝 z)) (hs : ∀ y ∈ s, Tendsto (F · y) l (𝓝 (f y)))
    (hx : x ∈ closure s) : Tendsto (F · x) l (𝓝 z) := by
  rw [(nhds_basis_uniformity (𝓤 α).basis_sets).tendsto_right_iff] at hf ⊢
  intro U hU
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, _, hVU⟩
  rw [mem_closure_iff_nhdsWithin_neBot] at hx
  have : ∀ᶠ y in 𝓝[s] x, y ∈ s ∧ (∀ i, (F i x, F i y) ∈ V) ∧ (f y, z) ∈ V :=
    eventually_mem_nhdsWithin.and <| (hF V hV).and (hf V hV)
  rcases this.exists with ⟨y, hys, hFy, hfy⟩
  filter_upwards [hs y hys (SetRel.ball_mem_nhds _ hV)] with i hi
  exact hVU ⟨_, ⟨_, hFy i, hi⟩, hfy⟩

namespace TauCeti

/-- A sequence of functions is equicontinuous at `x₀` if one of its tails `n ↦ F (n + N)` is,
and its first `N` members are continuous at `x₀`. -/
theorem equicontinuousAt_of_equicontinuousAt_add {F : ℕ → X → α} {x₀ : X} (N : ℕ)
    (hF : EquicontinuousAt (fun n ↦ F (n + N)) x₀) (hc : ∀ n < N, ContinuousAt (F n) x₀) :
    EquicontinuousAt F x₀ := by
  intro U hU
  have hfin : EquicontinuousAt (fun n : Fin N ↦ F n) x₀ :=
    equicontinuousAt_finite.2 fun n ↦ hc n n.isLt
  filter_upwards [hF U hU, hfin U hU] with x htail hhead n
  rcases lt_or_ge n N with hn | hn
  · exact hhead ⟨n, hn⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact htail k

/-- If a family `F : ι → X → α` restricts on a set `S ∈ l` to a family equicontinuous at `x`
within `s`, converges pointwise to `f` on `s`, and `f` tends to `z` along `𝓝[s] x` at a point
`x ∈ closure s`, then `F · x` tends to `z` along `l`. -/
theorem tendsto_of_mem_closure_of_equicontinuousWithinAt {l : Filter ι} {F : ι → X → α}
    {f : X → α} {s : Set X} {x : X} {z : α} {S : Set ι} (hS : S ∈ l)
    (hF : EquicontinuousWithinAt (fun j : S ↦ F j.val) s x)
    (hf : Tendsto f (𝓝[s] x) (𝓝 z)) (hs : ∀ y ∈ s, Tendsto (F · y) l (𝓝 (f y)))
    (hx : x ∈ closure s) : Tendsto (F · x) l (𝓝 z) := by
  have hmap : (l.comap ((↑) : S → ι)).map ((↑) : S → ι) = l :=
    map_comap_of_mem (by rwa [Subtype.range_coe])
  have hmem : Tendsto (fun j : S ↦ F j.val x) (l.comap (↑)) (𝓝 z) :=
    hF.tendsto_of_mem_closure hf (fun y hy ↦ (hs y hy).comp tendsto_comap) hx
  rwa [← hmap, tendsto_map'_iff]

/-- If a family `F : ι → β → α` between uniform spaces restricts on a set `S ∈ l` to a family
uniformly equicontinuous on a totally bounded set `s`, and converges pointwise to `f` on `s`, then
`F` converges uniformly to `f` on `s` along `l`. -/
theorem tendstoUniformlyOn_of_uniformEquicontinuousOn {ι β α : Type*} [UniformSpace β]
    [UniformSpace α] {l : Filter ι} {F : ι → β → α} {f : β → α} {s : Set β} {S : Set ι}
    (hS : S ∈ l) (hF : UniformEquicontinuousOn (fun j : S ↦ F j.val) s) (hs : TotallyBounded s)
    (hpt : ∀ x ∈ s, Tendsto (F · x) l (𝓝 (f x))) : TendstoUniformlyOn F f l s := by
  rcases eq_or_neBot l with rfl | hl
  · exact fun _ _ ↦ eventually_bot
  have : (l.comap ((↑) : S → ι)).NeBot := hl.comap_of_range_mem (by rwa [Subtype.range_coe])
  have hf : UniformContinuousOn f s :=
    Filter.Tendsto.uniformContinuousOn_of_uniformEquicontinuousOn
      (fun x hx ↦ (hpt x hx).comp tendsto_comap) hF
  intro U hU
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
  let W : Set (β × β) :=
    {xy | xy ∈ s ×ˢ s → (f xy.1, f xy.2) ∈ V ∧ ∀ j : S, (F j.val xy.1, F j.val xy.2) ∈ V}
  have hW : W ∈ 𝓤 β := by
    have h1 : {xy : β × β | xy ∈ s ×ˢ s → (f xy.1, f xy.2) ∈ V} ∈ 𝓤 β :=
      mem_inf_principal.mp (hf hV)
    have h2 : {xy : β × β | xy ∈ s ×ˢ s → ∀ j : S, (F j.val xy.1, F j.val xy.2) ∈ V} ∈ 𝓤 β :=
      mem_inf_principal.mp (hF V hV)
    filter_upwards [h1, h2] with xy hxy1 hxy2 hxy
    exact ⟨hxy1 hxy, hxy2 hxy⟩
  have hW' : W ∩ Prod.swap ⁻¹' W ∈ 𝓤 β := inter_mem hW (symm_le_uniformity hW)
  obtain ⟨t, hts, htfin, hcov⟩ := hs.exists_subset hW'
  have hconv : ∀ᶠ i in l, ∀ y ∈ t, (f y, F i y) ∈ V :=
    (eventually_all_finite htfin).mpr fun y hy ↦
      Eventually.mono (hpt y (hts hy) (SetRel.ball_mem_nhds (f y) hV)) fun _ h ↦ hVsymm.symm _ _ h
  filter_upwards [hS, hconv] with i hiS hicov x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (hcov hx)
  have h1 : (f x, f y) ∈ V := (hxy.1 ⟨hx, hts hyt⟩).1
  have h2 : (f y, F i y) ∈ V := hicov y hyt
  have h3 : (F i y, F i x) ∈ V := (hxy.2 ⟨hts hyt, hx⟩).2 ⟨i, hiS⟩
  exact hVU ⟨_, ⟨_, h1, h2⟩, h3⟩

end TauCeti
