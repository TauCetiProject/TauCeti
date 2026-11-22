/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SphereBundle.Basic

/-!
# The negative disc bundle of a Morse–Bott level parametrized by a gauge disc bundle

Let `f = c - s + t` on a set `W` of a space `M`, the quadratic normal form of a function near a
critical submanifold on the level `c`, and suppose that the negative disc bundle
`{x ∈ W | t x = 0, s x ≤ ε}` is parametrized by the disc bundle `D_ρ(V)` of a fibre gauge `ρ` on a
bundle `V → B`: a map `g` carrying `D_ρ(V)` onto the negative disc bundle and the sphere bundle
`S_ρ(V)` onto its boundary `{t = 0, s = ε}`. This file collects the elementary facts about such a
parametrization used to read the attachment across the level in relative homology
(`TauCeti.Geometry.Manifold.Morse.Bott.Homology`) and in relative cohomology
(`TauCeti.Geometry.Manifold.Morse.Bott.Cohomology`).

* The negative disc bundle lies in the critical sublevel `{f ≤ c}`
  (`TauCeti.apply_le_of_mem_negativeDiscBundle`).
* When `g` is injective on `D_ρ(V)`, the points of `D_ρ(V)` sent into the lower sublevel
  `{f ≤ c - ε}` are exactly those of `S_ρ(V)` (`TauCeti.apply_le_sub_iff_mem_gaugeSphereBundle`).
* When `g` restricts to a closed embedding of `D_ρ(V)` and `{x ∈ W | s x + 2 t x ≤ 2ε}` is
  compact, the base `B` is compact
  (`TauCeti.compactSpace_of_isClosedEmbedding_gaugeDiscBundle`).
-/

public section

open Bundle Set Topology

universe u

namespace TauCeti

section Pointwise

variable {M F : Type*} {B : Type u} {V : B → Type u} {f s t : M → ℝ} {c ε : ℝ} {W : Set M}
  {ρ : TotalSpace F V → ℝ} {g : TotalSpace F V → M}

/-- **The negative disc bundle lies below the critical level.** If `f = c - s + t` on a set `W`
with `s ≥ 0` there, then `f ≤ c` on the negative disc bundle `{x ∈ W | t x = 0, s x ≤ ε}`. -/
theorem apply_le_of_mem_negativeDiscBundle (hf : ∀ x ∈ W, f x = c - s x + t x)
    (hs₀ : ∀ x ∈ W, 0 ≤ s x) {x : M} (hx : x ∈ {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε}) : f x ≤ c := by
  rw [hf x hx.1, hx.2.1]
  linarith [hs₀ x hx.1]

/-- **The sphere bundle is the part of the negative disc bundle in the lower sublevel.** Let
`f = c - s + t` on a set `W`, and let `g` be injective on the disc bundle `D_ρ(V)` of a function
`ρ` on the total space of a bundle, carrying it onto the negative disc bundle
`{x ∈ W | t x = 0, s x ≤ ε}` and the sphere bundle `S_ρ(V)` onto `{x ∈ W | t x = 0, s x = ε}`.
Then a point of `D_ρ(V)` is sent into the lower sublevel `{f ≤ c - ε}` exactly when it lies in
`S_ρ(V)`. -/
theorem apply_le_sub_iff_mem_gaugeSphereBundle (hf : ∀ x ∈ W, f x = c - s x + t x)
    (hg : InjOn g (gaugeDiscBundle ρ))
    (hgD : g '' gaugeDiscBundle ρ = {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε})
    (hgS : g '' gaugeSphereBundle ρ = {x | x ∈ W ∧ t x = 0 ∧ s x = ε}) {v : TotalSpace F V}
    (hv : v ∈ gaugeDiscBundle ρ) : f (g v) ≤ c - ε ↔ v ∈ gaugeSphereBundle ρ := by
  obtain ⟨hxW, htx, hsx⟩ : g v ∈ {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε} := hgD ▸ mem_image_of_mem g hv
  rw [hf _ hxW, htx]
  refine ⟨fun hle ↦ ?_, fun hvS ↦ ?_⟩
  · -- `s = ε` at `g v`, so `g v` is the image of a point of the sphere bundle, which is `v`.
    obtain ⟨w, hw, hwv⟩ : g v ∈ g '' gaugeSphereBundle ρ := hgS ▸ ⟨hxW, htx, by linarith⟩
    rwa [← hg (gaugeSphereBundle_subset_gaugeDiscBundle ρ hw) hv hwv]
  · have : g v ∈ {x | x ∈ W ∧ t x = 0 ∧ s x = ε} := hgS ▸ mem_image_of_mem g hvS
    linarith [this.2.2]

end Pointwise

section Compact

variable {M : Type*} [TopologicalSpace M] {s t : M → ℝ} {ε : ℝ} {W : Set M}
  {B : Type u} [TopologicalSpace B] {F : Type*} [TopologicalSpace F]
  {V : B → Type u} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  {ρ : TotalSpace F V → ℝ} {g : TotalSpace F V → M}

/-- **The base of a gauge disc bundle parametrizing a negative disc bundle is compact.** Let `g`
restrict to a closed embedding of the disc bundle `D_ρ(V)` of a fibre gauge `ρ` on a bundle
`V → B` onto the negative disc bundle `{x ∈ W | t x = 0, s x ≤ ε}`, with
`{x ∈ W | s x + 2 t x ≤ 2ε}` compact. Then the base `B` is compact: `g` carries the disc bundle
onto a closed subset of that compact set, and the disc bundle contains the zero section. In the
intended setting `f = c - s + t`, `B` is the critical submanifold of the Morse–Bott level `c`. -/
theorem compactSpace_of_isClosedEmbedding_gaugeDiscBundle (hε : 0 ≤ ε)
    (hK : IsCompact {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε}) (hρ : IsFiberGauge ρ)
    (hg : IsClosedEmbedding ((gaugeDiscBundle ρ).domRestrict g))
    (hgD : g '' gaugeDiscBundle ρ = {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε}) : CompactSpace B := by
  have hcpt : IsCompact (g '' gaugeDiscBundle ρ) :=
    hK.of_isClosed_subset (range_domRestrict g _ ▸ hg.isClosed_range)
      (hgD ▸ fun x ⟨hxW, htx, hsx⟩ ↦ ⟨hxW, by linarith⟩)
  have : CompactSpace (gaugeDiscBundle ρ) := isCompact_univ_iff.1 <| by
    simpa [preimage_eq_univ_iff.2 (range_domRestrict g _).le] using hg.isCompact_preimage hcpt
  exact hρ.compactSpace_of_compactSpace_gaugeDiscBundle

end Compact

end TauCeti
