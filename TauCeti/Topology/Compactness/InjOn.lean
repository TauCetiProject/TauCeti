/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Maps.Basic

/-!
# Limits read back through a map injective on a compact set

A map `f` continuous and injective on a compact set `K`, with values in a Hausdorff space, restricts
to a closed embedding of `K`. So a continuous pointwise limit `g` of maps `f ∘ x i`, where the `x i`
take values in `K`, is `f ∘ y` for a continuous pointwise limit `y` of the `x i`
(`IsCompact.exists_tendsto_of_tendsto_comp`). This is how a limit in a manifold without a metric is
constructed from a limit measured through an embedding into a normed space.
-/

public section

open Filter Function Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- **Limits read back through an injective map.** Let `f` be continuous and injective on a compact
set `K`, with values in a Hausdorff space, and let `x i` be maps from a space `T` with values in `K`
on a set `Ω ⊆ T`. If the maps `f ∘ x i` converge pointwise on `Ω` to a map `g` continuous on `Ω`,
then `g = f ∘ y` on `Ω` for a map `y` continuous on `Ω` with values in `K`, and the `x i` converge
pointwise on `Ω` to `y`. -/
theorem IsCompact.exists_tendsto_of_tendsto_comp [Nonempty X] {K : Set X} (hK : IsCompact K)
    {f : X → Y} (hf : ContinuousOn f K) (hinj : InjOn f K) {T : Type*} [TopologicalSpace T]
    {Ω : Set T} {ι : Type*} {l : Filter ι} [l.NeBot] {x : ι → T → X}
    (hxK : ∀ i, MapsTo (x i) Ω K) {g : T → Y} (hg : ContinuousOn g Ω)
    (hlim : ∀ t ∈ Ω, Tendsto (fun i ↦ f (x i t)) l (𝓝 (g t))) :
    ∃ y : T → X, ContinuousOn y Ω ∧ MapsTo y Ω K ∧ EqOn (f ∘ y) g Ω ∧
      ∀ t ∈ Ω, Tendsto (fun i ↦ x i t) l (𝓝 (y t)) := by
  have := isCompact_iff_compactSpace.1 hK
  have hemb : IsClosedEmbedding (K.domRestrict f) :=
    (continuousOn_iff_continuous_domRestrict.1 hf).isClosedEmbedding fun p q hpq ↦
      Subtype.ext (hinj p.2 q.2 hpq)
  -- The limit takes values in the closed set `f(K)`.
  have hgK (t : T) (ht : t ∈ Ω) : ∃ p ∈ K, f p = g t :=
    (hK.image_of_continuousOn hf).isClosed.mem_of_tendsto (hlim t ht)
      (Eventually.of_forall fun i ↦ mem_image_of_mem f (hxK i ht))
  set y : T → X := fun t ↦ invFunOn f K (g t)
  have hyK : MapsTo y Ω K := fun t ht ↦ invFunOn_mem (hgK t ht)
  have hfy : EqOn (f ∘ y) g Ω := fun t ht ↦ invFunOn_eq (hgK t ht)
  refine ⟨y, ?_, hyK, hfy, fun t ht ↦ ?_⟩
  · -- Inside `K`, continuity is read through the embedding `f`.
    rw [continuousOn_iff_continuous_domRestrict]
    have h : Continuous fun t : Ω ↦ (⟨y t, hyK t.2⟩ : K) := by
      rw [hemb.isEmbedding.continuous_iff]
      exact ((continuousOn_iff_continuous_domRestrict.1 hg).congr fun t ↦ (hfy t.2).symm)
    exact continuous_subtype_val.comp h
  · have h : Tendsto (fun i ↦ (⟨x i t, hxK i ht⟩ : K)) l (𝓝 ⟨y t, hyK ht⟩) := by
      rw [hemb.isEmbedding.tendsto_nhds_iff]
      simpa only [comp_def, domRestrict_apply, show f (y t) = g t from hfy ht] using hlim t ht
    exact (continuous_subtype_val.tendsto _).comp h
