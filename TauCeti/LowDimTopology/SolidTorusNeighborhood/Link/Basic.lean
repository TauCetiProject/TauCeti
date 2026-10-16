/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SmoothLink.Basic
public import TauCeti.Topology.MetricSpace.Thickening
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Basic

/-!
# Disjoint solid-torus neighbourhoods of links

The image of a finite link in `ℝ³` is a finite union of disjoint compact circles.  Compactness
gives one positive metric radius for which the thickenings of all components are pairwise
disjoint.  Applying the solid-torus neighbourhood theorem to each thickening gives the usual
disjoint tubular neighbourhoods of the link.

## Main declarations

* `TauCeti.IsSolidTorusLinkNeighborhood` records solid-torus neighbourhoods of every component
  together with pairwise disjoint images of the closed solid tori.
* `TauCeti.exists_isSolidTorusLinkNeighborhood` constructs these neighbourhoods for a finite
  family of pairwise disjoint `C²` embedded circles in `ℝ³`.

The resulting disjoint solid-torus images provide the componentwise neighborhoods used when
forming a link exterior. The canonical `SmoothLinkEmbedding` presentation has the same
existence result via `SmoothLinkEmbedding.exists_isSolidTorusLinkNeighborhood`.
-/

public section

open Set Metric Function Topology
open scoped Matrix Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {ι X : Type*} [TopologicalSpace X]

/-- A family of solid-torus neighbourhoods whose solid-torus images are pairwise disjoint. -/
structure IsSolidTorusLinkNeighborhood (f : ι → Circle → X)
    (Φ : ι → SolidTorus → X) : Prop where
  /-- Each component has a solid-torus neighbourhood. -/
  neighborhood : ∀ i, IsSolidTorusNeighborhood (f i) (Φ i)
  /-- The images of the closed solid tori for distinct components are disjoint. -/
  pairwiseDisjoint_range : Pairwise (Disjoint on fun i => range (Φ i))

namespace IsSolidTorusLinkNeighborhood

variable {f : ι → Circle → X} {Φ : ι → SolidTorus → X}

/-- The open solid torus images of distinct components are disjoint. -/
theorem pairwiseDisjoint_image (h : IsSolidTorusLinkNeighborhood f Φ) :
    Pairwise (Disjoint on fun i => Φ i '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1}) := by
  intro i j hij
  exact (h.pairwiseDisjoint_range hij).mono (image_subset_range _ _) (image_subset_range _ _)

/-- Transport a family of disjoint solid-torus neighborhoods along an open embedding. -/
theorem comp {Y : Type*} [TopologicalSpace Y] {e : X → Y} (he : IsOpenEmbedding e)
    (h : IsSolidTorusLinkNeighborhood f Φ) :
    IsSolidTorusLinkNeighborhood (fun i => e ∘ f i) (fun i => e ∘ Φ i) where
  neighborhood i := (h.neighborhood i).comp he
  pairwiseDisjoint_range := by
    intro i j hij
    simp only [range_comp]
    exact disjoint_image_of_injective he.injective (h.pairwiseDisjoint_range hij)

/-- The `i`-th component lies in the open image of its solid torus. -/
theorem range_subset_image (h : IsSolidTorusLinkNeighborhood f Φ) (i : ι) :
    range (f i) ⊆ Φ i '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} :=
  (h.neighborhood i).range_subset_image

/-- The `i`-th solid torus is a neighbourhood of its component. -/
theorem range_mem_nhdsSet (h : IsSolidTorusLinkNeighborhood f Φ) (i : ι) :
    range (Φ i) ∈ 𝓝ˢ (range (f i)) :=
  (h.neighborhood i).range_mem_nhdsSet

end IsSolidTorusLinkNeighborhood

/-! ### Existence in Euclidean three-space -/

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable [Finite ι]
variable {f : ι → Circle → ℝ³}

/-- A finite family of pairwise disjoint `C²` embedded circles in `ℝ³` has pairwise disjoint
solid-torus neighbourhoods. -/
theorem exists_isSolidTorusLinkNeighborhood
    (hf : ∀ i, ContMDiff (𝓡 1) 𝓘(ℝ, ℝ³) 2 (f i))
    (himm : ∀ i z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ³) (f i) z))
    (hinj : ∀ i, Injective (f i))
    (hdisj : Pairwise (Disjoint on fun i => range (f i))) :
    ∃ Φ : ι → SolidTorus → ℝ³, IsSolidTorusLinkNeighborhood f Φ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      refine ⟨fun i => False.elim (hι.false i), ?_⟩
      exact ⟨fun i => False.elim (hι.false i), fun i j _ => False.elim (hι.false i)⟩
  | inr hι =>
      have hcompact : ∀ i, IsCompact (range (f i)) := fun i =>
        isCompact_range (hf i).continuous
      obtain ⟨δ, hδ, hV_disj⟩ :=
        exists_thickenings_pairwiseDisjoint (fun i => range (f i)) hcompact hdisj
      have hV_mem (i : ι) : thickening δ (range (f i)) ∈ 𝓝ˢ (range (f i)) :=
        thickening_mem_nhdsSet _ hδ
      choose Φ hΦ hΦsub using fun i =>
        exists_isSolidTorusNeighborhood (hf i) (himm i) (hinj i) (hV_mem i)
      refine ⟨Φ, ⟨hΦ, ?_⟩⟩
      intro i j hij
      exact (hV_disj hij).mono (hΦsub i) (hΦsub j)

namespace SmoothLinkEmbedding

/-- A smooth link presentation in Euclidean three-space admits pairwise disjoint
solid-torus neighbourhoods of all its labeled components. -/
theorem exists_isSolidTorusLinkNeighborhood {n : ℕ}
    (L : SmoothLinkEmbedding 𝓘(ℝ, ℝ³) ℝ³ n) :
    ∃ Φ : Fin n → SolidTorus → ℝ³,
      IsSolidTorusLinkNeighborhood (fun i => L i) Φ :=
  TauCeti.exists_isSolidTorusLinkNeighborhood
    (fun i => (L i).contMDiff.of_le (by simp))
    (fun i z => (L i).isImmersion.mfderiv_injective (by simp) z)
    (fun i => (L i).isEmbedding.injective) L.pairwiseDisjoint_range

end SmoothLinkEmbedding

end TauCeti
