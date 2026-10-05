/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.LowDimTopology.SolidTorusNeighborhood

/-!
# Disjoint solid-torus neighbourhoods of links

The image of a finite link in `ℝ³` is a finite union of disjoint compact circles.  Compactness
gives one positive metric radius for which the thickenings of all components are pairwise
disjoint.  Applying the solid-torus neighbourhood theorem to each thickening gives the usual
disjoint tubular neighbourhoods of the link.

## Main declarations

* `TauCeti.IsSolidTorusLinkNeighborhood` records solid-torus neighbourhoods of every component
  together with pairwise disjoint open solid-torus images.
* `TauCeti.exists_isSolidTorusLinkNeighborhood` constructs these neighbourhoods for a finite
  family of pairwise disjoint `C²` embedded circles in `ℝ³`.

This is the Euclidean link-neighbourhood step in the GeometricTopology Layer 5 construction; the
transfer to `S³` and the smooth structure on the link exterior are separate steps.
-/

public section

open Set Metric Function Topology
open scoped Matrix Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {ι X : Type*} [TopologicalSpace X]

/-- A family of solid-torus neighbourhoods whose open images are pairwise disjoint. -/
structure IsSolidTorusLinkNeighborhood (f : ι → Circle → X)
    (Φ : ι → SolidTorus → X) : Prop where
  /-- Each component has a solid-torus neighbourhood. -/
  neighborhood : ∀ i, IsSolidTorusNeighborhood (f i) (Φ i)
  /-- The open solid-torus images of distinct components are disjoint. -/
  pairwiseDisjoint : Pairwise (Disjoint on fun i =>
    Φ i '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1})

namespace IsSolidTorusLinkNeighborhood

variable {f : ι → Circle → X} {Φ : ι → SolidTorus → X}

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

variable [Finite ι] [Nonempty ι]
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
  let _ := Fintype.ofFinite ι
  have hcompact : ∀ i, IsCompact (range (f i)) := fun i =>
    isCompact_range (hf i).continuous
  have hex : ∀ i j, i ≠ j → ∃ δ : ℝ, 0 < δ ∧
      Disjoint (thickening δ (range (f i))) (thickening δ (range (f j))) := by
    intro i j hij
    exact (hdisj hij).exists_thickenings (hcompact i) (hcompact j).isClosed
  let r : ι → ι → ℝ := fun i j =>
    if h : i = j then 1 else Classical.choose (hex i j h)
  have hr_pos : ∀ i j, 0 < r i j := by
    intro i j
    by_cases hij : i = j
    · simp [r, hij]
    · simpa [r, hij] using (Classical.choose_spec (hex i j hij)).1
  have hr_disj : ∀ i j, i ≠ j →
      Disjoint (thickening (r i j) (range (f i)))
        (thickening (r i j) (range (f j))) := by
    intro i j hij
    simpa [r, hij] using (Classical.choose_spec (hex i j hij)).2
  let P : Finset (ι × ι) := Finset.univ.product Finset.univ
  have hP : P.Nonempty := by
    exact Finset.Nonempty.product Finset.univ_nonempty Finset.univ_nonempty
  let Q : Finset ℝ := P.image (fun p => r p.1 p.2)
  have hQ : Q.Nonempty := hP.image _
  let δ : ℝ := Q.min' hQ
  have hδ_pos : 0 < δ := by
    have hqpos : ∀ q ∈ Q, 0 < q := by
      intro q hq
      rcases Finset.mem_image.1 hq with ⟨p, hp, rfl⟩
      exact hr_pos p.1 p.2
    exact hqpos _ (Finset.min'_mem Q hQ)
  have hδ_le (i j : ι) : δ ≤ r i j := by
    apply Finset.min'_le Q (r i j)
    exact Finset.mem_image.2 ⟨(i, j), by simp [P], rfl⟩
  have hV_disj : ∀ i j, i ≠ j →
      Disjoint (thickening δ (range (f i)))
        (thickening δ (range (f j))) := by
    intro i j hij
    apply (hr_disj i j hij).mono
    · exact thickening_mono (hδ_le i j) _
    · exact thickening_mono (hδ_le i j) _
  have hV_mem (i : ι) : thickening δ (range (f i)) ∈ 𝓝ˢ (range (f i)) :=
    thickening_mem_nhdsSet _ hδ_pos
  choose Φ hΦ hΦsub using fun i =>
    exists_isSolidTorusNeighborhood (hf i) (himm i) (hinj i) (hV_mem i)
  refine ⟨Φ, ⟨hΦ, ?_⟩⟩
  intro i j hij
  apply (hV_disj i j hij).mono
  · rintro _ ⟨p, hp, rfl⟩
    exact hΦsub i ⟨p, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hΦsub j ⟨p, rfl⟩

end TauCeti
