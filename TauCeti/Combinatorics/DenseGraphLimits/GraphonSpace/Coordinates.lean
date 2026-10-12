/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.HomDensity
import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Compact
import TauCeti.Combinatorics.DenseGraphLimits.Separation.Inverse

/-!
# Homomorphism densities as coordinates on graphon space

The homomorphism densities of all finite graphs, taken together, form one map from graphon space
into a countable product of copies of `ℝ`. This file shows that this map is a topological
embedding of every graphon space.

On the compact space `GraphonSpaceI` the densities separate points, so they are a continuous
injection into a Hausdorff space, hence a closed embedding. Every graphon space embeds
isometrically into `GraphonSpaceI` without changing any homomorphism density, so the density
coordinates are an embedding over any probability carrier.

## Main definitions

* `TauCeti.DenseGraphLimits.homDensityCoords` — the homomorphism densities of all graphs on
  `Fin n`, as one point of a product of copies of `ℝ`.

## Main results

* `TauCeti.DenseGraphLimits.isClosedEmbedding_homDensityCoords` — on the unit-interval graphon
  space, the density coordinates are a closed embedding;
* `TauCeti.DenseGraphLimits.isInducing_homDensityCoords` — on the graphon space over any
  probability carrier, the density coordinates are inducing.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Sections 2--3 (graph limits as a compact space coordinatised by homomorphism
  densities).
-/

public section

noncomputable section

open MeasureTheory Topology

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The homomorphism densities of all finite graphs on `Fin n`, each with its decidability
instance, as one point of a product of copies of `ℝ`. -/
def homDensityCoords (x : GraphonSpace Ω μ)
    (p : Σ n : ℕ, Σ F : SimpleGraph (Fin n), DecidableRel F.Adj) : ℝ :=
  letI := p.2.2
  homDensityOnSpace p.2.1 x

/-- Each density coordinate is the homomorphism density of its graph. -/
@[simp]
theorem homDensityCoords_apply (x : GraphonSpace Ω μ) {n : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] : homDensityCoords x ⟨n, F, ‹_›⟩ = homDensityOnSpace F x := by
  simp only [homDensityCoords]

/-- The density coordinates are continuous: each homomorphism density is. -/
theorem continuous_homDensityCoords : Continuous (homDensityCoords (μ := μ)) :=
  continuous_pi fun ⟨_, F, _⟩ => by
    simpa only [homDensityCoords_apply] using continuous_homDensityOnSpace F

/-- The density coordinates are injective: homomorphism densities separate graphon classes. -/
theorem injective_homDensityCoords : Function.Injective (homDensityCoords (μ := μ)) :=
  fun x y h => (graphonSpace_ext_iff_homDensity x y).2 fun n F _ => by
    simpa only [homDensityCoords_apply] using congrFun h ⟨n, F, ‹_›⟩

/-- Embedding into the unit-interval graphon space does not change the density coordinates. -/
@[simp]
theorem homDensityCoords_toGraphonSpaceI (x : GraphonSpace Ω μ) :
    homDensityCoords (toGraphonSpaceI x) = homDensityCoords x :=
  funext fun ⟨_, F, _⟩ => by
    simp only [homDensityCoords_apply, homDensityOnSpace_toGraphonSpaceI]

/-- **The density coordinates are a closed embedding of `GraphonSpaceI`.** They are a continuous
injection of a compact space into a Hausdorff space. -/
theorem isClosedEmbedding_homDensityCoords :
    IsClosedEmbedding (homDensityCoords (μ := (volume : Measure unitInterval))) :=
  continuous_homDensityCoords.isClosedEmbedding injective_homDensityCoords

/-- **The density coordinates embed every graphon space.** Every graphon space embeds
isometrically into `GraphonSpaceI` without changing any density, and there the density
coordinates are a closed embedding. -/
theorem isInducing_homDensityCoords : IsInducing (homDensityCoords (μ := μ)) := by
  have hcomp : homDensityCoords (μ := μ) =
      homDensityCoords (μ := (volume : Measure unitInterval)) ∘ toGraphonSpaceI :=
    funext fun x => (homDensityCoords_toGraphonSpaceI x).symm
  rw [hcomp]
  exact isClosedEmbedding_homDensityCoords.isInducing.comp
    isometry_toGraphonSpaceI.isEmbedding.isInducing

end DenseGraphLimits

end TauCeti
