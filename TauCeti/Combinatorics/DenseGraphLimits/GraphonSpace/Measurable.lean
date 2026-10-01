/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Compact
public import TauCeti.Combinatorics.DenseGraphLimits.Separation.Inverse
public import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurable maps into graphon space

Graphon space carries the Borel σ-algebra of the cut metric. This file shows that the
homomorphism densities are a complete set of measurable coordinates for it: a map into graphon
space is measurable exactly when each of its homomorphism densities is. This holds over every
probability carrier, with no standard-Borel hypothesis.

The reason is topological. The homomorphism densities of all finite graphs separate the points of
the compact space `GraphonSpaceI`, so together they embed it as a closed subspace of a countable
product of copies of `ℝ`. Every graphon space embeds isometrically into `GraphonSpaceI` without
changing any homomorphism density, so the density coordinates are a topological embedding of every
graphon space. An embedding pulls the Borel σ-algebra back to the Borel σ-algebra.

The criterion turns joint measurability into measurability of the class: if `(t, x, y) ↦ W t x y`
is measurable, then each density `t ↦ t(F, W t)` is a measurable parametric integral, so
`t ↦ ⟦W t⟧` is measurable. This is what makes the law of the class of a random graphon, the
pushforward of a measure on the parameter space, a mixing measure on graphon space.

## Main results

* `TauCeti.DenseGraphLimits.measurable_graphonSpace_iff` — a map into graphon space is measurable
  if and only if all its homomorphism densities are;
* `TauCeti.DenseGraphLimits.measurable_homDensity` — the homomorphism density of a jointly
  measurable family of graphons is measurable in the parameter;
* `TauCeti.DenseGraphLimits.measurable_graphonSpace_mk` — the class of a jointly measurable family
  of graphons is measurable in the parameter.

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
  {T : Type*} [MeasurableSpace T]

section Coordinates

/-- The homomorphism densities of all finite graphs on `Fin n`, as one point of a countable
product of copies of `ℝ`. -/
private def homDensityCoords (x : GraphonSpace Ω μ) (F : Σ n : ℕ, SimpleGraph (Fin n)) : ℝ :=
  letI := Classical.decRel F.2.Adj
  homDensityOnSpace F.2 x

private theorem continuous_homDensityCoords : Continuous (homDensityCoords (μ := μ)) :=
  continuous_pi fun F => by
    let := Classical.decRel F.2.Adj
    exact continuous_homDensityOnSpace F.2

private theorem injective_homDensityCoords : Function.Injective (homDensityCoords (μ := μ)) := by
  intro x y h
  refine (graphonSpace_ext_iff_homDensity x y).2 fun n F _ => ?_
  have hF := congrFun h ⟨n, F⟩
  simp only [homDensityCoords] at hF
  convert hF

private theorem homDensityCoords_toGraphonSpaceI (x : GraphonSpace Ω μ) :
    homDensityCoords (toGraphonSpaceI x) = homDensityCoords x := by
  funext F
  let := Classical.decRel F.2.Adj
  exact homDensityOnSpace_toGraphonSpaceI F.2 x

/-- The density coordinates embed every graphon space: on the compact `GraphonSpaceI` they are a
continuous injection into a Hausdorff space, hence a closed embedding, and every graphon space
embeds isometrically into `GraphonSpaceI` without changing any density. -/
private theorem isInducing_homDensityCoords : IsInducing (homDensityCoords (μ := μ)) := by
  have hI : IsClosedEmbedding (homDensityCoords (μ := (volume : Measure unitInterval))) :=
    continuous_homDensityCoords.isClosedEmbedding injective_homDensityCoords
  have hcomp : homDensityCoords (μ := μ) =
      homDensityCoords (μ := (volume : Measure unitInterval)) ∘ toGraphonSpaceI :=
    funext fun x => (homDensityCoords_toGraphonSpaceI x).symm
  rw [hcomp]
  exact hI.isInducing.comp isometry_toGraphonSpaceI.isEmbedding.isInducing

end Coordinates

/-- **Homomorphism densities are measurable coordinates on graphon space.** A map into graphon
space, over any probability carrier, is measurable if and only if the homomorphism density of
every finite graph along it is measurable. -/
theorem measurable_graphonSpace_iff {g : T → GraphonSpace Ω μ} :
    Measurable g ↔ ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      Measurable fun t => homDensityOnSpace F (g t) := by
  refine ⟨fun hg n F _ => (continuous_homDensityOnSpace F).measurable.comp hg, fun h => ?_⟩
  refine isInducing_homDensityCoords.measurable_comp_iff.1 (measurable_pi_iff.2 fun F => ?_)
  exact @h F.1 F.2 (Classical.decRel _)

/-- **Homomorphism densities of a measurable family of graphons.** If a family of graphons depends
jointly measurably on a parameter, then so does the homomorphism density of every finite graph in
it. -/
theorem measurable_homDensity {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    {W : T → Graphon Ω μ} (hW : Measurable fun p : T × Ω × Ω => W p.1 p.2.1 p.2.2) :
    Measurable fun t => homDensity F (W t) := by
  simp_rw [homDensity_def]
  refine (StronglyMeasurable.integral_prod_right'
    (f := fun p : T × (V → Ω) => ∏ e ∈ F.edgeFinset, edgeFactor (W p.1) p.2 e) ?_).measurable
  refine (Finset.measurable_prod _ fun e _ => ?_).stronglyMeasurable
  induction e using Sym2.ind with
  | _ a b =>
    simp only [edgeFactor_mk]
    exact hW.comp (f := fun p : T × (V → Ω) => (p.1, p.2 a, p.2 b)) (by fun_prop)

/-- **The class of a measurable family of graphons is measurable.** If a family of graphons
depends jointly measurably on a parameter, then its class in graphon space depends measurably on
the parameter. -/
theorem measurable_graphonSpace_mk {W : T → Graphon Ω μ}
    (hW : Measurable fun p : T × Ω × Ω => W p.1 p.2.1 p.2.2) :
    Measurable fun t => (SeparationQuotient.mk (W t) : GraphonSpace Ω μ) :=
  measurable_graphonSpace_iff.2 fun _ F _ => by
    simpa only [homDensityOnSpace_mk] using measurable_homDensity F hW

end DenseGraphLimits

end TauCeti
