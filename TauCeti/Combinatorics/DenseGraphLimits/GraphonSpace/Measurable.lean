/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.HomDensity
import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Coordinates
import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Measurable
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurable maps into graphon space

Graphon space carries the Borel σ-algebra of the cut metric. This file shows that the
homomorphism densities are a complete set of measurable coordinates for it: a map into graphon
space is measurable exactly when each of its homomorphism densities is. This holds over every
probability carrier, with no standard-Borel hypothesis.

The reason is topological. The homomorphism densities of all finite graphs are a topological
embedding of every graphon space into a countable product of copies of `ℝ`
(`isInducing_homDensityCoords`), and an embedding pulls the Borel σ-algebra back to the Borel
σ-algebra.

The criterion turns joint measurability into measurability of the class: if `(t, x, y) ↦ W t x y`
is measurable, then each density `t ↦ t(F, W t)` is measurable (`measurable_homDensity`), so
`t ↦ ⟦W t⟧` is measurable. This is what makes the law of the class of a random graphon, the
pushforward of a measure on the parameter space, a mixing measure on graphon space.

## Main results

* `TauCeti.DenseGraphLimits.measurable_graphonSpace_iff_forall_homDensity` — a map into graphon
  space is measurable if and only if all its homomorphism densities are;
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

/-- **Homomorphism densities are measurable coordinates on graphon space.** A map into graphon
space, over any probability carrier, is measurable if and only if the homomorphism density of
every finite graph along it is measurable. -/
theorem measurable_graphonSpace_iff_forall_homDensity {g : T → GraphonSpace Ω μ} :
    Measurable g ↔ ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      Measurable fun t => homDensityOnSpace F (g t) := by
  refine ⟨fun hg n F _ => (continuous_homDensityOnSpace F).measurable.comp hg, fun h => ?_⟩
  refine isInducing_homDensityCoords.measurable_comp_iff.1 (measurable_pi_iff.2 fun ⟨n, F, _⟩ => ?_)
  simpa only [Function.comp_def, homDensityCoords_apply] using h n F

/-- **The class of a measurable family of graphons is measurable.** If a family of graphons
depends jointly measurably on a parameter, then its class in graphon space depends measurably on
the parameter. -/
theorem measurable_graphonSpace_mk {W : T → Graphon Ω μ}
    (hW : Measurable fun p : T × Ω × Ω => W p.1 p.2.1 p.2.2) :
    Measurable fun t => (SeparationQuotient.mk (W t) : GraphonSpace Ω μ) :=
  measurable_graphonSpace_iff_forall_homDensity.2 fun _ F _ => by
    simpa only [homDensityOnSpace_mk] using measurable_homDensity F hW

end DenseGraphLimits

end TauCeti
