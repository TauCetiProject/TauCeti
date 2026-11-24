/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Basic
public import TauCeti.Geometry.Sphere.Unitary
public import TauCeti.MeasureTheory.Group.Action
public import TauCeti.Probability.Distributions.Uniform.Sphere.Basic
public import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Haar-random rotations of the sphere

Let `E` be a finite-dimensional real inner product space. Its rotation group is modelled as
`unitary (E →L[ℝ] E)`, the orthogonal operators on `E`, a compact topological group carrying the
normalized Haar measure `TauCeti.haarProb`. This file shows that the uniform law on the unit sphere
is the only rotation-invariant probability law on it, and that it is the law of a Haar-random
rotation of any fixed unit vector.

These are the two facts that let estimates for the uniform law on the sphere be transferred to a
Haar-random rotation. For a fixed point `x` of the sphere, `U • x` has the uniform law, so the
probability over `U` that a fixed finite set of points is moved into a bad set is bounded by a
union of uniform-law estimates. This is how random subspaces are produced from concentration of
measure on the sphere, as in the proof of Dvoretzky's theorem.

## Main results

* `TauCeti.Probability.smulInvariantMeasure_uniformSphereMeasure`: the uniform law on the sphere
  is invariant under the rotation group.
* `TauCeti.Probability.eq_measure_univ_smul_uniformSphereMeasure`: every s-finite
  rotation-invariant measure on the sphere is its total mass times the uniform law.
* `TauCeti.Probability.map_smul_haarProb`, `TauCeti.Probability.hasLaw_smul_haarProb`: the
  rotation of a fixed unit vector by a Haar-random rotation has the uniform law.

## References

* V. D. Milman and G. Schechtman, *Asymptotic Theory of Finite Dimensional Normed Spaces*,
  Lecture Notes in Mathematics 1200, Springer, 1986.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The uniform law on the sphere is invariant under the rotation group
`unitary (E →L[ℝ] E)`. -/
instance smulInvariantMeasure_uniformSphereMeasure :
    SMulInvariantMeasure (unitary (E →L[ℝ] E)) (sphere (0 : E) 1) (uniformSphereMeasure E) where
  measure_preimage_smul U s hs := by
    set f := Unitary.linearIsometryEquiv U
    have hU : (U • · : sphere (0 : E) 1 → sphere (0 : E) 1) =
        Subtype.map f fun x hx ↦ by simpa using hx :=
      funext fun x ↦ by
        rw [← Unitary.linearIsometryEquiv_smul_unitSphere]
        exact Subtype.ext (LinearIsometryEquiv.coe_smul_unitSphere f x)
    rw [hU, ← Measure.map_apply (f.continuous.measurable.subtype_map _) hs,
      f.map_uniformSphereMeasure]

/-- **A Haar-random rotation of a unit vector is uniform on the sphere.** The image of a fixed
unit vector `x` under a rotation drawn from normalized Haar measure on `unitary (E →L[ℝ] E)` has
the uniform law on the sphere. -/
theorem map_smul_haarProb (x : sphere (0 : E) 1) :
    (haarProb (unitary (E →L[ℝ] E))).map (· • x) = uniformSphereMeasure E := by
  have : Nontrivial E := ⟨⟨x, 0, ne_zero_of_mem_sphere one_ne_zero x⟩⟩
  have h := eq_measure_univ_smul_map_smul_const (haarProb (unitary (E →L[ℝ] E)))
    (uniformSphereMeasure E) x
  rwa [measure_univ, one_smul, eq_comm] at h

/-- **Uniqueness of the uniform law on the sphere.** Every s-finite measure on the unit sphere that
is invariant under the rotation group is its total mass times the uniform law. In particular the
uniform law is the only rotation-invariant probability law on the sphere. -/
theorem eq_measure_univ_smul_uniformSphereMeasure (ν : Measure (sphere (0 : E) 1)) [SFinite ν]
    [SMulInvariantMeasure (unitary (E →L[ℝ] E)) (sphere (0 : E) 1) ν] :
    ν = ν univ • uniformSphereMeasure E := by
  rcases isEmpty_or_nonempty (sphere (0 : E) 1) with hS | ⟨⟨x⟩⟩
  · simp [Measure.eq_zero_of_isEmpty ν]
  -- `ν` is a multiple of the law of a Haar-random rotation of `x`, which is the uniform law.
  rw [← map_smul_haarProb x]
  exact eq_measure_univ_smul_map_smul_const _ ν x

/-- The random variable `U ↦ U • x` on the rotation group with normalized Haar measure has the
uniform law on the sphere. -/
theorem hasLaw_smul_haarProb (x : sphere (0 : E) 1) :
    HasLaw (· • x) (uniformSphereMeasure E) (haarProb (unitary (E →L[ℝ] E))) where
  aemeasurable := (measurable_smul_const x).aemeasurable
  map_eq := map_smul_haarProb x

end TauCeti.Probability
