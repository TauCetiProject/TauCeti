/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.FiniteGraph
public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Pullback.Basic

/-!
# Atomic regressions for the map form of the cut distance

The harder direction of `cutDist_eq_cutDistPullback` applies Janson's Thm A.9 to the *coupling*, so
the atomic cases to check are atomic couplings. The named regression theorems below run the
equivalence at a point-mass coupling, at finitely atomic ones, and at ones mixing an atomic with a
continuous direction. The accompanying examples retain the computed map-form distances.

The values come from the coupling side, where they can be computed exactly: against a constant
graphon, and against a graphon on a point mass, every coupling contributes the same cut norm
(`cutDist_const_right`, `cutDist_dirac_dirac`). Each value is in general nonzero, so these checks
also rule out the failure mode an atomic carrier invites: a map form whose index set is empty on
atomic carriers — for instance one ranging over measure-preserving *bijections* with `(I, volume)`,
of which an atomic carrier has none — is the junk value `0` there, and would contradict them.

The finitely atomic and mixed checks both compare the complete graph `K₂` on the uniform two-point
carrier with the constant graphon `1/2`. Their cut distance is `1/8`: the difference kernel is `1/2`
off the diagonal and `-1/2` on it, the cut norm is attained on an off-diagonal cell of mass `1/4`,
and no rectangle does better (`cutDist_finiteGraphGraphonOnFin_top_two_const_half`).

These regressions compare the map form with independently computed distances on carriers with
different atomic structures. In each case the nonzero value witnesses that the map form includes
the relevant pullbacks. `CutMetric.Pullback.Constant` computes the same values from the definition
of the map form, without the equivalence (`cutDistPullback_dirac_dirac`,
`cutDistPullback_finiteGraphGraphonOnFin_top_two_const_half`).

## Main results

* `cutDistPullback_dirac_regression`, `cutDistPullback_finite_atomic_regression`, and
  `cutDistPullback_mixed_regression` are named instances of `cutDist_eq_cutDistPullback` for the
  point-mass, finitely atomic, and mixed cases; the examples also check their computed values.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Thm 6.9 and Thm A.9.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

/-- **The coupling and map forms agree for two point-mass graphons.** This named regression checks
the Layer 5 equivalence in the case where neither carrier admits a measure-preserving bijection
with `(I, volume)`. -/
theorem cutDistPullback_dirac_regression (U : Graphon ℝ (Measure.dirac 0))
    (W : Graphon ℝ (Measure.dirac 1)) :
    cutDist U W = cutDistPullback U W :=
  cutDist_eq_cutDistPullback U W

example (U : Graphon ℝ (Measure.dirac 0))
    (W : Graphon ℝ (Measure.dirac 1)) : cutDistPullback U W = |U 0 0 - W 1 1| := by
  rw [← cutDistPullback_dirac_regression, cutDist_dirac_dirac]

/-- **The coupling and map forms agree between a uniform two-point graphon and a Bernoulli
carrier, and the common distance is `1/8`.** This tests finite atomic couplings, including the
point-mass endpoint parameters. -/
theorem cutDistPullback_finite_atomic_regression {p : I} :
    cutDist (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const (bernoulliMeasure (0 : ℝ) 1 p) ⟨2⁻¹, by norm_num, by norm_num⟩) =
    cutDistPullback (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const (bernoulliMeasure (0 : ℝ) 1 p) ⟨2⁻¹, by norm_num, by norm_num⟩) :=
  cutDist_eq_cutDistPullback _ _

example {p : I} :
    cutDistPullback (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const (bernoulliMeasure (0 : ℝ) 1 p) ⟨2⁻¹, by norm_num, by norm_num⟩) = 1 / 8 := by
  rw [← cutDistPullback_finite_atomic_regression,
    cutDist_finiteGraphGraphonOnFin_top_two_const_half]

/-- **The coupling and map forms agree between an atomic graphon and the unit interval, and the
common distance is `1/8`.** This tests couplings with an atomic and a continuous coordinate. -/
theorem cutDistPullback_mixed_regression :
    cutDist (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const (volume : Measure I) ⟨2⁻¹, by norm_num, by norm_num⟩) =
    cutDistPullback (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const (volume : Measure I) ⟨2⁻¹, by norm_num, by norm_num⟩) :=
  cutDist_eq_cutDistPullback _ _

example :
    cutDistPullback (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const (volume : Measure I) ⟨2⁻¹, by norm_num, by norm_num⟩) = 1 / 8 := by
  rw [← cutDistPullback_mixed_regression,
    cutDist_finiteGraphGraphonOnFin_top_two_const_half]

end DenseGraphLimits

end TauCeti
