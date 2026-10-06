/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.FiniteGraph
import Mathlib.Probability.Distributions.Bernoulli
import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Pullback.Basic

/-!
# Atomic regressions for the map form of the cut distance

The harder direction of `cutDist_eq_cutDistPullback` applies Janson's Thm A.9 to the *coupling*, so
the atomic cases to check are atomic couplings. The three checks below run the equivalence at a
point-mass coupling, at finitely atomic ones, and at ones mixing an atomic with a continuous
direction, and in each case they **evaluate** the map form rather than only instantiating the
equivalence.

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

These examples compare the map form with independently computed distances on carriers with
different atomic structures. In each case the nonzero value witnesses that the map form includes
the relevant pullbacks.

## Main results

* The point-mass, finitely atomic, and mixed examples evaluate `cutDistPullback` using
  `cutDist_dirac_dirac` and `cutDist_finiteGraphGraphonOnFin_top_two_const_half`.

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

-- Regression: both carriers are point masses, so the only coupling is a point mass. The map form
-- is still the distance of the two values, although no bijection relates either carrier to
-- `(I, volume)`.
example (U : Graphon ℝ (Measure.dirac 0)) (W : Graphon ℝ (Measure.dirac 1)) :
    cutDistPullback U W = |U 0 0 - W 1 1| := by
  rw [← cutDist_eq_cutDistPullback, cutDist_dirac_dirac]

-- Regression: the uniform two-point carrier against a Bernoulli law, carried by at most two atoms
-- — an endpoint parameter collapses it to a point mass — so every coupling is finitely atomic, and
-- for an interior parameter there are infinitely many of them.
example {p : I} :
    cutDistPullback (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const (bernoulliMeasure (0 : ℝ) 1 p) ⟨2⁻¹, by norm_num, by norm_num⟩) =
      1 / 8 := by
  rw [← cutDist_eq_cutDistPullback, cutDist_finiteGraphGraphonOnFin_top_two_const_half]

-- Regression: the uniform two-point carrier against `(I, volume)`, so a coupling has an atomic and
-- a continuous direction at once.
example :
    cutDistPullback (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const (volume : Measure I) ⟨2⁻¹, by norm_num, by norm_num⟩) = 1 / 8 := by
  rw [← cutDist_eq_cutDistPullback, cutDist_finiteGraphGraphonOnFin_top_two_const_half]

end DenseGraphLimits

end TauCeti
