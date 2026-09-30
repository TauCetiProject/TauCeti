/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Constant
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic
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

Keeping these design-validation checks separate avoids adding their Bernoulli and finite-graph
dependencies to the canonical `CutMetric.Pullback.Basic` API module. The repository build includes
this module, so the regressions remain part of the build gate for the contract they test.

## Main results

* `cutDist_finiteGraphGraphonOnFin_top_two_const_half` — the reference value `1/8` for the finitely
  atomic and mixed checks.

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

/-- **The complete graph on the uniform two-point carrier is at cut distance `1/8` from the
constant graphon `1/2`**, whatever the probability carrier of the constant graphon.

The difference kernel is `1/2` on the two off-diagonal cells and `-1/2` on the two diagonal cells,
each of mass `1/4`; an off-diagonal cell attains `1/8`, and no rectangle does better. -/
theorem cutDist_finiteGraphGraphonOnFin_top_two_const_half {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    cutDist (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const μ ⟨1 / 2, by norm_num, by norm_num⟩) = 1 / 8 := by
  rw [cutDist_const_right]
  set K := (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2))).toSymmKernel -
    (Graphon.const (uniformOn Set.univ) ⟨1 / 2, by norm_num, by norm_num⟩).toSymmKernel
  have hK (i j : Fin 2) : K i j = ((if i = j then -1 else 1 : ℤ) : ℝ) / 2 := by
    by_cases h : i = j <;> simp [K, h] <;> norm_num
  have hrect (S T : Finset (Fin 2)) : K.rectIntegral (uniformOn Set.univ) S T =
      (∑ i ∈ S, ∑ j ∈ T, ((if i = j then -1 else 1 : ℤ) : ℝ)) / 8 := by
    rw [SymmKernel.rectIntegral_uniformOn_univ, Fintype.card_fin]
    simp_rw [hK, ← Finset.sum_div, div_div]
    norm_num
  -- The signed sum over a rectangle is decided over the sixteen rectangles of `Fin 2`.
  have hbound : ∀ S T : Finset (Fin 2),
      |∑ i ∈ S, ∑ j ∈ T, (if i = j then -1 else 1 : ℤ)| ≤ 1 := by decide
  refine le_antisymm (cutNorm_le _ fun S _ T _ => ?_) ?_
  · rw [← S.toFinite.coe_toFinset, ← T.toFinite.coe_toFinset, hrect, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 8), div_le_div_iff_of_pos_right (by norm_num)]
    exact_mod_cast hbound _ _
  · have h := abs_rectIntegral_le_cutNorm _ K
      (MeasurableSet.of_discrete (s := ((({0} : Finset (Fin 2))) : Set (Fin 2))))
      (MeasurableSet.of_discrete (s := ((({1} : Finset (Fin 2))) : Set (Fin 2))))
    rw [hrect] at h
    simpa using h

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
      (Graphon.const (bernoulliMeasure (0 : ℝ) 1 p) ⟨1 / 2, by norm_num, by norm_num⟩) =
      1 / 8 := by
  rw [← cutDist_eq_cutDistPullback, cutDist_finiteGraphGraphonOnFin_top_two_const_half]

-- Regression: the uniform two-point carrier against `(I, volume)`, so a coupling has an atomic and
-- a continuous direction at once.
example :
    cutDistPullback (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const (volume : Measure I) ⟨1 / 2, by norm_num, by norm_num⟩) = 1 / 8 := by
  rw [← cutDist_eq_cutDistPullback, cutDist_finiteGraphGraphonOnFin_top_two_const_half]

end DenseGraphLimits

end TauCeti
