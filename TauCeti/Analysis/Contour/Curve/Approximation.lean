/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Smooth endpoint-preserving approximation of continuous complex curves

Every continuous map from the unit interval to `ℂ` is uniformly approximated, to any positive
tolerance, by a smooth curve on `ℝ` taking the same values at `0` and `1`. The approximants are
Mathlib's Bernstein approximations, read as polynomial functions on all of `ℝ`, which is what makes
their smoothness and their endpoint values immediate.

## Main results

* `TauCeti.Contour.exists_contDiff_eq_endpoints_dist_lt` — the endpoint-preserving smooth
  approximation.
* `JoinedIn.exists_contDiff_mapsTo` — two points joined by a path in an open set are joined by a
  smooth curve that stays in the set.

This is the regularization step that lets the merely continuous intermediate paths of a path
homotopy be compared with the piecewise-`C¹` winding number.

## Provenance

The construction and its uniform convergence are Mathlib's `bernsteinApproximation` and
`bernsteinApproximation_uniform`; the polynomials themselves are Mathlib's `bernsteinPolynomial`.
No formal source is vendored.
-/

public section

noncomputable section

open scoped unitInterval

namespace TauCeti.Contour

/-- Mathlib's `n`-th Bernstein approximation of `f`, read as a polynomial function on all of `ℝ`.
Keeping the polynomial off the unit interval makes its smoothness immediate, while
`bernsteinCurve_apply` connects it to Mathlib's uniform approximation theorem. -/
private def bernsteinCurve (n : ℕ) (f : C(I, ℂ)) (t : ℝ) : ℂ :=
  ∑ k : Fin (n + 1), Polynomial.aeval t (bernsteinPolynomial ℝ n k) • f (bernstein.z k)

private theorem bernsteinCurve_apply (n : ℕ) (f : C(I, ℂ)) (t : I) :
    bernsteinCurve n f t = bernsteinApproximation n f t := by
  simp [bernsteinCurve, bernsteinApproximation.apply, bernstein, Polynomial.coe_aeval_eq_eval]

private theorem contDiff_bernsteinCurve (n : ℕ) (f : C(I, ℂ)) :
    ContDiff ℝ ⊤ (bernsteinCurve n f) :=
  ContDiff.sum fun _ _ => (Polynomial.contDiff_aeval _ _).smul_const _

/-- **Endpoint-preserving smooth approximation of a continuous complex path.** Every continuous map
from the unit interval to `ℂ` is uniformly approximated, to any positive tolerance, by a smooth
curve on `ℝ` with the same values at `0` and `1`.

The approximants are Mathlib's Bernstein approximations, read as polynomial functions on `ℝ`; a
consumer needing only piecewise-`C¹` regularity gets it from `IsPiecewiseC1On.of_contDiffOn`. -/
theorem exists_contDiff_eq_endpoints_dist_lt (f : C(I, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → ℂ, ContDiff ℝ ⊤ γ ∧ γ 0 = f 0 ∧ γ 1 = f 1 ∧ ∀ t : I, dist (γ t) (f t) < ε := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (bernsteinApproximation_uniform f) ε hε
  let n := max N 1
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hn : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _))
  refine ⟨bernsteinCurve n f, contDiff_bernsteinCurve n f, ?_, ?_, ?_⟩
  · exact (bernsteinCurve_apply n f 0).trans (bernsteinApproximation.apply_zero n f)
  · exact (bernsteinCurve_apply n f 1).trans (bernsteinApproximation.apply_one hn f)
  · intro t
    rw [bernsteinCurve_apply]
    exact (ContinuousMap.dist_apply_le_dist t).trans_lt (hN n hnN)

/-- **Smoothing a path inside an open set.** Two points joined by a path in an open set `U ⊆ ℂ`
are joined by a smooth curve on `ℝ` that maps the unit interval into `U`. -/
theorem _root_.JoinedIn.exists_contDiff_mapsTo {U : Set ℂ} {z w : ℂ} (h : JoinedIn U z w)
    (hU : IsOpen U) :
    ∃ γ : ℝ → ℂ, ContDiff ℝ ⊤ γ ∧ γ 0 = z ∧ γ 1 = w ∧ Set.MapsTo γ (Set.Icc 0 1) U := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_range π.continuous).exists_thickening_subset_open hU
    (Set.range_subset_iff.2 hπ)
  obtain ⟨γ, hγ, hγ0, hγ1, hγδ⟩ := exists_contDiff_eq_endpoints_dist_lt π.toContinuousMap hδ
  refine ⟨γ, hγ, hγ0.trans π.source, hγ1.trans π.target, fun t ht => hthick ?_⟩
  rw [Metric.mem_thickening_iff]
  exact ⟨π ⟨t, ht⟩, ⟨_, rfl⟩, by simpa using hγδ ⟨t, ht⟩⟩

end TauCeti.Contour

end
