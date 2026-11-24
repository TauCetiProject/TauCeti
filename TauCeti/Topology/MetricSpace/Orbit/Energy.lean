/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import TauCeti.Dynamics.BirkhoffSum.Cyclic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Centers of finite orbit energies

On a compact ball in a pseudometric space, a finite sum of squared distances attains its
minimum. If one summand is the distance to the center, the energy at the center controls
the distance of a minimizer. For a periodic motion, orbit-sum invariance gives a second
minimizer; the same energy bound keeps both points inside the ball.

These are the compact minimization and periodicity steps in the finite-orbit argument for
injectivity estimates in Morgan--Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 1.36.
Strict convexity along geodesics is a separate geometric input.

Public formalization references:
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Function

namespace IsCompact

variable {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]

/-- A finite family retaining the identity has an energy minimizer whose squared distance
from the center is bounded by the energy at the center. -/
theorem exists_isMinOn_sum_dist_sq {p : X} {r : ℝ}
    (hcompact : IsCompact (Metric.closedBall p r)) (hr : 0 ≤ r)
    (A : ι → X → X) (i₀ : ι)
    (hA : ∀ i, ContinuousOn (A i) (Metric.closedBall p r))
    (hA₀ : EqOn (A i₀) id (Metric.closedBall p r)) :
    ∃ y ∈ Metric.closedBall p r,
      IsMinOn (fun z ↦ ∑ i, dist (A i z) p ^ 2) (Metric.closedBall p r) y ∧
      dist y p ^ 2 ≤ ∑ i, dist (A i p) p ^ 2 := by
  classical
  have hp : p ∈ Metric.closedBall p r := Metric.mem_closedBall_self hr
  have hcont : ContinuousOn (fun z ↦ ∑ i, dist (A i z) p ^ 2)
      (Metric.closedBall p r) :=
    continuousOn_finsetSum _ (fun i _ x hx ↦
      ((hA i x hx).dist continuousWithinAt_const).pow 2)
  obtain ⟨y, hy, hmin⟩ := hcompact.exists_isMinOn ⟨p, hp⟩ hcont
  refine ⟨y, hy, hmin, le_trans ?_ (hmin hp)⟩
  calc
    dist y p ^ 2 = dist (A i₀ y) p ^ 2 := by rw [hA₀ hy, id_eq]
    _ ≤ ∑ i, dist (A i y) p ^ 2 :=
      Finset.single_le_sum (fun i _ ↦ sq_nonneg (dist (A i y) p)) (Finset.mem_univ i₀)

/-- A fixed-point-free periodic motion has two distinct minimizers of its orbit energy.
An energy bound at the center places both minimizers within `ρ` of the center, so both remain
in the original minimizing ball. No displacement estimate is required. -/
theorem exists_ne_isMinOn_birkhoffSum_dist_sq {p : X} {m : ℕ} {r ρ : ℝ}
    (hcompact : IsCompact (Metric.closedBall p r)) (hm : 0 < m)
    (hρ : 0 < ρ) (hr : ρ ≤ r) (d : X → X)
    (hcont : ∀ i : Fin m, ContinuousOn (d^[i.val]) (Metric.closedBall p r))
    (henergy : (∑ i : Fin m, dist (d^[i.val] p) p ^ 2) < ρ ^ 2)
    (hperiod : EqOn (d^[m]) id (Metric.closedBall p r))
    (hfree : ∀ x ∈ Metric.closedBall p r, d x ≠ x) :
    ∃ y : X, y ≠ d y ∧ dist y p < ρ ∧ dist (d y) p < ρ ∧
      y ∈ Metric.closedBall p r ∧ d y ∈ Metric.closedBall p r ∧
      IsMinOn (birkhoffSum d (fun z ↦ dist z p ^ 2) m) (Metric.closedBall p r) y ∧
      IsMinOn (birkhoffSum d (fun z ↦ dist z p ^ 2) m) (Metric.closedBall p r) (d y) := by
  classical
  have hr₀ : 0 ≤ r := hρ.le.trans hr
  have hp : p ∈ Metric.closedBall p r := Metric.mem_closedBall_self hr₀
  obtain ⟨y, hy, hmin, hbound⟩ := exists_isMinOn_sum_dist_sq hcompact hr₀
    (fun i : Fin m ↦ d^[i.val]) ⟨0, hm⟩ hcont (by intro x _; rfl)
  have hyρ : dist y p < ρ := by
    have := hbound.trans_lt henergy
    nlinarith [dist_nonneg (x := y) (y := p)]
  have hm₁ : m ≠ 1 := by
    rintro rfl
    exact hfree y hy (by simpa using hperiod hy)
  have h₁m : 1 < m := lt_of_le_of_ne (Nat.succ_le_of_lt hm) hm₁.symm
  have hdy : dist (d y) p < ρ := by
    have hsingle : dist (d y) p ^ 2 ≤ ∑ i : Fin m, dist (d^[i.val] y) p ^ 2 := by
      simpa using Finset.single_le_sum (fun (i : Fin m) _ ↦ sq_nonneg (dist (d^[i.val] y) p))
        (Finset.mem_univ (⟨1, h₁m⟩ : Fin m))
    have := hsingle.trans_lt ((hmin hp).trans_lt henergy)
    nlinarith [dist_nonneg (x := d y) (y := p)]
  have hmin' : IsMinOn (birkhoffSum d (fun z ↦ dist z p ^ 2) m)
      (Metric.closedBall p r) y := by
    have hfun : (fun z ↦ ∑ i : Fin m, dist (d^[i.val] z) p ^ 2) =
        birkhoffSum d (fun z ↦ dist z p ^ 2) m := by
      funext z
      exact Fin.sum_univ_eq_sum_range (fun i ↦ dist (d^[i] z) p ^ 2) m
    rw [← hfun]
    exact hmin
  refine ⟨y, (hfree y hy).symm, hyρ, hdy, hy,
    Metric.mem_closedBall.mpr (hdy.le.trans hr), hmin', ?_⟩
  intro z hz
  have hper : IsPeriodicPt d m y := hperiod hy
  rw [hper.birkhoffSum_apply_eq]
  exact hmin' hz

end IsCompact
