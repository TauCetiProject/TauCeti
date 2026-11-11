/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import TauCeti.Dynamics.BirkhoffSum.Cyclic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Centers of finite orbit energies

On a proper pseudometric space, a finite sum of squared distances attains its minimum on a
closed ball. If one summand is the distance to the center, the energy at the center controls
the distance of a minimizer. For a periodic motion, orbit-sum invariance gives a second
minimizer; a displacement bound keeps both points inside the ball.

These are the compact minimization and periodicity steps in the finite-orbit argument for
injectivity estimates in Morgan--Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 1.36.
Strict convexity along geodesics is a separate geometric input.

Public formalization references:
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Function

namespace TauCeti

variable {X ι : Type*} [PseudoMetricSpace X] [ProperSpace X] [Fintype ι]

/-- A finite family retaining the identity has an energy minimizer whose squared distance
from the center is bounded by the energy at the center. -/
theorem exists_isMinOn_sum_dist_sq {p : X} {r : ℝ} (hr : 0 ≤ r)
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
  obtain ⟨y, hy, hmin⟩ := (isCompact_closedBall p r).exists_isMinOn ⟨p, hp⟩ hcont
  refine ⟨y, hy, hmin, le_trans ?_ (hmin hp)⟩
  calc
    dist y p ^ 2 = dist (A i₀ y) p ^ 2 := by rw [hA₀ hy, id_eq]
    _ ≤ ∑ i, dist (A i y) p ^ 2 :=
      Finset.single_le_sum (fun i _ ↦ sq_nonneg (dist (A i y) p)) (Finset.mem_univ i₀)

/-- A short fixed-point-free periodic motion has two distinct minimizers of its orbit energy.
The energy bound places the first within `ρ` of the center; the displacement bound places its
image within `δ + 2 * ρ`. The hypothesis on these radii ensures the image remains in the
original minimizing ball. -/
theorem exists_ne_isMinOn_birkhoffSum_dist_sq {p : X} {m : ℕ} (hm : 0 < m)
    {r ρ δ : ℝ} (hρ : 0 < ρ) (hr : δ + 2 * ρ ≤ r)
    (henergy : (m : ℝ) * δ ^ 2 < ρ ^ 2) (d : X → X)
    (hcont : ∀ i : Fin m, ContinuousOn (d^[i.val]) (Metric.closedBall p r))
    (hcenter : ∀ i : Fin m, dist (d^[i.val] p) p ≤ δ)
    (hperiod : EqOn (d^[m]) id (Metric.closedBall p r))
    (hdisplace : ∀ x ∈ Metric.closedBall p r, dist (d x) p ≤ δ + 2 * dist x p)
    (hfree : ∀ x ∈ Metric.closedBall p r, d x ≠ x) :
    ∃ y : X, y ≠ d y ∧ dist y p < ρ ∧ dist (d y) p < δ + 2 * ρ ∧
      y ∈ Metric.closedBall p r ∧ d y ∈ Metric.closedBall p r ∧
      IsMinOn (birkhoffSum d (fun z ↦ dist z p ^ 2) m) (Metric.closedBall p r) y ∧
      IsMinOn (birkhoffSum d (fun z ↦ dist z p ^ 2) m) (Metric.closedBall p r) (d y) := by
  classical
  have hδ : 0 ≤ δ := (dist_nonneg (x := d^[0] p) (y := p)).trans (hcenter ⟨0, hm⟩)
  have hr₀ : 0 ≤ r := le_trans (by linarith) hr
  obtain ⟨y, hy, hmin, hbound⟩ := exists_isMinOn_sum_dist_sq hr₀
    (fun i : Fin m ↦ d^[i.val]) ⟨0, hm⟩ hcont (by intro x hx; rfl)
  have hsum : (∑ i : Fin m, dist (d^[i.val] p) p ^ 2) ≤ (m : ℝ) * δ ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin m, δ ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ dist_nonneg (hcenter i) 2
      _ = _ := by simp
  have hyρ : dist y p < ρ := by
    have := (hbound.trans hsum).trans_lt henergy
    nlinarith [dist_nonneg (x := y) (y := p)]
  have hdy : dist (d y) p < δ + 2 * ρ := by linarith [hdisplace y hy]
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

end TauCeti
