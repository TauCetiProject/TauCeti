/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Radius
import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Power series evaluation and `HasFPowerSeriesOnBall`

Over a complete nontrivially normed field `K`, a formal power series `g : K⟦X⟧` of positive radius
is the power series at `a` of the function `z ↦ g(z - a)` on the open ball of radius `radius g`
about `a`, in the sense of Mathlib's `HasFPowerSeriesOnBall`, with the scalar formal multilinear
series `FormalMultilinearSeries.ofScalars K (coeff · g)`. Conversely, if `F : K → K` has a power
series `P` on the ball of radius `r` about `a`, then the formal power series with the coefficients
of `P` has radius at least `r` and takes the value `F z` at `z - a` on that ball. Two series of
radius at least `r > 0` that agree as functions of `z - a` on the open ball of radius `r` about
`a` are equal.

## Main results

* `PowerSeries.hasFPowerSeriesOnBall_evalAt_sub` and
  `PowerSeries.hasFPowerSeriesOnBall_of_forall_eq_evalAt_sub`: a series of radius at least `r > 0`
  gives `HasFPowerSeriesOnBall` on the ball of radius `r`.
* `HasFPowerSeriesOnBall.le_radius_mk_coeff` and `HasFPowerSeriesOnBall.evalAt_mk_coeff_sub`: the
  converse comparison.
* `PowerSeries.eq_of_forall_evalAt_sub_eq`: uniqueness of the series representing a function on a
  ball of positive radius.
-/

public section

open Metric
open scoped ENNReal

namespace PowerSeries

variable {K : Type*} [NontriviallyNormedField K]

/-- **Comparison with `HasFPowerSeriesOnBall`.** A series `g` of positive radius is the power
series at `a` of the function `z ↦ g(z - a)` on the open ball of radius `radius g` about `a`. -/
theorem hasFPowerSeriesOnBall_evalAt_sub [CompleteSpace K] (g : K⟦X⟧) (hg : 0 < g.radius) (a : K) :
    HasFPowerSeriesOnBall (fun z ↦ g.evalAt (z - a))
      (FormalMultilinearSeries.ofScalars K fun n ↦ coeff n g) a g.radius := by
  have hrad := radius_eq_radius_ofScalars K g
  have h := ((FormalMultilinearSeries.ofScalars K fun n ↦ coeff n g).hasFPowerSeriesOnBall
    (hrad ▸ hg)).comp_sub a
  rw [zero_add, ← hrad] at h
  convert h using 2 with z
  exact evalAt_eq_ofScalarsSum g (z - a)

/-- If `F` agrees on the open ball of radius `r > 0` about `a` with `z ↦ g(z - a)` for a series `g`
of radius at least `r`, then `F` has the scalar power series of `g` on that ball. Values of `F` off
the ball are irrelevant. -/
theorem hasFPowerSeriesOnBall_of_forall_eq_evalAt_sub [CompleteSpace K] {a : K} {r : ℝ≥0∞}
    (hr : 0 < r) {F : K → K} {g : K⟦X⟧} (hg : r ≤ g.radius)
    (hF : ∀ z : eball a r, F z = g.evalAt ((z : K) - a)) :
    HasFPowerSeriesOnBall F (FormalMultilinearSeries.ofScalars K fun n ↦ coeff n g) a r :=
  ((hasFPowerSeriesOnBall_evalAt_sub g (hr.trans_le hg) a).mono hr hg).congr
    fun z hz ↦ (hF ⟨z, hz⟩).symm

/-- Two power series of radius at least `r > 0` that agree, as functions of `z - a`, on the open
ball of radius `r` about `a` are equal. -/
theorem eq_of_forall_evalAt_sub_eq [CompleteSpace K] {a : K} {r : ℝ≥0∞} (hr : 0 < r)
    {g₁ g₂ : K⟦X⟧} (hg₁ : r ≤ g₁.radius) (hg₂ : r ≤ g₂.radius)
    (h : ∀ z : eball a r, g₁.evalAt ((z : K) - a) = g₂.evalAt ((z : K) - a)) : g₁ = g₂ := by
  have h₁ := hasFPowerSeriesOnBall_of_forall_eq_evalAt_sub hr hg₁ (F := fun z ↦ g₁.evalAt (z - a))
    fun _ ↦ rfl
  have h₂ := hasFPowerSeriesOnBall_of_forall_eq_evalAt_sub hr hg₂ (F := fun z ↦ g₁.evalAt (z - a))
    fun z ↦ h z
  ext n
  exact congrFun ((FormalMultilinearSeries.ofScalars_series_eq_iff _ _ _).mp
    (h₁.hasFPowerSeriesAt.eq_formalMultilinearSeries h₂.hasFPowerSeriesAt)) n

/-- If `F` has the power series `P` on the open ball of radius `r` about `a`, then the series with
the coefficients of `P` has radius at least `r`. -/
theorem _root_.HasFPowerSeriesOnBall.le_radius_mk_coeff {F : K → K}
    {P : FormalMultilinearSeries K K K} {a : K} {r : ℝ≥0∞} (hF : HasFPowerSeriesOnBall F P a r) :
    r ≤ (mk P.coeff).radius := by
  rw [radius_eq_radius_of_norm_eq P fun n ↦ by simp]
  exact hF.r_le

/-- **Comparison with `HasFPowerSeriesOnBall`, converse.** If `F` has the power series `P` on the
open ball of radius `r` about `a`, then the series with the coefficients of `P` takes the value
`F z` at `z - a` for every `z` in that ball. -/
theorem _root_.HasFPowerSeriesOnBall.evalAt_mk_coeff_sub {F : K → K}
    {P : FormalMultilinearSeries K K K} {a : K} {r : ℝ≥0∞} (hF : HasFPowerSeriesOnBall F P a r)
    {z : K} (hz : z ∈ eball a r) : (mk P.coeff).evalAt (z - a) = F z := by
  have h := hF.hasSum (y := z - a) (by simpa using TauCeti.mem_eball_iff_eNorm.mp hz)
  rw [add_sub_cancel] at h
  rw [evalAt_def, ← h.tsum_eq]
  simp [mul_comm]

end PowerSeries
