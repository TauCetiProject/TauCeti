/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.SplitModel
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.PartialHomeomorph.Defs

/-!
# Passage of the split hyperbolic flow past the origin

The split hyperbolic flow `φ t (x, y) = (e^{-t} x, e^t y)` (`TauCeti.splitQuadraticFlow`) is the
local model of a negative-gradient flow near a nondegenerate critical point: the first coordinate
`x` is the contracting (stable) one and the second coordinate `y` the expanding (unstable) one.
This file describes how its orbits cross the box `‖x‖ ≤ ε, ‖y‖ ≤ ε` around the origin. This is
the local analysis behind both halves of the compactification of spaces of Morse trajectories:
a sequence of trajectories that converges to the stable set must break at the critical point,
and, conversely, every broken trajectory through the critical point is the limit of a one-parameter
family of unbroken ones.

The norms of the two coordinates move as `‖x(t)‖ = e^{-t} ‖x‖` and `‖y(t)‖ = e^t ‖y‖`, so their
product is constant along orbits. An orbit with `x ≠ 0` and `y ≠ 0` lies in the box exactly for
`t` between the **entry time** `log (‖x‖ / ε)` (`TauCeti.splitEntryTime`) and the **exit time**
`log (ε / ‖y‖)` (`TauCeti.splitExitTime`). Orbits enter through the *entrance face*
`‖x‖ = ε` and leave through the *exit face* `‖y‖ = ε`; an orbit on the stable set `y = 0` stays
in the box for all later times once inside, and one on the unstable set `x = 0` for all earlier
times.

The **passage map** `TauCeti.splitPassage ε` sends a point `z = (x, y)` of the entrance face off the
stable set to the point where its orbit leaves the box,

`(x, y) ↦ ((‖y‖ / ε) • x, (ε / ‖y‖) • y)`.

It is a partial homeomorphism from the entrance face minus the stable set onto the exit face minus
the unstable set, whose inverse follows each orbit back to the entrance face. It keeps the
directions of both coordinates and swaps their sizes: the norm of the contracting coordinate at the
exit is the norm `‖y‖` of the expanding coordinate at the entrance
(`TauCeti.norm_fst_splitPassage`). Hence:

* **Breaking.** If entrance points approach the stable set, their exit times tend to `+∞` and
  their exit points approach the unstable set (`TauCeti.tendsto_splitExitTime_atTop`,
  `TauCeti.tendsto_fst_splitPassage_nhds_zero`).
* **Linear λ-lemma.** For entrance points `(x r, r • y₀)` approaching the stable set along any
  family `x r` in the sphere `‖x‖ = ε` (for instance along a disc in the entrance face transverse
  to the stable set), the exit points converge to the point `(0, y₀)` of the unstable set
  (`TauCeti.tendsto_splitPassage_toLp_smul`). So the passage of a transverse disc accumulates on
  every point of the exit sphere of the unstable set.
* **Gluing.** For a point `(x₀, 0)` of the stable set on the entrance face and a point `(0, y₀)` of
  the unstable set on the exit face, the orbits that enter at `x₀` and leave at `y₀` are exactly
  those through `(x₀, r • y₀)` for `0 < r ≤ 1`; the passage sends this point to `(r • x₀, y₀)`
  (`TauCeti.splitPassage_toLp_smul`, `TauCeti.setOf_mem_splitPassage_source_eq_image`). As the
  gluing parameter `r` tends to `0`, the entrance points tend to `(x₀, 0)` and the exit points to
  `(0, y₀)`: these orbits converge to the broken orbit through those two points.

Only the norms of the two factors enter, so the statements hold for arbitrary real normed spaces;
the `L²` product norm carried by `WithLp 2` plays no role.

## Main declarations

* `TauCeti.norm_fst_mul_norm_snd_splitQuadraticFlow`: `‖x‖ ‖y‖` is a first integral.
* `TauCeti.splitEntryTime`, `TauCeti.splitExitTime`: the entry and exit times, characterized by
  `TauCeti.norm_fst_splitQuadraticFlow_le_iff` and `TauCeti.norm_snd_splitQuadraticFlow_le_iff`.
* `TauCeti.splitPassage`: the passage map from the entrance face to the exit face.
* `TauCeti.fst_splitPassage`, `TauCeti.snd_splitPassage`, `TauCeti.norm_fst_splitPassage`: its
  explicit form, and `TauCeti.fst_splitPassage_symm`, `TauCeti.snd_splitPassage_symm`,
  `TauCeti.norm_snd_splitPassage_symm`: that of its inverse.
* `TauCeti.tendsto_splitExitTime_atTop`, `TauCeti.tendsto_fst_splitPassage_nhds_zero`: breaking.
* `TauCeti.tendsto_splitPassage_toLp_smul`: the linear λ-lemma.
* `TauCeti.toLp_smul_mem_splitPassage_source`, `TauCeti.splitPassage_toLp_smul`,
  `TauCeti.splitPassage_symm_toLp_smul`, `TauCeti.setOf_mem_splitPassage_source_eq_image`: gluing.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness and gluing of spaces of trajectories, via the flow near a critical point
  in which a pseudo-gradient is linear).
* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 2
  (the λ-lemma).
-/

public section

open Filter Set Topology

noncomputable section

namespace TauCeti

section Time

variable {Eₛ Eᵤ : Type*} {ε : ℝ} {z : WithLp 2 (Eₛ × Eᵤ)}

/-- The **entry time** of `z` into the box `‖x‖ ≤ ε, ‖y‖ ≤ ε`: when `z.fst ≠ 0` and `ε > 0`, the
time at which the first coordinate of its orbit has norm `ε`. Before it, the orbit lies outside the
box (`TauCeti.norm_fst_splitQuadraticFlow_le_iff`). -/
def splitEntryTime [Norm Eₛ] (ε : ℝ) (z : WithLp 2 (Eₛ × Eᵤ)) : ℝ :=
  Real.log (‖z.fst‖ / ε)

/-- The **exit time** of `z` from the box `‖x‖ ≤ ε, ‖y‖ ≤ ε`: when `z.snd ≠ 0` and `ε > 0`, the
time at which the second coordinate of its orbit has norm `ε`. After it, the orbit lies outside the
box (`TauCeti.norm_snd_splitQuadraticFlow_le_iff`). -/
def splitExitTime [Norm Eᵤ] (ε : ℝ) (z : WithLp 2 (Eₛ × Eᵤ)) : ℝ :=
  Real.log (ε / ‖z.snd‖)

theorem splitEntryTime_def [Norm Eₛ] (ε : ℝ) (z : WithLp 2 (Eₛ × Eᵤ)) :
    splitEntryTime ε z = Real.log (‖z.fst‖ / ε) :=
  (rfl)

theorem splitExitTime_def [Norm Eᵤ] (ε : ℝ) (z : WithLp 2 (Eₛ × Eᵤ)) :
    splitExitTime ε z = Real.log (ε / ‖z.snd‖) :=
  (rfl)

/-- A point of the entrance face `‖x‖ = ε` has entry time zero. -/
theorem splitEntryTime_eq_zero [Norm Eₛ] (hε : ε ≠ 0) (hz : ‖z.fst‖ = ε) :
    splitEntryTime ε z = 0 := by
  rw [splitEntryTime, hz, div_self hε, Real.log_one]

/-- A point of the exit face `‖y‖ = ε` has exit time zero. -/
theorem splitExitTime_eq_zero [Norm Eᵤ] (hε : ε ≠ 0) (hz : ‖z.snd‖ = ε) :
    splitExitTime ε z = 0 := by
  rw [splitExitTime, hz, div_self hε, Real.log_one]

/-- The exit time is nonnegative for a point whose second coordinate is nonzero and lies in the
closed ball of radius `ε`. -/
theorem splitExitTime_nonneg [NormedAddCommGroup Eᵤ] (hz : z.snd ≠ 0) (hzε : ‖z.snd‖ ≤ ε) :
    0 ≤ splitExitTime ε z :=
  Real.log_nonneg ((one_le_div (norm_pos_iff.2 hz)).2 hzε)

/-- **Long passages near the stable set.** If points approach the stable set `y = 0` from outside
it, their exit times tend to `+∞`. -/
theorem tendsto_splitExitTime_atTop [NormedAddCommGroup Eᵤ] {ι : Type*} {l : Filter ι}
    {z : ι → WithLp 2 (Eₛ × Eᵤ)} (hε : 0 < ε) (hz : ∀ᶠ i in l, (z i).snd ≠ 0)
    (hlim : Tendsto (fun i ↦ (z i).snd) l (𝓝 0)) :
    Tendsto (fun i ↦ splitExitTime ε (z i)) l atTop := by
  have hnorm : Tendsto (fun i ↦ ‖(z i).snd‖) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using hlim.norm,
      hz.mono fun i hi ↦ mem_Ioi.2 (norm_pos_iff.2 hi)⟩
  exact Real.tendsto_log_atTop.comp
    ((hnorm.inv_tendsto_nhdsGT_zero.const_mul_atTop hε).congr fun i ↦ (div_eq_mul_inv _ _).symm)

end Time

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [NormedSpace ℝ Eₛ]
  [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ] {ε t : ℝ} {z : WithLp 2 (Eₛ × Eᵤ)}

/-! ### Norms along an orbit -/

/-- The flow contracts the norm of the first coordinate by the factor `e^{-t}`. -/
theorem norm_fst_splitQuadraticFlow (t : ℝ) (z : WithLp 2 (Eₛ × Eᵤ)) :
    ‖(splitQuadraticFlow t z).fst‖ = Real.exp (-t) * ‖z.fst‖ := by
  simp [norm_smul]

/-- The flow expands the norm of the second coordinate by the factor `e^t`. -/
theorem norm_snd_splitQuadraticFlow (t : ℝ) (z : WithLp 2 (Eₛ × Eᵤ)) :
    ‖(splitQuadraticFlow t z).snd‖ = Real.exp t * ‖z.snd‖ := by
  simp [norm_smul]

/-- The product `‖x‖ ‖y‖` of the norms of the two coordinates is a first integral of the flow:
every orbit lies on one of the hyperbolas `‖x‖ ‖y‖ = c`. -/
theorem norm_fst_mul_norm_snd_splitQuadraticFlow (t : ℝ) (z : WithLp 2 (Eₛ × Eᵤ)) :
    ‖(splitQuadraticFlow t z).fst‖ * ‖(splitQuadraticFlow t z).snd‖ = ‖z.fst‖ * ‖z.snd‖ := by
  rw [norm_fst_splitQuadraticFlow, norm_snd_splitQuadraticFlow, Real.exp_neg]
  field_simp

/-! ### Entry and exit along an orbit -/

/-- The first coordinate of the orbit of `z` has norm at most `ε` exactly from the entry time on. -/
theorem norm_fst_splitQuadraticFlow_le_iff (hε : 0 < ε) (hz : z.fst ≠ 0) :
    ‖(splitQuadraticFlow t z).fst‖ ≤ ε ↔ splitEntryTime ε z ≤ t := by
  rw [norm_fst_splitQuadraticFlow, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos t), splitEntryTime,
    Real.log_le_iff_le_exp (div_pos (norm_pos_iff.2 hz) hε), div_le_iff₀ hε, mul_comm]

/-- The second coordinate of the orbit of `z` has norm at most `ε` exactly up to the exit time. -/
theorem norm_snd_splitQuadraticFlow_le_iff (hε : 0 < ε) (hz : z.snd ≠ 0) :
    ‖(splitQuadraticFlow t z).snd‖ ≤ ε ↔ t ≤ splitExitTime ε z := by
  rw [norm_snd_splitQuadraticFlow, ← le_div_iff₀ (norm_pos_iff.2 hz), splitExitTime,
    Real.le_log_iff_exp_le (div_pos hε (norm_pos_iff.2 hz))]

/-- Flowing for time `t` moves the entry time back by `t`. -/
theorem splitEntryTime_splitQuadraticFlow (hε : ε ≠ 0) (hz : z.fst ≠ 0) (t : ℝ) :
    splitEntryTime ε (splitQuadraticFlow t z) = splitEntryTime ε z - t := by
  have := norm_ne_zero_iff.2 hz
  simp only [splitEntryTime, norm_fst_splitQuadraticFlow, mul_div_assoc]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
  ring

/-- Flowing for time `t` moves the exit time back by `t`. -/
theorem splitExitTime_splitQuadraticFlow (hε : ε ≠ 0) (hz : z.snd ≠ 0) (t : ℝ) :
    splitExitTime ε (splitQuadraticFlow t z) = splitExitTime ε z - t := by
  have := norm_ne_zero_iff.2 hz
  simp only [splitExitTime, norm_snd_splitQuadraticFlow, div_mul_eq_div_div_swap]
  rw [Real.log_div (by positivity) (by positivity), Real.log_exp]

/-- The point of the orbit of `z` at its exit time, in coordinates. -/
theorem splitQuadraticFlow_splitExitTime (hε : 0 < ε) (hz : z.snd ≠ 0) :
    splitQuadraticFlow (splitExitTime ε z) z =
      WithLp.toLp 2 ((‖z.snd‖ / ε) • z.fst, (ε / ‖z.snd‖) • z.snd) := by
  rw [splitQuadraticFlow_apply, splitExitTime, Real.exp_neg,
    Real.exp_log (div_pos hε (norm_pos_iff.2 hz)), inv_div]

/-- The point of the orbit of `z` at its entry time, in coordinates. -/
theorem splitQuadraticFlow_splitEntryTime (hε : 0 < ε) (hz : z.fst ≠ 0) :
    splitQuadraticFlow (splitEntryTime ε z) z =
      WithLp.toLp 2 ((ε / ‖z.fst‖) • z.fst, (‖z.fst‖ / ε) • z.snd) := by
  rw [splitQuadraticFlow_apply, splitEntryTime, Real.exp_neg,
    Real.exp_log (div_pos (norm_pos_iff.2 hz) hε), inv_div]

/-- At the exit time, the second coordinate of the orbit has norm `ε`. -/
theorem norm_snd_splitQuadraticFlow_splitExitTime (hε : 0 < ε) (hz : z.snd ≠ 0) :
    ‖(splitQuadraticFlow (splitExitTime ε z) z).snd‖ = ε := by
  have := norm_pos_iff.2 hz
  rw [norm_snd_splitQuadraticFlow, splitExitTime, Real.exp_log (by positivity)]
  field_simp

/-- At the exit time, the first coordinate of the orbit has norm `‖x‖ ‖y‖ / ε`. -/
theorem norm_fst_splitQuadraticFlow_splitExitTime (hε : 0 < ε) (hz : z.snd ≠ 0) :
    ‖(splitQuadraticFlow (splitExitTime ε z) z).fst‖ = ‖z.fst‖ * ‖z.snd‖ / ε := by
  have h := norm_fst_mul_norm_snd_splitQuadraticFlow (splitExitTime ε z) z
  rw [norm_snd_splitQuadraticFlow_splitExitTime hε hz] at h
  rw [eq_div_iff hε.ne', h]

/-- At the entry time, the first coordinate of the orbit has norm `ε`. -/
theorem norm_fst_splitQuadraticFlow_splitEntryTime (hε : 0 < ε) (hz : z.fst ≠ 0) :
    ‖(splitQuadraticFlow (splitEntryTime ε z) z).fst‖ = ε := by
  have := norm_pos_iff.2 hz
  rw [norm_fst_splitQuadraticFlow, splitEntryTime, Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

/-- At the entry time, the second coordinate of the orbit has norm `‖x‖ ‖y‖ / ε`. -/
theorem norm_snd_splitQuadraticFlow_splitEntryTime (hε : 0 < ε) (hz : z.fst ≠ 0) :
    ‖(splitQuadraticFlow (splitEntryTime ε z) z).snd‖ = ‖z.fst‖ * ‖z.snd‖ / ε := by
  have h := norm_fst_mul_norm_snd_splitQuadraticFlow (splitEntryTime ε z) z
  rw [norm_fst_splitQuadraticFlow_splitEntryTime hε hz] at h
  rw [eq_div_iff hε.ne', mul_comm, h]

/-! ### The passage map -/

omit [NormedSpace ℝ Eₛ] [NormedSpace ℝ Eᵤ] in
/-- A point of the entrance face off the stable set forces `0 < ε` and `x ≠ 0`. -/
private theorem pos_and_fst_ne_zero_of_entrance (hz : ‖z.fst‖ = ε ∧ z.snd ≠ 0 ∧ ‖z.snd‖ ≤ ε) :
    0 < ε ∧ z.fst ≠ 0 :=
  have hε := (norm_pos_iff.2 hz.2.1).trans_le hz.2.2
  ⟨hε, norm_ne_zero_iff.1 (hz.1 ▸ hε.ne')⟩

omit [NormedSpace ℝ Eₛ] [NormedSpace ℝ Eᵤ] in
/-- A point of the exit face off the unstable set forces `0 < ε` and `y ≠ 0`. -/
private theorem pos_and_snd_ne_zero_of_exit (hz : ‖z.snd‖ = ε ∧ z.fst ≠ 0 ∧ ‖z.fst‖ ≤ ε) :
    0 < ε ∧ z.snd ≠ 0 :=
  have hε := (norm_pos_iff.2 hz.2.1).trans_le hz.2.2
  ⟨hε, norm_ne_zero_iff.1 (hz.1 ▸ hε.ne')⟩

/-- The **passage map** of the split hyperbolic flow through the box `‖x‖ ≤ ε, ‖y‖ ≤ ε`. Its
source is the entrance face `‖x‖ = ε, ‖y‖ ≤ ε` minus the stable set `y = 0`, its target is the
exit face `‖y‖ = ε, ‖x‖ ≤ ε` minus the unstable set `x = 0`, and it sends a point to the point where
its orbit leaves the box, reached at the exit time. The inverse follows the orbit backwards to the
entry time. -/
def splitPassage (ε : ℝ) :
    PartialHomeomorph (WithLp 2 (Eₛ × Eᵤ)) (WithLp 2 (Eₛ × Eᵤ)) where
  toFun z := splitQuadraticFlow (splitExitTime ε z) z
  invFun z := splitQuadraticFlow (splitEntryTime ε z) z
  source := {z | ‖z.fst‖ = ε ∧ z.snd ≠ 0 ∧ ‖z.snd‖ ≤ ε}
  target := {z | ‖z.snd‖ = ε ∧ z.fst ≠ 0 ∧ ‖z.fst‖ ≤ ε}
  map_source' := by
    rintro z hz
    obtain ⟨hε, hx0⟩ := pos_and_fst_ne_zero_of_entrance hz
    obtain ⟨hx, hy, hyε⟩ := hz
    refine ⟨norm_snd_splitQuadraticFlow_splitExitTime hε hy, by simp [hx0], ?_⟩
    rw [norm_fst_splitQuadraticFlow_splitExitTime hε hy, hx, mul_div_cancel_left₀ _ hε.ne']
    exact hyε
  map_target' := by
    rintro z hz
    obtain ⟨hε, hy0⟩ := pos_and_snd_ne_zero_of_exit hz
    obtain ⟨hy, hx, hxε⟩ := hz
    refine ⟨norm_fst_splitQuadraticFlow_splitEntryTime hε hx, by simp [hy0], ?_⟩
    rw [norm_snd_splitQuadraticFlow_splitEntryTime hε hx, hy, mul_div_cancel_right₀ _ hε.ne']
    exact hxε
  left_inv' := by
    rintro z hz
    obtain ⟨hε, hx0⟩ := pos_and_fst_ne_zero_of_entrance hz
    rw [splitEntryTime_splitQuadraticFlow hε.ne' hx0, ← Flow.map_add, sub_add_cancel,
      splitEntryTime_eq_zero hε.ne' hz.1, Flow.map_zero_apply]
  right_inv' := by
    rintro z hz
    obtain ⟨hε, hy0⟩ := pos_and_snd_ne_zero_of_exit hz
    rw [splitExitTime_splitQuadraticFlow hε.ne' hy0, ← Flow.map_add, sub_add_cancel,
      splitExitTime_eq_zero hε.ne' hz.1, Flow.map_zero_apply]
  continuousOn_toFun := by
    refine splitQuadraticFlow.cont'.comp_continuousOn (ContinuousOn.prodMk ?_ continuousOn_id)
    refine ContinuousOn.log (continuousOn_const.div ?_ ?_) ?_
    · exact (continuous_norm.comp (WithLp.sndL 2 ℝ Eₛ Eᵤ).continuous).continuousOn
    · rintro z ⟨-, hy, -⟩
      exact norm_ne_zero_iff.2 hy
    · rintro z hz
      exact (div_pos (pos_and_fst_ne_zero_of_entrance hz).1 (norm_pos_iff.2 hz.2.1)).ne'
  continuousOn_invFun := by
    refine splitQuadraticFlow.cont'.comp_continuousOn (ContinuousOn.prodMk ?_ continuousOn_id)
    refine ContinuousOn.log
      ((continuous_norm.comp (WithLp.fstL 2 ℝ Eₛ Eᵤ).continuous).continuousOn.div
        continuousOn_const ?_) ?_
    · rintro z hz
      exact (pos_and_snd_ne_zero_of_exit hz).1.ne'
    · rintro z hz
      exact (div_pos (norm_pos_iff.2 hz.2.1) (pos_and_snd_ne_zero_of_exit hz).1).ne'

@[simp]
theorem splitPassage_apply (ε : ℝ) (z : WithLp 2 (Eₛ × Eᵤ)) :
    splitPassage ε z = splitQuadraticFlow (splitExitTime ε z) z :=
  (rfl)

@[simp]
theorem splitPassage_symm_apply (ε : ℝ) (z : WithLp 2 (Eₛ × Eᵤ)) :
    (splitPassage ε).symm z = splitQuadraticFlow (splitEntryTime ε z) z :=
  (rfl)

@[simp]
theorem mem_splitPassage_source :
    z ∈ (splitPassage ε).source ↔ ‖z.fst‖ = ε ∧ z.snd ≠ 0 ∧ ‖z.snd‖ ≤ ε :=
  Iff.rfl

@[simp]
theorem mem_splitPassage_target :
    z ∈ (splitPassage ε).target ↔ ‖z.snd‖ = ε ∧ z.fst ≠ 0 ∧ ‖z.fst‖ ≤ ε :=
  Iff.rfl

/-- The radius is positive as soon as the passage has a point to act on. -/
theorem pos_of_mem_splitPassage_source (hz : z ∈ (splitPassage ε).source) : 0 < ε :=
  (pos_and_fst_ne_zero_of_entrance hz).1

/-- The radius is positive as soon as the inverse passage has a point to act on. -/
theorem pos_of_mem_splitPassage_target (hz : z ∈ (splitPassage ε).target) : 0 < ε :=
  (pos_and_snd_ne_zero_of_exit hz).1

/-- The passage scales the first coordinate by `‖y‖ / ε`. -/
theorem fst_splitPassage (hz : z ∈ (splitPassage ε).source) :
    (splitPassage ε z).fst = (‖z.snd‖ / ε) • z.fst := by
  rw [splitPassage_apply, splitQuadraticFlow_splitExitTime (pos_of_mem_splitPassage_source hz)
    hz.2.1]
  simp

/-- The passage scales the second coordinate by `ε / ‖y‖`. -/
theorem snd_splitPassage (hz : z ∈ (splitPassage ε).source) :
    (splitPassage ε z).snd = (ε / ‖z.snd‖) • z.snd := by
  rw [splitPassage_apply, splitQuadraticFlow_splitExitTime (pos_of_mem_splitPassage_source hz)
    hz.2.1]
  simp

/-- **The passage swaps the sizes of the two coordinates.** At the exit, the first coordinate has
the norm that the second coordinate had at the entrance. Thus the exit point lies within distance
`‖y‖` of the unstable set `x = 0`. -/
theorem norm_fst_splitPassage (hz : z ∈ (splitPassage ε).source) :
    ‖(splitPassage ε z).fst‖ = ‖z.snd‖ := by
  have hε := pos_of_mem_splitPassage_source hz
  rw [splitPassage_apply, norm_fst_splitQuadraticFlow_splitExitTime hε hz.2.1, hz.1,
    mul_div_cancel_left₀ _ hε.ne']

/-- The inverse passage scales the first coordinate by `ε / ‖x‖`. -/
theorem fst_splitPassage_symm (hz : z ∈ (splitPassage ε).target) :
    ((splitPassage ε).symm z).fst = (ε / ‖z.fst‖) • z.fst := by
  rw [splitPassage_symm_apply,
    splitQuadraticFlow_splitEntryTime (pos_of_mem_splitPassage_target hz) hz.2.1]
  simp

/-- The inverse passage scales the second coordinate by `‖x‖ / ε`. -/
theorem snd_splitPassage_symm (hz : z ∈ (splitPassage ε).target) :
    ((splitPassage ε).symm z).snd = (‖z.fst‖ / ε) • z.snd := by
  rw [splitPassage_symm_apply,
    splitQuadraticFlow_splitEntryTime (pos_of_mem_splitPassage_target hz) hz.2.1]
  simp

/-- The inverse passage also swaps the sizes of the two coordinates: at the entrance, the second
coordinate has the norm that the first coordinate had at the exit. -/
theorem norm_snd_splitPassage_symm (hz : z ∈ (splitPassage ε).target) :
    ‖((splitPassage ε).symm z).snd‖ = ‖z.fst‖ := by
  have hε := pos_of_mem_splitPassage_target hz
  rw [splitPassage_symm_apply, norm_snd_splitQuadraticFlow_splitEntryTime hε hz.2.1, hz.1,
    mul_div_cancel_right₀ _ hε.ne']

/-- For a point of the entrance face, the orbit lies in the box `‖x‖ ≤ ε, ‖y‖ ≤ ε` exactly between
time `0` and the exit time. -/
theorem norm_fst_le_and_norm_snd_le_iff_of_mem_splitPassage_source
    (hz : z ∈ (splitPassage ε).source) :
    ‖(splitQuadraticFlow t z).fst‖ ≤ ε ∧ ‖(splitQuadraticFlow t z).snd‖ ≤ ε ↔
      t ∈ Icc 0 (splitExitTime ε z) := by
  obtain ⟨hε, hx⟩ := pos_and_fst_ne_zero_of_entrance hz
  rw [norm_fst_splitQuadraticFlow_le_iff hε hx, norm_snd_splitQuadraticFlow_le_iff hε hz.2.1,
    splitEntryTime_eq_zero hε.ne' hz.1, mem_Icc]

/-! ### Breaking, gluing, and the linear λ-lemma -/

/-- **Breaking.** If points of the entrance face approach the stable set `y = 0`, their exit points
approach the unstable set `x = 0`. -/
theorem tendsto_fst_splitPassage_nhds_zero {ι : Type*} {l : Filter ι}
    {z : ι → WithLp 2 (Eₛ × Eᵤ)} (hz : ∀ᶠ i in l, z i ∈ (splitPassage ε).source)
    (hlim : Tendsto (fun i ↦ (z i).snd) l (𝓝 0)) :
    Tendsto (fun i ↦ (splitPassage ε (z i)).fst) l (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  refine (tendsto_zero_iff_norm_tendsto_zero.1 hlim).congr' ?_
  filter_upwards [hz] with i hi
  exact (norm_fst_splitPassage hi).symm

/-- For `x₀` and `y₀` of norm `ε > 0` and `0 < r ≤ 1`, the point `(x₀, r • y₀)` lies on the
entrance face off the stable set. -/
theorem toLp_smul_mem_splitPassage_source {x₀ : Eₛ} {y₀ : Eᵤ} (hx₀ : ‖x₀‖ = ε) (hy₀ : ‖y₀‖ = ε)
    (hε : 0 < ε) {r : ℝ} (hr : r ∈ Ioc 0 1) :
    WithLp.toLp 2 (x₀, r • y₀) ∈ (splitPassage ε).source := by
  have hy₀0 : y₀ ≠ 0 := norm_ne_zero_iff.1 (hy₀ ▸ hε.ne')
  refine ⟨hx₀, smul_ne_zero hr.1.ne' hy₀0, ?_⟩
  rw [WithLp.snd, WithLp.ofLp_toLp, norm_smul, Real.norm_of_nonneg hr.1.le, hy₀]
  exact mul_le_of_le_one_left hε.le hr.2

/-- **The glued points.** For `y₀` of norm `ε > 0` and `0 < r`, the passage map carries
`(x₀, r • y₀)` to `(r • x₀, y₀)`. -/
theorem splitPassage_toLp_smul (x₀ : Eₛ) {y₀ : Eᵤ} (hy₀ : ‖y₀‖ = ε) (hε : 0 < ε) {r : ℝ}
    (hr : 0 < r) :
    splitPassage ε (WithLp.toLp 2 (x₀, r • y₀)) = WithLp.toLp 2 (r • x₀, y₀) := by
  have hy₀0 : (WithLp.toLp 2 (x₀, r • y₀)).snd ≠ 0 :=
    smul_ne_zero hr.ne' (norm_ne_zero_iff.1 (hy₀ ▸ hε.ne'))
  have hnorm : ‖r • y₀‖ = r * ε := by
    rw [norm_smul, Real.norm_of_nonneg hr.le, hy₀]
  have h₁ : r * ε / ε = r := mul_div_cancel_right₀ _ hε.ne'
  have h₂ : ε / (r * ε) * r = 1 := by field_simp [hr.ne', hε.ne']
  rw [splitPassage_apply, splitQuadraticFlow_splitExitTime hε hy₀0]
  simp [hnorm, smul_smul, h₁, h₂]

/-- **The glued points, backwards.** For `x₀` of norm `ε > 0` and `0 < r`, the inverse passage
carries `(r • x₀, y₀)` to `(x₀, r • y₀)`. -/
theorem splitPassage_symm_toLp_smul {x₀ : Eₛ} (y₀ : Eᵤ) (hx₀ : ‖x₀‖ = ε) (hε : 0 < ε) {r : ℝ}
    (hr : 0 < r) :
    (splitPassage ε).symm (WithLp.toLp 2 (r • x₀, y₀)) = WithLp.toLp 2 (x₀, r • y₀) := by
  have hx₀0 : (WithLp.toLp 2 (r • x₀, y₀)).fst ≠ 0 :=
    smul_ne_zero hr.ne' (norm_ne_zero_iff.1 (hx₀ ▸ hε.ne'))
  have hnorm : ‖r • x₀‖ = r * ε := by
    rw [norm_smul, Real.norm_of_nonneg hr.le, hx₀]
  have h₁ : r * ε / ε = r := mul_div_cancel_right₀ _ hε.ne'
  have h₂ : ε / (r * ε) * r = 1 := by field_simp [hr.ne', hε.ne']
  rw [splitPassage_symm_apply, splitQuadraticFlow_splitEntryTime hε hx₀0]
  simp [hnorm, smul_smul, h₁, h₂]

/-- **Gluing.** For `x₀` and `y₀` of norm `ε`, the points of the entrance face with first
coordinate `x₀` whose passage has second coordinate `y₀` are exactly the points `(x₀, r • y₀)` with
`0 < r ≤ 1`. So the orbits entering with first coordinate exactly `x₀` and leaving with second
coordinate exactly `y₀` form a single family indexed by the gluing parameter `r`. -/
theorem setOf_mem_splitPassage_source_eq_image {x₀ : Eₛ} {y₀ : Eᵤ} (hx₀ : ‖x₀‖ = ε) (hy₀ : ‖y₀‖ = ε)
    (hε : 0 < ε) :
    {z | z ∈ (splitPassage ε).source ∧ z.fst = x₀ ∧ (splitPassage ε z).snd = y₀} =
      (fun r : ℝ ↦ WithLp.toLp 2 (x₀, r • y₀)) '' Ioc 0 1 := by
  ext z
  constructor
  · rintro ⟨hz, hzx, hzy⟩
    have hb : 0 < ‖z.snd‖ := norm_pos_iff.2 hz.2.1
    refine ⟨‖z.snd‖ / ε, ⟨div_pos hb hε, (div_le_one hε).2 hz.2.2⟩, ?_⟩
    rw [snd_splitPassage hz] at hzy
    have hc : ‖z.snd‖ / ε * (ε / ‖z.snd‖) = 1 := by field_simp
    have hzsnd : (‖z.snd‖ / ε) • y₀ = z.snd := by
      rw [← hzy, smul_smul, hc, one_smul]
    apply WithLp.ofLp_injective
    ext
    · simpa using hzx.symm
    · simpa using hzsnd
  · rintro ⟨r, hr, rfl⟩
    refine ⟨toLp_smul_mem_splitPassage_source hx₀ hy₀ hε hr, rfl, ?_⟩
    simp [splitPassage_toLp_smul x₀ hy₀ hε hr.1]

/-- **The linear λ-lemma.** Let `x r` be points of norm `ε` in the first factor, for instance the
first coordinates `g (r • y₀)` of a disc `y ↦ (g y, y)` in the entrance face transverse to the
stable set. As `r → 0⁺`, the points `(x r, r • y₀)` approach the stable set, and their exit points
converge to the point `(0, y₀)` of the unstable set. -/
theorem tendsto_splitPassage_toLp_smul {x : ℝ → Eₛ} {y₀ : Eᵤ}
    (hx : ∀ᶠ r in 𝓝[>] 0, ‖x r‖ = ε) (hy₀ : ‖y₀‖ = ε) (hε : 0 < ε) :
    Tendsto (fun r ↦ splitPassage ε (WithLp.toLp 2 (x r, r • y₀))) (𝓝[>] 0)
      (𝓝 (WithLp.toLp 2 (0, y₀))) := by
  have hpass : (fun r ↦ WithLp.toLp 2 (r • x r, y₀)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun r ↦ splitPassage ε (WithLp.toLp 2 (x r, r • y₀)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (splitPassage_toLp_smul (x r) hy₀ hε hr).symm
  refine Tendsto.congr' hpass ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).continuousAt.tendsto.comp
    (Tendsto.prodMk_nhds ?_ tendsto_const_nhds))
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  have h : Tendsto (fun r : ℝ ↦ r * ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const ε)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hx] with r hr hxr
  rw [norm_smul, Real.norm_of_nonneg (le_of_lt hr), hxr]

end TauCeti
