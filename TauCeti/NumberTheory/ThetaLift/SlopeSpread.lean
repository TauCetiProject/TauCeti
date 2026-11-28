/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.SpecialFunctions.Log.Perspective
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The slope-spread error in the theta-chain comparison

The difference between the largest corrected maximal slope and the rank-weighted mean
of corrected slopes is bounded by comparing two words. The gains common to all words cancel;
only the original slope range, variation of the type costs and lift heights, and the source
loss remain. This gives a bound for the logarithmic term of the nearly tight frame error
at a specified slope range.

The comparison follows the slope ledger of Levent Alpöge's
`Formalism.LFunctionChainParameters.WeightedSlopeBounds.each_unit_bound_statement` in
`Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Finset

namespace TauCeti

/-- Bound the spread of the corrected slopes of the divided sources. The bounds `S`, `T`, `V`
and `L` are respectively the cross-word source slope range, the variation of type costs and
lift heights, and the uniform loss. The shift `gain` is common to every word. -/
theorem thetaChainSlopeSpread_mem_Icc {ι : Type*} {W : Finset ι}
    {d μ μMax ν νMax cost height loss : ι → ℝ} {gain S T V L : ℝ}
    (hd : ∀ i ∈ W, 0 ≤ d i) (hdpos : 0 < ∑ i ∈ W, d i)
    (hν : ∀ i ∈ W, ν i ≤ νMax i)
    (hlower : ∀ i ∈ W, μ i + gain - cost i - loss i ≤ ν i)
    (hupper : ∀ i ∈ W, νMax i ≤ μMax i + gain - cost i)
    (hsource : ∀ i ∈ W, ∀ j ∈ W, μMax i - μ j ≤ S)
    (hcost : ∀ i ∈ W, ∀ j ∈ W, cost j - cost i ≤ T)
    (hheight : ∀ i ∈ W, ∀ j ∈ W, height j - height i ≤ V)
    (hloss : ∀ i ∈ W, loss i ≤ L) :
    let hW := nonempty_of_ne_empty (s := W) (by rintro rfl; simp at hdpos)
    W.sup' hW (fun i ↦ νMax i - height i) - W.centerMass d (fun i ↦ ν i - height i) ∈
      Set.Icc 0 (S + T + V + L) := by
  intro hW
  refine ⟨sub_nonneg.mpr ((centerMass_le_sup hd hdpos).trans ?_), sub_le_iff_le_add.mpr ?_⟩
  · exact sup'_mono_fun (fun i hi ↦ sub_le_sub_right (hν i hi) _)
  · apply sup'_le
    intro i hi
    have hinf : νMax i - height i - (S + T + V + L) ≤ W.inf' hW (fun j ↦ ν j - height j) := by
      apply le_inf'
      intro j hj
      linarith only [hupper i hi, hlower j hj, hsource i hi j hj, hcost i hi j hj,
        hheight i hi j hj, hloss j hj]
    linarith only [hinf.trans (inf_le_centerMass hd hdpos)]

/-- If the slope spread is at most `U` and the frame is evaluated at range `z * b`, its error
is bounded using `log (1 + z)`. Here `D` is the inverse good-row fraction and `F` is the
combined frame defect. There is no positivity requirement on the actual spread `u` beyond
nonnegativity: at `u = 0` the logarithmic term vanishes. -/
theorem thetaChainFramePenalty_le {u U z b D F : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ U) (hz : 0 ≤ z) (hb : 0 ≤ b) (hD : 0 ≤ D) :
    D * (4 * u * Real.log (1 + (z * b) / u) + F * (z * b)) ≤
      D * 4 * Real.log (1 + z) * (U + b) + D * (F * z) * b := by
  have hUb : 0 ≤ U + b := add_nonneg (hu.trans huU) hb
  have hmon := Real.monotoneOn_mul_log_one_add_div (mul_nonneg hz hb) hu hUb
    (huU.trans (le_add_of_nonneg_right hb))
  have hratio : z * b / (U + b) ≤ z := by
    rcases hUb.eq_or_lt with h | h
    · rw [← h, div_zero]
      exact hz
    · exact (div_le_iff₀ h).mpr (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (hu.trans huU)) hz)
  have hlog := Real.log_le_log (by positivity : 0 < 1 + z * b / (U + b))
    (add_le_add_right hratio 1)
  have hbound := hmon.trans (mul_le_mul_of_nonneg_left hlog hUb)
  calc
    _ ≤ D * (4 * ((U + b) * Real.log (1 + z)) + F * (z * b)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hbound]) hD
    _ = _ := by ring

end TauCeti
