/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.Basic
public import TauCeti.Topology.Path.Separation
import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.Chord

/-!
# The sides of a crosscut

A crosscut separates two points when they lie in different connected components of the domain
after its range is removed. This file verifies the general `Path.SeparatesIn` relation on the
basic model: the real diameter of the unit disc. The two components of the cut disc are exactly
its open upper and lower half-discs.

The definition records membership in the cut domain as well as inequality of components. This
makes separation false for points on the crosscut or outside the domain. `Path.SeparatesIn` states
Pommerenke's separation condition, which null chains satisfy by `TauCeti.IsNullChain.separatesIn`.
Reversing the path does not change the relation, and ambient homeomorphisms preserve it.

The real diameter is the chord of the unit disc perpendicular to `I` (or to `-I`) at level `0`,
so its two sides are the caps of `TauCeti.connectedComponentIn_ball_sdiff_unitDiscChord`.

## Main declarations

* `TauCeti.connectedComponentIn_unitDisc_diff_realDiameter_eq_upper` -- the upper side of the
  diameter is one connected component.
* `TauCeti.connectedComponentIn_unitDisc_diff_realDiameter_eq_lower` -- the lower side is the
  other connected component.
* `TauCeti.realDiameter_separates_I_div_two_neg_I_div_two` -- a concrete nontrivial crosscut
  separation.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Chapter 2.
* C. Carathéodory, *Über die Begrenzung einfach zusammenhängender Gebiete*, Math. Ann. 73
  (1913).
-/

public section

open Metric Set Topology

namespace TauCeti

/-- The connected component of a point in the open upper half of the unit disc, after removing
the real diameter, is exactly that upper half-disc. -/
theorem connectedComponentIn_unitDisc_diff_realDiameter_eq_upper {z : ℂ}
    (hz : z ∈ ball 0 1 ∩ {w : ℂ | 0 < w.im}) :
    connectedComponentIn (ball 0 1 \ range (Path.segment (-1 : ℂ) 1)) z =
      ball 0 1 ∩ {w : ℂ | 0 < w.im} := by
  have hI : {w : ℂ | 0 < w.im} = {w | 0 < inner ℝ Complex.I w} := by ext; simp [Complex.inner]
  rw [hI] at hz ⊢
  rw [← unitDiscChord_I_zero]
  exact connectedComponentIn_ball_sdiff_unitDiscChord (by simp) hz

/-- The connected component of a point in the open lower half of the unit disc, after removing
the real diameter, is exactly that lower half-disc. -/
theorem connectedComponentIn_unitDisc_diff_realDiameter_eq_lower {z : ℂ}
    (hz : z ∈ ball 0 1 ∩ {w : ℂ | w.im < 0}) :
    connectedComponentIn (ball 0 1 \ range (Path.segment (-1 : ℂ) 1)) z =
      ball 0 1 ∩ {w : ℂ | w.im < 0} := by
  have hI : {w : ℂ | w.im < 0} = {w | 0 < inner ℝ (-Complex.I) w} := by
    ext; simp [Complex.inner]
  rw [hI] at hz ⊢
  rw [← unitDiscChord_neg_I_zero]
  exact connectedComponentIn_ball_sdiff_unitDiscChord (by simp) hz

/-- The real diameter separates `I / 2` from `-I / 2` in the unit disc. Together with
`Path.isCrosscut_segment_ball`, this is the basic nondegenerate crosscut model for the side
relation used by prime-end chains. -/
theorem realDiameter_separates_I_div_two_neg_I_div_two :
    (Path.segment (-1 : ℂ) 1).SeparatesIn (ball 0 1)
      (Complex.I / 2) (-Complex.I / 2) := by
  have hpos : Complex.I / 2 ∈ ball (0 : ℂ) 1 ∩ {w : ℂ | 0 < w.im} := by
    constructor <;> norm_num [mem_ball, Complex.norm_I]
  have hneg : -Complex.I / 2 ∈ ball (0 : ℂ) 1 ∩ {w : ℂ | w.im < 0} := by
    constructor <;> norm_num [mem_ball, Complex.norm_I]
  rw [Path.separatesIn_def]
  refine ⟨?_, ?_, ?_⟩
  · refine connectedComponentIn_nonempty_iff.mp ⟨Complex.I / 2, ?_⟩
    rw [connectedComponentIn_unitDisc_diff_realDiameter_eq_upper hpos]
    exact hpos
  · refine connectedComponentIn_nonempty_iff.mp ⟨-Complex.I / 2, ?_⟩
    rw [connectedComponentIn_unitDisc_diff_realDiameter_eq_lower hneg]
    exact hneg
  · rw [connectedComponentIn_unitDisc_diff_realDiameter_eq_upper hpos,
      connectedComponentIn_unitDisc_diff_realDiameter_eq_lower hneg]
    intro h
    have hmem : Complex.I / 2 ∈ ball (0 : ℂ) 1 ∩ {w : ℂ | w.im < 0} := h ▸ hpos
    norm_num at hmem

end TauCeti

end
