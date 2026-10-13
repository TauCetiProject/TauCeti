/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.Basic
public import TauCeti.Topology.Path.Separation
import Mathlib.Analysis.Complex.Convex
import TauCeti.Topology.ConnectedComponents

/-!
# The sides of a crosscut

A crosscut separates two points when they lie in different connected components of the domain
after its range is removed. This file verifies the general `Path.SeparatesIn` relation on the
basic model: the real diameter of the unit disc. The two components of the cut disc are exactly
its open upper and lower half-discs.

The definition records membership in the cut domain as well as inequality of components. This
makes separation false for points on the crosscut or outside the domain and gives a stable API for
null chains of crosscuts, whose nesting condition compares the sides selected by successive
crosscuts. Reversing the path does not change the relation, and ambient homeomorphisms preserve it.

For the model diameter, the proof uses only convexity and the intermediate value theorem. Each
open half-disc is convex. Conversely, a connected subset of the cut disc cannot meet both signs of
the imaginary coordinate, since it would then meet the removed diameter.

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

private lemma mem_range_realDiameter_of_mem_unitDisc_of_im_eq_zero {z : ℂ}
    (hz : z ∈ ball 0 1) (hzim : z.im = 0) :
    z ∈ range (Path.segment (-1 : ℂ) 1) := by
  have hre_lower : -1 < z.re := by
    have habs : |z.re| < 1 := (Complex.abs_re_le_norm z).trans_lt (by simpa using hz)
    exact (abs_lt.mp habs).1
  have hre_upper : z.re < 1 := by
    have habs : |z.re| < 1 := (Complex.abs_re_le_norm z).trans_lt (by simpa using hz)
    exact (abs_lt.mp habs).2
  let t : unitInterval := ⟨(z.re + 1) / 2, by constructor <;> linarith⟩
  refine ⟨t, ?_⟩
  apply Complex.ext
  · simp [t, Path.segment_apply, AffineMap.lineMap_apply_module]
    ring
  · simp [hzim, Path.segment_apply, AffineMap.lineMap_apply_module]

private lemma range_realDiameter_im_eq_zero {z : ℂ}
    (hz : z ∈ range (Path.segment (-1 : ℂ) 1)) : z.im = 0 := by
  obtain ⟨t, rfl⟩ := hz
  simp [Path.segment_apply, AffineMap.lineMap_apply_module]

/-- The connected component of a point in the open upper half of the unit disc, after removing
the real diameter, is exactly that upper half-disc. -/
theorem connectedComponentIn_unitDisc_diff_realDiameter_eq_upper {z : ℂ}
    (hz : z ∈ ball 0 1 ∩ {w : ℂ | 0 < w.im}) :
    connectedComponentIn (ball 0 1 \ range (Path.segment (-1 : ℂ) 1)) z =
      ball 0 1 ∩ {w : ℂ | 0 < w.im} := by
  let D := ball (0 : ℂ) 1 \ range (Path.segment (-1 : ℂ) 1)
  let H := ball (0 : ℂ) 1 ∩ {w : ℂ | 0 < w.im}
  have hHD : H ⊆ D := by
    rintro q ⟨hqball, hqim⟩
    have hqim' : 0 < q.im := hqim
    refine ⟨hqball, fun hqrange => ?_⟩
    exact (ne_of_gt hqim') (range_realDiameter_im_eq_zero hqrange)
  apply connectedComponentIn_eq_of_lt
      ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_im_gt 0)).isPreconnected hHD hz hz.2
      Complex.continuous_im.continuousOn
  · intro q hq hqim
    exact hq.2 (mem_range_realDiameter_of_mem_unitDisc_of_im_eq_zero hq.1 hqim)
  · intro q hq hqim
    exact ⟨hq.1, hqim⟩

/-- The connected component of a point in the open lower half of the unit disc, after removing
the real diameter, is exactly that lower half-disc. -/
theorem connectedComponentIn_unitDisc_diff_realDiameter_eq_lower {z : ℂ}
    (hz : z ∈ ball 0 1 ∩ {w : ℂ | w.im < 0}) :
    connectedComponentIn (ball 0 1 \ range (Path.segment (-1 : ℂ) 1)) z =
      ball 0 1 ∩ {w : ℂ | w.im < 0} := by
  let D := ball (0 : ℂ) 1 \ range (Path.segment (-1 : ℂ) 1)
  let H := ball (0 : ℂ) 1 ∩ {w : ℂ | w.im < 0}
  have hHD : H ⊆ D := by
    rintro q ⟨hqball, hqim⟩
    have hqim' : q.im < 0 := hqim
    refine ⟨hqball, fun hqrange => ?_⟩
    exact (ne_of_lt hqim') (range_realDiameter_im_eq_zero hqrange)
  apply connectedComponentIn_eq_of_lt (φ := fun w : ℂ ↦ -w.im)
      ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_im_lt 0)).isPreconnected hHD hz
      (neg_pos.mpr hz.2) Complex.continuous_im.neg.continuousOn
  · intro q hq hqim
    apply hq.2
    apply mem_range_realDiameter_of_mem_unitDisc_of_im_eq_zero hq.1
    simpa using hqim
  · intro q hq hqim
    refine ⟨hq.1, ?_⟩
    simpa using hqim

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
  · refine ⟨hpos.1, fun h => ?_⟩
    have hposim : 0 < (Complex.I / 2).im := hpos.2
    exact (ne_of_gt hposim) (range_realDiameter_im_eq_zero h)
  · refine ⟨hneg.1, fun h => ?_⟩
    have hnegim : (-Complex.I / 2).im < 0 := hneg.2
    exact (ne_of_lt hnegim) (range_realDiameter_im_eq_zero h)
  · rw [connectedComponentIn_unitDisc_diff_realDiameter_eq_upper hpos,
      connectedComponentIn_unitDisc_diff_realDiameter_eq_lower hneg]
    intro h
    have hmem : Complex.I / 2 ∈ ball (0 : ℂ) 1 ∩ {w : ℂ | w.im < 0} := h ▸ hpos
    norm_num at hmem

end TauCeti

end
