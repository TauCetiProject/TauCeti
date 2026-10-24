/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
public import TauCeti.LowDimTopology.Heegaard.Splitting

/-!
# The Heegaard surface of a splitting

A Heegaard splitting `TauCeti.HeegaardSplitting M` records its two handlebodies as subsets of `M`
meeting in the frontier of each, so for a general space `M` that frontier need not be the boundary
surface of the handlebodies. When `M` is a `3`-manifold without boundary it is: by invariance of
domain (`Homeomorph.coe_apply_mem_frontier_iff`), any homeomorphism from one handlebody of the
splitting onto the standard handlebody `TauCeti.handlebody g ⊆ ℂ × ℝ` maps the points where the
two handlebodies meet exactly onto the frontier of `TauCeti.handlebody g` in `ℂ × ℝ`, its boundary
surface of genus `g`.

This is the identification through which results about the standard handlebody and its boundary
surface, such as the computation of fundamental groups, apply to the two sides of a splitting and
to the surface along which they meet.

## Main results

* `TauCeti.HeegaardSplitting.coe_mem_right_iff`: a point of the first handlebody lies in the
  second exactly when it corresponds to a point of the frontier of the standard handlebody.
* `TauCeti.HeegaardSplitting.coe_mem_left_iff`: the same, with the two handlebodies exchanged.

## References

* M. Scharlemann, *Heegaard splittings of compact 3-manifolds*, in *Handbook of Geometric
  Topology*, North-Holland (2002), Section 2.
-/

public section

open Module

namespace TauCeti

namespace HeegaardSplitting

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M] (s : HeegaardSplitting M)

/-- The model space `ℂ × ℝ` of the standard handlebodies is three-dimensional. -/
private theorem finrank_eq_finrank_complex_prod_real (hE : finrank ℝ E = 3) :
    finrank ℝ E = finrank ℝ (ℂ × ℝ) := by
  simp [hE, finrank_prod]

/-- **The two handlebodies of a splitting of a `3`-manifold meet in their boundary surface.** In a
Heegaard splitting of a manifold without boundary charted on a three-dimensional real normed
space, a point of the first handlebody lies in the second exactly when, under a homeomorphism of
the first handlebody onto the standard one, it corresponds to a point of the frontier of the
standard handlebody in `ℂ × ℝ`. -/
theorem coe_mem_right_iff (hE : finrank ℝ E = 3) (e : s.left ≃ₜ handlebody s.genus)
    (x : s.left) : (x : M) ∈ s.right ↔ (e x : ℂ × ℝ) ∈ frontier (handlebody s.genus) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  rw [e.coe_apply_mem_frontier_iff (finrank_eq_finrank_complex_prod_real hE),
    ← s.inter_eq_frontier_left, Set.mem_inter_iff, and_iff_right x.2]

/-- **The two handlebodies of a splitting of a `3`-manifold meet in their boundary surface.** In a
Heegaard splitting of a manifold without boundary charted on a three-dimensional real normed
space, a point of the second handlebody lies in the first exactly when, under a homeomorphism of
the second handlebody onto the standard one, it corresponds to a point of the frontier of the
standard handlebody in `ℂ × ℝ`. -/
theorem coe_mem_left_iff (hE : finrank ℝ E = 3) (e : s.right ≃ₜ handlebody s.genus)
    (x : s.right) : (x : M) ∈ s.left ↔ (e x : ℂ × ℝ) ∈ frontier (handlebody s.genus) := by
  have := s.symm.coe_mem_right_iff hE
  rw [symm_left, symm_right, symm_genus] at this
  exact this e x

end HeegaardSplitting

end TauCeti
