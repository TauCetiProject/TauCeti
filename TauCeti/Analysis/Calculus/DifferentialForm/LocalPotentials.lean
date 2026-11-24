/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials
public import TauCeti.Analysis.Calculus.DifferentialForm.Gradient

/-!
# Local potentials of closed one-forms

A closed `C¹` one-form with values in a complete real normed space has local potentials.
We apply the star-convex potential lemma
`StarConvex.exists_contDiffOn_forall_hasFDerivAt_of_extDeriv_eq_zero`, a consequence of the flat
Poincaré lemma `StarConvex.exists_contDiffOn_forall_extDeriv_eq`, on balls.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, the Poincaré lemma.
-/

public section

open Set Metric ContinuousAlternatingMap
open scoped ContDiff

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A closed `C¹` covector field on an open set has local potentials. Closedness is expressed
by the exterior derivative of the corresponding alternating one-form. -/
theorem hasLocalPotentials_of_extDeriv_eq_zero {s : Set E} {φ : E → E →L[ℝ] F}
    (hs : IsOpen s) (hφ : ContDiffOn ℝ 1 φ s)
    (hd : ∀ x ∈ s, extDeriv (fun y ↦ ofSubsingletonLIE (0 : Fin 1) (φ y)) x = 0) :
    HasLocalPotentials s φ := by
  rw [hasLocalPotentials_iff]
  intro x hx
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs x hx
  obtain ⟨g, hg, hgφ⟩ := ((convex_ball x r).starConvex (mem_ball_self hr))
    |>.exists_contDiffOn_forall_hasFDerivAt_of_extDeriv_eq_zero isOpen_ball le_rfl (hφ.mono hrs)
      fun y hy ↦ hd y (hrs hy)
  exact ⟨r, hr, hrs, g, hg.of_le (by norm_num), hgφ⟩

end TauCeti
