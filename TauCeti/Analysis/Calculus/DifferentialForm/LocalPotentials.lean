/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare

/-!
# Local potentials of closed one-forms

A closed `C¹` one-form with values in a complete real normed space has local potentials.
We use the flat Poincaré lemma
`StarConvex.exists_contDiffOn_forall_extDeriv_eq` on balls, and the degree-zero and degree-one
linear isometries to pass between alternating forms and functions or covectors.

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
  let oneForm : E → E [⋀^Fin 1]→L[ℝ] F := fun y ↦ ofSubsingletonLIE (0 : Fin 1) (φ y)
  have hω : ContDiffOn ℝ 1 oneForm (ball x r) :=
    (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)).contDiff.comp_contDiffOn
      (hφ.mono hrs)
  have hstar : StarConvex ℝ x (ball x r) := (convex_ball x r).starConvex (mem_ball_self hr)
  obtain ⟨α, hα, -, hdα⟩ := hstar.exists_contDiffOn_forall_extDeriv_eq
    isOpen_ball le_rfl hω (fun y hy ↦ hd y (hrs hy))
  let e := constOfIsEmptyLIE ℝ E F (Fin 0)
  let g : E → F := fun y ↦ e.symm (α y)
  have hg : ContDiffOn ℝ 1 g (ball x r) := e.symm.contDiff.comp_contDiffOn hα
  have hαg : α = fun y ↦ constOfIsEmpty ℝ E (Fin 0) (g y) := by
    funext y
    exact (e.apply_symm_apply (α y)).symm
  refine ⟨r, hr, hrs, g, hg, fun y hy ↦ ?_⟩
  have heq := hdα y hy
  rw [hαg, extDeriv_constOfIsEmpty] at heq
  have hder : fderiv ℝ g y = φ y :=
    (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)).injective heq
  rw [← hder]
  exact ((hg.differentiableOn one_ne_zero y hy).differentiableAt
    (isOpen_ball.mem_nhds hy)).hasFDerivAt

end TauCeti
