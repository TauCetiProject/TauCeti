/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.Geometry.Euclidean.PolarGraph.Basic

/-!
# The polar cover of the punctured plane

The positive radius and unrestricted angle form a contractible cover of the nonzero complex
numbers. A homeomorphism with the complex plane identifies the polar projection with complex
exponentiation, so the covering property follows from the exponential covering map.
-/

public noncomputable section

namespace TauCeti.PolarGraph

/-- Logarithmic radius and angle identify the total space with `ℂ` via `log r + iθ`. -/
def polarPointHomeomorphComplex : PolarPoint ≃ₜ ℂ where
  toFun p := ⟨Real.log (radius p), angle p⟩
  invFun z := ⟨(Real.exp z.re, z.im), Real.exp_pos _⟩
  left_inv p := by
    apply PolarPoint.ext
    · simpa only [radius_def] using Real.exp_log (radius_pos p)
    · simp only [angle_def]
  right_inv z := by
    apply Complex.ext
    · simpa only [radius_def] using Real.log_exp z.re
    · simp only [angle_def]
  continuous_toFun := by
    simp only [Complex.mk_eq_add_mul_I, radius_def, angle_def]
    exact (Complex.continuous_ofReal.comp
      (continuous_subtypeVal.fst.log fun p : PolarPoint ↦ ne_of_gt p.property)).add
      ((Complex.continuous_ofReal.comp continuous_subtypeVal.snd).mul_const Complex.I)
  continuous_invFun :=
    ((Real.continuous_exp.comp Complex.continuous_re).prodMk
      Complex.continuous_im).subtype_mk _

@[simp] theorem polarPointHomeomorphComplex_re (p : PolarPoint) :
    (polarPointHomeomorphComplex p).re = Real.log (radius p) := (rfl)

@[simp] theorem polarPointHomeomorphComplex_im (p : PolarPoint) :
    (polarPointHomeomorphComplex p).im = angle p := (rfl)

@[simp] theorem radius_polarPointHomeomorphComplex_symm (z : ℂ) :
    radius (polarPointHomeomorphComplex.symm z) = Real.exp z.re := by
  simp [radius_def, polarPointHomeomorphComplex]

@[simp] theorem angle_polarPointHomeomorphComplex_symm (z : ℂ) :
    angle (polarPointHomeomorphComplex.symm z) = z.im := by
  simp [angle_def, polarPointHomeomorphComplex]

/-- The polar projection, with its nonvanishing proof bundled in the codomain. -/
def projectionToNonzero (p : PolarPoint) : {z : ℂ // z ≠ 0} :=
  ⟨projection p, projection_ne_zero p⟩

@[simp, grind =] theorem coe_projectionToNonzero (p : PolarPoint) :
    (projectionToNonzero p : ℂ) = projection p := (rfl)

@[simp, grind =] theorem projectionToNonzero_deckShift (k : ℤ) (p : PolarPoint) :
    projectionToNonzero (deckShift k p) = projectionToNonzero p :=
  Subtype.ext (projection_deckShift k p)

/-- Under logarithmic coordinates, polar projection is complex exponentiation. -/
theorem projectionToNonzero_eq_exp (p : PolarPoint) :
    projectionToNonzero p =
      ⟨Complex.exp (polarPointHomeomorphComplex p), Complex.exp_ne_zero _⟩ := by
  apply Subtype.ext
  apply Complex.ext <;>
    simp [Complex.exp_re, Complex.exp_im, Real.exp_log (radius_pos p)]

/-- The polar projection is a covering map of the punctured complex plane. -/
theorem isCoveringMap_projectionToNonzero : IsCoveringMap projectionToNonzero := by
  have h := Complex.isCoveringMap_exp.comp_homeomorph polarPointHomeomorphComplex
  convert h using 1
  funext p
  exact projectionToNonzero_eq_exp p

/-- Every nonzero complex number has a polar lift. -/
theorem projectionToNonzero_surjective : Function.Surjective projectionToNonzero := by
  intro z
  refine ⟨polarPointHomeomorphComplex.symm (Complex.log z), ?_⟩
  rw [projectionToNonzero_eq_exp, Homeomorph.apply_symm_apply]
  exact Subtype.ext (Complex.exp_log z.property)

/-- The total space of the polar covering is contractible, hence simply connected. -/
instance : ContractibleSpace PolarPoint :=
  polarPointHomeomorphComplex.contractibleSpace

end TauCeti.PolarGraph
