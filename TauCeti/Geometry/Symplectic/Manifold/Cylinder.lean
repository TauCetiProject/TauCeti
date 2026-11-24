/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle
import TauCeti.Geometry.Manifold.DeRham.Wedge
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The area form of the cylinder

For a positive period `p`, the cylinder `ℝ × AddCircle p` has coordinates `(r, θ)` and tangent
spaces `ℝ × ℝ`. Its **area form** is

`ω = dr ∧ dθ` (`TauCeti.cylinderAreaForm p`),

the wedge of the coordinate form of the line with the time form of the circle. It pairs the
tangent vectors `v` and `w` to the determinant `v₁ w₂ - w₁ v₂`, and it is closed, as is every
two-form on a surface.

## Main definitions

* `TauCeti.cylinderAreaForm p`: the area form `dr ∧ dθ` of `ℝ × AddCircle p`.
* `TauCeti.cylinderAreaClosedForm p`: the same form, bundled as a closed form.

## Main results

* `TauCeti.eval₂_cylinderAreaForm`, `TauCeti.cylinderAreaForm_apply`: the area form evaluates as
  the determinant of two tangent vectors.
* `TauCeti.isClosed_cylinderAreaForm`: the area form is closed.
* `TauCeti.cylinderAreaForm_mem_exactForms`: the area form is exact, `dr ∧ dθ = d(r dθ)`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 3.1 (area forms on surfaces).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable (p : ℝ) [Fact (0 < p)]

/-- The **area form** `dr ∧ dθ` of the cylinder `ℝ × AddCircle p`: the wedge of the coordinate
form of the line with the time form of the circle. -/
def cylinderAreaForm : SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) ℝ 2 :=
  SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst SmoothForm.realLineCoordForm)
    (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm p))

/-- The area form `dr ∧ dθ` evaluates as the determinant of the two tangent vectors. -/
theorem eval₂_cylinderAreaForm (y : ℝ × AddCircle p) (v w : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) y) :
    SmoothBundleForm.eval₂ (cylinderAreaForm p) y v w = v.1 * w.2 - w.1 * v.2 := by
  simp only [cylinderAreaForm, SmoothForm.eval₂_wedge_one_one, SmoothForm.mpullback_fst_apply,
    SmoothForm.mpullback_snd_apply, AddCircle.timeForm_apply, SmoothForm.realLineCoordForm_apply,
    Manifold.tangentSpaceProdEquiv_apply, Matrix.cons_val_zero]

/-- The area form `dr ∧ dθ` on a pair of tangent vectors, given as a family indexed by `Fin 2`. -/
theorem cylinderAreaForm_apply (y : ℝ × AddCircle p)
    (v : Fin 2 → TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) y) :
    (cylinderAreaForm p).val y v = (v 0).1 * (v 1).2 - (v 1).1 * (v 0).2 := by
  have hv : v = ![v 0, v 1] := funext fun i ↦ by fin_cases i <;> rfl
  calc (cylinderAreaForm p).val y v = (cylinderAreaForm p).val y ![v 0, v 1] := congrArg _ hv
    _ = _ := (SmoothBundleForm.eval₂_apply _ y (v 0) (v 1)).symm.trans
      (eval₂_cylinderAreaForm p y (v 0) (v 1))

/-- The area form of the cylinder is closed, as is every two-form on a surface. -/
theorem isClosed_cylinderAreaForm : (cylinderAreaForm p).IsClosed :=
  SmoothForm.isClosed_of_finrank_le (by simp) _

/-- The area form `dr ∧ dθ` of the cylinder, as a closed form. -/
def cylinderAreaClosedForm : closedForms (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) 2 :=
  ⟨cylinderAreaForm p, (mem_closedForms _ _).mpr
    ((SmoothForm.isClosed_def _).mp (isClosed_cylinderAreaForm p))⟩

/-- The underlying form of the closed area form is `dr ∧ dθ`. -/
@[simp]
theorem coe_cylinderAreaClosedForm : (cylinderAreaClosedForm p).val = cylinderAreaForm p :=
  (rfl)

/-- **The area form of the cylinder is exact**: it is the exterior derivative of the one-form
`r dθ`, the coordinate function `r` of the line times the time form of the circle. -/
theorem cylinderAreaForm_mem_exactForms :
    cylinderAreaForm p ∈ exactForms (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) 2 := by
  let r : C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), ℝ × AddCircle p; ℝ⟯ := ⟨Prod.fst, contMDiff_fst⟩
  -- The pulled back coordinate form `dr` is the differential of `r`, and `dθ` is closed.
  have hdr : SmoothForm.mpullback (M := ℝ × AddCircle p) Prod.fst contMDiff_fst
      SmoothForm.realLineCoordForm ∈ exactForms (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × AddCircle p) 1 := by
    rw [exactForms_succ]
    refine ⟨SmoothForm.ofFunction r, Subtype.ext ?_⟩
    rw [SmoothForm.coe_mpullback, mextDerivₗ_apply, SmoothForm.coe_ofFunction]
    exact (SmoothForm.mpullback_realLineCoordForm _).symm
  rw [cylinderAreaForm]
  exact SmoothForm.wedge_mem_exactForms_of_left_mem hdr ((mem_closedForms _ _).mpr
    ((SmoothForm.isClosed_def _).mp
      ((AddCircle.isClosed_timeForm p).mpullback Prod.snd contMDiff_snd)))

end TauCeti
