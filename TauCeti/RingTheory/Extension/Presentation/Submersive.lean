/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import TauCeti.RingTheory.Extension.Presentation.Basic

/-!
# The Jacobian minor at points of a submersive presentation

For a presubmersive presentation of an `R`-algebra `S` and a `k`-algebra point `x` of `S`, the
Jacobian minor evaluated at the coefficient restriction and generator values of `x` is the value
of the algebraic Jacobian of the presentation at `x`. For a submersive presentation the Jacobian
is a unit, so the evaluated minor is invertible at every solution of the relations, with the
coefficient point allowed to vary. These are the local equations to which the implicit function
theorem applies.

We use Mathlib's `Algebra.PreSubmersivePresentation` and `Algebra.SubmersivePresentation`,
developed by Jung Tao Cheng, Christian Merten and Andrew Yang. The submersive case supplies the
local equations of B. Conrad, *Weil and Grothendieck approaches to adelic points*, §4.

## Main results

* `Algebra.PreSubmersivePresentation.det_jacobiMatrix_points_coordinates`: the evaluated Jacobian
  minor at a point is the value of the Jacobian.
* `Algebra.SubmersivePresentation.isUnit_det_jacobiMatrix_solution`: the evaluated Jacobian minor
  of a submersive presentation is invertible at every solution.
-/

public section

open MvPolynomial

namespace Algebra.PreSubmersivePresentation

variable {k R S E ι σ : Type*} [CommSemiring k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [CommRing E] [Algebra k E]
  [Fintype σ] [DecidableEq σ] (P : PreSubmersivePresentation R S ι σ)

/-- At every point of a presubmersive presentation, the evaluated Jacobian minor is the
value of the algebraic Jacobian. Mathlib indexes this minor by variable first, relation second. -/
theorem det_jacobiMatrix_points_coordinates (x : S →ₐ[k] E) :
    ((aevalTower (x.comp (IsScalarTower.toAlgHom k R S))
      (fun i ↦ x (P.val i))).mapMatrix P.jacobiMatrix).det =
        x P.jacobian := by
  rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply]
  -- `AlgHom.mapMatrix` and its underlying `RingHom.mapMatrix` agree on matrices.
  exact ((aevalTower (x.comp (IsScalarTower.toAlgHom k R S))
    (fun i ↦ x (P.val i))).toRingHom.map_det _).symm.trans
      (P.toPresentation.aevalTower_comp_toAlgHom_val x _)

end Algebra.PreSubmersivePresentation

namespace Algebra.SubmersivePresentation

variable {k R S E ι σ : Type*} [CommSemiring k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [CommRing E] [Algebra k E] [Fintype σ] [DecidableEq σ]
  (P : SubmersivePresentation R S ι σ)

/-- The Jacobian minor is invertible at every solution of a submersive presentation. -/
theorem isUnit_det_jacobiMatrix_solution
    (z : {z : (R →ₐ[k] E) × (ι → E) // ∀ j, aevalTower z.1 z.2 (P.relation j) = 0}) :
    IsUnit (((aevalTower z.val.1 z.val.2).mapMatrix P.jacobiMatrix).det) := by
  obtain ⟨x, hx⟩ := (Set.ext_iff.mp (P.toPresentation.range_points_coordinates
    (k := k) (E := E)) z.val).mpr z.property
  rw [← hx, P.det_jacobiMatrix_points_coordinates]
  exact P.jacobian_isUnit.map x

end Algebra.SubmersivePresentation
