/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.InnerProductSpace.NormDet
import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# The special orthogonal group of a real inner product space

The orthogonal group of a real inner product space `V` is the unitary group
`unitary (V →L[ℝ] V)` of its operator algebra, with the operator-norm topology. This file defines
its subgroup of transformations of determinant `1`, the special orthogonal group
`TauCeti.specialOrthogonalGroup V`. It is the structure group of the oriented orthonormal frame
bundle of an oriented Riemannian vector bundle.

When `V` is finite-dimensional an orthogonal transformation has determinant `1` or `-1`
(`Unitary.det_eq_one_or_eq_neg_one`), so it is special orthogonal exactly when its determinant is
positive (`TauCeti.mem_specialOrthogonalGroup_iff_det_pos`) and not special orthogonal exactly when
its determinant is negative (`TauCeti.notMem_specialOrthogonalGroup_iff_det_neg`). In positive
dimension the reflection in a hyperplane is an orthogonal transformation of determinant `-1`
(`Unitary.exists_det_eq_neg_one`).
-/

public section

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace Unitary

/-- An orthogonal transformation of a finite-dimensional real inner product space has determinant
`1` or `-1`. -/
theorem abs_det_eq_one [FiniteDimensional ℝ V] (g : unitary (V →L[ℝ] V)) :
    |(g : V →L[ℝ] V).det| = 1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.normDet_eq_abs_det]
  exact (linearIsometryEquiv g).toLinearIsometry.normDet_eq_one

/-- An orthogonal transformation of a finite-dimensional real inner product space has determinant
`1` or `-1`. -/
theorem det_eq_one_or_eq_neg_one [FiniteDimensional ℝ V] (g : unitary (V →L[ℝ] V)) :
    (g : V →L[ℝ] V).det = 1 ∨ (g : V →L[ℝ] V).det = -1 :=
  abs_eq (zero_le_one' ℝ) |>.1 (abs_det_eq_one g)

/-- In positive dimension there is an orthogonal transformation of determinant `-1`: the
reflection in a hyperplane. -/
theorem exists_det_eq_neg_one [FiniteDimensional ℝ V] (hV : 0 < Module.finrank ℝ V) :
    ∃ r : unitary (V →L[ℝ] V), (r : V →L[ℝ] V).det = -1 := by
  have := Module.nontrivial_of_finrank_pos hV
  obtain ⟨r, hr⟩ := TauCeti.exists_det_eq_neg_one (F := V)
  refine ⟨linearIsometryEquiv.symm r, ?_⟩
  rw [coe_symm_linearIsometryEquiv_apply, ContinuousLinearMap.det, ← hr, LinearEquiv.coe_det]
  rfl

end Unitary

namespace TauCeti

variable [CompleteSpace V]

variable (V) in
/-- The special orthogonal group of a real inner product space `V`: the orthogonal
transformations of `V`, as elements of the unitary group of `V →L[ℝ] V`, of determinant `1`. -/
def specialOrthogonalGroup : Subgroup (unitary (V →L[ℝ] V)) :=
  (LinearMap.det.comp
    (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp (unitary (V →L[ℝ] V)).subtype)).ker

/-- An orthogonal transformation is special orthogonal exactly when its determinant is `1`. -/
@[simp]
theorem mem_specialOrthogonalGroup_iff {g : unitary (V →L[ℝ] V)} :
    g ∈ specialOrthogonalGroup V ↔ (g : V →L[ℝ] V).det = 1 :=
  MonoidHom.mem_ker

/-- An orthogonal transformation is special orthogonal exactly when its determinant is positive.
In infinite dimension every determinant is `1`, so both sides hold. -/
theorem mem_specialOrthogonalGroup_iff_det_pos {g : unitary (V →L[ℝ] V)} :
    g ∈ specialOrthogonalGroup V ↔ 0 < (g : V →L[ℝ] V).det := by
  rw [mem_specialOrthogonalGroup_iff]
  by_cases hV : FiniteDimensional ℝ V
  · rcases Unitary.det_eq_one_or_eq_neg_one g with h | h <;> rw [h] <;> norm_num
  · have h : (g : V →L[ℝ] V).det = 1 :=
      LinearMap.det_eq_one_of_not_module_finite (by simpa [FiniteDimensional] using hV) _
    simp [h]

variable [FiniteDimensional ℝ V]

/-- In finite dimension, an orthogonal transformation is not special orthogonal exactly when its
determinant is negative. -/
theorem notMem_specialOrthogonalGroup_iff_det_neg {g : unitary (V →L[ℝ] V)} :
    g ∉ specialOrthogonalGroup V ↔ (g : V →L[ℝ] V).det < 0 := by
  rw [mem_specialOrthogonalGroup_iff_det_pos, not_lt]
  rcases Unitary.det_eq_one_or_eq_neg_one g with h | h <;> rw [h] <;> norm_num

end TauCeti
