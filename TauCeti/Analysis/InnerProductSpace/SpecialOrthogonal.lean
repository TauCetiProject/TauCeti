/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

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

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

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
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hV
  refine ⟨linearIsometryEquiv.symm (ℝ ∙ v)ᗮ.reflection, ?_⟩
  -- `ContinuousLinearMap.det` is the determinant of the underlying linear map, while
  -- `Submodule.det_reflection` is stated for the linear-equivalence coercion of the reflection.
  -- Mathlib has no lemma identifying the two underlying linear maps, so compare them pointwise.
  have hcoe : (((ℝ ∙ v)ᗮ.reflection : V →L[ℝ] V) : V →ₗ[ℝ] V) =
      (ℝ ∙ v)ᗮ.reflection.toLinearMap :=
    LinearMap.ext fun x => by
      rw [ContinuousLinearMap.coe_coe, LinearIsometryEquiv.coe_coe'', LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv]
  rw [coe_symm_linearIsometryEquiv_apply, ContinuousLinearMap.det, hcoe,
    Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hv, pow_one]

end Unitary

namespace TauCeti

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

variable [FiniteDimensional ℝ V]

/-- In finite dimension, an orthogonal transformation is special orthogonal exactly when its
determinant is positive. -/
theorem mem_specialOrthogonalGroup_iff_det_pos {g : unitary (V →L[ℝ] V)} :
    g ∈ specialOrthogonalGroup V ↔ 0 < (g : V →L[ℝ] V).det := by
  rw [mem_specialOrthogonalGroup_iff]
  rcases Unitary.det_eq_one_or_eq_neg_one g with h | h <;> rw [h] <;> norm_num

/-- In finite dimension, an orthogonal transformation is not special orthogonal exactly when its
determinant is negative. -/
theorem notMem_specialOrthogonalGroup_iff_det_neg {g : unitary (V →L[ℝ] V)} :
    g ∉ specialOrthogonalGroup V ↔ (g : V →L[ℝ] V).det < 0 := by
  rw [mem_specialOrthogonalGroup_iff_det_pos, not_lt]
  rcases Unitary.det_eq_one_or_eq_neg_one g with h | h <;> rw [h] <;> norm_num

end TauCeti
