/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
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

An orthogonal transformation of a real inner product space has determinant `1` or `-1`
(`Unitary.det_eq_one_or_eq_neg_one`; in infinite dimension every determinant is `1`), so it is
special orthogonal exactly when its determinant is positive
(`TauCeti.mem_specialOrthogonalGroup_iff_det_pos`) and not special orthogonal exactly when its
determinant is negative (`TauCeti.notMem_specialOrthogonalGroup_iff_det_neg`). Because the
determinant is continuous in the operator-norm topology, the special orthogonal group is open,
closed, and hence clopen in the orthogonal group (`TauCeti.isOpen_specialOrthogonalGroup`,
`TauCeti.isClosed_specialOrthogonalGroup`, `TauCeti.isClopen_specialOrthogonalGroup`). In positive
dimension the reflection in a hyperplane is an orthogonal transformation of determinant `-1`
(`Unitary.exists_det_eq_neg_one`). The reflection in the hyperplane orthogonal to a nonzero vector
`v` is not special orthogonal
(`TauCeti.reflection_orthogonal_singleton_notMem_specialOrthogonalGroup`), and it fixes every
vector orthogonal to `v` (`TauCeti.reflection_orthogonal_singleton_mem_stabilizer`).
-/

public section

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

namespace Unitary

/-- An orthogonal transformation of a real inner product space has determinant of absolute value
`1`. In infinite dimension every determinant is `1`. -/
theorem abs_det_eq_one (g : unitary (V →L[ℝ] V)) : |(g : V →L[ℝ] V).det| = 1 := by
  by_cases hV : FiniteDimensional ℝ V
  · rw [ContinuousLinearMap.det, ← LinearMap.normDet_eq_abs_det]
    exact (linearIsometryEquiv g).toLinearIsometry.normDet_eq_one
  · have h : (g : V →L[ℝ] V).det = 1 :=
      LinearMap.det_eq_one_of_not_module_finite (by simpa [FiniteDimensional] using hV) _
    simp [h]

/-- An orthogonal transformation of a real inner product space has determinant `1` or `-1`. -/
theorem det_eq_one_or_eq_neg_one (g : unitary (V →L[ℝ] V)) :
    (g : V →L[ℝ] V).det = 1 ∨ (g : V →L[ℝ] V).det = -1 :=
  abs_eq (zero_le_one' ℝ) |>.1 (abs_det_eq_one g)

/-- In positive dimension there is an orthogonal transformation of determinant `-1`: the
reflection in a hyperplane. -/
theorem exists_det_eq_neg_one (hV : 0 < Module.finrank ℝ V) :
    ∃ r : unitary (V →L[ℝ] V), (r : V →L[ℝ] V).det = -1 := by
  have := Module.finite_of_finrank_pos hV
  have := Module.nontrivial_of_finrank_pos hV
  obtain ⟨r, hr⟩ := TauCeti.exists_det_eq_neg_one (F := V)
  refine ⟨linearIsometryEquiv.symm r, ?_⟩
  rw [coe_symm_linearIsometryEquiv_apply, ContinuousLinearMap.det, ← hr, LinearEquiv.coe_det]
  rfl

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

/-- An orthogonal transformation is special orthogonal exactly when its determinant is positive.
In infinite dimension every determinant is `1`, so both sides hold. -/
theorem mem_specialOrthogonalGroup_iff_det_pos {g : unitary (V →L[ℝ] V)} :
    g ∈ specialOrthogonalGroup V ↔ 0 < (g : V →L[ℝ] V).det := by
  rw [mem_specialOrthogonalGroup_iff]
  rcases Unitary.det_eq_one_or_eq_neg_one g with h | h <;> rw [h] <;> norm_num

/-- An orthogonal transformation is not special orthogonal exactly when its determinant is
negative. In infinite dimension both sides fail. -/
theorem notMem_specialOrthogonalGroup_iff_det_neg {g : unitary (V →L[ℝ] V)} :
    g ∉ specialOrthogonalGroup V ↔ (g : V →L[ℝ] V).det < 0 := by
  rw [mem_specialOrthogonalGroup_iff_det_pos, not_lt]
  rcases Unitary.det_eq_one_or_eq_neg_one g with h | h <;> rw [h] <;> norm_num

/-- The special orthogonal group is open in the orthogonal group `unitary (V →L[ℝ] V)`. In
infinite dimension it is the whole group. -/
theorem isOpen_specialOrthogonalGroup :
    IsOpen (specialOrthogonalGroup V : Set (unitary (V →L[ℝ] V))) := by
  have : (specialOrthogonalGroup V : Set (unitary (V →L[ℝ] V))) =
      {g : unitary (V →L[ℝ] V) | (0 : ℝ) < (g : V →L[ℝ] V).det} :=
    Set.ext fun _ ↦ mem_specialOrthogonalGroup_iff_det_pos
  rw [this]
  exact isOpen_lt continuous_const (ContinuousLinearMap.continuous_det.comp continuous_subtypeVal)

/-- The special orthogonal group is closed in the orthogonal group `unitary (V →L[ℝ] V)`. -/
theorem isClosed_specialOrthogonalGroup :
    IsClosed (specialOrthogonalGroup V : Set (unitary (V →L[ℝ] V))) := by
  have : (specialOrthogonalGroup V : Set (unitary (V →L[ℝ] V))) =
      {g : unitary (V →L[ℝ] V) | (g : V →L[ℝ] V).det = 1} :=
    Set.ext fun _ ↦ mem_specialOrthogonalGroup_iff
  rw [this]
  exact isClosed_eq (ContinuousLinearMap.continuous_det.comp continuous_subtypeVal)
    continuous_const

/-- The special orthogonal group is clopen in the orthogonal group `unitary (V →L[ℝ] V)`. -/
theorem isClopen_specialOrthogonalGroup :
    IsClopen (specialOrthogonalGroup V : Set (unitary (V →L[ℝ] V))) :=
  ⟨isClosed_specialOrthogonalGroup, isOpen_specialOrthogonalGroup⟩

/-- The reflection in the hyperplane orthogonal to a nonzero vector, as an orthogonal
transformation, is not special orthogonal: its determinant is `-1`. -/
theorem reflection_orthogonal_singleton_notMem_specialOrthogonalGroup [FiniteDimensional ℝ V]
    {v : V} (hv : v ≠ 0) :
    Unitary.linearIsometryEquiv.symm (ℝ ∙ v)ᗮ.reflection ∉ specialOrthogonalGroup V := by
  rw [mem_specialOrthogonalGroup_iff, Unitary.coe_symm_linearIsometryEquiv_apply,
    ContinuousLinearMap.det]
  intro h
  have hdet := linearEquiv_det_reflection_orthogonal_singleton hv
  rw [LinearEquiv.coe_det] at hdet
  -- The coercion of the reflection to a linear map is `toLinearMap` by definition.
  have h₁ : (1 : ℝ) = -1 := h.symm.trans hdet
  norm_num at h₁

/-- The reflection in the hyperplane orthogonal to `v`, as an orthogonal transformation, fixes
every vector `w` orthogonal to `v`. -/
theorem reflection_orthogonal_singleton_mem_stabilizer {v w : V} (h : inner ℝ v w = 0) :
    Unitary.linearIsometryEquiv.symm (ℝ ∙ v)ᗮ.reflection ∈
      MulAction.stabilizer (unitary (V →L[ℝ] V)) w :=
  MulAction.mem_stabilizer_iff.2 (reflection_orthogonal_singleton_eq_self_of_inner_eq_zero h)

end TauCeti
