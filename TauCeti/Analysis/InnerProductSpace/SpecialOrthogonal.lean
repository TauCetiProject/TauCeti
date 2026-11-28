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
`TauCeti.specialOrthogonalGroup V`, the kernel of the determinant `Unitary.detMonoidHom V`. It is
the structure group of the oriented orthonormal frame bundle of an oriented Riemannian vector
bundle.

An orthogonal transformation of a real inner product space has determinant `1` or `-1`
(`Unitary.det_eq_one_or_eq_neg_one`; in infinite dimension every determinant is `1`), the same as
the determinant of its inverse (`Unitary.det_inv_eq_det`), so it is
special orthogonal exactly when its determinant is positive
(`TauCeti.mem_specialOrthogonalGroup_iff_det_pos`) and not special orthogonal exactly when its
determinant is negative (`TauCeti.notMem_specialOrthogonalGroup_iff_det_neg`). Because the
determinant is continuous in the operator-norm topology, the special orthogonal group is open,
closed, and hence clopen in the orthogonal group (`TauCeti.isOpen_specialOrthogonalGroup`,
`TauCeti.isClosed_specialOrthogonalGroup`, `TauCeti.isClopen_specialOrthogonalGroup`). In positive
dimension the reflection in a hyperplane is an orthogonal transformation of determinant `-1`
(`Unitary.exists_det_eq_neg_one`); in dimension at least two it can be chosen to fix a given
vector (`Unitary.exists_det_eq_neg_one_apply_eq_self`). The reflection in the hyperplane orthogonal
to a nonzero vector `v` is not special orthogonal
(`TauCeti.reflection_orthogonal_singleton_notMem_specialOrthogonalGroup`), and it fixes every
vector orthogonal to `v` (`TauCeti.reflection_orthogonal_singleton_mem_stabilizer`).

The special orthogonal stabilizer `TauCeti.specialOrthogonalStabilizer V v₀` of a vector `v₀` is
the subgroup of special orthogonal transformations fixing `v₀`
(`TauCeti.mem_specialOrthogonalStabilizer_iff`): for a unit vector it is `SO(N - 1)`, and in an
oriented three-dimensional space it is the circle group of rotations about the axis `ℝ v₀`. It is
the structure group of the frames adapted to an oriented plane field.
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

variable (V) in
/-- The determinant of the orthogonal transformations of `V`, as a monoid homomorphism. -/
def detMonoidHom : unitary (V →L[ℝ] V) →* ℝ :=
  LinearMap.det.comp (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp (unitary _).subtype)

/-- `Unitary.detMonoidHom V` sends an orthogonal transformation to its determinant. -/
@[simp]
theorem detMonoidHom_apply (g : unitary (V →L[ℝ] V)) :
    detMonoidHom V g = (g : V →L[ℝ] V).det :=
  (rfl)

/-- An orthogonal transformation and its inverse have the same determinant `±1`. -/
@[simp]
theorem det_inv_eq_det (g : unitary (V →L[ℝ] V)) :
    ((g⁻¹ : unitary (V →L[ℝ] V)) : V →L[ℝ] V).det = (g : V →L[ℝ] V).det := by
  have h : ((g⁻¹ : unitary (V →L[ℝ] V)) : V →L[ℝ] V).det * (g : V →L[ℝ] V).det = 1 := by
    rw [← detMonoidHom_apply, ← detMonoidHom_apply, ← map_mul, inv_mul_cancel, map_one]
  rcases det_eq_one_or_eq_neg_one g with hg | hg <;> rw [hg] at h ⊢ <;> linarith

/-- The orthogonal transformation corresponding to a linear isometry `r` has the determinant of
`r`. -/
theorem det_coe_symm_linearIsometryEquiv (r : V ≃ₗᵢ[ℝ] V) :
    ((linearIsometryEquiv.symm r : unitary (V →L[ℝ] V)) : V →L[ℝ] V).det =
      LinearEquiv.det r.toLinearEquiv := by
  rw [coe_symm_linearIsometryEquiv_apply, ContinuousLinearMap.det, LinearEquiv.coe_det]
  -- Both sides are the determinant of the linear map underlying `r`, by definition.
  rfl

/-- In positive dimension there is an orthogonal transformation of determinant `-1`: the
reflection in a hyperplane. -/
theorem exists_det_eq_neg_one (hV : 0 < Module.finrank ℝ V) :
    ∃ r : unitary (V →L[ℝ] V), (r : V →L[ℝ] V).det = -1 := by
  have := Module.finite_of_finrank_pos hV
  have := Module.nontrivial_of_finrank_pos hV
  obtain ⟨r, hr⟩ := TauCeti.exists_det_eq_neg_one (F := V)
  exact ⟨linearIsometryEquiv.symm r, by rw [det_coe_symm_linearIsometryEquiv, hr]⟩

/-- In dimension at least two, every vector `v` is fixed by an orthogonal transformation of
determinant `-1`: the reflection in the hyperplane orthogonal to a nonzero vector orthogonal to
`v`. -/
theorem exists_det_eq_neg_one_apply_eq_self (hV : 2 ≤ Module.finrank ℝ V) (v : V) :
    ∃ r : unitary (V →L[ℝ] V), (r : V →L[ℝ] V).det = -1 ∧ (r : V →L[ℝ] V) v = v := by
  obtain ⟨r, hr, hrv⟩ := TauCeti.exists_det_eq_neg_one_apply_eq_self hV v
  exact ⟨linearIsometryEquiv.symm r, by rw [det_coe_symm_linearIsometryEquiv, hr],
    by simpa using hrv⟩

end Unitary

namespace TauCeti

variable (V) in
/-- The special orthogonal group of a real inner product space `V`: the orthogonal
transformations of `V`, as elements of the unitary group of `V →L[ℝ] V`, of determinant `1`. -/
def specialOrthogonalGroup : Subgroup (unitary (V →L[ℝ] V)) :=
  (Unitary.detMonoidHom V).ker

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

variable (V) in
/-- The special orthogonal transformations of `V` fixing a vector `v₀`. For a unit vector of an
oriented three-dimensional space this is the circle group of rotations about the axis `ℝ v₀`; it
is the structure group of the frames adapted to an oriented plane field. -/
def specialOrthogonalStabilizer (v₀ : V) : Subgroup (unitary (V →L[ℝ] V)) :=
  MulAction.stabilizer (unitary (V →L[ℝ] V)) v₀ ⊓ specialOrthogonalGroup V

variable (V) in
/-- The special orthogonal stabilizer of `v₀` is the stabilizer of `v₀` in the special orthogonal
group. -/
theorem specialOrthogonalStabilizer_def (v₀ : V) :
    specialOrthogonalStabilizer V v₀ =
      MulAction.stabilizer (unitary (V →L[ℝ] V)) v₀ ⊓ specialOrthogonalGroup V :=
  (rfl)

/-- An orthogonal transformation lies in the special orthogonal stabilizer of `v₀` exactly when it
fixes `v₀` and has determinant `1`. -/
@[simp]
theorem mem_specialOrthogonalStabilizer_iff {v₀ : V} {g : unitary (V →L[ℝ] V)} :
    g ∈ specialOrthogonalStabilizer V v₀ ↔ (g : V →L[ℝ] V) v₀ = v₀ ∧ (g : V →L[ℝ] V).det = 1 :=
  Subgroup.mem_inf.trans (and_congr Iff.rfl mem_specialOrthogonalGroup_iff)

end TauCeti
