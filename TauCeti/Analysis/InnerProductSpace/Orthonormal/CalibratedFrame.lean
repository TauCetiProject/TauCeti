/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.InnerProductSpace.Orientation
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# Calibrated frames

Let `φ` be a real alternating `k`-form on a real inner product space `E`. An ordered frame
`v : Fin k → E` is *calibrated* by `φ` when it is orthonormal and `φ v = 1`. When the comass `‖φ‖`
is at most one, `1` is the largest value of `φ` on orthonormal frames, so the calibrated frames
are the positively oriented orthonormal frames of the planes on which `φ` restricts to the volume
form: the equality planes, or contact set, of `φ`. They are the possible oriented tangent planes
of the submanifolds calibrated by a calibration whose value at a point is `φ`.

Among orthonormal frames, being calibrated depends only on the wedge `v₁ ∧ ⋯ ∧ vₖ`. A change of
frame `vⱼ ↦ ∑ i, A j i • vᵢ` by an orthogonal matrix `A` multiplies the value of `φ` by
`det A = ±1`: special orthogonal changes of frame preserve calibrated frames, and reversing the
orientation of a frame, for instance by negating one vector, exchanges the calibrated frames of
`φ` and `-φ`. Calibrated frames are natural under pullback along linear isometries. The zero form
calibrates no frame, in degree zero the constant `c` calibrates the empty frame exactly when
`c = 1`, and the unit decomposable form `⟪e₁ ∧ ⋯ ∧ eₖ, ·⟫` of an orthonormal frame `e` calibrates
exactly the frames `A • e` with `A ∈ SO(k)`, the positively oriented orthonormal frames of the
span of `e`.

## Main definitions

* `ContinuousAlternatingMap.IsCalibratedFrame φ v`: `v` is orthonormal and `φ v = 1`.

## Main results

* `ContinuousAlternatingMap.IsCalibratedFrame.one_le_norm` and
  `ContinuousAlternatingMap.IsCalibratedFrame.norm_eq_one`: a form calibrating a frame has comass
  at least one (hence comass one when `‖φ‖ ≤ 1`), and
  `ContinuousAlternatingMap.isCalibratedFrame_iff_one_le_apply`: for a form of comass at most one
  it suffices that the value on an orthonormal frame is at least one.
* `ContinuousAlternatingMap.IsCalibratedFrame.of_ιMulti_eq`: calibration of orthonormal frames
  depends only on their wedge.
* `ContinuousAlternatingMap.isCalibratedFrame_sum_smul_iff`: an orthogonal change of frame by `A`
  turns calibration by `φ` into calibration by `det A • φ`;
  `ContinuousAlternatingMap.isCalibratedFrame_sum_smul_iff_of_mem_specialOrthogonalGroup` and
  `ContinuousAlternatingMap.isCalibratedFrame_neg_iff_update_neg` are its two cases.
* `ContinuousAlternatingMap.isCalibratedFrame_compContinuousLinearMap_iff`: naturality under
  pullback along linear isometries.
* `ContinuousAlternatingMap.isCalibratedFrame_volumeFormL_orthonormalBasis_iff`: on an oriented
  `k`-dimensional space, `o.volumeFormL` calibrates an orthonormal basis iff it is positively
  oriented.
* `ContinuousAlternatingMap.isCalibratedFrame_alternatingFormEquiv_ιMulti_iff` and
  `ContinuousAlternatingMap.isCalibratedFrame_alternatingFormEquiv_ιMulti_iff_ιMulti_eq`: the frames
  calibrated by a unit decomposable form.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. 148 (1982), §II.3.
* D. Joyce, *Lectures on special Lagrangian geometry*, Definition 2.1.
-/

public section

open exteriorPower
open scoped Matrix RealInnerProductSpace

namespace ContinuousAlternatingMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {k : ℕ} {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v w : Fin k → E}

/-- An ordered frame `v` is **calibrated** by a real alternating `k`-form `φ` when it is
orthonormal and `φ v = 1`. For a form of comass at most one these are the positively oriented
orthonormal frames of its equality planes. -/
structure IsCalibratedFrame (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) : Prop where
  /-- A calibrated frame is orthonormal. -/
  orthonormal : Orthonormal ℝ v
  /-- The form takes the value one on a calibrated frame. -/
  apply_eq_one : φ v = 1

theorem isCalibratedFrame_iff : φ.IsCalibratedFrame v ↔ Orthonormal ℝ v ∧ φ v = 1 :=
  ⟨fun h ↦ ⟨h.orthonormal, h.apply_eq_one⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- A form that calibrates some frame has comass at least one. -/
theorem IsCalibratedFrame.one_le_norm (h : φ.IsCalibratedFrame v) : 1 ≤ ‖φ‖ := by
  simpa [h.apply_eq_one] using
    (opNorm_le_iff_le_orthonormal (norm_nonneg φ)).1 le_rfl v h.orthonormal

/-- A form of comass at most one that calibrates some frame has comass one. -/
theorem IsCalibratedFrame.norm_eq_one (h : φ.IsCalibratedFrame v) (hφ : ‖φ‖ ≤ 1) : ‖φ‖ = 1 :=
  le_antisymm hφ h.one_le_norm

/-- A form with comass strictly less than one calibrates no frame. -/
theorem not_isCalibratedFrame_of_norm_lt_one (hφ : ‖φ‖ < 1) : ¬φ.IsCalibratedFrame v :=
  fun h ↦ hφ.not_ge h.one_le_norm

/-- For a form of comass at most one, an orthonormal frame is calibrated as soon as the value of
the form on it is at least one. -/
theorem isCalibratedFrame_iff_one_le_apply (hφ : ‖φ‖ ≤ 1) :
    φ.IsCalibratedFrame v ↔ Orthonormal ℝ v ∧ 1 ≤ φ v := by
  refine ⟨fun h ↦ ⟨h.orthonormal, h.apply_eq_one.ge⟩, fun ⟨hv, h1⟩ ↦ ⟨hv, le_antisymm ?_ h1⟩⟩
  simpa using (le_abs_self (φ v)).trans
    (by simpa using (opNorm_le_iff_le_orthonormal zero_le_one).1 hφ v hv)

/-- The zero form calibrates no frame. -/
@[simp]
theorem not_isCalibratedFrame_zero : ¬(0 : E [⋀^Fin k]→L[ℝ] ℝ).IsCalibratedFrame v :=
  fun h ↦ zero_ne_one (α := ℝ) (by simpa using h.apply_eq_one)

/-- A form that calibrates some frame is nonzero. -/
theorem IsCalibratedFrame.ne_zero (h : φ.IsCalibratedFrame v) : φ ≠ 0 :=
  fun h0 ↦ not_isCalibratedFrame_zero (h0 ▸ h)

/-- In degree zero, the empty frame is calibrated by `φ` if and only if `φ ![] = 1`. -/
theorem isCalibratedFrame_zero_iff (φ : E [⋀^Fin 0]→L[ℝ] ℝ) (v : Fin 0 → E) :
    φ.IsCalibratedFrame v ↔ φ ![] = 1 := by
  rw [isCalibratedFrame_iff, Matrix.empty_eq v]
  exact and_iff_right (orthonormal_iff_ite.2 fun i ↦ i.elim0)

/-- In degree zero the constant form `c` calibrates the empty frame exactly when `c = 1`. -/
@[simp]
theorem isCalibratedFrame_constOfIsEmpty_iff (c : ℝ) (v : Fin 0 → E) :
    (constOfIsEmpty ℝ E (Fin 0) c).IsCalibratedFrame v ↔ c = 1 := by
  simp [isCalibratedFrame_iff]

/-- Calibrated frames are natural under pullback along a linear isometry `L`: a frame `v` is
calibrated by the pulled-back form exactly when `L ∘ v` is calibrated by `φ`. -/
@[simp]
theorem isCalibratedFrame_compContinuousLinearMap_iff (L : F →ₗᵢ[ℝ] E) {v : Fin k → F} :
    (φ.compContinuousLinearMap L.toContinuousLinearMap).IsCalibratedFrame v ↔
      φ.IsCalibratedFrame (L ∘ v) := by
  simp [isCalibratedFrame_iff, L.orthonormal_comp_iff]

/-- Among orthonormal frames, being calibrated depends only on the wedge of the frame. -/
theorem IsCalibratedFrame.of_ιMulti_eq (h : φ.IsCalibratedFrame v) (hw : Orthonormal ℝ w)
    (hvw : ιMulti ℝ k w = ιMulti ℝ k v) : φ.IsCalibratedFrame w := by
  refine ⟨hw, ?_⟩
  simpa [h.apply_eq_one] using congr(alternatingMapLinearEquiv φ.toAlternatingMap $hvw)

/-- An orthogonal change of frame `vⱼ ↦ ∑ i, A j i • vᵢ` multiplies the value of a form by
`det A = ±1`, so it carries the frames calibrated by `det A • φ` to those calibrated by `φ`. -/
theorem isCalibratedFrame_sum_smul_iff {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin k) ℝ) :
    φ.IsCalibratedFrame (fun j ↦ ∑ i, A j i • v i) ↔ (A.det • φ).IsCalibratedFrame v := by
  have hval : φ (fun j ↦ ∑ i, A j i • v i) = (A.det • φ) v := by
    simpa using φ.toAlternatingMap.map_sum_smul A v
  rw [isCalibratedFrame_iff, isCalibratedFrame_iff,
    TauCeti.orthonormal_sum_smul_iff_of_mem_unitaryGroup hA, hval]

/-- A special orthogonal change of frame `vⱼ ↦ ∑ i, A j i • vᵢ` preserves calibrated frames. -/
theorem isCalibratedFrame_sum_smul_iff_of_mem_specialOrthogonalGroup
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin k) ℝ) :
    φ.IsCalibratedFrame (fun j ↦ ∑ i, A j i • v i) ↔ φ.IsCalibratedFrame v := by
  obtain ⟨hAO, hdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.1 hA
  rw [isCalibratedFrame_sum_smul_iff hAO, hdet, one_smul]

/-- Negating one vector of a frame reverses its orientation: the frames calibrated by `-φ` are
those which become calibrated by `φ` after one of their vectors is negated. -/
theorem isCalibratedFrame_neg_iff_update_neg (i : Fin k) :
    (-φ).IsCalibratedFrame v ↔ φ.IsCalibratedFrame (Function.update v i (-v i)) := by
  classical
  have hval : φ (Function.update v i (-v i)) = -φ v := by
    rw [← neg_one_smul ℝ (v i), φ.map_update_smul, Function.update_eq_self, neg_one_smul]
  have hsign (j : Fin k) : Function.update v i (-v i) j = v j ∨
      Function.update v i (-v i) j = -v j := by
    rcases eq_or_ne j i with rfl | hj
    · exact .inr (Function.update_self ..)
    · exact .inl (Function.update_of_ne hj ..)
  have horth : Orthonormal ℝ (Function.update v i (-v i)) ↔ Orthonormal ℝ v :=
    ⟨fun hu ↦ hu.orthonormal_of_forall_eq_or_eq_neg fun j ↦ (hsign j).imp
      (fun h ↦ h.symm) fun h ↦ by rw [h, neg_neg],
      fun hv ↦ hv.orthonormal_of_forall_eq_or_eq_neg hsign⟩
  rw [isCalibratedFrame_iff, isCalibratedFrame_iff, horth, hval, neg_apply]

/-- On an oriented `k`-dimensional real inner product space, `o.volumeFormL` calibrates a frame `v`
if and only if `v` is orthonormal and `0 < o.volumeForm v`. -/
theorem isCalibratedFrame_volumeFormL_iff_pos [Fact (Module.finrank ℝ E = k)]
    (o : Orientation ℝ E (Fin k)) (v : Fin k → E) :
    o.volumeFormL.IsCalibratedFrame v ↔ Orthonormal ℝ v ∧ 0 < o.volumeForm v := by
  rw [isCalibratedFrame_iff, Orientation.volumeFormL_apply]
  refine and_congr_right fun hv ↦ ⟨fun h ↦ by linarith, fun hpos ↦ ?_⟩
  have habs := o.abs_volumeForm_apply_eq_sqrt_det_gram v
  rwa [abs_of_pos hpos, Matrix.gram_eq_one_iff_orthonormal.2 hv, Matrix.det_one, Real.sqrt_one]
    at habs

/-- On an oriented `k`-dimensional real inner product space, `o.volumeFormL` calibrates an
orthonormal basis `b` if and only if `b` is positively oriented for `o`. -/
@[simp]
theorem isCalibratedFrame_volumeFormL_orthonormalBasis_iff [Fact (Module.finrank ℝ E = k)]
    (o : Orientation ℝ E (Fin k)) (b : OrthonormalBasis (Fin k) ℝ E) :
    o.volumeFormL.IsCalibratedFrame b ↔ b.toBasis.orientation = o := by
  rw [isCalibratedFrame_volumeFormL_iff_pos, and_iff_right b.orthonormal,
    ← OrthonormalBasis.coe_toBasis, Orientation.volumeForm_apply_pos_iff]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **Wedge characterization of equality planes of a simple calibration**: for an orthonormal frame
`e : Fin k → E`, the unit decomposable form `⟪e₁ ∧ ⋯ ∧ eₖ, ·⟫` calibrates `v` if and only if `v` is
orthonormal and spans the same oriented `k`-plane as `e` (`ιMulti ℝ k v = ιMulti ℝ k e`). -/
theorem isCalibratedFrame_alternatingFormEquiv_ιMulti_iff_ιMulti_eq {e : Fin k → E}
    (he : Orthonormal ℝ e) :
    (TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)).IsCalibratedFrame v ↔
      Orthonormal ℝ v ∧ ιMulti ℝ k v = ιMulti ℝ k e := by
  rw [isCalibratedFrame_iff, TauCeti.alternatingFormEquiv_apply]
  refine and_congr_right fun hv ↦ ⟨fun h1 ↦ ?_, fun heq ↦ ?_⟩
  · exact (inner_eq_one_iff_of_norm_eq_one he.norm_ιMulti hv.norm_ιMulti).1 h1 |>.symm
  · rw [heq, real_inner_self_eq_norm_sq, he.norm_ιMulti, one_pow]

/-- The unit decomposable form `⟪e₁ ∧ ⋯ ∧ eₖ, ·⟫` of an orthonormal frame `e` calibrates exactly
the frames `A • e` with `A ∈ SO(k)`, the positively oriented orthonormal frames of the span of
`e`. -/
theorem isCalibratedFrame_alternatingFormEquiv_ιMulti_iff {e : Fin k → E} (he : Orthonormal ℝ e) :
    (TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)).IsCalibratedFrame v ↔
      ∃ A ∈ Matrix.specialOrthogonalGroup (Fin k) ℝ, v = fun j ↦ ∑ i, A j i • e i := by
  rw [isCalibratedFrame_alternatingFormEquiv_ιMulti_iff_ιMulti_eq he]
  refine ⟨fun ⟨hv, heq⟩ ↦ (he.ιMulti_eq_ιMulti_iff hv).1 heq, ?_⟩
  rintro ⟨A, hA, rfl⟩
  have hv : Orthonormal ℝ (fun j ↦ ∑ i, A j i • e i) :=
    (TauCeti.orthonormal_sum_smul_iff_of_mem_unitaryGroup
      (Matrix.mem_specialOrthogonalGroup_iff.1 hA).1).2 he
  exact ⟨hv, (he.ιMulti_eq_ιMulti_iff hv).2 ⟨A, hA, rfl⟩⟩

end FiniteDimensional

end ContinuousAlternatingMap

namespace Orthonormal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ} {u : Fin k → E}

/-- The unit decomposable form `⟪u₁ ∧ ⋯ ∧ uₖ, ·⟫` of an orthonormal frame `u` calibrates `u`
itself. -/
theorem isCalibratedFrame_alternatingFormEquiv_ιMulti (hu : Orthonormal ℝ u) :
    (TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u)).IsCalibratedFrame u :=
  (ContinuousAlternatingMap.isCalibratedFrame_alternatingFormEquiv_ιMulti_iff_ιMulti_eq hu).2
    ⟨hu, rfl⟩

end Orthonormal
