/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.FrameAction.Basic
public import TauCeti.LinearAlgebra.Orientation.Subspace
import Mathlib.Analysis.InnerProductSpace.Orientation
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# Oriented spans of Stiefel frames

A frame orients its span by its ordered basis. Two frames give the same oriented span exactly
when they differ by a rotation. In positive rank every oriented subspace occurs as such a span.
-/

public section

noncomputable section

open Cardinal Matrix Module Set Submodule

namespace TauCeti.stiefel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-- The span of a frame with the orientation given by its ordered basis. -/
def orientedSpan (v : stiefel E k) : OrientedSubspace ℝ E k :=
  let b := (orthonormalBasisOfSpanEq v rfl).toBasis
  letI := Module.Finite.of_basis b
  ⟨⟨span ℝ (range v.val), by rw [← finrank_eq_rank, finrank_span_range]⟩, b.orientation⟩

/-- The underlying plane of the oriented span is the span of the frame vectors. -/
@[simp]
theorem coe_fst_orientedSpan (v : stiefel E k) :
    (orientedSpan v).1.val = span ℝ (range v.val) :=
  (rfl)

/-- The empty frame induces the positive orientation of its zero-dimensional span. -/
@[simp]
theorem orientation_orientedSpan_zero (v : stiefel E 0) :
    (orientedSpan v).2 = positiveOrientation :=
  (orthonormalBasisOfSpanEq v rfl).toBasis.orientation_isEmpty

/-- Write the oriented span using a specified subspace spanned by the frame. -/
theorem orientedSpan_eq_mk (v : stiefel E k)
    (P : {P : Submodule ℝ E // Module.rank ℝ P = (k : Cardinal)})
    (hP : span ℝ (range v.val) = P.val) :
    orientedSpan v = ⟨P, (orthonormalBasisOfSpanEq v hP).toBasis.orientation⟩ := by
  obtain ⟨P, hdim⟩ := P
  simp only at hP
  subst P
  rfl

/-- The empty frame selects the positive sign of the zero plane. -/
@[simp]
theorem orientedSubspaceZeroEquiv_orientedSpan (v : stiefel E 0) :
    orientedSubspaceZeroEquiv (orientedSpan v) = true := by
  symm
  apply orientedSubspaceZeroEquiv.symm_apply_eq.1
  rw [orientedSubspaceZeroEquiv_symm_true, orientedSpan_eq_mk v ⟨⊥, by simp⟩ (by simp)]
  rw [Module.Basis.orientation_isEmpty]

/-- At positive rank every orientation of a plane is realized by an orthonormal basis. -/
theorem surjective_orientedSpan [NeZero k] :
    Function.Surjective (orientedSpan : stiefel E k → OrientedSubspace ℝ E k) := by
  rintro ⟨⟨P, hdim⟩, o⟩
  let : FiniteDimensional ℝ P := Module.finite_of_rank_eq_nat hdim
  let b := ((stdOrthonormalBasis ℝ P).reindex
    (finCongr (Module.finrank_eq_of_rank_eq hdim))).adjustToOrientation o
  let v : stiefel E k := ⟨fun i ↦ (b i : E), mem_stiefel_iff.2
    (b.orthonormal.comp_linearIsometry P.subtypeₗᵢ)⟩
  have hP : span ℝ (range v.val) = P := by
    exact (Submodule.span_range_subtype_eq_top_iff P (fun i ↦ (b i).property)).1
      b.toBasis.span_eq
  have hb : (orthonormalBasisOfSpanEq v hP).toBasis = b.toBasis := by
    ext i : 1
    exact Subtype.ext (coe_orthonormalBasisOfSpanEq_apply _ _ _)
  refine ⟨v, ?_⟩
  rw [orientedSpan_eq_mk v ⟨P, hdim⟩ hP, hb,
    OrthonormalBasis.orientation_adjustToOrientation]

/-- Orthogonal changes of basis relate precisely the frames with the same span. -/
theorem span_range_eq_iff_mem_orbit_orthogonalGroup {v w : stiefel E k} :
    span ℝ (range v.val) = span ℝ (range w.val) ↔
      w ∈ MulAction.orbit (orthogonalGroup (Fin k) ℝ) v := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · let P := span ℝ (range v.val)
    let b := orthonormalBasisOfSpanEq v (P := P) rfl
    let c := orthonormalBasisOfSpanEq w h.symm
    let A := (b.toBasis.toMatrix c.toBasis)ᵀ
    have hAv (j : Fin k) : ∑ i, A j i • v.val i = w.val j := by
      have hj := congrArg P.subtype (b.toBasis.sum_toMatrix_smul_self c.toBasis j)
      simpa only [A, Matrix.transpose_apply, map_sum, map_smul, Submodule.subtype_apply,
        OrthonormalBasis.coe_toBasis, b, c, coe_orthonormalBasisOfSpanEq_apply] using hj
    have hu : A ∈ unitaryGroup (Fin k) ℝ :=
      ((mem_stiefel_iff.1 v.property).orthonormal_sum_smul_iff_mem_unitaryGroup A).1
        ((funext hAv).symm ▸ mem_stiefel_iff.1 w.property)
    exact ⟨⟨A, hu⟩,
      Subtype.ext (funext fun j ↦ (coe_orthogonalGroup_smul_apply _ _ _).trans (hAv j))⟩
  · rintro ⟨A, rfl⟩
    exact (span_range_orthogonalGroup_smul A v).symm

/-- In their common span, an orthogonal change of basis preserves orientation when its determinant
is one and reverses orientation when its determinant is minus one. -/
theorem orientation_orthonormalBasisOfSpanEq_orthogonalGroup_smul
    (A : orthogonalGroup (Fin k) ℝ) (v : stiefel E k) :
    (orthonormalBasisOfSpanEq (A • v) (span_range_orthogonalGroup_smul A v)).toBasis.orientation =
      if A.val.det = 1 then (orthonormalBasisOfSpanEq v rfl).toBasis.orientation
      else -(orthonormalBasisOfSpanEq v rfl).toBasis.orientation := by
  let b := (orthonormalBasisOfSpanEq v rfl).toBasis
  let c := (orthonormalBasisOfSpanEq (A • v) (span_range_orthogonalGroup_smul A v)).toBasis
  have hc : (c : Fin k → span ℝ (range v.val)) = fun j ↦ ∑ i, A.val j i • b i := by
    funext j
    exact Subtype.ext (by simp [b, c])
  have hdet : b.det c = A.val.det := by
    rw [hc, AlternatingMap.map_sum_smul, Module.Basis.det_self, smul_eq_mul, mul_one]
  -- The two bases above both take values in the span of the original frame.
  change c.orientation = if A.val.det = 1 then b.orientation else -b.orientation
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup A.property with h | h
  · rw [ite_eq_left h]
    exact ((b.orientation_eq_iff_det_pos c).2 (by rw [hdet, h]; exact zero_lt_one)).symm
  · rw [ite_eq_right (h.trans_ne (by norm_num))]
    apply (b.orientation_ne_iff_eq_neg c.orientation).1
    intro hor
    have hpos := (b.orientation_eq_iff_det_pos c).1 hor.symm
    rw [hdet, h] at hpos
    norm_num at hpos

/-- A rotation of the frame preserves the induced orientation. -/
@[simp]
theorem orientedSpan_specialOrthogonalGroup_smul (A : specialOrthogonalGroup (Fin k) ℝ)
    (v : stiefel E k) : orientedSpan (A • v) = orientedSpan v := by
  rw [specialOrthogonalGroup_smul_def]
  let B := Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A
  have hB : B.val.det = 1 := (mem_specialUnitaryGroup_iff.1 A.property).2
  let P : {P : Submodule ℝ E // Module.rank ℝ P = (k : Cardinal)} :=
    ⟨span ℝ (range v.val), (orientedSpan v).1.property⟩
  rw [orientedSpan_eq_mk v P rfl,
    orientedSpan_eq_mk (B • v) P (span_range_orthogonalGroup_smul B v),
    orientation_orthonormalBasisOfSpanEq_orthogonalGroup_smul, ite_eq_left hB]

/-- Two orthonormal frames have equal oriented spans exactly when they are related by a
special orthogonal change of basis. -/
theorem orientedSpan_eq_iff {v w : stiefel E k} :
    orientedSpan v = orientedSpan w ↔ w ∈ MulAction.orbit (specialOrthogonalGroup (Fin k) ℝ) v := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hspan := congrArg (fun p : OrientedSubspace ℝ E k ↦ p.1.val) h
    obtain ⟨A, rfl⟩ := span_range_eq_iff_mem_orbit_orthogonalGroup.1 hspan
    have hdet : A.val.det = 1 := by
      by_contra hne
      let P : {P : Submodule ℝ E // Module.rank ℝ P = (k : Cardinal)} :=
        ⟨span ℝ (range v.val), (orientedSpan v).1.property⟩
      rw [orientedSpan_eq_mk v P rfl,
        orientedSpan_eq_mk (A • v) P (span_range_orthogonalGroup_smul A v),
        orientation_orthonormalBasisOfSpanEq_orthogonalGroup_smul, ite_eq_right hne] at h
      exact Module.Ray.ne_neg_self _ (eq_of_heq (Sigma.mk.inj h).2)
    exact ⟨⟨A.val, mem_specialUnitaryGroup_iff.2 ⟨A.property, hdet⟩⟩, rfl⟩
  · rintro ⟨A, rfl⟩
    exact (orientedSpan_specialOrthogonalGroup_smul A v).symm

end TauCeti.stiefel
