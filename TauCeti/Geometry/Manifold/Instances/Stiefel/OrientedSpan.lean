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

/-!
# Oriented spans of Stiefel frames

A frame orients its span by its ordered basis. Two frames give the same oriented span exactly
when they differ by a rotation. In positive rank every oriented subspace occurs as such a span.
-/

public section

noncomputable section

open Matrix Module Set Submodule

namespace TauCeti.stiefel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-- The span of a frame with the orientation given by its ordered basis. -/
def orientedSpan (v : stiefel E k) : OrientedSubspace E k :=
  ⟨⟨span ℝ (range v.val), finrank_span_range v⟩,
    (orthonormalBasisOfSpanEq v rfl).toBasis.orientation⟩

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
theorem orientedSpan_eq_mk (v : stiefel E k) (P : {P : Submodule ℝ E // finrank ℝ P = k})
    (hP : span ℝ (range v.val) = P.val) :
    orientedSpan v = ⟨P, (orthonormalBasisOfSpanEq v hP).toBasis.orientation⟩ := by
  obtain ⟨P, hdim⟩ := P
  simp only at hP
  subst P
  rfl

/-- The empty frame selects the positive sign of the zero plane. -/
@[simp]
theorem orientedSubspaceZeroEquiv_orientedSpan [Module.Finite ℝ E] (v : stiefel E 0) :
    orientedSubspaceZeroEquiv (orientedSpan v) = true := by
  symm
  apply orientedSubspaceZeroEquiv.symm_apply_eq.1
  rw [orientedSubspaceZeroEquiv_symm_true, orientedSpan_eq_mk v ⟨⊥, by simp⟩ (by simp)]
  rw [Module.Basis.orientation_isEmpty]

/-- At positive rank every orientation of a plane is realized by an orthonormal basis. -/
theorem surjective_orientedSpan [NeZero k] :
    Function.Surjective (orientedSpan : stiefel E k → OrientedSubspace E k) := by
  rintro ⟨⟨P, hdim⟩, o⟩
  let : FiniteDimensional ℝ P := Module.finite_of_finrank_pos (hdim ▸ Nat.pos_of_ne_zero
    (NeZero.ne k))
  let b := ((stdOrthonormalBasis ℝ P).reindex (finCongr hdim)).adjustToOrientation o
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

/-- A rotation of the frame preserves the induced orientation. -/
@[simp]
theorem orientedSpan_specialOrthogonalGroup_smul (A : specialOrthogonalGroup (Fin k) ℝ)
    (v : stiefel E k) : orientedSpan (A • v) = orientedSpan v := by
  let P : {P : Submodule ℝ E // finrank ℝ P = k} := ⟨_, finrank_span_range v⟩
  let b := orthonormalBasisOfSpanEq v rfl
  let c := orthonormalBasisOfSpanEq (A • v) (span_range_specialOrthogonalGroup_smul A v)
  have hc : (c.toBasis : Fin k → P.val) = fun j ↦ ∑ i, A.val j i • b.toBasis i := by
    funext j
    exact Subtype.ext (by simp [b, c])
  have hdet : b.toBasis.det c.toBasis = 1 := by
    rw [hc, AlternatingMap.map_sum_smul, Module.Basis.det_self, smul_eq_mul, mul_one]
    exact (mem_specialUnitaryGroup_iff.1 A.property).2
  have hor : b.toBasis.orientation = c.toBasis.orientation :=
    (b.toBasis.orientation_eq_iff_det_pos c.toBasis).2 (hdet ▸ zero_lt_one)
  rw [orientedSpan_eq_mk v P rfl,
    orientedSpan_eq_mk (A • v) P (span_range_specialOrthogonalGroup_smul A v), ← hor]

/-- Two orthonormal frames have equal oriented spans exactly when they are related by a
special orthogonal change of basis. -/
theorem orientedSpan_eq_iff {v w : stiefel E k} :
    orientedSpan v = orientedSpan w ↔ w ∈ MulAction.orbit (specialOrthogonalGroup (Fin k) ℝ) v := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · let P : {P : Submodule ℝ E // finrank ℝ P = k} := ⟨_, finrank_span_range v⟩
    have hw : span ℝ (range w.val) = P.val :=
      congrArg (fun p : OrientedSubspace E k ↦ p.1.val) h.symm
    let b := orthonormalBasisOfSpanEq v (P := P.val) rfl
    let c := orthonormalBasisOfSpanEq w hw
    have hor : b.toBasis.orientation = c.toBasis.orientation := by
      rw [orientedSpan_eq_mk v P rfl, orientedSpan_eq_mk w P hw] at h
      exact eq_of_heq (Sigma.mk.inj h).2
    let A := (b.toBasis.toMatrix c.toBasis)ᵀ
    have hAv (j : Fin k) : ∑ i, A j i • v.val i = w.val j := by
      have hj := congrArg P.val.subtype (b.toBasis.sum_toMatrix_smul_self c.toBasis j)
      simpa only [A, Matrix.transpose_apply, map_sum, map_smul, Submodule.subtype_apply,
        OrthonormalBasis.coe_toBasis, b, c, coe_orthonormalBasisOfSpanEq_apply] using hj
    have hu : A ∈ unitaryGroup (Fin k) ℝ :=
      ((mem_stiefel_iff.1 v.property).orthonormal_sum_smul_iff_mem_unitaryGroup A).1
        ((funext hAv).symm ▸ mem_stiefel_iff.1 w.property)
    have hd : A.det = 1 := by
      rw [Matrix.det_transpose, ← Module.Basis.det_apply]
      exact b.det_to_matrix_orthonormalBasis_of_same_orientation c hor
    exact ⟨⟨A, mem_specialUnitaryGroup_iff.2 ⟨hu, hd⟩⟩,
      Subtype.ext (funext fun j ↦ (coe_specialOrthogonalGroup_smul_apply _ _ _).trans (hAv j))⟩
  · rintro ⟨A, rfl⟩
    exact (orientedSpan_specialOrthogonalGroup_smul A v).symm


end TauCeti.stiefel
