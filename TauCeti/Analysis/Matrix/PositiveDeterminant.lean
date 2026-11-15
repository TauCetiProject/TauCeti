/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.ContDiff
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smooth paths of real matrices with positive determinant

Over any nontrivially normed field, a special-linear matrix admits a smooth determinant-one
family from the identity, parameterized by the field.

Every real matrix with positive determinant is joined to the identity by a smooth family of
matrices with positive determinant, defined on all of `ℝ`. First use generation by elementary
transvections to construct a determinant-one family. Then restore the determinant by multiplying
one coordinate by `exp (t * log (det A))`. This also covers the zero-dimensional space.

Such families give linear isotopies fixing the origin, the linear step in the disc theorem.

The algebraic input is the transvection generation theorem
`Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field`.
Reference: M. Hirsch, *Differential Topology*, Chapter 4, §6, Theorem 6.6.
-/

public section

open scoped ContDiff Matrix.Norms.Elementwise

namespace Matrix.SpecialLinearGroup

-- `SpecialLinearGroup`, matrix identity and determinant require decidable equality
-- while elaborating the theorem statement.
variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]

/-- A special-linear matrix over a nontrivially normed field admits a smooth matrix family
from the identity whose determinant is one for every parameter in the field. -/
theorem exists_contDiff_det_eq_one (A : SpecialLinearGroup ι 𝕜) :
    ∃ γ : 𝕜 → Matrix ι ι 𝕜, ContDiff 𝕜 ∞ γ ∧ γ 0 = 1 ∧ γ 1 = A ∧
      ∀ t, (γ t).det = 1 := by
  have hA : A ∈ Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct ι 𝕜 → SpecialLinearGroup ι 𝕜)) := by
    rw [closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top A
  induction hA using Subgroup.closure_induction with
  | mem A hA =>
    obtain ⟨T, rfl⟩ := hA
    refine ⟨fun t => Matrix.transvection T.i T.j (t * T.c), ?_, ?_, ?_, ?_⟩
    · apply contDiff_pi.mpr
      intro i
      apply contDiff_pi.mpr
      intro j
      simp only [Matrix.transvection, Matrix.add_apply, Matrix.single, Matrix.of_apply]
      split_ifs <;> fun_prop
    · simp
    · simp only [one_mul, TransvectionStruct.toSpecialLinearGroup_coe,
        TransvectionStruct.toMatrix]
    · intro t
      exact det_transvection_of_ne _ _ T.hij _
  | one => exact ⟨fun _ => 1, contDiff_const, rfl, rfl, fun _ => det_one⟩
  | mul A B _ _ hA hB =>
    obtain ⟨γ, hγ, hγ0, hγ1, hγdet⟩ := hA
    obtain ⟨δ, hδ, hδ0, hδ1, hδdet⟩ := hB
    exact ⟨fun t => γ t * δ t, hγ.matrix_mul hδ, by simp [hγ0, hδ0],
      by simp [hγ1, hδ1], fun t => by simp [det_mul, hγdet, hδdet]⟩
  | inv A _ hA =>
    obtain ⟨γ, hγ, hγ0, hγ1, hγdet⟩ := hA
    refine ⟨fun t => γ (1 - t) * (↑(A⁻¹) : Matrix ι ι 𝕜),
      (hγ.comp (contDiff_const.sub contDiff_id)).matrix_mul contDiff_const, ?_, ?_, ?_⟩
    · simp only [sub_zero, hγ1, ← coe_mul, mul_inv_cancel, coe_one]
    · simp only [sub_self, hγ0, one_mul]
    · intro t
      rw [det_mul, hγdet, (A⁻¹).property, one_mul]

end Matrix.SpecialLinearGroup

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real matrix with positive determinant is joined to the identity by a smooth family
with positive determinant at every real parameter. No positive-dimensional assumption is needed. -/
theorem exists_contDiff_det_pos (A : Matrix ι ι ℝ) (hA : 0 < A.det) :
    ∃ γ : ℝ → Matrix ι ι ℝ, ContDiff ℝ ∞ γ ∧ γ 0 = 1 ∧ γ 1 = A ∧
      ∀ t, 0 < (γ t).det := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have h : A = 1 := Subsingleton.elim _ _
    exact ⟨fun _ => 1, contDiff_const, rfl, h.symm, fun _ => by simp⟩
  | inr hι =>
    let i : ι := Classical.choice hι
    let D : ℝ → Matrix ι ι ℝ := fun t =>
      diagonal (fun j => if j = i then Real.exp (t * Real.log A.det) else 1)
    have hDdet (t : ℝ) : (D t).det = Real.exp (t * Real.log A.det) := by
      simp [D, det_diagonal, Finset.prod_ite_eq']
    have hD0 : D 0 = 1 := by
      ext j k
      simp [D, diagonal_apply, Matrix.one_apply]
    have hD1 : (D 1).det = A.det := by
      simp [hDdet, Real.exp_log hA]
    have hD : ContDiff ℝ ∞ D := by
      apply contDiff_pi.mpr
      intro j
      apply contDiff_pi.mpr
      intro k
      simp only [D, diagonal_apply]
      split_ifs <;> fun_prop
    let B : SpecialLinearGroup ι ℝ := ⟨(D 1)⁻¹ * A, by
      rw [det_mul, det_nonsing_inv, hD1, Ring.inverse_eq_inv]
      exact inv_mul_cancel₀ hA.ne'⟩
    obtain ⟨δ, hδ, hδ0, hδ1, hδdet⟩ := B.exists_contDiff_det_eq_one
    refine ⟨fun t => D t * δ t, hD.matrix_mul hδ, ?_, ?_, ?_⟩
    · simp [hD0, hδ0]
    · dsimp only
      rw [hδ1]
      -- The subtype constructor defining `B` has the chosen matrix as its value.
      dsimp [B]
      rw [← mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hD1 ▸ hA.ne')),
        one_mul]
    · intro t
      simp [det_mul, hδdet, hDdet, Real.exp_pos]

end Matrix
