/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Continuous oriented volume forms

This file packages Mathlib's oriented volume form as a continuous alternating map.  The
construction is shared by the manifold Riemannian volume form and the planar complex area form.

It also evaluates the volume form on an arbitrary, not necessarily orthonormal, family of vectors:
its absolute value is the square root of the Gram determinant, and on a basis its sign records
whether the basis is positively oriented. In a coordinate frame of a Riemannian manifold this is
the familiar formula `vol = ±√(det g) dx¹ ∧ ⋯ ∧ dxⁿ`.

Finally, two oriented inner product spaces of the same positive finite dimension are related by an
orientation-preserving linear isometric equivalence
(`Orientation.exists_linearIsometryEquiv_map_eq`). So every orientation of an inner product space
is transported from a given orientation of a model space by some orthonormal frame.
-/

public section

noncomputable section

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (Module.finrank ℝ E = n)]

/-- Mathlib's oriented volume form, equipped with its norm bound as a continuous map. -/
def volumeFormL (o : Orientation ℝ E (Fin n)) : E [⋀^Fin n]→L[ℝ] ℝ :=
  o.volumeForm.mkContinuous 1 fun v ↦ by
    simpa only [Real.norm_eq_abs, one_mul] using o.abs_volumeForm_apply_le v

/-- Evaluation of `volumeFormL` is the underlying oriented volume form. -/
@[simp]
theorem volumeFormL_apply (o : Orientation ℝ E (Fin n)) (v : Fin n → E) :
    o.volumeFormL v = o.volumeForm v := (rfl)

/-- `volumeFormL` evaluates to one on a positively oriented orthonormal basis. -/
theorem volumeFormL_apply_orthonormal (o : Orientation ℝ E (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation = o) :
    o.volumeFormL b = 1 := by
  rw [volumeFormL_apply, o.volumeForm_robust b hb]
  exact b.toBasis.det_self

/-- A top form taking value one on an oriented orthonormal basis is the volume form. -/
theorem eq_volumeFormL_of_apply_orthonormal (o : Orientation ℝ E (Fin n))
    (ω : E [⋀^Fin n]→L[ℝ] ℝ) (b : OrthonormalBasis (Fin n) ℝ E)
    (hb : b.toBasis.orientation = o) (hω : ω b = 1) :
    ω = o.volumeFormL := by
  have hω' : ω b.toBasis = 1 := by
    simpa only [OrthonormalBasis.coe_toBasis] using hω
  ext v
  rw [ContinuousAlternatingMap.apply_eq_det_mul ω b.toBasis, hω', mul_one,
    volumeFormL_apply, o.volumeForm_robust b hb]

/-- **The volume of a family of vectors is the square root of its Gram determinant**, up to
sign: `|vol v| = √(det ⟪vᵢ, vⱼ⟫)`. -/
theorem abs_volumeForm_apply_eq_sqrt_det_gram (o : Orientation ℝ E (Fin n)) (v : Fin n → E) :
    |o.volumeForm v| = √(Matrix.gram ℝ v).det := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  let b : OrthonormalBasis (Fin (n + 1)) ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)
  -- In the orthonormal basis `b`, the Gram matrix of `v` is `Aᵀ A` for the coordinate matrix `A`.
  have hA : b.toBasis.toMatrix v = Matrix.of fun i j ↦ b.repr (v j) i := by
    ext i j
    simp [Module.Basis.toMatrix_apply]
  rw [o.volumeForm_robust' b, Module.Basis.det_apply, Matrix.gram_eq_conjTranspose_mul b,
    Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, Real.sqrt_mul_self_eq_abs, hA]

/-- The volume form is positive on a basis exactly when the basis is positively oriented. -/
theorem volumeForm_apply_pos_iff {o : Orientation ℝ E (Fin n)} {b : Module.Basis (Fin n) ℝ E} :
    0 < o.volumeForm b ↔ b.orientation = o := by
  rcases n with - | n
  · rw [b.orientation_isEmpty]
    refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl
    · simp
    · simp only [volumeForm_zero_neg, neg_apply,
        AlternatingMap.constLinearEquivOfIsEmpty_apply, AlternatingMap.constOfIsEmpty_apply,
        Left.neg_pos_iff]
      exact iff_of_false (by norm_num) (Module.Ray.ne_neg_self _)
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  let f := ((stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)).adjustToOrientation o
  rw [o.volumeForm_robust f (OrthonormalBasis.orientation_adjustToOrientation _ _),
    ← Module.Basis.orientation_eq_iff_det_pos, OrthonormalBasis.orientation_adjustToOrientation,
    eq_comm]

/-- The volume of a positively oriented basis is the square root of its Gram determinant. -/
theorem volumeForm_apply_eq_sqrt_det_gram (o : Orientation ℝ E (Fin n))
    (b : Module.Basis (Fin n) ℝ E) (hb : b.orientation = o) :
    o.volumeForm b = √(Matrix.gram ℝ b).det := by
  rw [← abs_of_pos (volumeForm_apply_pos_iff.2 hb), abs_volumeForm_apply_eq_sqrt_det_gram]

/-- The volume of a negatively oriented basis is minus the square root of its Gram determinant. -/
theorem volumeForm_apply_eq_neg_sqrt_det_gram (o : Orientation ℝ E (Fin n))
    (b : Module.Basis (Fin n) ℝ E) (hb : b.orientation ≠ o) :
    o.volumeForm b = -√(Matrix.gram ℝ b).det := by
  have hb' : b.orientation = -o := by
    rw [(b.orientation_ne_iff_eq_neg o).1 (Ne.symm hb)]
    exact (neg_neg b.orientation).symm
  have h := (-o).volumeForm_apply_eq_sqrt_det_gram b hb'
  rwa [volumeForm_neg_orientation, neg_apply, neg_eq_iff_eq_neg] at h

section LinearIsometryEquiv

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup W]
  [InnerProductSpace ℝ W] {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Two oriented real inner product spaces of the same positive finite dimension are related by an
orientation-preserving linear isometric equivalence: it carries a positively oriented orthonormal
basis of one to a positively oriented orthonormal basis of the other. -/
theorem exists_linearIsometryEquiv_map_eq (hV : Module.finrank ℝ V = Fintype.card ι)
    (hW : Module.finrank ℝ W = Fintype.card ι) (o : Orientation ℝ V ι) (o' : Orientation ℝ W ι) :
    ∃ φ : V ≃ₗᵢ[ℝ] W, Orientation.map ι φ.toLinearEquiv o = o' := by
  classical
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (hV ▸ Fintype.card_pos)
  have : FiniteDimensional ℝ W := Module.finite_of_finrank_pos (hW ▸ Fintype.card_pos)
  let bV₀ := (stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq hV.symm).symm
  let bW₀ := (stdOrthonormalBasis ℝ W).reindex (Fintype.equivFinOfCardEq hW.symm).symm
  let φ := (bV₀.adjustToOrientation o).equiv (bW₀.adjustToOrientation o') (Equiv.refl ι)
  have hmap : (bV₀.adjustToOrientation o).toBasis.map φ.toLinearEquiv =
      (bW₀.adjustToOrientation o').toBasis :=
    Module.Basis.eq_of_apply_eq fun i ↦ by simp [φ]
  refine ⟨φ, ?_⟩
  rw [← bV₀.orientation_adjustToOrientation o, ← Module.Basis.orientation_map, hmap,
    bW₀.orientation_adjustToOrientation]

end LinearIsometryEquiv

end Orientation
