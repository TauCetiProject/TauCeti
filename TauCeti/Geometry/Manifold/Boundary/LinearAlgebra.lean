/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Model
public import TauCeti.LinearAlgebra.Orientation.Basis

/-!
# Determinants at the boundary hyperplane

A linear map preserving the boundary hyperplane has determinant equal to its normal factor
times the determinant of its restriction. This is the algebra behind outward-first orientation.
The linear model orientation is
characterized by prepending an outward vector, including in dimension zero.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open TauCeti

/-- The determinant splits into the normal factor and the boundary restriction determinant. -/
theorem det_eq_normal_mul_boundary {n : ℕ}
    (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {a : ℝ} (hA : ∀ v, A v 0 = a * v 0) :
    A.det = a * ((euclideanHalfSpaceBoundaryProj n).comp
      (A.comp (euclideanHalfSpaceBoundaryParam n))).det := by
  let b := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  let c := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let T := LinearMap.toMatrix b b A.toLinearMap
  have ht (i j : Fin (n + 1)) : T i j = A (b j) i := by
    simp [T, b, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  have hp (j : Fin n) : euclideanHalfSpaceBoundaryParam n (c j) = b j.succ := by
    ext i
    refine Fin.cases ?_ (fun k ↦ ?_) i <;>
      simp [b, c, EuclideanSpace.basisFun_apply]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
  -- Fold the chosen matrix T after changing the basis: the expansion theorem matches
  -- its determinant, while rewriting does not fold a local matrix abbreviation.
  change T.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hzero : ∀ j : Fin n, T 0 j.succ = 0 := by
    intro j
    rw [ht, hA]
    simp [b, EuclideanSpace.basisFun_apply]
  simp only [hzero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero,
    pow_zero, one_mul, Fin.succAbove_zero]
  have h00 : T 0 0 = a := by
    rw [ht, hA]
    simp [b, EuclideanSpace.basisFun_apply]
  rw [h00]
  congr 1
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix c]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, ht, LinearMap.toMatrix_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  rw [hp]
  simp [c, OrthonormalBasis.coe_toBasis_repr_apply]

end ContinuousLinearMap

namespace EuclideanSpace

open TauCeti

/-- The standard-basis determinant of the prepended family equals `v 0` times the
boundary family's standard-basis determinant. -/
theorem det_cons_boundary {n : ℕ} (v : EuclideanSpace ℝ (Fin (n + 1)))
    (w : Fin n → EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det
      (Fin.cons v (fun i ↦ euclideanHalfSpaceBoundaryParam n (w i))) =
        v 0 * (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det w := by
  rw [Module.Basis.det_apply, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, Fin.cons_succ, euclideanHalfSpaceBoundaryParam_apply_zero,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul,
    Fin.cons_zero, Fin.succAbove_zero]
  rw [Module.Basis.det_apply]
  congr 1
  congr 1
  ext i j
  simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]

end EuclideanSpace

namespace Orientation

open TauCeti

open Classical in
/-- The outward-first orientation on the coordinate-zero boundary of an oriented half-space. -/
def halfSpaceBoundaryOrientation {n : ℕ}
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Fin (n + 1))) :
    Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
  if o = (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation then
    -(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation
  else (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation

/-- The standard positive ambient basis induces the negative standard boundary orientation,
including in dimension zero. -/
@[simp]
theorem halfSpaceBoundaryOrientation_basisFun (n : ℕ) :
    halfSpaceBoundaryOrientation (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation =
      -(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation := by
  simp only [halfSpaceBoundaryOrientation, ↓reduceIte]

/-- Reversing the ambient model orientation reverses its boundary orientation. -/
@[simp]
theorem halfSpaceBoundaryOrientation_neg {n : ℕ}
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Fin (n + 1))) :
    halfSpaceBoundaryOrientation (-o) = -halfSpaceBoundaryOrientation o := by
  classical
  let e := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation
  let f := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation
  have heq : (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation = e := rfl
  have he : - -e = e := _root_.neg_neg e
  have hf : - -f = f := _root_.neg_neg f
  have hn : -e ≠ e := (Module.Ray.ne_neg_self e).symm
  rcases Orientation.eq_or_eq_neg o e (by simp) with h | h
  · simp only [halfSpaceBoundaryOrientation, h, heq,
      hn, ↓reduceIte]
    exact hf.symm
  · simp only [halfSpaceBoundaryOrientation, h, heq,
      he, hn, ↓reduceIte]


/-- The boundary model orientation is characterized by placing an outward vector first. -/
theorem halfSpaceBoundaryOrientation_spec {n : ℕ}
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Fin (n + 1)))
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : v 0 < 0)
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (b' : Module.Basis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (hb' : ⇑b' = Fin.cons v (fun i ↦ euclideanHalfSpaceBoundaryParam n (b i))) :
    b.orientation = halfSpaceBoundaryOrientation o ↔ b'.orientation = o := by
  classical
  let e := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  let f := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have heq : (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation =
      e.orientation := rfl
  have hd : e.det b' = v 0 * f.det b := by
    rw [hb']
    exact EuclideanSpace.det_cons_boundary v b
  have hp : b.orientation = f.orientation ↔ 0 < f.det b :=
    eq_comm.trans (f.orientation_eq_iff_det_pos b)
  have hp' : b'.orientation = e.orientation ↔ 0 < e.det b' :=
    eq_comm.trans (e.orientation_eq_iff_det_pos b')
  rcases e.orientation_eq_or_eq_neg o with h | h
  · rw [h]
    simp only [halfSpaceBoundaryOrientation, heq,
      ↓reduceIte]
    rw [← f.orientation_ne_iff_eq_neg, ne_comm, b.orientation_ne_iff_eq_neg,
      f.orientation_eq_neg_iff_det_neg b, hp', hd]
    exact (smul_pos_iff_of_neg_left hv).symm
  · rw [h]
    simp only [halfSpaceBoundaryOrientation, heq,
      (Module.Ray.ne_neg_self e.orientation).symm, ↓reduceIte]
    rw [hp, ← e.orientation_ne_iff_eq_neg, ne_comm, b'.orientation_ne_iff_eq_neg,
      e.orientation_eq_neg_iff_det_neg b', hd]
    exact (smul_neg_iff_of_neg_left hv).symm

end Orientation

namespace Orientation

/-- The actual half-space boundary orientation changes the relative standard-basis sign by
minus one in every dimension, including dimension zero. -/
theorem signBasis_halfSpaceBoundaryOrientation {n : ℕ}
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Fin (n + 1))) :
    Orientation.signBasis (halfSpaceBoundaryOrientation o)
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis =
      -Orientation.signBasis o (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis := by
  rcases (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation_eq_or_eq_neg o with h | h
  · rw [h]
    simp
  · rw [h]
    simp only [halfSpaceBoundaryOrientation_neg, halfSpaceBoundaryOrientation_basisFun,
      Orientation.signBasis_neg, Orientation.signBasis_orientation]

end Orientation
