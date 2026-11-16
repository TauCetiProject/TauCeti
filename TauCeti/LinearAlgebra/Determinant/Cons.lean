/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Determinants of families with a distinguished first vector

Let `b` be a basis of `M` indexed by `Fin (m + 1)`. This file computes the determinant in `b` of
families that single out the first basis vector `b 0`.

* If the remaining vectors `b l.succ` are the images `f (b' l)` of a basis `b'` of a module `N`
  under a linear map `f : N → M`, then a family made of a multiple `a • b 0` followed by images
  `f (v l)` has determinant `a` times the determinant of `v` in `b'`
  (`Module.Basis.det_cons_smul_comp`). Inserting `b 0` at the position `p` instead multiplies the
  determinant of `v` by the sign `(-1) ^ p` of moving it to the front
  (`Module.Basis.det_insertNth_comp`). This is the determinant of a block diagonal family, in a
  basis split as the line through `b 0` and the image of `b'`, without assuming `f` injective.
* Adding multiples `t l • x` of a first vector `x` to the remaining basis vectors `b l.succ` does
  not change the determinant, which is then the coordinate of `x` along `b 0`
  (`Module.Basis.det_cons_add_smul`). This is the determinant of a unitriangular change of basis
  when `x` has coordinate `1` along `b 0`.

These are the changes of basis by which a based chain complex splits off an elementary two-term
complex, as in the cancellation of a pair of generators joined by an invertible entry of the
differential.
-/

public section

namespace Module.Basis

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {m : ℕ} (b : Basis (Fin (m + 1)) R M)

section Comp

variable (b' : Basis (Fin m) R N) {f : N →ₗ[R] M}

/-- If the basis vectors `b l.succ` are the images `f (b' l)` of a basis `b'`, the determinant in
`b` of the family `a • b 0, f (v 0), …, f (v (m - 1))` is `a` times the determinant of `v` in
`b'`. -/
theorem det_cons_smul_comp (hb : ∀ l, b l.succ = f (b' l)) (a : R) (v : Fin m → N) :
    b.det (Fin.cons (a • b 0) (f ∘ v)) = a * b'.det v := by
  -- With its first argument `b 0` fixed, `b.det` precomposed with `f` is an alternating map on
  -- `N` taking the value `1` on `b'`, so it is `b'.det`.
  have h₁ : (b.det.curryLeft (b 0)).compLinearMap f b' = 1 := by
    rw [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply, Matrix.vecCons]
    convert b.det_self
    ext l
    induction l using Fin.cases <;> simp [hb]
  have h₂ := ((b.det.curryLeft (b 0)).compLinearMap f).eq_smul_basis_det b'
  rw [h₁, one_smul] at h₂
  calc b.det (Fin.cons (a • b 0) (f ∘ v)) = b.det.curryLeft (a • b 0) (f ∘ v) := by
        rw [AlternatingMap.curryLeft_apply_apply, Matrix.vecCons]
    _ = a * (b.det.curryLeft (b 0)).compLinearMap f v := by
        rw [map_smul, smul_apply, smul_eq_mul, AlternatingMap.compLinearMap_apply,
          Function.comp_def]
    _ = a * b'.det v := by rw [h₂]

/-- If the basis vectors `b l.succ` are the images `f (b' l)` of a basis `b'`, inserting `b 0` at
the position `p` into the family `f ∘ v` gives a family whose determinant in `b` is `(-1) ^ p`
times the determinant of `v` in `b'`. -/
theorem det_insertNth_comp (hb : ∀ l, b l.succ = f (b' l)) (p : Fin (m + 1)) (v : Fin m → N) :
    b.det (p.insertNth (b 0) (f ∘ v)) = (-1) ^ (p : ℕ) * b'.det v := by
  rw [AlternatingMap.map_insertNth, Matrix.vecCons, ← one_smul R (b 0),
    det_cons_smul_comp b b' hb, one_mul]
  simp

end Comp

/-- Adding multiples `t l • x` of a vector `x` to the basis vectors `b l.succ` gives, after `x`
itself, a family whose determinant in `b` is the coordinate of `x` along `b 0`. In particular it
is `1` when `x = b 0`. -/
theorem det_cons_add_smul (x : M) (t : Fin m → R) :
    b.det (Fin.cons x fun l ↦ b l.succ + t l • x) = b.repr x 0 := by
  classical
  -- In coordinates, the columns `l.succ` are those of the identity plus `t l` times the column of
  -- `x`; subtracting these multiples leaves a lower triangular matrix with diagonal `x 0, 1, …, 1`.
  let B : Matrix (Fin (m + 1)) (Fin (m + 1)) R := b.toMatrix (Fin.cons x fun l ↦ b l.succ)
  rw [det_apply, ← Matrix.det_transpose,
    Matrix.det_eq_of_forall_row_eq_smul_add_const (B := B.transpose) (Fin.cons 0 t) 0 rfl ?_,
    Matrix.det_transpose, Matrix.det_of_isLowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp [B, Basis.toMatrix_apply]
  · intro r k hrk
    induction k using Fin.cases with
    | zero => exact absurd hrk (Fin.not_lt_zero _)
    | succ k =>
      simp only [B, Basis.toMatrix_apply, Fin.cons_succ, repr_self, Finsupp.single_apply]
      exact ite_eq_right_iff.2 fun h ↦ absurd (h ▸ hrk) (lt_irrefl _)
  · intro r k
    induction r using Fin.cases <;> simp [B, Basis.toMatrix_apply]

end Module.Basis
