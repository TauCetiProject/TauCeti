/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Homology.HomologicalComplex.Basic
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Schur complement of a cancelled differential

Let `φ : D ⟶ C` be a chain map of homological complexes of modules over a commutative ring `R`,
with ordered bases `ci`, `ci'` of `C` and `ei`, `ei'` of `D` in degrees `i` and `i'`. Suppose `φ`
sends each `ei l` to `ci l.succ` up to a multiple of `ci 0`, and each `ei' l` to `ci' l.succ` up
to a multiple of `d (ci 0)`, where the `(0, 0)`-entry `a` of the matrix of `C.d i i'` is
invertible. Writing this matrix in block form `[[a, v], [w, N]]`, the matrix of `D.d i i'` in the
bases `ei`, `ei'` is the Schur complement `N - w · ⅟a · v`
(`HomologicalComplex.toMatrix_d_eq_of_cancel_of_invertible`). Over a field `F`, invertibility is
simply nonvanishing of the `(0, 0)`-entry, giving `N - w · a⁻¹ · v`
(`HomologicalComplex.toMatrix_d_eq_of_cancel`).

This is the algebraic cancellation formula for differentials of based complexes of any shape over
commutative rings (such as Novikov rings with unit pivots) as well as fields; see
`TauCeti.Algebra.Homology.ReidemeisterTorsion.Cancellation` for the accompanying acyclicity and
two-periodic Reidemeister torsion identities.

## Main results

* `HomologicalComplex.toMatrix_d_eq_of_cancel_of_invertible`: over a commutative ring, the matrix of
  the cancelled differential is the Schur complement of an invertible `(0, 0)`-entry.
* `HomologicalComplex.toMatrix_d_eq_of_cancel`: the same over a field, for a nonzero `(0, 0)`-entry.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  209–244, §3.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), 221–311.
-/

public section

open CategoryTheory Module

namespace HomologicalComplex

variable {ι : Type*} {rel : ComplexShape ι} {i i' : ι} {m m' : ℕ}

/-- **The cancelled differential is the Schur complement, over a commutative ring.** For any chain
map `φ : D ⟶ C` of homological complexes of modules over a commutative ring `R` and ordered bases
`ci, ci'` of `C` and `ei, ei'` of `D` in degrees `i` and `i'`, if `φ` sends `ei l` to `ci l.succ`
up to a multiple of `ci 0` and `ei' l` to `ci' l.succ` up to a multiple of `d (ci 0)`, and the
`(0, 0)`-entry `a` of the matrix of `C.d i i'` is invertible, then the matrix of `D.d i i'` in
`ei, ei'` is the Schur complement `N - w · ⅟a · v`. In the matrix of `C.d i i'` in `ci, ci'`,
`v` is the rest of row zero, `w` is the rest of column zero, and `N` is the block on successor
rows and columns. -/
theorem toMatrix_d_eq_of_cancel_of_invertible {R : Type*} [CommRing R]
    {C D : HomologicalComplex (ModuleCat R) rel} {φ : D ⟶ C}
    {ci : Basis (Fin (m + 1)) R (C.X i)} {ci' : Basis (Fin (m' + 1)) R (C.X i')}
    {ei : Basis (Fin m) R (D.X i)} {ei' : Basis (Fin m') R (D.X i')}
    [Invertible (LinearMap.toMatrix ci ci' (C.d i i').hom 0 0)]
    (hφ : ∀ l, (φ.f i).hom (ei l) - ci l.succ ∈ R ∙ ci 0)
    (hφ' : ∀ l, (φ.f i').hom (ei' l) - ci' l.succ ∈ R ∙ (C.d i i').hom (ci 0)) :
    LinearMap.toMatrix ei ei' (D.d i i').hom = Matrix.of fun r k ↦
      LinearMap.toMatrix ci ci' (C.d i i').hom r.succ k.succ -
        LinearMap.toMatrix ci ci' (C.d i i').hom r.succ 0 *
          ⅟(LinearMap.toMatrix ci ci' (C.d i i').hom 0 0) *
            LinearMap.toMatrix ci ci' (C.d i i').hom 0 k.succ := by
  let a := LinearMap.toMatrix ci ci' (C.d i i').hom 0 0
  have ha : ci'.repr ((C.d i i').hom (ci 0)) 0 = a :=
    (LinearMap.toMatrix_apply ci ci' (C.d i i').hom 0 0).symm
  -- The coordinate-recovery lemma uses the basis form of the same pivot and inverse.
  let : Invertible (ci'.repr ((C.d i i').hom (ci 0)) 0) :=
    (inferInstance : Invertible a).copy _ ha
  have hmul : ci'.repr ((C.d i i').hom (ci 0)) 0 * ⅟a = 1 := by rw [ha, mul_invOf_self]
  have hinv : ⅟(ci'.repr ((C.d i i').hom (ci 0)) 0) = ⅟a := invOf_eq_right_inv hmul
  refine Matrix.ext fun r k ↦ ?_
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (hφ k)
  have hφe : (φ.f i).hom (ei k) = ci k.succ + t • ci 0 := by rw [ht, add_sub_cancel]
  have h := ei'.repr_eq_sub_mul_invOf_mul ci' (φ.f i').hom (Fin.succ_injective _)
    Fin.succ_ne_zero hφ' ((D.d i i').hom (ei k)) r
  have hcomm := (Hom.comm_apply φ i i' (ei k)).symm
  rw [hinv, hcomm, hφe] at h
  simp only [LinearMap.toMatrix_apply, Matrix.of_apply, h, map_add, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  linear_combination -t * (ci'.repr ((C.d i i').hom (ci 0)) r.succ) * hmul

/-- **The cancelled differential is the Schur complement, over a field.** Specialization of
`HomologicalComplex.toMatrix_d_eq_of_cancel_of_invertible` to a field `F`, where invertibility of
the `(0, 0)`-entry reduces to nonvanishing. -/
theorem toMatrix_d_eq_of_cancel {F : Type*} [Field F]
    {C D : HomologicalComplex (ModuleCat F) rel} {φ : D ⟶ C}
    {ci : Basis (Fin (m + 1)) F (C.X i)} {ci' : Basis (Fin (m' + 1)) F (C.X i')}
    {ei : Basis (Fin m) F (D.X i)} {ei' : Basis (Fin m') F (D.X i')}
    (hφ : ∀ l, (φ.f i).hom (ei l) - ci l.succ ∈ F ∙ ci 0)
    (hφ' : ∀ l, (φ.f i').hom (ei' l) - ci' l.succ ∈ F ∙ (C.d i i').hom (ci 0))
    (ha : ci'.repr ((C.d i i').hom (ci 0)) 0 ≠ 0) :
    LinearMap.toMatrix ei ei' (D.d i i').hom = Matrix.of fun r k ↦
      LinearMap.toMatrix ci ci' (C.d i i').hom r.succ k.succ -
        LinearMap.toMatrix ci ci' (C.d i i').hom r.succ 0 *
          (LinearMap.toMatrix ci ci' (C.d i i').hom 0 0)⁻¹ *
            LinearMap.toMatrix ci ci' (C.d i i').hom 0 k.succ := by
  let : Invertible (LinearMap.toMatrix ci ci' (C.d i i').hom 0 0) :=
    invertibleOfNonzero (by simpa [LinearMap.toMatrix_apply] using ha)
  simpa only [invOf_eq_inv] using toMatrix_d_eq_of_cancel_of_invertible hφ hφ'

end HomologicalComplex
