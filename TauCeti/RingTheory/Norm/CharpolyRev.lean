/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.LinearAlgebra.Charpoly.Projective
public import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# The norm along a line and the reversed characteristic polynomial

For an `R`-algebra `S`, possibly noncommutative, with a finite basis `b` and an element `w : S`,
the norm of `1 - t w` is the reversed characteristic polynomial `det (1 - X M)` evaluated at `t`,
where `M` is the matrix of left multiplication by `w`. This turns the norm restricted to the line
`t ↦ 1 - t w` into a polynomial in `t` whose low-degree coefficients are known: its constant term
is `1` (`Matrix.eval_charpolyRev`) and its linear coefficient is `-tr M`
(`Matrix.coeff_charpolyRev_eq_neg_trace`).

For finite projective algebras, the reversed characteristic polynomial of multiplication
is invariant under algebra isomorphisms and commutes with maps of the scalar algebra.
These comparisons allow its coefficients to be descended to rings of invariant functions.

## Main results

* `TauCeti.Algebra.eval_charpolyRev_leftMulMatrix`: along the line `t ↦ 1 - t w`, the norm is
  the reversed characteristic polynomial of multiplication by `w`.
* `AlgEquiv.projectiveCharpolyRev_lmul`: invariance under algebra isomorphisms.
* `AlgHom.projectiveCharpolyRev_lmul_rTensor`: arbitrary base change of the scalar algebra.

The scalar-extension comparison follows `Algebra.projectiveNorm_rTensor`.
-/

public section

open Polynomial

namespace TauCeti

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]

/-- The norm along the line `t ↦ 1 - t w` is the reversed characteristic polynomial
`det (1 - X M)` of the matrix `M` of left multiplication by `w`, evaluated at `t`. -/
theorem Algebra.eval_charpolyRev_leftMulMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) (w : S) (t : R) :
    (Algebra.leftMulMatrix b w).charpolyRev.eval t = Algebra.norm R (1 - t • w) := by
  simp [Matrix.charpolyRev, eval_det, ← Matrix.smul_eq_mul_diagonal,
    Algebra.norm_eq_matrix_det b]

end TauCeti

open scoped TensorProduct

namespace AlgEquiv

variable {R S T : Type*} [CommRing R] [Ring S] [Ring T] [Algebra R S] [Algebra R T]
  [Module.Finite R S] [Module.Projective R S] [Module.Finite R T] [Module.Projective R T]

/-- The reversed characteristic polynomial of multiplication is invariant under an algebra
isomorphism of finite projective algebras. -/
theorem projectiveCharpolyRev_lmul (e : S ≃ₐ[R] T) (x : S) :
    LinearMap.projectiveCharpolyRev (Algebra.lmul R T (e x)) =
      LinearMap.projectiveCharpolyRev (Algebra.lmul R S x) := by
  simpa using LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq e.toLinearEquiv
    (f := Algebra.lmul R S x) (g := Algebra.lmul R T (e x)) (fun y ↦ by simp)

end AlgEquiv

namespace AlgHom

variable {R S A A' : Type*} [CommRing R] [Ring S] [Algebra R S]
  [Module.Finite R S] [Module.Projective R S] [CommRing A] [Algebra R A]
  [CommRing A'] [Algebra R A']

/-- The reversed characteristic polynomial of multiplication on a scalar extension commutes
with an arbitrary map of the scalar algebra. -/
theorem projectiveCharpolyRev_lmul_rTensor (φ : A →ₐ[R] A') (x : A ⊗[R] S) :
    LinearMap.projectiveCharpolyRev
        (Algebra.lmul A' (A' ⊗[R] S) (Algebra.TensorProduct.rTensor S φ x)) =
      (LinearMap.projectiveCharpolyRev (Algebra.lmul A (A ⊗[R] S) x)).map φ := by
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R A A' := .of_algebraMap_eq fun a ↦ (φ.commutes a).symm
  let e := (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv R A S A').symm
  have hx : e (Algebra.TensorProduct.rTensor S φ x) = (1 : A') ⊗ₜ[A] x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      have : φ a = a • (1 : A') := by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      simp [e, this, TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  rw [← e.projectiveCharpolyRev_lmul, hx, ← Algebra.baseChange_lmul,
    LinearMap.projectiveCharpolyRev_baseChange]
  rfl

end AlgHom
