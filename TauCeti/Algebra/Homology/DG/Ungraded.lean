/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.CharP.Two
public import TauCeti.Algebra.Homology.DG.Twisted.Continuation
public import TauCeti.LinearAlgebra.Matrix.Kronecker.Basic

/-!
# Ungraded differential algebras and modules, and matrices over them

An **ungraded differential algebra** is an `R`-algebra `A` with an `R`-linear map `d` which
squares to zero and satisfies the Leibniz rule `d (a * b) = d a * b + a * d b` with no sign
(`TauCeti.IsUngradedDGAlgebra`). An **ungraded differential right module** over it is a right
`A`-module `M`, written as a module over `Aᵐᵒᵖ`, with a square-zero `R`-linear map `dM` such that
`dM (m * a) = dM m * a + m * d a` (`TauCeti.IsUngradedDGRightModule`).

These are the algebraic objects of bordered Heegaard Floer homology over `𝔽₂`, whose strands
algebras are graded by noncommutative groups rather than by `ℤ`. Tau Ceti's differential
graded algebras (`TauCeti.IsDGAlgebra`) are internally `ℤ`-graded with a differential of degree
one, so an ungraded differential does not fit them: placing an algebra in degree zero forces the
differential to vanish. Over a ring of characteristic two the Koszul signs of the graded theory
all disappear, which is why the ungraded Leibniz rule is the right one there.

The differential acts on matrices over `A` entrywise, through `Matrix.map`, and satisfies the
Leibniz rule for matrix products (`TauCeti.IsUngradedDGAlgebra.map_mul_matrix`) and for the action
`TauCeti.continuationMap` of matrices on row vectors with entries in a right module
(`TauCeti.IsUngradedDGRightModule.map_continuationMap`). Matrices are how type `D` structures and
their morphisms are written in a basis.

The tensor product `A ⊗[R] B` of two algebras with ungraded differentials `d` and `d'` carries the
differential `d ⊗ 1 + 1 ⊗ d'` (`TauCeti.ungradedTensorDifferential`). It always satisfies the
Leibniz rule, and over a ring of characteristic two, where the Koszul sign of the graded tensor
product disappears, it also squares to zero (`TauCeti.IsUngradedDGAlgebra.tensorProduct`). This is
the algebra over which bordered Heegaard Floer homology writes its type `DD` bimodules.

## Main definitions

* `TauCeti.IsUngradedDGAlgebra`: an ungraded differential on an algebra.
* `TauCeti.IsUngradedDGRightModule`: an ungraded differential on a right module.
* `TauCeti.ungradedTensorDifferential`: the differential `d ⊗ 1 + 1 ⊗ d'` of a tensor product.

## Main results

* `TauCeti.IsUngradedDGAlgebra.isUngradedDGRightModule`: an ungraded differential algebra is an
  ungraded differential right module over itself.
* `TauCeti.IsUngradedDGAlgebra.map_mul_matrix`: `d (F * G) = d F * G + F * d G` for matrices.
* `TauCeti.IsUngradedDGRightModule.map_continuationMap`: `dM (φ ⬝ F) = dM φ ⬝ F + φ ⬝ d F`.
* `TauCeti.IsUngradedDGAlgebra.tensorProduct`: in characteristic two, the tensor product of
  ungraded differential algebras is an ungraded differential algebra.
* `Matrix.kroneckerTMul_map_ungradedTensorDifferential`: `d (F ⊗ₖₜ G) = d F ⊗ₖₜ G + F ⊗ₖₜ d' G`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (differential algebras and modules over `𝔽₂`).
* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), 525–724, [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), §2.2
  (type `DD` structures as type `D` structures over a tensor product of algebras).
-/

public section

open MulOpposite

namespace TauCeti

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- `d` is an **ungraded differential** on the `R`-algebra `A`: it squares to zero and satisfies
the Leibniz rule `d (a * b) = d a * b + a * d b`, with no sign. -/
structure IsUngradedDGAlgebra (d : A →ₗ[R] A) : Prop where
  /-- The Leibniz rule. -/
  map_mul (a b : A) : d (a * b) = d a * b + a * d b
  /-- The differential squares to zero. -/
  map_map (a : A) : d (d a) = 0

/-- `dM` is an **ungraded differential** on the right `A`-module `M` over the ungraded
differential `d` of `A`: it squares to zero and satisfies `dM (m * a) = dM m * a + m * d a`, the
right action being written `MulOpposite.op a • m`. -/
structure IsUngradedDGRightModule [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
    (d : A →ₗ[R] A) (dM : M →ₗ[R] M) : Prop where
  /-- The Leibniz rule for the right action. -/
  map_smul (a : A) (m : M) : dM (op a • m) = op a • dM m + op (d a) • m
  /-- The differential squares to zero. -/
  map_map (m : M) : dM (dM m) = 0

namespace IsUngradedDGAlgebra

variable {d : A →ₗ[R] A}

/-- The differential of an ungraded differential algebra kills the unit. -/
@[simp]
theorem map_one (hd : IsUngradedDGAlgebra d) : d 1 = 0 := by
  have h := hd.map_mul 1 1
  simp only [mul_one, one_mul] at h
  simpa using h

/-- An ungraded differential algebra is an ungraded differential right module over itself. -/
theorem isUngradedDGRightModule (hd : IsUngradedDGAlgebra d) : IsUngradedDGRightModule d d where
  map_smul a b := by simp [hd.map_mul]
  map_map := hd.map_map

variable {m n o : Type*}

/-- **The Leibniz rule for matrices.** The entrywise differential of a product of matrices is
`d (F * G) = d F * G + F * d G`. -/
theorem map_mul_matrix [Fintype n] (hd : IsUngradedDGAlgebra d) (F : Matrix m n A)
    (G : Matrix n o A) :
    (F * G).map d = F.map d * G + F * G.map d := by
  ext x z
  simp [Matrix.mul_apply, hd.map_mul, Finset.sum_add_distrib]

/-- The entrywise differential of a matrix squares to zero. -/
theorem map_map_matrix (hd : IsUngradedDGAlgebra d) (F : Matrix m n A) :
    (F.map d).map d = 0 := by
  ext x y
  simp [hd.map_map]

end IsUngradedDGAlgebra


namespace IsUngradedDGRightModule

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] {d : A →ₗ[R] A} {dM : M →ₗ[R] M} {m n : Type*}
  [Fintype m]

/-- **The Leibniz rule for the action of matrices.** Applying the differential to the row vector
`φ ⬝ F = continuationMap R M F φ` gives `dM φ ⬝ F + φ ⬝ d F`. -/
theorem map_continuationMap (hM : IsUngradedDGRightModule d dM) (φ : m → M) (F : Matrix m n A)
    (y : n) :
    dM (continuationMap R M F φ y) =
      continuationMap R M F (fun x => dM (φ x)) y + continuationMap R M (F.map d) φ y := by
  simp [continuationMap_apply (R := R) (M := M) F,
    continuationMap_apply (R := R) (M := M) (F.map d), hM.map_smul, Finset.sum_add_distrib]

end IsUngradedDGRightModule

/-! ### Tensor products -/

section TensorProduct

open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- The differential `d ⊗ 1 + 1 ⊗ d'` on the tensor product `A ⊗[R] B` of two algebras with
differentials `d` and `d'`, with no Koszul sign. It satisfies the Leibniz rule
(`TauCeti.ungradedTensorDifferential_mul`), and in characteristic two it is an ungraded
differential (`TauCeti.IsUngradedDGAlgebra.tensorProduct`). -/
noncomputable def ungradedTensorDifferential (d : A →ₗ[R] A) (d' : B →ₗ[R] B) :
    A ⊗[R] B →ₗ[R] A ⊗[R] B :=
  TensorProduct.map d LinearMap.id + TensorProduct.map LinearMap.id d'

@[simp]
theorem ungradedTensorDifferential_tmul (d : A →ₗ[R] A) (d' : B →ₗ[R] B) (a : A) (b : B) :
    ungradedTensorDifferential d d' (a ⊗ₜ b) = d a ⊗ₜ b + a ⊗ₜ d' b := by
  simp [ungradedTensorDifferential]

/-- **The Leibniz rule on a tensor product.** If `d` and `d'` satisfy the ungraded Leibniz rule,
then so does `d ⊗ 1 + 1 ⊗ d'`; no hypothesis on the characteristic is needed. -/
theorem ungradedTensorDifferential_mul {d : A →ₗ[R] A} {d' : B →ₗ[R] B}
    (hd : ∀ a a', d (a * a') = d a * a' + a * d a')
    (hd' : ∀ b b', d' (b * b') = d' b * b' + b * d' b') (x y : A ⊗[R] B) :
    ungradedTensorDifferential d d' (x * y) =
      ungradedTensorDifferential d d' x * y + x * ungradedTensorDifferential d d' y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [add_mul, map_add, hx, hx']
    abel
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [mul_add, map_add, hy, hy']
      abel
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, ungradedTensorDifferential_tmul, hd, hd',
        add_mul, mul_add, TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel

/-- **The tensor product of ungraded differential algebras.** Over a ring of characteristic two,
`d ⊗ 1 + 1 ⊗ d'` is an ungraded differential on `A ⊗[R] B`. Its square is `2 (d ⊗ d')`, which is
why the characteristic matters. -/
theorem IsUngradedDGAlgebra.tensorProduct [CharP R 2] {d : A →ₗ[R] A} {d' : B →ₗ[R] B}
    (hd : IsUngradedDGAlgebra d) (hd' : IsUngradedDGAlgebra d') :
    IsUngradedDGAlgebra (ungradedTensorDifferential d d') where
  map_mul := ungradedTensorDifferential_mul hd.map_mul hd'.map_mul
  map_map x := by
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp only [map_add, hx, hx', add_zero]
    | tmul a b =>
      simp only [ungradedTensorDifferential_tmul, map_add, hd.map_map, hd'.map_map,
        TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add, add_zero]
      exact add_self_eq_zero_of_charTwo R _

end TensorProduct

end TauCeti

namespace Matrix

open scoped Kronecker TensorProduct

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- **The Leibniz rule for Kronecker products.** The entrywise differential `d ⊗ 1 + 1 ⊗ d'` of
the Kronecker product `F ⊗ₖₜ G` of matrices over `A` and over `B` is `d F ⊗ₖₜ G + F ⊗ₖₜ d' G`. -/
@[simp]
theorem kroneckerTMul_map_ungradedTensorDifferential {l m n p : Type*} {d : A →ₗ[R] A}
    {d' : B →ₗ[R] B} (F : Matrix l m A) (G : Matrix n p B) :
    (F ⊗ₖₜ[R] G).map (TauCeti.ungradedTensorDifferential d d') =
      F.map d ⊗ₖₜ[R] G + F ⊗ₖₜ[R] G.map d' := by
  ext ⟨i, k⟩ ⟨j, o⟩
  simp

end Matrix
