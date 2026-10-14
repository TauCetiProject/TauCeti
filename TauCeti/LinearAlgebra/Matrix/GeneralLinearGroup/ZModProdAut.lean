/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.Fin
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis

/-!
# `GL₂(ℤ/Nℤ)` is the automorphism group of `(ℤ/Nℤ)²`

Every additive map between `ℤ/Nℤ`-modules is `ℤ/Nℤ`-linear (`ZMod.map_smul`), so the group
automorphisms of `(ℤ/Nℤ)²` are its linear automorphisms, and those are the invertible `2 × 2`
matrices over `ℤ/Nℤ` in the standard basis (`Module.Basis.toGL`). The group `(ℤ/Nℤ)²` is written
multiplicatively, as `Multiplicative (ZMod N × ZMod N)`, as for the homomorphisms out of it in
`TauCeti.zmodProdMonoidHomEquiv`.

A matrix `g = !![a, b; c, d]` acts on column vectors, `(x, y) ↦ (a x + b y, c x + d y)`
(`TauCeti.zmodProdMulAutEquiv_apply`). Precomposing a homomorphism `φ : (ℤ/Nℤ)² →* G` with this
automorphism replaces the pair `(P, Q) = (φ (1, 0), φ (0, 1))` by `(aP + cQ, bP + dQ)`: it is the
right action of `g` on the row vector `(P, Q)`, the convention used by Katz and Mazur for level
structures on elliptic curves.

## Main definitions

* `TauCeti.zmodProdMulAutEquiv N`: the group isomorphism `GL₂(ℤ/Nℤ) ≃* Aut((ℤ/Nℤ)²)`.

## Main results

* `TauCeti.zmodProdMulAutEquiv_apply`: the automorphism of a matrix is multiplication of column
  vectors by it.
* `TauCeti.coe_zmodProdMulAutEquiv_symm_apply`: the matrix of an automorphism `σ` has columns
  `σ (1, 0)` and `σ (0, 1)`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.1 and §7.1, for the action of
  `GL₂(ℤ/Nℤ)` on level structures.
-/

public section

open scoped MatrixGroups

namespace TauCeti

variable (N : ℕ)

/-- **`GL₂(ℤ/Nℤ)` is the automorphism group of `(ℤ/Nℤ)²`.** An invertible matrix acts on
`(ℤ/Nℤ)²` by multiplication of column vectors (`zmodProdMulAutEquiv_apply`), and every group
automorphism of `(ℤ/Nℤ)²` arises from a unique invertible matrix, whose columns are the images of
`(1, 0)` and `(0, 1)` (`coe_zmodProdMulAutEquiv_symm_apply`). -/
noncomputable def zmodProdMulAutEquiv :
    GL (Fin 2) (ZMod N) ≃* MulAut (Multiplicative (ZMod N × ZMod N)) where
  toFun g := AddEquiv.toMultiplicative ((Module.Basis.finTwoProd (ZMod N)).toGL.symm g).toAddEquiv
  invFun σ := (Module.Basis.finTwoProd (ZMod N)).toGL
    { AddEquiv.toMultiplicative.symm σ with
      map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm σ) }
  left_inv g := (congrArg _ (LinearEquiv.ext fun _ ↦ by simp)).trans (MulEquiv.apply_symm_apply _ g)
  right_inv _ := MulEquiv.ext fun _ ↦ by simp
  map_mul' _ _ := MulEquiv.ext fun _ ↦ by simp

variable {N}

/-- The automorphism of `(ℤ/Nℤ)²` of an invertible matrix `g` is multiplication of column vectors
by `g`: it sends `(x, y)` to `(g₀₀ x + g₀₁ y, g₁₀ x + g₁₁ y)`. -/
@[simp]
theorem zmodProdMulAutEquiv_apply (g : GL (Fin 2) (ZMod N)) (x y : ZMod N) :
    zmodProdMulAutEquiv N g (.ofAdd (x, y)) =
      .ofAdd (g 0 0 * x + g 0 1 * y, g 1 0 * x + g 1 1 * y) := by
  simp [zmodProdMulAutEquiv]

/-- The matrix of an automorphism `σ` of `(ℤ/Nℤ)²` has columns the images `σ (1, 0)` and
`σ (0, 1)` of the standard basis vectors. -/
@[simp]
theorem coe_zmodProdMulAutEquiv_symm_apply (σ : MulAut (Multiplicative (ZMod N × ZMod N))) :
    ((zmodProdMulAutEquiv N).symm σ : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      !![(σ (.ofAdd (1, 0))).toAdd.1, (σ (.ofAdd (0, 1))).toAdd.1;
        (σ (.ofAdd (1, 0))).toAdd.2, (σ (.ofAdd (0, 1))).toAdd.2] := by
  obtain ⟨g, rfl⟩ := (zmodProdMulAutEquiv N).surjective σ
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end TauCeti
