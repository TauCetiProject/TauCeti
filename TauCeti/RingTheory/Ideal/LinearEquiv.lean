/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The split sum map of two comaximal ideals

For ideals `I` and `J` of a commutative ring with `i + j = 1`, `i ∈ I`, `j ∈ J`, the sum map
`I × J → R`, `(x, y) ↦ x + y` is onto with kernel the antidiagonal copy of `I ⊓ J`, and
`r ↦ (i r, j r)` splits it. This gives an isomorphism `I × J ≃ R × (I ⊓ J)`, a submodule
counterpart of the Chinese remainder isomorphism `Ideal.quotientInfEquivQuotientProd`.

## Main definitions

* `Ideal.prodEquivProdInf`: for ideals `I`, `J` and `i ∈ I`, `j ∈ J` with `i + j = 1`, the
  isomorphism `I × J ≃ R × (I ⊓ J)`, `(x, y) ↦ (x + y, j x - i y)`.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R] {I J : Ideal R} {i j : R}

/-- For ideals `I` and `J` with `i ∈ I`, `j ∈ J` and `i + j = 1`, the sum map `I × J → R` splits
with kernel `I ⊓ J`: the map `(x, y) ↦ (x + y, j x - i y)` is an isomorphism
`I × J ≃ R × (I ⊓ J)`, with inverse `(r, z) ↦ (i r + z, j r - z)`. -/
def prodEquivProdInf (hi : i ∈ I) (hj : j ∈ J) (hij : i + j = 1) :
    (I × J) ≃ₗ[R] R × ↥(I ⊓ J) where
  toFun x := (x.1 + x.2, ⟨j * x.1 - i * x.2,
    sub_mem ⟨I.mul_mem_left j x.1.2, J.mul_mem_right _ hj⟩
      ⟨I.mul_mem_right _ hi, J.mul_mem_left i x.2.2⟩⟩)
  invFun y := (⟨i * y.1 + y.2, add_mem (I.mul_mem_right _ hi) (mem_inf.1 y.2.2).1⟩,
    ⟨j * y.1 - y.2, sub_mem (J.mul_mem_right _ hj) (mem_inf.1 y.2.2).2⟩)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp <;> ring
  left_inv x := by
    ext
    · simp; linear_combination (x.1 : R) * hij
    · simp; linear_combination (x.2 : R) * hij
  right_inv y := by
    ext
    · simp; linear_combination y.1 * hij
    · simp; linear_combination (y.2 : R) * hij

@[simp]
theorem prodEquivProdInf_apply_fst (hi : i ∈ I) (hj : j ∈ J) (hij : i + j = 1) (x : I × J) :
    (prodEquivProdInf hi hj hij x).1 = x.1 + x.2 :=
  (rfl)

@[simp]
theorem coe_prodEquivProdInf_apply_snd (hi : i ∈ I) (hj : j ∈ J) (hij : i + j = 1) (x : I × J) :
    ((prodEquivProdInf hi hj hij x).2 : R) = j * x.1 - i * x.2 :=
  (rfl)

@[simp]
theorem coe_prodEquivProdInf_symm_apply_fst (hi : i ∈ I) (hj : j ∈ J) (hij : i + j = 1)
    (y : R × ↥(I ⊓ J)) : (((prodEquivProdInf hi hj hij).symm y).1 : R) = i * y.1 + y.2 :=
  (rfl)

@[simp]
theorem coe_prodEquivProdInf_symm_apply_snd (hi : i ∈ I) (hj : j ∈ J) (hij : i + j = 1)
    (y : R × ↥(I ⊓ J)) : (((prodEquivProdInf hi hj hij).symm y).2 : R) = j * y.1 - y.2 :=
  (rfl)

end Ideal
