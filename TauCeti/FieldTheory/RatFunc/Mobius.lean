/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.FieldTheory.RatFunc.Automorphism

/-!
# Linear fractional transformations of the rational function field

Four elements `a, b, c, d` of a field `k` with `a d - b c ≠ 0` give the linear fractional
transformation `(a X + b) / (c X + d)` of `k(X)`. The inverse of the coefficient matrix recovers
`X` from it, so it is a transcendental generator of `k(X)` over `k` and therefore the image of `X`
under an automorphism of `k(X)` over `k`.

The coefficients form an invertible `2 × 2` matrix, and conversely every invertible `2 × 2` matrix
over `k` has nonzero determinant, so the construction applies to `GL₂(k)`.

## Main definitions

* `RatFunc.mobiusOf`: the linear fractional transformation of four coefficients, with its defining
  equation `mobiusOf_def`.
* `RatFunc.mobiusAutOf`: the automorphism of `k(X)` sending `X` to it.
* `RatFunc.mobius` (with `mobius_def`) and `RatFunc.mobiusAut`: the same for an invertible
  matrix.
* `RatFunc.mobiusAutHom`: the group homomorphism `GL₂(k) →* Aut(k(X)/k)`.
* `RatFunc.translationAut`: the translation `X ↦ X + c`.

## Main results

* `RatFunc.transcendental_mobiusOf` and `RatFunc.adjoin_mobiusOf_eq_top`: a linear fractional
  transformation is a transcendental generator of `k(X)`.
* `RatFunc.X_eq_div_mobiusOf`: the inverse coefficient matrix recovers `X`.
* `RatFunc.mobiusAut_mobius` and `RatFunc.mobiusAutHom`: substitution composes the coefficient
  matrices in the opposite order, so inversion turns the construction into a group homomorphism
  `GL₂(k) →* Aut(k(X)/k)`.
* `RatFunc.infinite_algEquiv`: over an infinite field the translations already make
  `Aut(k(X)/k)` infinite.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Exercise 1.2.
-/

public section

open scoped MatrixGroups

namespace RatFunc

variable {K : Type*} [Field K]

/-- A nonzero linear polynomial in `X`, read in `k(X)`, is nonzero. -/
theorem mul_X_add_C_ne_zero {c d : K} (hcd : c ≠ 0 ∨ d ≠ 0) : C c * X + C d ≠ 0 := by
  have hmap : C c * X + C d =
      algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
    rw [map_add, map_mul, algebraMap_C, algebraMap_C, algebraMap_X]
  rw [hmap, Ne, map_eq_zero_iff _ (algebraMap_injective K)]
  intro h0
  have h1 : c = 0 := by simpa using congrArg (fun p : Polynomial K ↦ p.coeff 1) h0
  have h0' : d = 0 := by simpa using congrArg (fun p : Polynomial K ↦ p.coeff 0) h0
  rcases hcd with h | h
  · exact h h1
  · exact h h0'

/-- **A constant lies in every intermediate field** of `k(X) / k`. -/
theorem C_mem (S : IntermediateField K (RatFunc K)) (x : K) : C x ∈ S := by
  rw [← algebraMap_eq_C]
  exact IntermediateField.algebraMap_mem _ x

/-- A constant of `k(X)` is nonzero when the scalar is. -/
theorem C_ne_zero {x : K} (hx : x ≠ 0) : (C x : RatFunc K) ≠ 0 := by
  rw [← algebraMap_eq_C, Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K (RatFunc K))]
  exact hx

/-- An automorphism of `k(X)` over `k` fixes the constants. -/
@[simp]
theorem algEquiv_apply_C (σ : RatFunc K ≃ₐ[K] RatFunc K) (x : K) : σ (C x) = C x := by
  rw [← algebraMap_eq_C]
  exact σ.commutes x

section MobiusOf

variable (a b c d : K)

/-- The **linear fractional transformation** `(a X + b) / (c X + d)` of `k(X)`. -/
noncomputable def mobiusOf : RatFunc K := (C a * X + C b) / (C c * X + C d)

/-- The defining equation of `mobiusOf`. -/
theorem mobiusOf_def : mobiusOf a b c d = (C a * X + C b) / (C c * X + C d) := (rfl)

variable {a b c d} (hdet : a * d - b * c ≠ 0)
include hdet

/-- The denominator of a linear fractional transformation with invertible coefficients is
nonzero. -/
theorem mobiusOf_den_ne_zero : C c * X + C d ≠ 0 := by
  refine mul_X_add_C_ne_zero ?_
  by_contra h
  simp only [not_or, not_not] at h
  exact hdet (by rw [h.1, h.2]; ring)

/-- Clearing the denominator of a linear fractional transformation. -/
theorem mobiusOf_mul_den : mobiusOf a b c d * (C c * X + C d) = C a * X + C b :=
  div_mul_cancel₀ _ (mobiusOf_den_ne_zero hdet)

/-- The coefficient `a - c · m` scaled by the denominator is the determinant. -/
theorem sub_mul_mobiusOf_mul_den :
    (C a - C c * mobiusOf a b c d) * (C c * X + C d) = C (a * d - b * c) := by
  have h := mobiusOf_mul_den hdet
  rw [map_sub, map_mul, map_mul]
  linear_combination (-(C c)) * h

/-- **The coefficient `a - c · m` is nonzero**, being the determinant over the denominator. -/
theorem sub_mul_mobiusOf_ne_zero : C a - C c * mobiusOf a b c d ≠ 0 := by
  intro h0
  refine C_ne_zero hdet ?_
  rw [← sub_mul_mobiusOf_mul_den hdet, h0, zero_mul]

/-- **The inverse coefficient matrix recovers `X`**: `X · (a - c · m) = d · m - b`, both sides
being the determinant times `X` over the denominator. -/
theorem X_mul_sub_mul_mobiusOf :
    (X : RatFunc K) * (C a - C c * mobiusOf a b c d) = C d * mobiusOf a b c d - C b := by
  refine mul_right_cancel₀ (mobiusOf_den_ne_zero hdet) ?_
  have h := mobiusOf_mul_den hdet
  linear_combination (-(C c * X + C d)) * h

/-- **`X` is a linear fractional transformation of `m`**, by the inverse coefficient matrix. -/
theorem X_eq_div_mobiusOf :
    (X : RatFunc K) =
      (C d * mobiusOf a b c d - C b) / (C a - C c * mobiusOf a b c d) :=
  (eq_div_iff (sub_mul_mobiusOf_ne_zero hdet)).mpr (X_mul_sub_mul_mobiusOf hdet)

/-- **A linear fractional transformation generates `k(X)`**, since `X` is a linear fractional
transformation of it. -/
theorem adjoin_mobiusOf_eq_top : IntermediateField.adjoin K {mobiusOf a b c d} = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← adjoin_X]
  refine IntermediateField.adjoin_simple_le_iff.mpr ?_
  rw [X_eq_div_mobiusOf hdet]
  exact div_mem
    (sub_mem (mul_mem (C_mem _ _) (IntermediateField.mem_adjoin_simple_self _ _))
      (C_mem _ _))
    (sub_mem (C_mem _ _)
      (mul_mem (C_mem _ _) (IntermediateField.mem_adjoin_simple_self _ _)))

/-- **A linear fractional transformation is transcendental**, being a generator of `k(X)`. -/
theorem transcendental_mobiusOf : Transcendental K (mobiusOf a b c d) :=
  transcendental_of_adjoin_eq_top (adjoin_mobiusOf_eq_top hdet)

/-- **The automorphism of `k(X)` given by a linear fractional transformation**: the automorphism
sending `X` to `(a X + b) / (c X + d)`. -/
noncomputable def mobiusAutOf : RatFunc K ≃ₐ[K] RatFunc K :=
  algEquivOfAdjoinEqTop (adjoin_mobiusOf_eq_top hdet)

@[simp]
theorem mobiusAutOf_X : mobiusAutOf hdet X = mobiusOf a b c d :=
  algEquivOfAdjoinEqTop_X _

section Comp

variable {a' b' c' d' : K} (hdet' : a' * d' - b' * c' ≠ 0)
include hdet hdet'

/-- The determinant of a product of coefficient matrices is the product of the determinants, so it
is nonzero. -/
theorem det_comp_ne_zero :
    (a' * a + b' * c) * (c' * b + d' * d) - (a' * b + b' * d) * (c' * a + d' * c) ≠ 0 := by
  intro h
  exact mul_ne_zero hdet' hdet (by linear_combination h)

omit hdet' in
/-- Substituting a linear fractional transformation into another is a linear fractional
transformation, with the product coefficient matrix: the denominator. -/
theorem mul_mobiusOf_add_mul_den :
    (C c' * mobiusOf a b c d + C d') * (C c * X + C d) =
      C (c' * a + d' * c) * X + C (c' * b + d' * d) := by
  have hm := mobiusOf_mul_den hdet
  simp only [map_add, map_mul]
  linear_combination (C c') * hm

/-- The denominator of the substituted transformation is nonzero. -/
theorem mul_mobiusOf_add_ne_zero : C c' * mobiusOf a b c d + C d' ≠ 0 := by
  intro h0
  refine mobiusOf_den_ne_zero (det_comp_ne_zero hdet hdet') ?_
  rw [← mul_mobiusOf_add_mul_den hdet, h0, zero_mul]

/-- **Substitution composes linear fractional transformations by multiplying their coefficient
matrices in the opposite order.** -/
theorem mobiusAutOf_mobiusOf :
    mobiusAutOf hdet (mobiusOf a' b' c' d') =
      mobiusOf (a' * a + b' * c) (a' * b + b' * d) (c' * a + d' * c) (c' * b + d' * d) := by
  have hm := mobiusOf_mul_den hdet
  have hsub : mobiusAutOf hdet (mobiusOf a' b' c' d') =
      (C a' * mobiusOf a b c d + C b') / (C c' * mobiusOf a b c d + C d') := by
    rw [mobiusOf, map_div₀, map_add, map_add, map_mul, map_mul, algEquiv_apply_C,
      algEquiv_apply_C, algEquiv_apply_C, algEquiv_apply_C, mobiusAutOf_X]
  rw [hsub]
  conv_rhs => rw [mobiusOf]
  rw [div_eq_div_iff (mul_mobiusOf_add_ne_zero hdet hdet')
    (mobiusOf_den_ne_zero (det_comp_ne_zero hdet hdet'))]
  simp only [map_add, map_mul]
  linear_combination (C a' * C d' - C b' * C c') * hm

end Comp

end MobiusOf

section GeneralLinear

variable (A : GL (Fin 2) K)

/-- The determinant of an invertible `2 × 2` matrix, in terms of its entries. -/
theorem det_entries_ne_zero :
    (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
  rw [← Matrix.det_fin_two]
  exact Matrix.GeneralLinearGroup.det_ne_zero A

/-- The **linear fractional transformation of an invertible matrix** `A = !![a, b; c, d]`. -/
noncomputable def mobius : RatFunc K :=
  mobiusOf ((A : Matrix (Fin 2) (Fin 2) K) 0 0) ((A : Matrix (Fin 2) (Fin 2) K) 0 1)
    ((A : Matrix (Fin 2) (Fin 2) K) 1 0) ((A : Matrix (Fin 2) (Fin 2) K) 1 1)

/-- The defining equation of `mobius`. -/
theorem mobius_def : mobius A =
    mobiusOf ((A : Matrix (Fin 2) (Fin 2) K) 0 0) ((A : Matrix (Fin 2) (Fin 2) K) 0 1)
      ((A : Matrix (Fin 2) (Fin 2) K) 1 0) ((A : Matrix (Fin 2) (Fin 2) K) 1 1) := (rfl)

/-- The automorphism of `k(X)` given by an invertible matrix. -/
noncomputable def mobiusAut : RatFunc K ≃ₐ[K] RatFunc K :=
  mobiusAutOf (det_entries_ne_zero A)

@[simp]
theorem mobiusAut_X : mobiusAut A X = mobius A :=
  mobiusAutOf_X _

/-- **Substituting one linear fractional transformation into another multiplies the matrices in
the opposite order.** -/
theorem mobiusAut_mobius (B : GL (Fin 2) K) : mobiusAut A (mobius B) = mobius (B * A) := by
  rw [mobiusAut, mobius_def, mobius_def,
    mobiusAutOf_mobiusOf (det_entries_ne_zero A) (det_entries_ne_zero B)]
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- The identity matrix gives the identity transformation. -/
@[simp]
theorem mobius_one : mobius (1 : GL (Fin 2) K) = X := by
  rw [mobius, mobiusOf]
  simp

/-- **The linear fractional transformations as a group of automorphisms**: the homomorphism
`GL₂(k) →* Aut(k(X)/k)` sending `A` to the automorphism `X ↦ (a X + b) / (c X + d)` of the inverse
matrix. Inversion is what makes it a homomorphism rather than an antihomomorphism, since
substitution composes the matrices in the opposite order. -/
noncomputable def mobiusAutHom : GL (Fin 2) K →* (RatFunc K ≃ₐ[K] RatFunc K) where
  toFun A := mobiusAut A⁻¹
  map_one' := algEquiv_ext (by simp)
  map_mul' A B := algEquiv_ext (by
    rw [AlgEquiv.mul_apply, mobiusAut_X, mobiusAut_X, mobiusAut_mobius, mul_inv_rev])

@[simp]
theorem mobiusAutHom_apply_X : mobiusAutHom A X = mobius A⁻¹ :=
  mobiusAut_X _

end GeneralLinear

section Translation

variable (b : K)

/-- A translation `X + c` is a linear fractional transformation. -/
theorem mobiusOf_one_right (c : K) : mobiusOf 1 c 0 1 = X + C c := by
  rw [mobiusOf]
  simp

/-- The **translation automorphism** `X ↦ X + c` of `k(X)`. -/
noncomputable def translationAut : RatFunc K ≃ₐ[K] RatFunc K :=
  mobiusAutOf (a := 1) (b := b) (c := 0) (d := 1) (by simp)

@[simp]
theorem translationAut_X : translationAut b X = X + C b := by
  rw [translationAut, mobiusAutOf_X, mobiusOf_one_right]

/-- Distinct scalars give distinct translations. -/
theorem translationAut_injective : Function.Injective (translationAut : K → _) := by
  intro b₁ b₂ h
  have hX := congrArg (fun σ : RatFunc K ≃ₐ[K] RatFunc K ↦ σ X) h
  simp only [translationAut_X, add_right_inj] at hX
  exact (FaithfulSMul.algebraMap_injective K (RatFunc K)) (by rwa [algebraMap_eq_C])

/-- **The automorphism group of `k(X)` over an infinite field is infinite**, witnessed by the
translations. This is why the finiteness of the automorphism group of a function field needs genus
at least two. -/
theorem infinite_algEquiv [Infinite K] : Infinite (RatFunc K ≃ₐ[K] RatFunc K) :=
  Infinite.of_injective _ (translationAut_injective (K := K))

end Translation

end RatFunc
