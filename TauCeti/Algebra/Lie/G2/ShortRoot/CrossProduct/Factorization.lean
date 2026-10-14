/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Unitriangular

/-!
# Ordered positive-root factors for the short-root G₂ cross product

The six-coordinate upper-unitriangular normal form factors uniquely into six one-parameter
matrices, in the order α₁, α₂, α₁ + α₂, 2α₁ + α₂, 3α₁ + α₂, 3α₁ + 2α₂.
The first two factors are the numbered raising root elements. The remaining factors use the
coordinate-axis normalization of `crossUnipotentMatrix`; their signs need not agree with
root vectors obtained by iterated Lie brackets.

The polynomial factorization works over every commutative ring. In particular, it uses no
inversion of three, so it supplies the coordinate step for identifying the upper-unitriangular
intersection of the characteristic-three carrier with its positive subgroup. It does not
assert containment of the six factors in that positive subgroup.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--28 (ordered root-subgroup products).
* The coordinates are those of
  `TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Unitriangular`.
-/

public section

open Matrix

namespace TauCeti.G2ShortRoot

variable {R : Type*} [CommRing R]

/-- The coordinate-axis positive root matrices, ordered as α₁, α₂, α₁ + α₂,
2α₁ + α₂, 3α₁ + α₂, 3α₁ + 2α₂ in Bourbaki numbering. -/
def positiveRootMatrix (i : Fin 6) (t : R) : Matrix (Fin 7) (Fin 7) R :=
  ![crossUnipotentMatrix t 0 0 0 0 0, crossUnipotentMatrix 0 t 0 0 0 0,
    crossUnipotentMatrix 0 0 t 0 0 0, crossUnipotentMatrix 0 0 0 t 0 0,
    crossUnipotentMatrix 0 0 0 0 t 0, crossUnipotentMatrix 0 0 0 0 0 t] i

/-- The positive root matrices are the six axes of the cross-product normal form. -/
theorem positiveRootMatrix_def (i : Fin 6) (t : R) :
    positiveRootMatrix i t =
      ![crossUnipotentMatrix t 0 0 0 0 0, crossUnipotentMatrix 0 t 0 0 0 0,
        crossUnipotentMatrix 0 0 t 0 0 0, crossUnipotentMatrix 0 0 0 t 0 0,
        crossUnipotentMatrix 0 0 0 0 t 0, crossUnipotentMatrix 0 0 0 0 0 t] i :=
  (rfl)

/-- Each coordinate-axis root matrix at parameter zero is the identity. -/
@[simp]
theorem positiveRootMatrix_zero (i : Fin 6) : positiveRootMatrix i (0 : R) = 1 := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [positiveRootMatrix_def, crossUnipotentMatrix_def]

/-- Multiplication in the six-coordinate normal form is polynomial over the base ring. -/
theorem crossUnipotentMatrix_mul (a b c d e f a' b' c' d' e' f' : R) :
    crossUnipotentMatrix a b c d e f * crossUnipotentMatrix a' b' c' d' e' f' =
      crossUnipotentMatrix (a + a') (b + b') (c + c' + a * b')
        (d + d' + a * (a' * b' - c') + c * a')
        (e + e' + a * (a' ^ 2 * b' - a' * c' - d') + c * a' ^ 2 + 2 * d * a')
        (f + f' + a * (a' * b' * c' - c' ^ 2 - b' * d') +
          c * (a' * c' - d') + 2 * d * c' + e * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossUnipotentMatrix_def, Matrix.mul_apply, Fin.sum_univ_seven] <;> ring

/-- Each coordinate-axis root matrix is additive in its parameter. -/
theorem positiveRootMatrix_add (i : Fin 6) (s t : R) :
    positiveRootMatrix i (s + t) = positiveRootMatrix i s * positiveRootMatrix i t := by
  fin_cases i <;> simp [positiveRootMatrix_def, crossUnipotentMatrix_mul]

/-- An ordered product of the six positive root matrices in normal-form coordinates. -/
theorem positiveRootMatrix_product (a b c d e f : R) :
    positiveRootMatrix 0 a * positiveRootMatrix 1 b * positiveRootMatrix 2 c *
        positiveRootMatrix 3 d * positiveRootMatrix 4 e * positiveRootMatrix 5 f =
      crossUnipotentMatrix a b (a * b + c) (d - a * c) (e - a * d)
        (f - a * c ^ 2 - (a * b + c) * d) := by
  simp only [positiveRootMatrix_def, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, crossUnipotentMatrix_mul]
  congr 1 <;> ring

/-- The six-coordinate normal form has an explicit ordered positive-root factorization.
The corrections recover the factor parameters from the six selected matrix entries. -/
theorem crossUnipotentMatrix_factorization (a b c d e f : R) :
    crossUnipotentMatrix a b c d e f =
      positiveRootMatrix 0 a * positiveRootMatrix 1 b *
        positiveRootMatrix 2 (c - a * b) * positiveRootMatrix 3 (d + a * (c - a * b)) *
        positiveRootMatrix 4 (e + a * (d + a * (c - a * b))) *
        positiveRootMatrix 5 (f + a * (c - a * b) ^ 2 + c * (d + a * (c - a * b))) := by
  rw [positiveRootMatrix_product]
  congr 1 <;> ring

/-- Ordered products have unique parameters over every commutative ring. -/
@[simp]
theorem positiveRootMatrix_product_inj {a b c d e f a' b' c' d' e' f' : R} :
    positiveRootMatrix 0 a * positiveRootMatrix 1 b * positiveRootMatrix 2 c *
        positiveRootMatrix 3 d * positiveRootMatrix 4 e * positiveRootMatrix 5 f =
      positiveRootMatrix 0 a' * positiveRootMatrix 1 b' * positiveRootMatrix 2 c' *
        positiveRootMatrix 3 d' * positiveRootMatrix 4 e' * positiveRootMatrix 5 f' ↔
      a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' := by
  rw [positiveRootMatrix_product, positiveRootMatrix_product, crossUnipotentMatrix_inj]
  constructor
  · rintro ⟨rfl, rfl, hc, hd, he, hf⟩
    have hcc : c = c' := add_left_cancel hc
    subst c'
    have hdd : d = d' := sub_left_inj.mp hd
    subst d'
    have hee : e = e' := sub_left_inj.mp he
    subst e'
    exact ⟨rfl, rfl, rfl, rfl, rfl, sub_left_inj.mp (sub_left_inj.mp hf)⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end TauCeti.G2ShortRoot
