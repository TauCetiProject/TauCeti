/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.RankTwo.Positive

/-!
# The Weyl dimension product in type B₂

For the pinned simply connected root datum of type `B₂`, with `α₀` the long and `α₁` the short
simple root, the four positive roots are `α₀`, `α₁`, `α₀ + α₁` and `α₀ + 2 α₁`. Their coroots are
`α₀^∨`, `α₁^∨`, `2 α₀^∨ + α₁^∨` and `α₀^∨ + α₁^∨`: the short root `α₀ + α₁` has a long coroot, in
which the coroot `α₀^∨` of the long simple root, a short coroot, appears twice. Consequently the
Weyl dimension product at the dominant weight with fundamental-weight coordinates `(a, b)` is

`(a + 1)(b + 1)(2a + b + 3)(a + b + 2) / 6`.

This is the root-datum computation needed to specialize the abstract Weyl dimension formula to
type `B₂`. In type `A₂` a root and its coroot have the same coordinates; in type `B₂` they do not,
so the computation checks that the positive-root product carries the right multiplicities. At
`(1, 0)`, `(0, 1)` and `(0, 2)` it returns `5`, `4` and `10`, the dimensions of the vector, spin
and adjoint representations of `𝔰𝔬₅`.

The positive roots and the heights of their coroots come from
`TauCeti.DynkinType.posRootsFinset_typeB_two` and `TauCeti.DynkinType.height_flip_b2Index`.

## Main results

* `TauCeti.DynkinType.prod_shiftedCorootPairing_typeB_two`: the numerator in the Weyl dimension
  formula.
* `TauCeti.DynkinType.prod_positiveCorootHeight_typeB_two`: the denominator in the formula.
* `TauCeti.DynkinType.weylDimensionProduct_typeB_two`: the `B₂` Weyl dimension product.
* `TauCeti.DynkinType.weylDimensionProduct_typeB_two_one_zero`,
  `TauCeti.DynkinType.weylDimensionProduct_typeB_two_zero_one` and
  `TauCeti.DynkinType.weylDimensionProduct_typeB_two_zero_two`: its values `5`, `4` and `10` at the
  two fundamental weights and at the highest root.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §24.3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
-/

public section

namespace TauCeti

open RootPairing

namespace DynkinType

private theorem prod_posRootsFinset_typeB_two (f : Fin (2 * 2 ^ 2) → ℤ) :
    ∏ i ∈ posRootsFinset (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2), f i =
      f (b2Index 0) * f (b2Index 1) * f (b2Index 2) * f (b2Index 3) := by
  rw [posRootsFinset_typeB_two,
    Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton,
      b2Index_injective.eq_iff]; decide),
    Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton,
      b2Index_injective.eq_iff]; decide),
    Finset.prod_pair (b2Index_injective.ne (by decide))]
  ring

/-- **The Weyl numerator product in type `B₂`.** At the fundamental-weight coordinates `(a, b)`,
its four factors are `a + 1`, `b + 1`, `2a + b + 3` and `a + b + 2`. -/
theorem prod_shiftedCorootPairing_typeB_two (a b : ℤ) :
    ∏ i ∈ posRootsFinset (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2),
        ((typeBSimplyConnectedRootDatum 2).toLinearMap ![a, b]
          ((typeBSimplyConnectedRootDatum 2).coroot i) +
            (typeBSimplyConnectedBase 2).flip.height i) =
      (a + 1) * (b + 1) * (2 * a + b + 3) * (a + b + 2) := by
  rw [prod_posRootsFinset_typeB_two]
  simp only [toLinearMap_typeBSimplyConnectedRootDatum, coroot_b2Index, height_flip_b2Index,
    dotProduct, Fin.sum_univ_two, b2Coroot, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The denominator in the `B₂` Weyl dimension formula is `6`: its factors are `1`, `1`, `3` and
`2`, the heights of the four positive coroots. -/
theorem prod_positiveCorootHeight_typeB_two :
    ∏ i ∈ posRootsFinset (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2),
      (typeBSimplyConnectedBase 2).flip.height i = 6 := by
  rw [prod_posRootsFinset_typeB_two]
  simp only [height_flip_b2Index]
  decide

/-- **The Weyl dimension product for type `B₂`.** At the weight with fundamental-weight
coordinates `(a, b)`, the quotient of the shifted coroot-pairing product by the positive-coroot
height product is `(a + 1)(b + 1)(2a + b + 3)(a + b + 2) / 6`. -/
theorem weylDimensionProduct_typeB_two (a b : ℤ) :
    ((∏ i ∈ posRootsFinset
          (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2),
        ((typeBSimplyConnectedRootDatum 2).toLinearMap ![a, b]
          ((typeBSimplyConnectedRootDatum 2).coroot i) +
            (typeBSimplyConnectedBase 2).flip.height i) : ℤ) : ℚ) /
      ((∏ i ∈ posRootsFinset
          (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2),
        (typeBSimplyConnectedBase 2).flip.height i : ℤ) : ℚ) =
      (((a + 1) * (b + 1) * (2 * a + b + 3) * (a + b + 2) : ℤ) : ℚ) / 6 := by
  rw [prod_shiftedCorootPairing_typeB_two, prod_positiveCorootHeight_typeB_two]
  norm_num

/-- At the fundamental weight of the long simple root the `B₂` Weyl dimension product is `5`, the
dimension of the vector representation of `𝔰𝔬₅`. -/
theorem weylDimensionProduct_typeB_two_one_zero :
    ((∏ i ∈ posRootsFinset
          (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2),
        ((typeBSimplyConnectedRootDatum 2).toLinearMap ![1, 0]
          ((typeBSimplyConnectedRootDatum 2).coroot i) +
            (typeBSimplyConnectedBase 2).flip.height i) : ℤ) : ℚ) /
      ((∏ i ∈ posRootsFinset
          (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2),
        (typeBSimplyConnectedBase 2).flip.height i : ℤ) : ℚ) = 5 := by
  rw [weylDimensionProduct_typeB_two]
  norm_num

/-- At the fundamental weight of the short simple root the `B₂` Weyl dimension product is `4`, the
dimension of the spin representation of `𝔰𝔬₅`. -/
theorem weylDimensionProduct_typeB_two_zero_one :
    ((∏ i ∈ posRootsFinset
          (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2),
        ((typeBSimplyConnectedRootDatum 2).toLinearMap ![0, 1]
          ((typeBSimplyConnectedRootDatum 2).coroot i) +
            (typeBSimplyConnectedBase 2).flip.height i) : ℤ) : ℚ) /
      ((∏ i ∈ posRootsFinset
          (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2),
        (typeBSimplyConnectedBase 2).flip.height i : ℤ) : ℚ) = 4 := by
  rw [weylDimensionProduct_typeB_two]
  norm_num

/-- At the highest root `α₀ + 2 α₁`, with fundamental-weight coordinates `(0, 2)`, the `B₂` Weyl
dimension product is `10`, the dimension of the adjoint representation of `𝔰𝔬₅`. -/
theorem weylDimensionProduct_typeB_two_zero_two :
    ((∏ i ∈ posRootsFinset
          (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2),
        ((typeBSimplyConnectedRootDatum 2).toLinearMap ![0, 2]
          ((typeBSimplyConnectedRootDatum 2).coroot i) +
            (typeBSimplyConnectedBase 2).flip.height i) : ℤ) : ℚ) /
      ((∏ i ∈ posRootsFinset
          (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2),
        (typeBSimplyConnectedBase 2).flip.height i : ℤ) : ℚ) = 10 := by
  rw [weylDimensionProduct_typeB_two]
  norm_num

end DynkinType

end TauCeti
