/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Positive

/-!
# The Weyl dimension product in type G₂

For the pinned simply connected root datum of type `G₂`, with `α₁` the short and `α₂` the long
simple root, the six positive roots are `α₁`, `α₂`, `α₁ + α₂`, `2α₁ + α₂`, `3α₁ + α₂` and
`3α₁ + 2α₂`. Their coroots are, in the simple-coroot basis, `(1, 0)`, `(0, 1)`, `(1, 3)`, `(2, 3)`,
`(1, 1)` and `(1, 2)`: each short root has a long coroot, in which the coroot `α₂^∨` of the long
simple root, a short coroot, appears three times as often as `α₂` does in the root. Consequently
the Weyl dimension product at the dominant weight with fundamental-weight coordinates `(a, b)` is

`(a + 1)(b + 1)(a + 3b + 4)(2a + 3b + 5)(a + b + 2)(a + 2b + 3) / 120`.

This is the root-datum computation needed to specialize the abstract Weyl dimension formula to
type `G₂`, where the squared root lengths differ by a factor of three, so it checks that the
positive-root product carries the right multiplicities. At `(1, 0)` and `(0, 1)` it returns `7`
and `14`, the dimensions of the two fundamental representations of `𝔤₂`; the second is the adjoint
representation, the highest root `3α₁ + 2α₂` being the fundamental weight of the long simple root.

The positive roots and the heights of their coroots come from
`TauCeti.DynkinType.posRootsFinset_g2` and `TauCeti.DynkinType.height_flip_g2SimplyConnectedBase`.

## Main results

* `TauCeti.DynkinType.prod_shiftedCorootPairing_g2`: the numerator in the Weyl dimension formula.
* `TauCeti.DynkinType.prod_positiveCorootHeight_g2`: the denominator in the formula.
* `TauCeti.DynkinType.weylDimensionProduct_g2`: the `G₂` Weyl dimension product.
* `TauCeti.DynkinType.weylDimensionProduct_g2_one_zero` and
  `TauCeti.DynkinType.weylDimensionProduct_g2_zero_one`: its values `7` and `14` at the two
  fundamental weights.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §24.3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
-/

public section

namespace TauCeti

open RootPairing

namespace DynkinType

private theorem prod_posRootsFinset_g2 (f : Fin 12 → ℤ) :
    ∏ i ∈ posRootsFinset g2SimplyConnectedRootDatum g2SimplyConnectedBase, f i =
      f 0 * f 1 * f 2 * f 3 * f 4 * f 5 := by
  rw [posRootsFinset_g2]
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton, Finset.prod_singleton,
    Fin.reduceEq, or_self, not_false_eq_true]
  ring

/-- **The Weyl numerator product in type `G₂`.** At the fundamental-weight coordinates `(a, b)`,
its six factors are `a + 1`, `b + 1`, `a + 3b + 4`, `2a + 3b + 5`, `a + b + 2` and
`a + 2b + 3`. -/
theorem prod_shiftedCorootPairing_g2 (a b : ℤ) :
    ∏ i ∈ posRootsFinset g2SimplyConnectedRootDatum g2SimplyConnectedBase,
        (g2SimplyConnectedRootDatum.toLinearMap ![a, b] (g2SimplyConnectedRootDatum.coroot i) +
          g2SimplyConnectedBase.flip.height i) =
      (a + 1) * (b + 1) * (a + 3 * b + 4) * (2 * a + 3 * b + 5) * (a + b + 2) *
        (a + 2 * b + 3) := by
  rw [prod_posRootsFinset_g2]
  simp only [g2SimplyConnectedRootDatum_toLinearMap, g2SimplyConnectedRootDatum_coroot,
    height_flip_g2SimplyConnectedBase, dotProduct, Fin.sum_univ_two, g2Coroot_apply,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The denominator in the `G₂` Weyl dimension formula is `120`: its factors are `1`, `1`, `4`,
`5`, `2` and `3`, the heights of the six positive coroots. -/
theorem prod_positiveCorootHeight_g2 :
    ∏ i ∈ posRootsFinset g2SimplyConnectedRootDatum g2SimplyConnectedBase,
      g2SimplyConnectedBase.flip.height i = 120 := by
  rw [prod_posRootsFinset_g2]
  simp only [height_flip_g2SimplyConnectedBase, g2Coroot_apply]
  decide

/-- **The Weyl dimension product for type `G₂`.** At the weight with fundamental-weight
coordinates `(a, b)`, the quotient of the shifted coroot-pairing product by the positive-coroot
height product is `(a + 1)(b + 1)(a + 3b + 4)(2a + 3b + 5)(a + b + 2)(a + 2b + 3) / 120`. -/
theorem weylDimensionProduct_g2 (a b : ℤ) :
    ((∏ i ∈ posRootsFinset g2SimplyConnectedRootDatum g2SimplyConnectedBase,
        (g2SimplyConnectedRootDatum.toLinearMap ![a, b] (g2SimplyConnectedRootDatum.coroot i) +
          g2SimplyConnectedBase.flip.height i) : ℤ) : ℚ) /
      ((∏ i ∈ posRootsFinset g2SimplyConnectedRootDatum g2SimplyConnectedBase,
        g2SimplyConnectedBase.flip.height i : ℤ) : ℚ) =
      (((a + 1) * (b + 1) * (a + 3 * b + 4) * (2 * a + 3 * b + 5) * (a + b + 2) *
        (a + 2 * b + 3) : ℤ) : ℚ) / 120 := by
  rw [prod_shiftedCorootPairing_g2, prod_positiveCorootHeight_g2]
  norm_num

/-- At the fundamental weight of the short simple root the `G₂` Weyl dimension product is `7`, the
dimension of the smallest nontrivial representation of `𝔤₂`. -/
theorem weylDimensionProduct_g2_one_zero :
    ((∏ i ∈ posRootsFinset g2SimplyConnectedRootDatum g2SimplyConnectedBase,
        (g2SimplyConnectedRootDatum.toLinearMap ![1, 0] (g2SimplyConnectedRootDatum.coroot i) +
          g2SimplyConnectedBase.flip.height i) : ℤ) : ℚ) /
      ((∏ i ∈ posRootsFinset g2SimplyConnectedRootDatum g2SimplyConnectedBase,
        g2SimplyConnectedBase.flip.height i : ℤ) : ℚ) = 7 := by
  rw [weylDimensionProduct_g2]
  norm_num

/-- At the fundamental weight of the long simple root, which is the highest root `3α₁ + 2α₂`, the
`G₂` Weyl dimension product is `14`, the dimension of the adjoint representation of `𝔤₂`. -/
theorem weylDimensionProduct_g2_zero_one :
    ((∏ i ∈ posRootsFinset g2SimplyConnectedRootDatum g2SimplyConnectedBase,
        (g2SimplyConnectedRootDatum.toLinearMap ![0, 1] (g2SimplyConnectedRootDatum.coroot i) +
          g2SimplyConnectedBase.flip.height i) : ℤ) : ℚ) /
      ((∏ i ∈ posRootsFinset g2SimplyConnectedRootDatum g2SimplyConnectedBase,
        g2SimplyConnectedBase.flip.height i : ℤ) : ℚ) = 14 := by
  rw [weylDimensionProduct_g2]
  norm_num

end DynkinType

end TauCeti
