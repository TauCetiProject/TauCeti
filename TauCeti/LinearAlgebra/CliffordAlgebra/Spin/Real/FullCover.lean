/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.FullCover
public import Mathlib.Basic.Real.Basic
import Mathlib.FieldTheory.IsRealClosed.Real
import TauCeti.FieldTheory.SquareClassGroup.Real
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.SpinorNorm
import TauCeti.Algebra.Order.Ring.Square

/-!
# The real full Clifford cover and the Spin group

For a nondegenerate real quadratic space, the normalized full Clifford cover
`CliffordAlgebra.cliffordFullCover Q`, the Lipschitz elements of reverse norm `±1`, covers `O(Q)`
with kernel `{±1}` in positive dimension, trivial in dimension zero, and its even part covers
`SO(Q)`. This file compares the even part with the Spin group, of even elements of reverse norm
`1`: for a definite form the Spin group is the whole even part of the full cover, while for an
indefinite form it has index two there, its image being the kernel of the spinor norm on `SO(Q)`.

## Main results

* `CliffordAlgebra.range_spinToCliffordFullCover_eq_cliffordFullCoverEven_of_posDef` and
  `CliffordAlgebra.range_spinToCliffordFullCover_eq_cliffordFullCoverEven_of_negDef`: for a
  definite form the Spin group is the even part of the full cover.
* `CliffordAlgebra.relIndex_range_spinToCliffordFullCover_of_indefinite`: for an indefinite form
  it has index two there.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.6 and Proposition 1.21.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti

universe v

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **For a positive definite form, Spin is the even full cover.** The spinor norm is trivial, so
every even element of the full cover has reverse norm `1`. -/
theorem range_spinToCliffordFullCover_eq_cliffordFullCoverEven_of_posDef (Q : QuadraticForm ℝ V)
    (hQ : Q.PosDef) :
    (spinToCliffordFullCover Q).range = cliffordFullCoverEven Q := by
  refine le_antisymm (range_spinToCliffordFullCover_le_cliffordFullCoverEven Q) ?_
  rw [← Subgroup.relIndex_eq_one, relIndex_range_spinToCliffordFullCover
    hQ.anisotropic.nondegenerate not_isSquare_neg_one IsRealClosed.isSquare_or_isSquare_neg,
    spinorNorm_eq_one_of_posDef Q hQ, MonoidHom.range_one, Subgroup.card_bot]

/-- **For a negative definite form, Spin is the even full cover.** The spinor norm is the
determinant square class, trivial on `SO(Q)`, so every even element of the full cover has reverse
norm `1`. -/
theorem range_spinToCliffordFullCover_eq_cliffordFullCoverEven_of_negDef (Q : QuadraticForm ℝ V)
    (hneg : (-Q).PosDef) :
    (spinToCliffordFullCover Q).range = cliffordFullCoverEven Q := by
  refine le_antisymm (range_spinToCliffordFullCover_le_cliffordFullCoverEven Q) ?_
  rw [← Subgroup.relIndex_eq_one, relIndex_range_spinToCliffordFullCover
    ((QuadraticMap.nondegenerate_neg Q).mp hneg.anisotropic.nondegenerate)
    not_isSquare_neg_one IsRealClosed.isSquare_or_isSquare_neg,
    spinorNorm_eq_one_of_negDef Q hneg, MonoidHom.range_one, Subgroup.card_bot]

/-- **For an indefinite form, Spin has index two in the even full cover.** The spinor norm then
takes both signs on `SO(Q)`, so the even part of the full cover contains elements of reverse norm
`-1`. -/
theorem relIndex_range_spinToCliffordFullCover_of_indefinite (Q : QuadraticForm ℝ V)
    (hQ : Q.Nondegenerate) (hpos : ∃ v, 0 < Q v) (hneg : ∃ v, Q v < 0) :
    (spinToCliffordFullCover Q).range.relIndex (cliffordFullCoverEven Q) = 2 := by
  rw [relIndex_range_spinToCliffordFullCover hQ not_isSquare_neg_one
      IsRealClosed.isSquare_or_isSquare_neg,
    MonoidHom.range_eq_top.2 (spinorNorm_surjective_of_indefinite Q hQ hpos hneg),
    Subgroup.card_top, natCard_units_quotient_square_real]

end CliffordAlgebra
