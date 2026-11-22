/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.FullCover.Even
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic

/-!
# The spinor norm on the normalized full Clifford cover

The normalized full Clifford cover `CliffordAlgebra.cliffordFullCover Q` consists of the Lipschitz
elements whose reverse norm `reverse x * x` is `1` or `-1`, and the Spin group is its subgroup of
even elements of reverse norm `1` (`CliffordAlgebra.mem_range_spinToCliffordFullCover_iff`).

Over a field in which `-1` is not a square, an element of the full cover of a nondegenerate
quadratic space has reverse norm `1` exactly when the spinor norm of its action is trivial. So the
Spin group is the part of the even full cover whose action has trivial spinor norm. When moreover
every element is a square up to sign, as over `ℝ`, the even part of the full cover covers all of
`SO(Q)` (`CliffordAlgebra.map_cliffordFullCoverEven`), and the Spin group has index in it the
number of values of the spinor norm on `SO(Q)`.

## Main results

* `CliffordAlgebra.cliffordNorm_eq_one_iff_orthogonalSpinorNorm_eq_one`: when `-1` is not a
  square, an element of the full cover has reverse norm `1` exactly when its action has trivial
  spinor norm.
* `CliffordAlgebra.range_spinToCliffordFullCover_eq_cliffordFullCoverEven_inf`: when `-1` is not a
  square, the Spin group is the part of the even full cover whose action has trivial spinor norm.
* `CliffordAlgebra.relIndex_range_spinToCliffordFullCover`: when moreover every element is a
  square up to sign, the index of the Spin group in the even part of the full cover is the number
  of values of the spinor norm on `SO(Q)`.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Proposition 1.21.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Invertible (2 : K)] {Q : QuadraticForm K V}

/-- **Reverse norm and spinor norm.** When `-1` is not a square, an element of the full cover of
a nondegenerate quadratic space has reverse norm `1`, rather than `-1`, exactly when the spinor
norm of its action is trivial. -/
theorem cliffordNorm_eq_one_iff_orthogonalSpinorNorm_eq_one (hQ : Q.Nondegenerate)
    (h : ¬IsSquare (-1 : K)) (x : cliffordFullCover Q) :
    cliffordNorm Q x = 1 ↔
      orthogonalSpinorNorm Q hQ (cliffordFullCoverToOrthogonal Q x) = 1 := by
  rw [cliffordFullCoverToOrthogonal_apply, orthogonalSpinorNorm_lipschitzToOrthogonal,
    squareClassHom_eq_one_iff]
  rcases (mem_cliffordFullCover_iff Q x).1 x.property with h1 | h1 <;> rw [h1]
  · simp
  · refine iff_of_false (fun h2 ↦ ?_) fun h2 ↦ h ?_
    · have h3 : (-1 : K) = 1 := by simpa using congrArg Units.val h2
      exact two_ne_zero (by linear_combination -h3 : (2 : K) = 0)
    · simpa using Units.isSquare_coe_iff.mpr h2

/-- **The Spin group inside the even full cover.** When `-1` is not a square, the Spin group is
the subgroup of even elements of the full cover whose action has trivial spinor norm. -/
theorem range_spinToCliffordFullCover_eq_cliffordFullCoverEven_inf (hQ : Q.Nondegenerate)
    (h : ¬IsSquare (-1 : K)) :
    (spinToCliffordFullCover Q).range =
      cliffordFullCoverEven Q ⊓
        ((orthogonalSpinorNorm Q hQ).comp (cliffordFullCoverToOrthogonal Q)).ker := by
  ext x
  rw [mem_range_spinToCliffordFullCover_iff, Subgroup.mem_inf, mem_cliffordFullCoverEven_iff,
    MonoidHom.mem_ker, MonoidHom.comp_apply,
    cliffordNorm_eq_one_iff_orthogonalSpinorNorm_eq_one hQ h]

/-- **The index of the Spin group in the even full cover.** Over a field in which `-1` is not a
square but every element is a square up to sign, the Spin group has index in the even part of the
full cover equal to the number of values of the spinor norm on `SO(Q)`. -/
theorem relIndex_range_spinToCliffordFullCover (hQ : Q.Nondegenerate) (h : ¬IsSquare (-1 : K))
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) :
    (spinToCliffordFullCover Q).range.relIndex (cliffordFullCoverEven Q) =
      Nat.card (spinorNorm Q hQ).range := by
  have hθ : spinorNorm Q hQ = (orthogonalSpinorNorm Q hQ).comp
      (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q) :=
    MonoidHom.ext (spinorNorm_apply Q hQ)
  rw [range_spinToCliffordFullCover_eq_cliffordFullCoverEven_inf hQ h, Subgroup.inf_relIndex_left,
    Subgroup.relIndex_ker, ← Subgroup.map_map, map_cliffordFullCoverEven hQ hK, hθ,
    MonoidHom.range_comp, _root_.QuadraticMap.range_specialOrthogonalToOrthogonal]

end CliffordAlgebra
