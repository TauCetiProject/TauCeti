/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.ThreeOne

/-!
# The real Spin group of signature `(1,3)`

The even Clifford algebra is unchanged, up to its canonical equivalence, when the quadratic form
is negated. Combining that equivalence with the coordinate block swap from the negation of the
`(3,1)` form to the `(1,3)` form identifies `Spin(1,3)` with `SL₂(ℂ)`.

## Main definition

* `TauCeti.realSpinThreeOneEquivOneThree` identifies the two opposite Lorentz signatures.
* `TauCeti.realSpinOneThreeEquivSpecialLinear` identifies `Spin(1,3)` with `SL₂(ℂ)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4.
-/

public section

namespace TauCeti

/-- Negation followed by the coordinate block swap identifies the two Lorentz Spin groups. -/
noncomputable def realSpinThreeOneEquivOneThree :
    spinGroup (realCliffordForm 3 1) ≃* spinGroup (realCliffordForm 1 3) :=
  (CliffordAlgebra.spinGroupEquivNegOfFinrankLeFour
    (realCliffordForm 3 1) (nondegenerate_realCliffordForm 3 1)
    (by norm_num) (by norm_num)).trans
      (realCliffordFormNegIsometry 3 1).spinGroupEquiv

/-- The real Spin group `Spin(1,3)` is `SL₂(ℂ)`. -/
noncomputable def realSpinOneThreeEquivSpecialLinear :
    spinGroup (realCliffordForm 1 3) ≃* Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  realSpinThreeOneEquivOneThree.symm.trans realSpinThreeOneEquivSpecialLinear

/-- The `Spin(1,3) ≃ SL₂(ℂ)` equivalence factors through negation and the landed `(3,1)` model. -/
@[simp]
theorem realSpinOneThreeEquivSpecialLinear_apply
    (s : spinGroup (realCliffordForm 1 3)) :
    realSpinOneThreeEquivSpecialLinear s =
      realSpinThreeOneEquivSpecialLinear (realSpinThreeOneEquivOneThree.symm s) := by
  rfl

end TauCeti

end
