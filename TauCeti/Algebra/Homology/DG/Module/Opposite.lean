/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Opposite
public import TauCeti.Algebra.Homology.DG.Module.Right.Defs
public import TauCeti.Algebra.Module.GradedModule.LeftToRight

/-!
# Left DG modules as right modules over the graded opposite

A left module over an internally graded algebra `A` determines a right module over the
Koszul-signed graded opposite of `A`.  On homogeneous elements of degrees `p` and `q`, the action
is

`x * op(a) = (-1) ^ (p * q) • (a • x)`.

With this action, a DG left module becomes a DG right module over the graded-opposite DG algebra.
Its differential obeys the right Leibniz rule with sign determined by the degree of the module
element, for arbitrary algebra elements.

## Main results

* `IsDGLeftModule.gradedOppositeRight`: a DG left module is a DG right module over the
  Koszul-signed graded opposite.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti.IsDGLeftModule

open GradedOpposite

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- A differential graded left module over `A` is a differential graded right module over the
Koszul-signed graded opposite of `A`, with action `GradedOpposite.leftToRightModule`. -/
theorem gradedOppositeRight
    {G : InternalGrading R A} {H : InternalGrading R M}
    [GradedAlgebra G.piece] [SetLike.GradedSMul G.piece H.piece]
    {d : A →ₗ[R] A} {hA : IsDGAlgebra G.piece d}
    {dM : M →ₗ[R] M}
    (hM : IsDGLeftModule hA H.piece dM) :
    @IsDGRightModule R (GradedOpposite G) M _ _ _ _ _
      (leftToRightModule G H) (grading G).piece inferInstance _
      (leftToRight_isScalarTower G H) hA.gradedOpposite H.piece
      (leftToRight_gradedSMul G H) inferInstance dM := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  let _ : IsScalarTower R (GradedOpposite G)ᵐᵒᵖ M := leftToRight_isScalarTower G H
  let _ : SetLike.GradedSMul
      (InternalGrading.ofDecomposition (grading G).piece).opposite.piece H.piece :=
    leftToRight_gradedSMul G H
  exact @IsDGRightModule.mk R (GradedOpposite G) M _ _ _ _ _
    (leftToRightModule G H) (grading G).piece inferInstance _
    (leftToRight_isScalarTower G H) hA.gradedOpposite H.piece
    (leftToRight_gradedSMul G H) inferInstance dM hM.isHomogeneous hM.sq_zero
    ((GradedOpposite.leftToRight_leibniz_iff G H hA.map_mem
      (fun hx ↦ hM.isHomogeneous.map_mem hx)).2 hM.leibniz)

end TauCeti.IsDGLeftModule
