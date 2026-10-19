/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Algebra.Opposite
public import TauCeti.Algebra.Homology.Curved.Module.Defs
public import TauCeti.Algebra.Homology.Curved.Module.Right.Defs
public import TauCeti.Algebra.Module.GradedModule.LeftToRight

/-!
# Curved left modules as right modules over the graded opposite

A graded left module over an internally graded algebra `A` is a right module over the
Koszul-signed graded opposite of `A`, with `x * op a = (-1) ^ (|a| * |x|) • (a • x)`
(`TauCeti.GradedOpposite.leftToRightModule`). For a curved differential graded algebra
`(A, d, w)` the graded opposite is a curved differential graded algebra of curvature `-op w`
(`TauCeti.IsCurvedDGAlgebra.gradedOpposite`). This file proves that the curved differential
graded left modules over `A` are exactly the curved differential graded right modules over this
graded opposite, on the same graded module and with the same differential.

The curvature is even, so it acts through the graded opposite without a Koszul sign, and the
right-module square `dM (dM x) = x * (-op w)` over the opposite reads `dM (dM x) = -(w • x)`.
Thus a left module does not satisfy the right-module square `w • x`: the sign is the one recorded
in `TauCeti.IsCurvedDGLeftModule`.

## Main results

* `TauCeti.isCurvedDGLeftModule_iff_gradedOppositeRight`: a differential makes a graded left
  module a curved differential graded left module exactly when it makes it a curved differential
  graded right module over the graded opposite.
* `TauCeti.IsCurvedDGLeftModule.gradedOppositeRight`: the forward direction, for dot notation.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
* B. Keller, *Deriving DG categories*, Section 1, for the Koszul-signed opposite.
-/

public section

namespace TauCeti

open GradedOpposite

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {G : InternalGrading R A} {H : InternalGrading R M}
  [GradedAlgebra G.piece] [SetLike.GradedSMul G.piece H.piece]
  {d : A →ₗ[R] A} {w : A} {h : IsCurvedDGAlgebra G.piece d w} {dM : M →ₗ[R] M}

/-- The curvature `-op w` of the graded opposite acts on a module element by minus the original
left action of `w`: the curvature has even degree, so no Koszul sign appears. -/
private theorem leftToRight_neg_op_curvature_smul (h : IsCurvedDGAlgebra G.piece d w) (x : M) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    MulOpposite.op (-op G w) • x = -(w • x) := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  rw [MulOpposite.op_neg, neg_smul,
    leftToRight_smul_of_mem_of_even G H h.curvature_mem even_two x]

/-- **Curved left modules through the graded opposite.** A differential `dM` makes the graded
left module `M` a curved differential graded left module over `(A, d, w)` exactly when it makes
`M`, with the transported action `GradedOpposite.leftToRightModule`, a curved differential graded
right module over the graded opposite, of curvature `-op w`. The right-module square
`dM (dM x) = x * (-op w)` over the opposite is the left-module square `dM (dM x) = -(w • x)`. -/
theorem isCurvedDGLeftModule_iff_gradedOppositeRight :
    IsCurvedDGLeftModule h H.piece dM ↔
      @IsCurvedDGRightModule R (GradedOpposite G) M _ _ _ _ _
        (leftToRightModule G H) (grading G).piece inferInstance _ _
        (leftToRight_isScalarTower G H) h.gradedOpposite H.piece
        (leftToRight_gradedSMul G H) inferInstance dM := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  constructor
  · intro hM
    exact @IsCurvedDGRightModule.mk R (GradedOpposite G) M _ _ _ _ _
      (leftToRightModule G H) (grading G).piece inferInstance _ _
      (leftToRight_isScalarTower G H) h.gradedOpposite H.piece
      (leftToRight_gradedSMul G H) inferInstance dM hM.isHomogeneous
      ((leftToRight_leibniz_iff G H h.map_mem fun hx ↦ hM.isHomogeneous.map_mem hx).2
        hM.leibniz)
      fun x ↦ by rw [hM.sq_eq, leftToRight_neg_op_curvature_smul h x]
  · -- Destructure rather than project: the projections would re-synthesize the transported
    -- graded action, whose decomposition instance differs from the one in the statement.
    rintro ⟨hhom, hleib, hsq⟩
    exact ⟨hhom, (leftToRight_leibniz_iff G H h.map_mem fun hx ↦ hhom.map_mem hx).1 hleib,
      fun x ↦ by rw [hsq, leftToRight_neg_op_curvature_smul h x]⟩

/-- A curved differential graded left module over `(A, d, w)` is a curved differential graded
right module over the Koszul-signed graded opposite, of curvature `-op w`, with action
`GradedOpposite.leftToRightModule`. -/
theorem IsCurvedDGLeftModule.gradedOppositeRight (hM : IsCurvedDGLeftModule h H.piece dM) :
    @IsCurvedDGRightModule R (GradedOpposite G) M _ _ _ _ _
      (leftToRightModule G H) (grading G).piece inferInstance _ _
      (leftToRight_isScalarTower G H) h.gradedOpposite H.piece
      (leftToRight_gradedSMul G H) inferInstance dM :=
  isCurvedDGLeftModule_iff_gradedOppositeRight.1 hM

end TauCeti
