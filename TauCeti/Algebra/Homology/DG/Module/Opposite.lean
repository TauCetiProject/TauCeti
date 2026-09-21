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

open scoped DirectSum

namespace TauCeti.GradedOpposite

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The right Leibniz rule for a homogeneous algebra element and homogeneous module element. -/
private theorem leftToRight_leibniz_of_mem
    (G : InternalGrading R A) (H : InternalGrading R M)
    [GradedAlgebra G.piece] [SetLike.GradedSMul G.piece H.piece]
    {d : A →ₗ[R] A} (hA : IsDGAlgebra G.piece d)
    {dM : M →ₗ[R] M}
    (hM : IsDGLeftModule hA H.piece dM)
    {p q : ℤ} {a : A} (ha : a ∈ G.piece p) {x : M} (hx : x ∈ H.piece q) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    dM (MulOpposite.op (op G a) • x) =
      MulOpposite.op (op G a) • dM x +
        q.negOnePow •
          (MulOpposite.op (GradedOpposite.differential G d (op G a)) • x) := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  have hdx : dM x ∈ H.piece (q + 1) := hM.isHomogeneous.map_mem hx
  rw [GradedOpposite.differential_op]
  rw [leftToRight_smul_of_mem G H ha hx, map_smul, hM.leibniz ha,
    leftToRight_smul_of_mem G H ha hdx,
    leftToRight_smul_of_mem G H (hA.map_mem ha) hx]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_add, smul_smul]
  have hfirst : (p * q).negOnePow * p.negOnePow = (p * (q + 1)).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    ring
  have hsecond : q.negOnePow * ((p + 1) * q).negOnePow = (p * q).negOnePow := by
    rw [← Int.negOnePow_add]
    apply (Int.negOnePow_eq_iff _ _).2
    use q
    ring
  rw [add_comm]
  congr 1
  · simpa only [Units.val_mul, Int.cast_mul] using
      congrArg (fun z : ℤˣ ↦ (((z : ℤ) : R) • (a • dM x))) hfirst
  · simpa only [Units.val_mul, Int.cast_mul] using
      congrArg (fun z : ℤˣ ↦ (((z : ℤ) : R) • (d a • x))) hsecond.symm

/-- The right Leibniz rule for an arbitrary algebra element and homogeneous module element. -/
private theorem leftToRight_leibniz
    (G : InternalGrading R A) (H : InternalGrading R M)
    [GradedAlgebra G.piece] [SetLike.GradedSMul G.piece H.piece]
    {d : A →ₗ[R] A} (hA : IsDGAlgebra G.piece d)
    {dM : M →ₗ[R] M}
    (hM : IsDGLeftModule hA H.piece dM)
    {q : ℤ} {x : M} (hx : x ∈ H.piece q) (b : GradedOpposite G) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    dM (MulOpposite.op b • x) =
      MulOpposite.op b • dM x + q.negOnePow •
        (MulOpposite.op (GradedOpposite.differential G d b) • x) := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  induction b using DirectSum.Decomposition.inductionOn
      (ℳ := (GradedOpposite.grading G).piece) with
  | zero => simp
  | add b c hb hc =>
      simp only [map_add, MulOpposite.op_add, add_smul, smul_add, hb, hc]
      abel
  | homogeneous b =>
      rw [← GradedOpposite.op_unop G b]
      exact leftToRight_leibniz_of_mem G H hA hM
        ((GradedOpposite.mem_piece_iff G _ b).1 b.property) hx

/-- A differential graded left module over `A` is a differential graded right module over the
Koszul-signed graded opposite of `A`, with action `leftToRightModule`. -/
theorem IsDGLeftModule.gradedOppositeRight
    (G : InternalGrading R A) (H : InternalGrading R M)
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
    (fun hx b ↦ leftToRight_leibniz G H hA hM hx b)

end TauCeti.GradedOpposite
