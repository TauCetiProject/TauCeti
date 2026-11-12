/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The operators `∂bar` and `∂` on functions over an almost complex manifold

Let `j` be a smooth almost complex structure on a manifold `M` and `F` a complex normed space.
Functions `M → F` are the sections of the trivial bundle `M × F`, and their `∂bar`,
`∂bar σ = (dσ)^{0,1}`, is the `(0,1)`-part of the canonical connection of the trivial bundle. So
it is a complex linear real Cauchy–Riemann operator: `∂bar (g σ) = g ∂bar σ + (∂bar g) ⊗ σ` for
real valued `g`. The complementary operator `∂ σ = dσ - ∂bar σ = (dσ)^{1,0}` is also defined here.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.dbarFunction`: the operator `σ ↦ (dσ)^{0,1}` on
  `F`-valued functions.
* `TauCeti.SmoothAlmostComplexStructure.isRealCauchyRiemannOperator_dbarFunction`,
  `TauCeti.SmoothAlmostComplexStructure.isComplexLinearOperator_dbarFunction`: it is a complex
  linear real Cauchy–Riemann operator on the trivial bundle.
* `TauCeti.SmoothAlmostComplexStructure.delFunction`: the operator `σ ↦ (dσ)^{1,0}` on
  `F`-valued functions.
* `TauCeti.SmoothAlmostComplexStructure.delFunction_add_dbarFunction`,
  `TauCeti.SmoothAlmostComplexStructure.delFunction_apply_almostComplex`: `dσ = ∂ σ + ∂bar σ`, and
  `∂ σ` is a `(1,0)`-form.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, Definition C.1.5.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (j : SmoothAlmostComplexStructure I M)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The operator `∂bar σ = (dσ)^{0,1}` on functions `σ : M → F` into a complex normed space, the
sections of the trivial bundle `M × F`:
`∂bar σ (v) = ½ (dσ (v) + i • dσ (j v))`
(`TauCeti.SmoothAlmostComplexStructure.dbarFunction_apply`). It is the `(0,1)`-part of the
canonical connection `CovariantDerivative.trivial` of the trivial bundle. -/
def dbarFunction (σ : M → F) (x : M) : TangentSpace I x →L[ℝ] F :=
  j.zeroOnePart (V := Bundle.Trivial M F) (mvfderiv I σ x)

theorem dbarFunction_apply (σ : M → F) (x : M) (v : E) :
    j.dbarFunction σ x v =
      (2⁻¹ : ℝ) • (mvfderiv I σ x v + Complex.I • mvfderiv I σ x (j x v)) :=
  j.zeroOnePart_apply (V := Bundle.Trivial M F) _ v

/-- `∂bar` on functions is the `(0,1)`-part of the canonical connection of the trivial bundle. -/
theorem dbarFunction_eq_zeroOnePart_trivial :
    j.dbarFunction (F := F) = fun σ x ↦
      j.zeroOnePart (V := Bundle.Trivial M F) (CovariantDerivative.trivial (I := I) F σ x) := by
  funext σ x
  rw [CovariantDerivative.trivial_apply]
  rfl

/-- `∂bar` on functions is a real Cauchy–Riemann operator on the trivial bundle: its values are
`(0,1)`-forms, and `∂bar (g σ) = g ∂bar σ + (∂bar g) ⊗ σ` for real valued `g`. -/
theorem isRealCauchyRiemannOperator_dbarFunction :
    IsRealCauchyRiemannOperator F j (V := Bundle.Trivial M F) j.dbarFunction := by
  rw [dbarFunction_eq_zeroOnePart_trivial]
  exact (CovariantDerivative.trivial (I := I) (M := M) F).isCovariantDerivativeOnUniv
    |>.isRealCauchyRiemannOperator_zeroOnePart j

/-- `∂bar` on functions is a complex linear real Cauchy–Riemann operator on the trivial bundle. -/
theorem isComplexLinearOperator_dbarFunction :
    IsComplexLinearOperator F (V := Bundle.Trivial M F) j.dbarFunction := by
  rw [dbarFunction_eq_zeroOnePart_trivial]
  refine (CovariantDerivative.trivial (I := I) (M := M) F).isCovariantDerivativeOnUniv
    |>.isComplexLinearOperator_zeroOnePart j fun σ x hσ ↦ ?_
  simp only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
    Trivial.trivialization_apply] at hσ
  simp only [CovariantDerivative.trivial_apply]
  exact mvfderiv_const_smul hσ Complex.I

/-- The operator `∂ σ = (dσ)^{1,0} = dσ - ∂bar σ`, `∂ σ (v) = ½ (dσ (v) - i • dσ (j v))`, on
functions `σ : M → F` into a complex normed space. -/
def delFunction (σ : M → F) (x : M) : TangentSpace I x →L[ℝ] F :=
  mvfderiv I σ x - j.dbarFunction σ x

theorem delFunction_apply (σ : M → F) (x : M) (v : E) :
    j.delFunction σ x v = mvfderiv I σ x v - j.dbarFunction σ x v :=
  sub_apply _ _ v

/-- The differential splits as `dσ = ∂ σ + ∂bar σ`. -/
@[simp]
theorem delFunction_add_dbarFunction (σ : M → F) (x : M) :
    j.delFunction σ x + j.dbarFunction σ x = mvfderiv I σ x :=
  sub_add_cancel _ _

/-- `∂ σ` is a `(1,0)`-form: it is complex linear, `∂ σ (j v) = i • ∂ σ (v)`. -/
@[simp]
theorem delFunction_apply_almostComplex (σ : M → F) (x : M) (v : TangentSpace I x) :
    j.delFunction σ x (j x v) = Complex.I • j.delFunction σ x v := by
  have hjj : j x (j x v) = -v := by
    simp [← ContinuousLinearMap.comp_apply, j.square_neg x]
  rw [delFunction, dbarFunction, sub_apply, sub_apply, zeroOnePart_apply, zeroOnePart_apply, hjj,
    map_neg, smul_neg]
  simp only [smul_sub, smul_add, smul_comm Complex.I (2⁻¹ : ℝ), smul_smul Complex.I Complex.I,
    Complex.I_mul_I, neg_one_smul]
  module

end SmoothAlmostComplexStructure

end TauCeti
