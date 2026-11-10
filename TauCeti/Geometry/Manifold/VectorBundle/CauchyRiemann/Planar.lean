/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The operators `∂bar`, `∂bar + ξbar dzbar` and `∂` on functions over a complex curve

Let `j` be a smooth almost complex structure on a manifold `M` and `F` a complex normed space.
Functions `M → F` are the sections of the trivial bundle `M × F`, and their `∂bar`,
`∂bar σ = (dσ)^{0,1}`, is the `(0,1)`-part of the canonical connection of the trivial bundle. So
it is a complex linear real Cauchy–Riemann operator: `∂bar (g σ) = g ∂bar σ + (∂bar g) ⊗ σ` for
real valued `g`.

On a complex curve `M`, a manifold modelled on `ℂ` with its complex structure, such as the plane
or the unit disc, every tangent space is `ℂ`, and the operator `ξ ↦ ∂bar ξ + ξbar dzbar` is a real
Cauchy–Riemann operator on the trivial line bundle, by the same Leibniz rule, since
`conj (g ξ) = g ξbar` for real `g`. It is not complex linear: its antilinear zeroth-order part
in the decomposition of McDuff–Salamon, Exercise C.1.7, is `ξ ↦ ξbar dzbar` and its complex
linear part is `∂bar`. The operator `∂`, `∂ σ = (dσ)^{1,0}`, is not a real Cauchy–Riemann
operator: its Leibniz rule `∂ (g σ) = g ∂ σ + (∂ g) σ` has `∂ g` where a real Cauchy–Riemann
operator has `∂bar g`, and its values are `(1,0)`-forms. The proof uses the latter: `∂ z` and
`∂bar z` would both be `(0,1)`-forms, and so would their sum `dz`, which is complex linear.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.dbarFunction`: the operator `σ ↦ (dσ)^{0,1}` on
  `F`-valued functions.
* `TauCeti.SmoothAlmostComplexStructure.isRealCauchyRiemannOperator_dbarFunction`,
  `TauCeti.SmoothAlmostComplexStructure.isComplexLinearOperator_dbarFunction`: it is a complex
  linear real Cauchy–Riemann operator on the trivial bundle.
* `TauCeti.SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_self_apply`: on a complex
  normed space with multiplication by `i`, it is the conjugate Wirtinger derivative.
* `TauCeti.conjSMulDzbar`: the zeroth-order term `ξ ↦ ξbar dzbar` on a complex curve.
* `TauCeti.isRealCauchyRiemannOperator_dbarFunction_add_conjSMulDzbar`: `∂bar + ξbar dzbar` is a
  real Cauchy–Riemann operator,
  `TauCeti.not_isComplexLinearOperator_dbarFunction_add_conjSMulDzbar`: which is not complex
  linear, and
  `TauCeti.antilinearPart_dbarFunction_add_conjSMulDzbar`,
  `TauCeti.sectionComplexLinearPart_dbarFunction_add_conjSMulDzbar`: whose antilinear part is
  `ξ ↦ ξbar dzbar` and whose complex linear part is `∂bar`.
* `TauCeti.delFunction`: the operator `σ ↦ (dσ)^{1,0}` on complex valued functions on a complex
  curve, and `TauCeti.not_isRealCauchyRiemannOperator_delFunction`: it is not a real
  Cauchy–Riemann operator.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, Definition C.1.5 and Exercise C.1.7.
-/

public section

open Bundle Complex ComplexConjugate
open scoped ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

/-! ### `∂bar` on functions over an almost complex manifold -/

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

end SmoothAlmostComplexStructure

open SmoothAlmostComplexStructure

/-- On a complex normed space `E`, with multiplication by `i` as its almost complex structure,
`∂bar` on functions is the conjugate Wirtinger derivative. -/
theorem SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_self_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (σ : E → F) (x v : E) :
    (ofComplexManifold E E).dbarFunction σ x v = conjWirtingerDeriv σ x v := by
  rw [dbarFunction_apply, ofComplexManifold_apply, conjWirtingerDeriv_apply, mvfderiv_eq_fderiv,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_inv, Complex.coe_smul]
  rfl

/-! ### The operators `∂bar + ξbar dzbar` and `∂` on a complex curve -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ∞ M]

/-- The zeroth-order term `ξ ↦ ξbar dzbar` at a point `x` of a complex curve, whose tangent
spaces are `ℂ`: `(ξbar dzbar) (v) = conj ξ * conj v` (`TauCeti.conjSMulDzbar_apply`). -/
def conjSMulDzbar (x : M) : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ :=
  (ContinuousLinearMap.compL ℝ ℂ ℂ ℂ Complex.conjCLE.toContinuousLinearMap).comp
    (ContinuousLinearMap.mul ℝ ℂ)

omit [IsManifold 𝓘(ℂ, ℂ) ∞ M] in
@[simp]
theorem conjSMulDzbar_apply (x : M) (ξ v : ℂ) :
    conjSMulDzbar x ξ v = conj ξ * conj v :=
  map_mul (starRingEnd ℂ) ξ v

omit [IsManifold 𝓘(ℂ, ℂ) ∞ M] in
/-- The term `ξbar dzbar` is complex antilinear in `ξ`. -/
theorem conjSMulDzbar_complex_I_smul (x : M) (ξ : ℂ) :
    conjSMulDzbar x (Complex.I • ξ) = -(Complex.I • conjSMulDzbar x ξ) := by
  refine ContinuousLinearMap.ext fun (v : ℂ) ↦ (conjSMulDzbar_apply x _ v).trans
    (Eq.trans ?_ (congrArg (fun w : ℂ ↦ -(I • w)) (conjSMulDzbar_apply x ξ v)).symm)
  rw [smul_eq_mul, smul_eq_mul, map_mul, conj_I]
  ring

/-- The term `ξbar dzbar` is a `(0,1)`-form. -/
theorem isZeroOneForm_conjSMulDzbar (x : M) (ξ : ℂ) :
    (ofComplexManifold ℂ M).IsZeroOneForm (V := Bundle.Trivial M ℂ) (conjSMulDzbar x ξ) := by
  refine isZeroOneForm_iff.2 fun (v : ℂ) ↦ ?_
  rw [ofComplexManifold_apply]
  refine (conjSMulDzbar_apply x ξ _).trans
    (Eq.trans ?_ (congrArg (fun w : ℂ ↦ -(I • w)) (conjSMulDzbar_apply x ξ v)).symm)
  rw [smul_eq_mul, smul_eq_mul, map_mul, conj_I]
  ring

/-- The operator `ξ ↦ ∂bar ξ + ξbar dzbar` on a complex curve is a real Cauchy–Riemann operator
on the trivial line bundle. -/
theorem isRealCauchyRiemannOperator_dbarFunction_add_conjSMulDzbar :
    IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ M) (V := Bundle.Trivial M ℂ)
      fun σ x ↦ (ofComplexManifold ℂ M).dbarFunction σ x + conjSMulDzbar x (σ x) :=
  (ofComplexManifold ℂ M).isRealCauchyRiemannOperator_dbarFunction.add_zeroOrder
    conjSMulDzbar isZeroOneForm_conjSMulDzbar

/-- The complex linear part of `∂bar + ξbar dzbar` is `∂bar`. -/
theorem sectionComplexLinearPart_dbarFunction_add_conjSMulDzbar {σ : M → ℂ} {x : M}
    (hσ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) σ x) :
    sectionComplexLinearPart (V := Bundle.Trivial M ℂ)
      (fun σ x ↦ (ofComplexManifold ℂ M).dbarFunction σ x + conjSMulDzbar x (σ x)) σ x =
      (ofComplexManifold ℂ M).dbarFunction σ x :=
  sectionComplexLinearPart_eq_of_eq_add
    (ofComplexManifold ℂ M).isComplexLinearOperator_dbarFunction conjSMulDzbar
    conjSMulDzbar_complex_I_smul (fun _ _ _ ↦ rfl)
    (by simpa only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_apply] using hσ)

/-- The operator `ξ ↦ ∂bar ξ + ξbar dzbar` on a nonempty complex curve is not complex linear: its
complex linear part `∂bar` differs from it on the constant section `1`. -/
theorem not_isComplexLinearOperator_dbarFunction_add_conjSMulDzbar [Nonempty M] :
    ¬IsComplexLinearOperator ℂ (V := Bundle.Trivial M ℂ)
      fun σ x ↦ (ofComplexManifold ℂ M).dbarFunction σ x + conjSMulDzbar x (σ x) := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty M›
  have hσ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun _ : M ↦ (1 : ℂ)) x :=
    mdifferentiableAt_const
  -- A complex linear operator is its own complex linear part, which is `∂bar` here.
  have h₁ := (h.sectionComplexLinearPart_eq (by
    simpa only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_apply] using hσ)).symm.trans
    (sectionComplexLinearPart_dbarFunction_add_conjSMulDzbar hσ)
  have h₂ : conjSMulDzbar x (1 : ℂ) = 0 := add_eq_left.1 h₁
  have h₃ : conjSMulDzbar x (1 : ℂ) (1 : ℂ) = 0 := by rw [h₂]; rfl
  rw [conjSMulDzbar_apply, map_one, one_mul] at h₃
  exact one_ne_zero h₃

/-- The antilinear zeroth-order part of `∂bar + ξbar dzbar`, in the decomposition of
McDuff–Salamon, Exercise C.1.7, is `ξ ↦ ξbar dzbar`. -/
theorem antilinearPart_dbarFunction_add_conjSMulDzbar
    (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ M) (V := Bundle.Trivial M ℂ)
      fun σ x ↦ (ofComplexManifold ℂ M).dbarFunction σ x + conjSMulDzbar x (σ x))
    (x : M) : hD.antilinearPart x = conjSMulDzbar x :=
  hD.antilinearPart_eq_of_eq_add
    (ofComplexManifold ℂ M).isComplexLinearOperator_dbarFunction conjSMulDzbar
    conjSMulDzbar_complex_I_smul (fun _ _ _ ↦ rfl) x

variable (M) in
/-- The operator `∂ σ = (dσ)^{1,0} = dσ - ∂bar σ`, `∂ σ (v) = ½ (dσ (v) - i • dσ (i v))`, on
complex valued functions on a complex curve. -/
def delFunction (σ : M → ℂ) (x : M) : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ :=
  mvfderiv 𝓘(ℝ, ℂ) σ x - (ofComplexManifold ℂ M).dbarFunction σ x

theorem delFunction_apply (σ : M → ℂ) (x : M) (v : ℂ) :
    delFunction M σ x v = mvfderiv 𝓘(ℝ, ℂ) σ x v - (ofComplexManifold ℂ M).dbarFunction σ x v :=
  sub_apply _ _ v

/-- The chart coordinate `z` at `x₀` has derivative the identity at `x₀`. -/
private theorem mvfderiv_extChartAt_self_apply (x₀ : M) (v : ℂ) :
    mvfderiv 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) x₀) x₀ v = v := by
  simp only [mvfderiv, mfderiv_extChartAt_self]
  rfl

/-- The operator `∂` on a nonempty complex curve is not a real Cauchy–Riemann operator. For the
chart coordinate `z`, `∂ z` and `∂bar z` would both be `(0,1)`-forms, and so would their sum
`dz`, which is complex linear. -/
theorem not_isRealCauchyRiemannOperator_delFunction [Nonempty M] :
    ¬IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ M) (V := Bundle.Trivial M ℂ)
      (delFunction M) := by
  intro h
  obtain ⟨x₀⟩ := ‹Nonempty M›
  set z : M → ℂ := ⇑(extChartAt 𝓘(ℝ, ℂ) x₀)
  have h₁ := isZeroOneForm_iff.1 (h.isZeroOneForm z x₀) (1 : ℂ)
  have h₂ := isZeroOneForm_iff.1
    ((ofComplexManifold ℂ M).isRealCauchyRiemannOperator_dbarFunction.isZeroOneForm z x₀) (1 : ℂ)
  rw [ofComplexManifold_apply] at h₁ h₂
  have h₁' : delFunction M z x₀ (I * 1) = -(I * delFunction M z x₀ (1 : ℂ)) := h₁
  have h₂' : (ofComplexManifold ℂ M).dbarFunction z x₀ (I * 1) =
      -(I * (ofComplexManifold ℂ M).dbarFunction z x₀ (1 : ℂ)) := h₂
  have h₃ (v : ℂ) : delFunction M z x₀ v + (ofComplexManifold ℂ M).dbarFunction z x₀ v = v := by
    rw [delFunction_apply, sub_add_cancel, mvfderiv_extChartAt_self_apply]
  have h₄ : I = -I := by
    linear_combination -h₃ (I * 1) + h₁' + h₂' - I * h₃ 1
  have h₅ := congrArg Complex.im h₄
  norm_num at h₅

end TauCeti
