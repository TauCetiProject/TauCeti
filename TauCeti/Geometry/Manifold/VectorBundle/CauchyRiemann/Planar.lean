/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial

/-!
# The operator `∂bar + ξbar dzbar` on functions over a planar domain

On an open subset `U` of `ℂ`, such as the plane or the unit disc, with the coordinate `z` given by
the inclusion, every tangent space is `ℂ` and the `(0,1)`-form `dzbar` is `v ↦ conj v`. The operator
`ξ ↦ ∂bar ξ + ξbar dzbar` is a real Cauchy–Riemann operator on the trivial line bundle. On a
nonempty `U` it is not complex linear: its antilinear zeroth-order part in the decomposition of
McDuff–Salamon, Exercise C.1.7, is `ξ ↦ ξbar dzbar` and its complex linear part is `∂bar`
(`TauCeti.SmoothAlmostComplexStructure.dbarFunction`). That `∂` is not a real Cauchy–Riemann
operator is `TauCeti.SmoothAlmostComplexStructure.not_isRealCauchyRiemannOperator_delFunction`.

## Main declarations

* `TauCeti.conjSMulDzbar`: the zeroth-order term `ξ ↦ ξbar dzbar` on an open subset of `ℂ`.
* `TauCeti.isRealCauchyRiemannOperator_dbarFunction_add_conjSMulDzbar`: `∂bar + ξbar dzbar` is a
  real Cauchy–Riemann operator,
  `TauCeti.not_isComplexLinearOperator_dbarFunction_add_conjSMulDzbar`: which on a nonempty open
  subset is not complex linear, and
  `TauCeti.antilinearPart_dbarFunction_add_conjSMulDzbar`,
  `TauCeti.sectionComplexLinearPart_dbarFunction_add_conjSMulDzbar`: whose antilinear part is
  `ξ ↦ ξbar dzbar` and whose complex linear part is `∂bar`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, Definition C.1.5 and Exercise C.1.7.
-/

public section

open Bundle Complex ComplexConjugate
open scoped ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

open SmoothAlmostComplexStructure

/-! ### The operator `∂bar + ξbar dzbar` on an open subset of `ℂ` -/

variable {U : TopologicalSpace.Opens ℂ}

/-- The zeroth-order term `ξ ↦ ξbar dzbar` at a point `x` of an open subset `U` of `ℂ`, for the
coordinate `z` given by the inclusion of `U`, whose charts identify every tangent space of `U`
with `ℂ`: `(ξbar dzbar) (v) = conj ξ * conj v` (`TauCeti.conjSMulDzbar_apply`). -/
def conjSMulDzbar (x : U) : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ :=
  (ContinuousLinearMap.compL ℝ ℂ ℂ ℂ Complex.conjCLE.toContinuousLinearMap).comp
    (ContinuousLinearMap.mul ℝ ℂ)

@[simp]
theorem conjSMulDzbar_apply (x : U) (ξ v : ℂ) :
    conjSMulDzbar x ξ v = conj ξ * conj v :=
  map_mul (starRingEnd ℂ) ξ v

/-- The term `ξbar dzbar` is complex antilinear in `ξ`. -/
theorem conjSMulDzbar_complex_I_smul (x : U) (ξ : ℂ) :
    conjSMulDzbar x (Complex.I • ξ) = -(Complex.I • conjSMulDzbar x ξ) := by
  -- The tangent space `TangentSpace 𝓘(ℝ, ℂ) x` is a type synonym of `ℂ`, so the lemmas
  -- `neg_apply` and `smul_apply` do not rewrite a functional applied to `v : ℂ`; the evaluations
  -- are transported along `conjSMulDzbar_apply` instead.
  refine ContinuousLinearMap.ext fun (v : ℂ) ↦ (conjSMulDzbar_apply x _ v).trans
    (Eq.trans ?_ (congrArg (fun w : ℂ ↦ -(I • w)) (conjSMulDzbar_apply x ξ v)).symm)
  rw [smul_eq_mul, smul_eq_mul, map_mul, conj_I]
  ring

/-- The term `ξbar dzbar` is a `(0,1)`-form. -/
theorem isZeroOneForm_conjSMulDzbar (x : U) (ξ : ℂ) :
    (ofComplexManifold ℂ U).IsZeroOneForm (V := Bundle.Trivial U ℂ) (conjSMulDzbar x ξ) := by
  refine isZeroOneForm_iff.2 fun (v : ℂ) ↦ ?_
  rw [ofComplexManifold_apply]
  -- As in `conjSMulDzbar_complex_I_smul`, the fibre `Bundle.Trivial U ℂ x` and the tangent space
  -- are type synonyms of `ℂ`, so the evaluations are transported along `conjSMulDzbar_apply`.
  refine (conjSMulDzbar_apply x ξ _).trans
    (Eq.trans ?_ (congrArg (fun w : ℂ ↦ -(I • w)) (conjSMulDzbar_apply x ξ v)).symm)
  rw [smul_eq_mul, smul_eq_mul, map_mul, conj_I]
  ring

/-- The operator `ξ ↦ ∂bar ξ + ξbar dzbar` on an open subset of `ℂ` is a real Cauchy–Riemann
operator on the trivial line bundle. -/
theorem isRealCauchyRiemannOperator_dbarFunction_add_conjSMulDzbar :
    IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ U) (V := Bundle.Trivial U ℂ)
      fun σ x ↦ (ofComplexManifold ℂ U).dbarFunction σ x + conjSMulDzbar x (σ x) :=
  (ofComplexManifold ℂ U).isRealCauchyRiemannOperator_dbarFunction.add_zeroOrder
    conjSMulDzbar isZeroOneForm_conjSMulDzbar

/-- The complex linear part of `∂bar + ξbar dzbar` is `∂bar`. -/
@[simp]
theorem sectionComplexLinearPart_dbarFunction_add_conjSMulDzbar (σ : U → ℂ) (x : U) :
    sectionComplexLinearPart (V := Bundle.Trivial U ℂ)
      (fun σ x ↦ (ofComplexManifold ℂ U).dbarFunction σ x + conjSMulDzbar x (σ x)) σ x =
      (ofComplexManifold ℂ U).dbarFunction σ x := by
  rw [sectionComplexLinearPart_apply, dbarFunction_const_smul, Pi.smul_apply,
    conjSMulDzbar_complex_I_smul]
  simp only [smul_add, smul_neg, smul_smul Complex.I Complex.I, Complex.I_mul_I]
  module

/-- The operator `ξ ↦ ∂bar ξ + ξbar dzbar` on a nonempty open subset of `ℂ` is not complex
linear. -/
theorem not_isComplexLinearOperator_dbarFunction_add_conjSMulDzbar [Nonempty U] :
    ¬IsComplexLinearOperator ℂ (V := Bundle.Trivial U ℂ)
      fun σ x ↦ (ofComplexManifold ℂ U).dbarFunction σ x + conjSMulDzbar x (σ x) := by
  -- Its complex linear part `∂bar` differs from it on the constant section `1`.
  intro h
  obtain ⟨x⟩ := ‹Nonempty U›
  have hσ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun _ : U ↦ (1 : ℂ)) x :=
    mdifferentiableAt_const
  -- A complex linear operator is its own complex linear part, which is `∂bar` here.
  have h₁ := (h.sectionComplexLinearPart_eq (by
    simpa only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_apply] using hσ)).symm.trans
    (sectionComplexLinearPart_dbarFunction_add_conjSMulDzbar _ x)
  have h₂ : conjSMulDzbar x (1 : ℂ) = 0 := add_eq_left.1 h₁
  have h₃ : conjSMulDzbar x (1 : ℂ) (1 : ℂ) = 0 := by
    -- The zero functional on the type synonym `TangentSpace 𝓘(ℝ, ℂ) x` of `ℂ` evaluates to `0`.
    rw [h₂]; rfl
  rw [conjSMulDzbar_apply, map_one, one_mul] at h₃
  exact one_ne_zero h₃

/-- The antilinear zeroth-order part of `∂bar + ξbar dzbar`, in the decomposition of
McDuff–Salamon, Exercise C.1.7, is `ξ ↦ ξbar dzbar`. -/
@[simp]
theorem antilinearPart_dbarFunction_add_conjSMulDzbar
    (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ U) (V := Bundle.Trivial U ℂ)
      fun σ x ↦ (ofComplexManifold ℂ U).dbarFunction σ x + conjSMulDzbar x (σ x))
    (x : U) : hD.antilinearPart x = conjSMulDzbar x :=
  hD.antilinearPart_eq_of_eq_add
    (ofComplexManifold ℂ U).isComplexLinearOperator_dbarFunction conjSMulDzbar
    conjSMulDzbar_complex_I_smul (fun _ _ _ ↦ rfl) x

end TauCeti
