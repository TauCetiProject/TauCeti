/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The operators `∂bar` and `∂` on functions over an almost complex manifold

Let `j` be a smooth almost complex structure on a manifold `M` and `F` a complex normed space.
Functions `M → F` are the sections of the trivial bundle `M × F`, and their `∂bar`,
`∂bar σ = (dσ)^{0,1}`, is the `(0,1)`-part of the canonical connection of the trivial bundle. So
it is a complex linear real Cauchy–Riemann operator: `∂bar (g σ) = g ∂bar σ + (∂bar g) ⊗ σ` for
real valued `g`. The complementary operator `∂ σ = dσ - ∂bar σ = (dσ)^{1,0}` is also defined here;
its values are `(1,0)`-forms, so it is not a real Cauchy–Riemann operator.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.dbarFunction`: the operator `σ ↦ (dσ)^{0,1}` on
  `F`-valued functions.
* `TauCeti.SmoothAlmostComplexStructure.isRealCauchyRiemannOperator_dbarFunction`,
  `TauCeti.SmoothAlmostComplexStructure.isComplexLinearOperator_dbarFunction`: it is a complex
  linear real Cauchy–Riemann operator on the trivial bundle.
* `TauCeti.SmoothAlmostComplexStructure.dbarFunction_const_smul`: it commutes with multiplication
  by a complex constant, with no differentiability hypothesis.
* `TauCeti.SmoothAlmostComplexStructure.delFunction`: the operator `σ ↦ (dσ)^{1,0}` on
  `F`-valued functions.
* `TauCeti.SmoothAlmostComplexStructure.delFunction_add_dbarFunction`,
  `TauCeti.SmoothAlmostComplexStructure.delFunction_apply_almostComplex`: `dσ = ∂ σ + ∂bar σ`, and
  `∂ σ` is a `(1,0)`-form.
* `TauCeti.SmoothAlmostComplexStructure.not_isRealCauchyRiemannOperator_delFunction`: `∂` is not a
  real Cauchy–Riemann operator on a nonempty manifold of positive dimension with nonzero target.

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

/-- `∂bar σ` is a `(0,1)`-form: `∂bar σ (j v) = -(i • ∂bar σ (v))`. -/
@[simp]
theorem dbarFunction_apply_almostComplex (σ : M → F) (x : M) (v : TangentSpace I x) :
    j.dbarFunction σ x (j x v) = -(Complex.I • j.dbarFunction σ x v) := by
  rw [dbarFunction, zeroOnePart_apply, zeroOnePart_apply, apply_apply, map_neg]
  simp only [smul_add, smul_neg, smul_comm Complex.I (2⁻¹ : ℝ), smul_smul Complex.I Complex.I,
    Complex.I_mul_I, neg_one_smul]
  module

/-- `∂bar` vanishes on constant functions. -/
@[simp]
theorem dbarFunction_const (c : F) (x : M) : j.dbarFunction (fun _ ↦ c) x = 0 := by
  rw [dbarFunction, mvfderiv_const]
  ext v
  simp

/-- `∂bar` on functions is additive on functions differentiable at the point. -/
theorem dbarFunction_add {σ τ : M → F} {x : M} (hσ : MDifferentiableAt I 𝓘(ℝ, F) σ x)
    (hτ : MDifferentiableAt I 𝓘(ℝ, F) τ x) :
    j.dbarFunction (σ + τ) x = j.dbarFunction σ x + j.dbarFunction τ x := by
  ext v
  simp only [dbarFunction, zeroOnePart_apply, add_apply, mvfderiv_add hσ hτ]
  module

/-- `∂bar` on functions commutes with multiplication by a complex constant. -/
@[simp]
theorem dbarFunction_const_smul (c : ℂ) (σ : M → F) (x : M) :
    j.dbarFunction (c • σ) x = c • j.dbarFunction σ x := by
  -- The derivative commutes with `c •`: both sides vanish if `σ` is not differentiable at `x`.
  have hd : mvfderiv I (c • σ) x = c • mvfderiv I σ x := by
    by_cases hσ : MDifferentiableAt I 𝓘(ℝ, F) σ x
    · exact mvfderiv_const_smul hσ c
    rcases eq_or_ne c 0 with rfl | hc
    · simp only [zero_smul]
      exact mvfderiv_zero
    have hcσ : ¬MDifferentiableAt I 𝓘(ℝ, F) (c • σ) x := fun hcσ ↦ hσ (by
      simpa [Function.comp_def, smul_smul, inv_mul_cancel₀ hc] using
        ((c⁻¹ • ContinuousLinearMap.id ℝ F).mdifferentiableAt (x := (c • σ) x)).comp x hcσ)
    simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hσ,
      mfderiv_zero_of_not_mdifferentiableAt hcσ]
  ext v
  rw [smul_apply, dbarFunction, dbarFunction, zeroOnePart_apply, zeroOnePart_apply, hd,
    smul_apply, smul_apply, smul_comm Complex.I c,
    ← smul_add, smul_comm (2⁻¹ : ℝ) c]

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

/-- `∂bar` on functions is a complex linear operator on the trivial bundle. -/
theorem isComplexLinearOperator_dbarFunction :
    IsComplexLinearOperator F (V := Bundle.Trivial M F) j.dbarFunction := by
  rw [dbarFunction_eq_zeroOnePart_trivial]
  refine (CovariantDerivative.trivial (I := I) (M := M) F).isCovariantDerivativeOnUniv
    |>.isComplexLinearOperator_zeroOnePart j fun σ x hσ ↦ ?_
  simp only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
    Trivial.trivialization_apply] at hσ
  simp only [CovariantDerivative.trivial_apply]
  exact mvfderiv_const_smul hσ Complex.I

/-- The operator `∂ σ = (dσ)^{1,0} = dσ - ∂bar σ` on functions `σ : M → F` into a complex normed
space: `∂ σ (v) = ½ (dσ (v) - i • dσ (j v))`
(`TauCeti.SmoothAlmostComplexStructure.delFunction_apply`). -/
def delFunction (σ : M → F) (x : M) : TangentSpace I x →L[ℝ] F :=
  mvfderiv I σ x - j.dbarFunction σ x

theorem delFunction_apply (σ : M → F) (x : M) (v : E) :
    j.delFunction σ x v =
      (2⁻¹ : ℝ) • (mvfderiv I σ x v - Complex.I • mvfderiv I σ x (j x v)) :=
  ((sub_apply _ _ v).trans (congrArg (mvfderiv I σ x v - ·) (j.dbarFunction_apply σ x v))).trans
    (by module)

/-- The differential splits as `dσ = ∂ σ + ∂bar σ`. -/
@[simp]
theorem delFunction_add_dbarFunction (σ : M → F) (x : M) :
    j.delFunction σ x + j.dbarFunction σ x = mvfderiv I σ x :=
  sub_add_cancel _ _

/-- `∂` vanishes on constant functions. -/
@[simp]
theorem delFunction_const (c : F) (x : M) : j.delFunction (fun _ ↦ c) x = 0 := by
  rw [delFunction, dbarFunction_const, mvfderiv_const, sub_zero]

/-- `∂ σ` is a `(1,0)`-form: it is complex linear, `∂ σ (j v) = i • ∂ σ (v)`. -/
@[simp]
theorem delFunction_apply_almostComplex (σ : M → F) (x : M) (v : TangentSpace I x) :
    j.delFunction σ x (j x v) = Complex.I • j.delFunction σ x v := by
  rw [delFunction, dbarFunction, sub_apply, sub_apply, zeroOnePart_apply, zeroOnePart_apply,
    apply_apply, map_neg]
  simp only [smul_sub, smul_add, smul_neg, smul_comm Complex.I (2⁻¹ : ℝ),
    smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul]
  module

/-- The operator `∂` on functions into a nonzero complex normed space, over a nonempty manifold
of positive dimension, is not a real Cauchy–Riemann operator: its values are not all
`(0,1)`-forms. -/
theorem not_isRealCauchyRiemannOperator_delFunction [Nontrivial E] [Nontrivial F] [Nonempty M] :
    ¬IsRealCauchyRiemannOperator F j (V := Bundle.Trivial M F) j.delFunction := by
  -- Read `z = f (φ y) • w` in the chart `φ` at `x₀`, for a real linear form `f` and `w ≠ 0`. If
  -- `∂ z` were a `(0,1)`-form at `x₀` it would vanish, being a `(1,0)`-form, so `dz = ∂bar z`
  -- would be a `(0,1)`-form; but `dz (j v) = f (j v) • w` is not `-(i • f v • w)` if `f v ≠ 0`.
  intro h
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  obtain ⟨f, -, hf⟩ := exists_dual_vector ℝ v (norm_ne_zero_iff.2 hv)
  obtain ⟨w, hw⟩ := exists_ne (0 : F)
  set z : M → F := f.smulRight w ∘ extChartAt I x₀
  have hdz (u : TangentSpace I x₀) : mvfderiv I z x₀ u = f u • w := by
    rw [ContinuousLinearMap.mvfderiv_comp_apply _
      (mdifferentiableAt_extChartAt (mem_chart_source H x₀)),
      mvfderiv_apply_of_eventuallyEq_extChartAt .rfl]
    -- The tangent vector `u` is read as a vector of the model space `E`.
    rfl
  have hdel (u : TangentSpace I x₀) : j.delFunction z x₀ u = 0 := by
    have h₁ := isZeroOneForm_iff.1 (h.isZeroOneForm z x₀) u
    rw [delFunction_apply_almostComplex, eq_neg_iff_add_eq_zero, ← two_smul ℂ, smul_eq_zero,
      smul_eq_zero] at h₁
    simpa [Complex.I_ne_zero] using h₁
  have hdbar (u : TangentSpace I x₀) : j.dbarFunction z x₀ u = f u • w := by
    rw [← hdz, ← delFunction_add_dbarFunction, add_apply, hdel, zero_add]
  have h₂ := dbarFunction_apply_almostComplex j z x₀ v
  rw [hdbar (j x₀ v), hdbar v] at h₂
  have h₃ : ((f (j x₀ v) : ℂ) + Complex.I * f v) • w = 0 := by
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, h₂, neg_add_cancel]
  have h₄ := congrArg Complex.im ((smul_eq_zero.1 h₃).resolve_right hw)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add, Complex.zero_im] at h₄
  rw [hf, RCLike.ofReal_real_eq_id, id, norm_eq_zero] at h₄
  exact hv h₄

end SmoothAlmostComplexStructure

end TauCeti
