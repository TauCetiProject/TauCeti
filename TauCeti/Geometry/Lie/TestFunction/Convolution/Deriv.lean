/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.TestFunction.Convolution.Basic
public import TauCeti.Geometry.Lie.TestFunction.RightDeriv.Basic
import TauCeti.Geometry.Lie.TestFunction.Continuity
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Deriv
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Derivatives of a convolution of test functions

Let `G` be a real Lie group and `μ` a measure on `G` that is finite on compact sets.
On complete models the left and right differentiations of test functions can be computed
along exponential lines through a point:

`R(X) a (g) = d/dt|₀ a (g exp(tX))`, `L_X a (g) = d/dt|₀ a (exp(tX) g)`

(`TauCeti.LieTestFunction.hasDerivAt_apply_mul_mulInvariantExp_smul_zero`,
`TauCeti.LieTestFunction.hasDerivAt_apply_mulInvariantExp_smul_mul_zero`).
Differentiating the convolution `(a * b) g = ∫ x, a x * b (x⁻¹ g) ∂μ` under the integral sign then
moves each derivative onto one factor:

* `R(X) (a * b) = a * R(X) b`, since `(a * b) (g exp(tX)) = ∫ x, a x * b (x⁻¹ g exp(tX)) ∂μ`;
* `L_X (a * b) = L_X a * b` for a left-invariant measure, since then
  `(a * b) (exp(tX) g) = ∫ x, a (exp(tX) x) * b (x⁻¹ g) ∂μ`.

In both cases the integrand vanishes outside one compact set for every `t`: outside the support
of `a` in the first, and outside `g (supp b)⁻¹` in the second.

## Main results

* `TauCeti.LieTestFunction.rightDeriv_convolution`: `R(X) (a * b) = a * R(X) b`.
* `TauCeti.LieTestFunction.leftDeriv_convolution`,
  `MeasureTheory.Measure.leftDerivWord_convolution`:
  left differentiation acts on the first factor for a left-invariant measure.

## References

* J. R. Getz, *An introduction to automorphic representations*, §3.3.
* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §2.5.
-/

public section

noncomputable section

open Function MeasureTheory Set
open scoped ContDiff Manifold

namespace TauCeti

namespace LieTestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-! ### Derivatives of convolutions -/

variable [I.Boundaryless] [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ]

/-- **Right differentiation acts on the second factor of a convolution**:
`R(X) (a * b) = a * R(X) b`. -/
theorem rightDeriv_convolution (X : GroupLieAlgebra I G) (a b : LieTestFunction I G) :
    rightDeriv X (convolution μ a b) = convolution μ a (rightDeriv X b) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  ext g
  let e : ℝ → G := fun t ↦ mulInvariantExp (I := I) (G := G) (t • X)
  have he : ContMDiff 𝓘(ℝ, ℝ) I ∞ e := contMDiff_mulInvariantExp_smul X
  let f : ℝ → G → ℂ := fun t x ↦ a x * b (x⁻¹ * (g * e t))
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℂ) ∞ (uncurry f) :=
    ((ContinuousLinearMap.mul ℝ ℂ).contMDiff.comp (a.contMDiff.comp contMDiff_snd)).clm_apply
      (b.contMDiff.comp (contMDiff_snd.inv.mul (contMDiff_const.mul (he.comp contMDiff_fst))))
  have hK := a.hasCompactSupport.isCompact
  have hderiv := hK.hasDerivAt_parametric_integral (μ := μ) (t₀ := 0) (f := f)
    (isClosed_tsupport _).measurableSet hK.measure_lt_top.ne
    (fun x _ ↦ (hf (0, x)).of_le (by simp))
    (.of_forall fun t x hx ↦ by simp [f, image_eq_zero_of_notMem_tsupport hx])
  have hfx (x : G) : deriv (fun s ↦ f s x) 0 = a x * rightDeriv X b (x⁻¹ * g) := by
    have h := (hasDerivAt_apply_mul_mulInvariantExp_smul_zero X b (x⁻¹ * g)).const_mul (a x)
    simp only [mul_assoc] at h
    exact h.deriv
  simp only [hfx] at hderiv
  refine (hasDerivAt_apply_mul_mulInvariantExp_smul_zero X (convolution μ a b) g).unique ?_
  simpa [f, e] using hderiv

omit [CompleteSpace E] [I.Boundaryless] in
/-- **Left differentiation acts on the first factor of a convolution** for a left-invariant
measure: `L_X (a * b) = L_X a * b`. -/
theorem leftDeriv_convolution [μ.IsMulLeftInvariant]
    (a b : LieTestFunction I G) (X : GroupLieAlgebra I G) :
    leftDeriv X (convolution μ a b) = convolution μ (leftDeriv X a) b := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have hi : I.IsInteriorPoint (1 : G) := ContMDiffMul.isInteriorPoint (n := ∞) (by simp) 1
  obtain ⟨γ, hγ₀, hγ, hvel⟩ := Manifold.exists_contMDiffAt_curveVelocity_eq (n := 1) 1 hi X 0
  have hcurve (c : LieTestFunction I G) (y : G) :
      HasDerivAt (fun t ↦ c (γ t * y)) (leftDeriv X c y) 0 := by
    have hγ' := Manifold.hasMFDerivAt_curveVelocity (hγ.mdifferentiableAt one_ne_zero)
    have hc := (rightTranslate y c).contMDiff.mdifferentiableAt (x := γ 0) (by simp)
    have hd := Manifold.hasDerivAt_comp_curve hc hγ'
    have heq := congrArg (fun z : G ↦ mvfderiv I (rightTranslate y c) z X) hγ₀
    rw [hvel, heq, ← mulRightInvariantVectorField_one (I := I) (G := G) X,
      ← leftDeriv_apply, leftDeriv_rightTranslate] at hd
    simpa only [Function.comp_def, rightTranslate_apply, one_mul] using hd
  ext g
  let f : ℝ → G → ℂ := fun t x ↦ a (γ t * x) * b (x⁻¹ * g)
  have hf (x : G) : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, ℂ) 1 (uncurry f) (0, x) := by
    have ha := a.contMDiff.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
    have hb := b.contMDiff.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
    have hab := ((ContinuousLinearMap.mul ℝ ℂ).contMDiff.contMDiffAt.comp (0, x)
      (ha.contMDiffAt.comp (0, x)
        ((hγ.comp (0, x) contMDiff_fst.contMDiffAt).mul contMDiff_snd.contMDiffAt))).clm_apply
      (hb.comp (contMDiff_snd.inv.mul (contMDiff_const (c := g)))).contMDiffAt
    simpa only [uncurry_def, Function.comp_apply, Pi.mul_apply, ContinuousLinearMap.mul_apply']
      using hab
  let K : Set G := (fun y ↦ g * y⁻¹) '' tsupport b
  have hK : IsCompact K := b.hasCompactSupport.isCompact.image (by fun_prop)
  have hKb {x : G} (hx : x ∉ K) : x⁻¹ * g ∉ tsupport b := fun h ↦ hx ⟨_, h, by group⟩
  have hderiv := hK.hasDerivAt_parametric_integral (μ := μ) (t₀ := 0) (f := f)
    hK.isClosed.measurableSet hK.measure_lt_top.ne (fun x _ ↦ hf x)
    (.of_forall fun t x hx ↦ by simp only [f, image_eq_zero_of_notMem_tsupport (hKb hx), mul_zero])
  have hfx (x : G) : deriv (fun s ↦ f s x) 0 = leftDeriv X a x * b (x⁻¹ * g) :=
    ((hcurve a x).mul_const (b (x⁻¹ * g))).deriv
  simp only [hfx] at hderiv
  refine (hcurve (convolution μ a b) g).unique ?_
  have hconv (t : ℝ) : convolution μ a b (γ t * g) = ∫ x, f t x ∂μ := by
    rw [convolution_apply]
    by_cases hμ : μ = 0
    · simp only [hμ, integral_zero_measure]
    have hmap := map_mul_left_eq_self μ (γ t)
    -- A non-AE-measurable pushforward would force `μ` to be a Dirac measure.
    have hm : AEMeasurable (γ t * ·) μ := by
      by_contra h
      have hdirac := hmap.symm.trans (Measure.map_of_not_aemeasurable_of_ne_zero h hμ)
      have : MeasurableSingletonClass G := ⟨fun x ↦ isClosed_singleton.measurableSet⟩
      exact h (hdirac ▸ aemeasurable_dirac)
    have hint := (integrable_mul_inv_mul μ a b (γ t * g)).aestronglyMeasurable
    rw [← hmap] at hint
    conv_lhs => rw [← hmap, integral_map hm hint]
    simp only [f, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  rwa [funext hconv, convolution_apply]

omit [CompleteSpace E] [I.Boundaryless] in
/-- Iterated left differentiation of a convolution against a left-invariant measure acts on
the first factor. -/
theorem _root_.MeasureTheory.Measure.leftDerivWord_convolution [μ.IsMulLeftInvariant]
    (a b : LieTestFunction I G) (w : List (GroupLieAlgebra I G)) :
    leftDerivWord w (convolution μ a b) = convolution μ (leftDerivWord w a) b := by
  induction w with
  | nil => simp only [leftDerivWord_nil, LinearMap.id_apply]
  | cons X w ih =>
    rw [leftDerivWord_cons, LinearMap.comp_apply, ih, leftDeriv_convolution, LinearMap.comp_apply]

end LieTestFunction

end TauCeti
