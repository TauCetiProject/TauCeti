/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.TestFunction.Convolution.Basic
public import TauCeti.Geometry.Lie.TestFunction.RightDeriv.Basic
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Deriv

/-!
# Derivatives of a convolution of test functions

Let `G` be a real Lie group modelled on a complete space and `μ` a measure on `G` that is finite on
compact sets. The left and right differentiations of test functions are the derivatives along the
exponential lines through a point:

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
* `TauCeti.LieTestFunction.leftDeriv_convolution`: `L_X (a * b) = L_X a * b` for a left-invariant
  measure.

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

/-- **Left differentiation acts on the first factor of a convolution** for a left-invariant
measure: `L_X (a * b) = L_X a * b`. -/
theorem leftDeriv_convolution [MeasurableMul G] [μ.IsMulLeftInvariant] (X : GroupLieAlgebra I G)
    (a b : LieTestFunction I G) :
    leftDeriv X (convolution μ a b) = convolution μ (leftDeriv X a) b := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  ext g
  let e : ℝ → G := fun t ↦ mulInvariantExp (I := I) (G := G) (t • X)
  have he : ContMDiff 𝓘(ℝ, ℝ) I ∞ e := contMDiff_mulInvariantExp_smul X
  let f : ℝ → G → ℂ := fun t x ↦ a (e t * x) * b (x⁻¹ * g)
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℂ) ∞ (uncurry f) :=
    ((ContinuousLinearMap.mul ℝ ℂ).contMDiff.comp
      (a.contMDiff.comp ((he.comp contMDiff_fst).mul contMDiff_snd))).clm_apply
      (b.contMDiff.comp (contMDiff_snd.inv.mul contMDiff_const))
  -- the integrand vanishes unless `x⁻¹ * g ∈ tsupport b`, a compact condition on `x`
  let K : Set G := (fun y ↦ g * y⁻¹) '' tsupport b
  have hK : IsCompact K := b.hasCompactSupport.isCompact.image (by fun_prop)
  have hKb {x : G} (hx : x ∉ K) : x⁻¹ * g ∉ tsupport b := fun h ↦ hx ⟨x⁻¹ * g, h, by group⟩
  have hderiv := hK.hasDerivAt_parametric_integral (μ := μ) (t₀ := 0) (f := f)
    hK.isClosed.measurableSet hK.measure_lt_top.ne
    (fun x _ ↦ (hf (0, x)).of_le (by simp))
    (.of_forall fun t x hx ↦ by simp [f, image_eq_zero_of_notMem_tsupport (hKb hx)])
  have hfx (x : G) : deriv (fun s ↦ f s x) 0 = leftDeriv X a x * b (x⁻¹ * g) :=
    ((hasDerivAt_apply_mulInvariantExp_smul_mul_zero X a x).mul_const (b (x⁻¹ * g))).deriv
  simp only [hfx] at hderiv
  refine (hasDerivAt_apply_mulInvariantExp_smul_mul_zero X (convolution μ a b) g).unique ?_
  -- substitute `x ↦ exp(tX) x` in `(a * b) (exp(tX) g)`
  have hconv (t : ℝ) :
      convolution μ a b (mulInvariantExp (I := I) (G := G) (t • X) * g) = ∫ x, f t x ∂μ := by
    rw [convolution_apply, ← integral_mul_left_eq_self _ (e t)]
    simp [f, e, mul_assoc]
  rw [funext hconv, convolution_apply]
  exact hderiv

end LieTestFunction

end TauCeti
