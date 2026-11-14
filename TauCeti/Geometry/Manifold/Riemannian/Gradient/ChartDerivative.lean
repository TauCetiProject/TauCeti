/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Symmetric.Signature
public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.VectorField.Chart.Derivative
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The chart derivative of a gradient at a critical point

Let `f` be a function on a boundaryless manifold `M` with a continuous Riemannian metric `g`, and
let `x` be a critical point of `f` at which `f` is `C²` and its gradient is differentiable, as
holds for a `C²` function and a `C¹` metric (`TauCeti.Manifold.contMDiffAt_mgradient`). The
gradient `grad f` vanishes at `x`, so its chart derivative
`D = TauCeti.vectorFieldChartDerivative I (grad f) x` is the derivative of a vector field at a
zero, whose determinant sign is the local index of the zero in the Poincaré–Hopf theorem. This
file identifies `D` with the critical Hessian raised by the metric at `x`:
`g_x (w, D v) = Hess f x (v, w)` (`TauCeti.inner_vectorFieldChartDerivative_mgradient`).
Consequently `D` is `g_x`-symmetric (`TauCeti.inner_vectorFieldChartDerivative_mgradient_comm`),
it is invertible exactly at a nondegenerate critical point, and there the sign of its determinant
is `(-1)` to the Morse index of `f` at `x`
(`TauCeti.sign_det_vectorFieldChartDerivative_mgradient`). In particular the index of the zero
of a gradient field does not depend on the metric.

The identification rests on a product rule at a zero
(`MDifferentiableAt.mvfderiv_inner_bundle_apply_of_eq_zero`): if a vector field `σ` is
differentiable at `x` and vanishes there, and `τ` is continuous at `x`, then `y ↦ g_y (σ y, τ y)`
is differentiable at `x` with derivative `v ↦ g_x (τ x, D v)`, where `D` is the chart derivative
of `σ`. Since `σ x = 0`, the variation of the metric and of `τ` does not contribute, so only the
continuity of the metric and of `τ` is needed. Applied to `σ = grad f` and a field `τ` with
`τ x = w`, the function `g(grad f, τ) = df(τ)` has derivative `Hess f x (·, w)` at the critical
point `x`.

## Main results

* `MDifferentiableAt.inner_bundle_of_eq_zero`,
  `MDifferentiableAt.mvfderiv_inner_bundle_apply_of_eq_zero`: the derivative of the metric
  pairing of a vector field with another at a zero of the first.
* `TauCeti.inner_vectorFieldChartDerivative_mgradient`: at a critical point, the chart derivative
  of the gradient is the critical Hessian raised by the metric.
* `TauCeti.inner_vectorFieldChartDerivative_mgradient_comm`: it is symmetric for the metric.
* `TauCeti.vectorFieldChartDerivative_mgradient_apply_eq_zero_iff`: its kernel is the kernel of
  the critical Hessian.
* `TauCeti.det_vectorFieldChartDerivative_mgradient_ne_zero_iff`: its determinant is nonzero
  exactly at a nondegenerate critical point.
* `TauCeti.sign_det_vectorFieldChartDerivative_mgradient`: at a nondegenerate critical point the
  sign of its determinant is `(-1) ^ manifoldMorseIndex I f x`.

## References

* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §6 (the index of a gradient field at a nondegenerate critical point).
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §2.
-/

public section

open Bundle Filter Set VectorField
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

section ProductRule

variable {σ τ : (x : M) → TangentSpace I x} {x : M}

/-- In the chart at a zero `x` of `σ`, the metric pairing of `σ` with a field `τ` continuous at
`x` has a derivative which evaluates to `g_x (τ x, D v)`, where `D` is the chart derivative of
`σ`. In the chart, the pairing is `z ↦ c z (U z)` for the coordinate field `U` of `σ` and the
continuous family `c z = g (τ, ·)` read through the inverse trivialization; at a zero of `U` only
the continuity of `c` matters. -/
private theorem exists_hasFDerivAt_inner_comp_extChartAt_symm_of_eq_zero
    (hσ : MDifferentiableAt I I.tangent (fun y ↦ (σ y : TangentBundle I M)) x) (hσ₀ : σ x = 0)
    (hτ : ContinuousAt (fun y ↦ (τ y : TangentBundle I M)) x) :
    ∃ L : E →L[ℝ] ℝ, HasFDerivAt ((fun y ↦ inner ℝ (σ y) (τ y)) ∘ (extChartAt I x).symm) L
      (extChartAt I x x) ∧
        ∀ v, L v = inner ℝ (τ x) (vectorFieldChartDerivative I σ x v : TangentSpace I x) := by
  set φ := extChartAt I x
  set e := trivializationAt E (TangentSpace I) x
  let U : E → E := mpullback 𝓘(ℝ, E) I φ.symm σ
  -- The coordinate field of `σ` is differentiable at the chart point, where it vanishes.
  have hU : DifferentiableAt ℝ U (φ x) := by
    have h := MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_extChartAt_symm
      (s := univ) hσ.mdifferentiableWithinAt
    rw [I.range_eq_univ, mpullbackWithin_univ, preimage_univ, inter_univ] at h
    exact h.differentiableAt univ_mem
  have hU₀ : U (φ x) = 0 := by
    simp only [U, φ, mpullback_extChartAt_symm_apply_eq_mfderiv σ (mem_extChartAt_source x), hσ₀,
      map_zero]
    -- The zero of the tangent space at the chart point is the zero of `E`.
    rfl
  -- The pairing with `τ`, read through the inverse trivialization, is continuous at the chart
  -- point: against each fixed `u` it pairs `τ` with the field of constant coordinates `u`.
  let c : E → E →L[ℝ] ℝ := fun z ↦ (innerSL ℝ (τ (φ.symm z))) ∘L e.symmL ℝ (φ.symm z)
  have hc : ContinuousAt c (φ x) := by
    rw [continuousAt_clm_apply]
    intro u
    let X := FiberBundle.extend E (e.symm x u)
    have hX : ∀ p, X p = e.symm p u := fun p ↦ by
      simp only [X, FiberBundle.extend, e]
      rw [Trivialization.apply_mk_symm _ (FiberBundle.mem_baseSet_trivializationAt' x)]
    have hXc : ContinuousAt (fun p ↦ (X p : TangentBundle I M)) x :=
      (FiberBundle.contMDiffAt_extend (k := 0) I E (e.symm x u)).continuousAt
    have h := (ContinuousAt.inner_bundle hτ hXc).comp_of_eq
      (continuousAt_extChartAt_symm (I := I) x) (extChartAt_to_inv x)
    refine h.congr ?_
    filter_upwards [extChartAt_target_mem_nhds (I := I) x] with z hz
    rw [Function.comp_apply, hX, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      Trivialization.symmL_apply _ (TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hz)]
  refine ⟨c (φ x) ∘L fderiv ℝ U (φ x), ?_, fun v ↦ ?_⟩
  · have h₁ := (HasFDerivWithinAt.clm_apply_of_eq_zero hc.continuousWithinAt
      hU.hasFDerivAt.hasFDerivWithinAt hU₀).hasFDerivAt univ_mem
    refine h₁.congr_of_eventuallyEq ?_
    filter_upwards [extChartAt_target_mem_nhds (I := I) x] with z hz
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ φ.source, φ y = z := ⟨_, φ.map_target hz, φ.right_inv hz⟩
    have hb : y ∈ e.baseSet := by
      simpa only [e, TangentBundle.trivializationAt_baseSet, φ, extChartAt_source] using hy
    -- In the chart, `σ` is recovered from its coordinate field by the inverse trivialization.
    have hσy : e.symmL ℝ y (U (φ y)) = σ y := by
      have h₁ : U (φ y) = e.continuousLinearMapAt ℝ y (σ y) :=
        (mpullback_extChartAt_symm_apply_eq_mfderiv σ hy).trans (DFunLike.congr_fun
          (TangentBundle.continuousLinearMapAt_trivializationAt (by simpa [φ] using hy))
            (σ y)).symm
      rw [h₁, Trivialization.symmL_continuousLinearMapAt _ hb]
    simp only [Function.comp_apply, c]
    rw [φ.left_inv hy, ContinuousLinearMap.comp_apply, innerSL_apply_apply, hσy, real_inner_comm]
  · have hxx : φ.symm (φ x) = x := extChartAt_to_inv x
    simp only [ContinuousLinearMap.comp_apply, c, innerSL_apply_apply]
    rw [hxx, Manifold.symmL_trivializationAt_self, vectorFieldChartDerivative_def]
    -- The chart derivative is the derivative of the coordinate field `U` at the chart point.
    rfl

/-- **The metric pairing at a zero is differentiable.** If a vector field `σ` is differentiable at
a zero `x` and `τ` is continuous at `x`, then for a continuous metric the pairing
`y ↦ g_y (σ y, τ y)` is differentiable at `x`. -/
theorem _root_.MDifferentiableAt.inner_bundle_of_eq_zero
    (hσ : MDifferentiableAt I I.tangent (fun y ↦ (σ y : TangentBundle I M)) x) (hσ₀ : σ x = 0)
    (hτ : ContinuousAt (fun y ↦ (τ y : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ inner ℝ (σ y) (τ y)) x := by
  obtain ⟨L, hL, -⟩ := exists_hasFDerivAt_inner_comp_extChartAt_symm_of_eq_zero hσ hσ₀ hτ
  exact mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm.mpr hL.differentiableAt

/-- **The product rule at a zero.** If a vector field `σ` is differentiable at a zero `x` and `τ`
is continuous at `x`, then for a continuous metric the derivative at `x` of the pairing
`y ↦ g_y (σ y, τ y)` in the direction `v` is `g_x (τ x, D v)`, where `D` is the chart derivative
of `σ` at `x`. Neither the metric nor `τ` needs to be differentiable. -/
theorem _root_.MDifferentiableAt.mvfderiv_inner_bundle_apply_of_eq_zero
    (hσ : MDifferentiableAt I I.tangent (fun y ↦ (σ y : TangentBundle I M)) x) (hσ₀ : σ x = 0)
    (hτ : ContinuousAt (fun y ↦ (τ y : TangentBundle I M)) x) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ inner ℝ (σ y) (τ y)) x v =
      inner ℝ (τ x) (vectorFieldChartDerivative I σ x v : TangentSpace I x) := by
  obtain ⟨L, hL, hLv⟩ := exists_hasFDerivAt_inner_comp_extChartAt_symm_of_eq_zero hσ hσ₀ hτ
  rw [mvfderiv_eq_fderiv_comp_extChartAt_symm, hL.fderiv]
  exact hLv v

end ProductRule

section Gradient

variable [IsManifold I 2 M] {f : M → ℝ} {x : M}

/-- **The chart derivative of the gradient at a critical point is the Hessian.** At a critical
point `x` of a function `f` which is `C²` at `x`, if the gradient of `f` is differentiable at `x`,
its chart derivative `D` satisfies `g_x (w, D v) = Hess f x (v, w)`: it is the critical Hessian
raised by the metric at `x`. -/
theorem inner_vectorFieldChartDerivative_mgradient
    (hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : mvfderiv I f x = 0) (v w : TangentSpace I x) :
    inner ℝ w (vectorFieldChartDerivative I (Manifold.mgradient I f) x v : TangentSpace I x) =
      criticalHessian I f x v w := by
  -- Extend `w` to a vector field `Y`; then `Hess f x (v, w)` differentiates `df(Y) = g(grad f, Y)`.
  let Y := FiberBundle.extend E w
  have hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x :=
    FiberBundle.mdifferentiableAt_extend I E w
  have hH := criticalHessian_apply_eq_mvfderiv hf hcrit hY v
  have hpair : (fun y ↦ mvfderiv I f y (Y y)) = fun y ↦ inner ℝ (Manifold.mgradient I f y) (Y y) :=
    funext fun y ↦ (Manifold.inner_mgradient _).symm
  rw [hpair, hgrad.mvfderiv_inner_bundle_apply_of_eq_zero
    (Manifold.mgradient_eq_zero_iff.mpr hcrit) hY.continuousAt v] at hH
  simpa only [Y, FiberBundle.extend_apply_self] using hH.symm

/-- At a critical point of a `C²` function with differentiable gradient, the chart derivative `D`
of the gradient is symmetric for the metric at the critical point: `g_x (w, D v) = g_x (v, D w)`. -/
theorem inner_vectorFieldChartDerivative_mgradient_comm
    (hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : mvfderiv I f x = 0) (v w : TangentSpace I x) :
    inner ℝ w (vectorFieldChartDerivative I (Manifold.mgradient I f) x v : TangentSpace I x) =
      inner ℝ v (vectorFieldChartDerivative I (Manifold.mgradient I f) x w : TangentSpace I x) := by
  rw [inner_vectorFieldChartDerivative_mgradient hgrad hf hcrit,
    inner_vectorFieldChartDerivative_mgradient hgrad hf hcrit, criticalHessian_apply_swap hf]

/-- At a critical point of a `C²` function with differentiable gradient, a tangent vector is in
the kernel of the chart derivative of the gradient exactly when it is in the kernel of the critical
Hessian. -/
theorem vectorFieldChartDerivative_mgradient_apply_eq_zero_iff
    (hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : mvfderiv I f x = 0) (v : TangentSpace I x) :
    vectorFieldChartDerivative I (Manifold.mgradient I f) x v = 0 ↔
      criticalHessian I f x v = 0 := by
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun w ↦ ?_, fun h ↦ ?_⟩
  · rw [← inner_vectorFieldChartDerivative_mgradient hgrad hf hcrit, h]
    exact inner_zero_right _
  · have h' := inner_vectorFieldChartDerivative_mgradient hgrad hf hcrit v
      (vectorFieldChartDerivative I (Manifold.mgradient I f) x v)
    rw [h] at h'
    exact (inner_self_eq_zero (𝕜 := ℝ) (E := TangentSpace I x)).mp h'

/-- **The index of a gradient at a nondegenerate critical point.** At a nondegenerate critical
point `x` of a function whose gradient is differentiable at `x`, the sign of the determinant of the
chart derivative of the gradient is `(-1)` to the Morse index of the function at `x`. In
particular it does not depend on the metric. -/
theorem sign_det_vectorFieldChartDerivative_mgradient
    (hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x)
    (h : IsManifoldNondegenerateCriticalPoint I f x) :
    SignType.sign (LinearMap.det (vectorFieldChartDerivative I (Manifold.mgradient I f) x)) =
      (-1) ^ manifoldMorseIndex I f x := by
  obtain ⟨hf, hcrit, hinv⟩ := isManifoldNondegenerateCriticalPoint_iff_criticalHessian.mp h
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  let D := vectorFieldChartDerivative I (Manifold.mgradient I f) x
  -- Read `D` as an endomorphism of the tangent space at `x`, which carries the metric at `x`.
  let T : TangentSpace I x →ₗ[ℝ] TangentSpace I x := D
  have hH (v w : TangentSpace I x) : inner ℝ w (T v) = criticalHessian I f x v w :=
    inner_vectorFieldChartDerivative_mgradient hgrad hf hcrit v w
  have hT : T.IsSymmetric := fun v w ↦ by
    rw [real_inner_comm]
    exact inner_vectorFieldChartDerivative_mgradient_comm hgrad hf hcrit v w
  have hker : LinearMap.ker T = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun v hv ↦ hinv.injective ?_
    rw [map_zero]
    exact (vectorFieldChartDerivative_mgradient_apply_eq_zero_iff hgrad hf hcrit v).mp hv
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian]
  refine hT.sign_det_eq_neg_one_pow_sigNeg hker fun v ↦ ?_
  rw [LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply,
    real_inner_comm, hH]

/-- **Nondegeneracy from the chart derivative of the gradient.** At a critical point of a `C²`
function with differentiable gradient, the chart derivative of the gradient has nonzero
determinant exactly when the critical point is nondegenerate. -/
theorem det_vectorFieldChartDerivative_mgradient_ne_zero_iff
    (hgrad : MDifferentiableAt I I.tangent
      (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : mvfderiv I f x = 0) :
    LinearMap.det (vectorFieldChartDerivative I (Manifold.mgradient I f) x) ≠ 0 ↔
      IsManifoldNondegenerateCriticalPoint I f x := by
  refine ⟨fun hdet ↦ ?_, fun h hdet ↦ ?_⟩
  · -- A nonzero determinant makes `D` injective, hence the critical Hessian injective.
    have hD := LinearMap.ker_eq_bot.mp <| (LinearMap.isUnit_iff_ker_eq_bot _).mp <|
      (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    refine isManifoldNondegenerateCriticalPoint_iff_criticalHessian.mpr ⟨hf, hcrit,
      criticalHessian_isInvertible_of_injective <| (injective_iff_map_eq_zero _).mpr
        fun v hv ↦ (injective_iff_map_eq_zero _).mp hD v ?_⟩
    exact (vectorFieldChartDerivative_mgradient_apply_eq_zero_iff hgrad hf hcrit v).mpr hv
  · have hs := sign_det_vectorFieldChartDerivative_mgradient hgrad h
    rw [hdet, sign_zero] at hs
    rcases neg_one_pow_eq_or SignType (manifoldMorseIndex I f x) with h1 | h1 <;>
      rw [h1] at hs <;> exact absurd hs (by decide)

end Gradient

end TauCeti
