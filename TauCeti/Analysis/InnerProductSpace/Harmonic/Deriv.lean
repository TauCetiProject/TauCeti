/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl

/-!
# Derivatives of harmonic functions are harmonic

Let `E` be a finite-dimensional real inner product space and `F` a finite-dimensional real normed
space. If `f : E → F` is harmonic at `x`, then so is each of its directional derivatives
`y ↦ Df(y) v` (`InnerProductSpace.HarmonicAt.fderiv_apply`), and so is its Fréchet derivative
`y ↦ Df(y)` with values in `E →L[ℝ] F` (`InnerProductSpace.HarmonicAt.fderiv`). For
`f : E → ℝ` the gradient `∇f`, whose coordinates in an orthonormal basis are directional
derivatives, is harmonic as well (`InnerProductSpace.HarmonicAt.gradient`).
Consequently every estimate proved for harmonic functions, such as the decay of their oscillation
and of their integrals on shrinking balls, applies verbatim to the partial derivatives, to the
gradient and to the Hessian of a harmonic function. This is how gradient and Hessian decay
estimates for solutions of constant-coefficient elliptic equations are reduced to the harmonic
case.

## Main declarations

* `InnerProductSpace.HarmonicAt.fderiv_apply`: a directional derivative of a function harmonic at
  `x` is harmonic at `x`.
* `InnerProductSpace.HarmonicOnNhd.fderiv_apply`: the same on a set.
* `InnerProductSpace.HarmonicAt.fderiv` and
  `InnerProductSpace.HarmonicOnNhd.fderiv`: the Fréchet derivative of a harmonic
  function is harmonic.
* `InnerProductSpace.HarmonicAt.gradient` and `InnerProductSpace.HarmonicOnNhd.gradient`: the
  gradient of a harmonic function is harmonic.

## Implementation notes

Since harmonicity only asks for two continuous derivatives, the identity `Δ (∂ᵥf) = ∂ᵥ(Δf)` is
not available classically. Instead, `∂ᵥf` is a weak derivative of the weakly harmonic function
`f`, hence weakly harmonic (`TauCeti.HasWeakLineDerivOn.weaklyHarmonicOn`), and being continuous
it is harmonic by Weyl's lemma (`TauCeti.harmonicOnNhd_iff_weaklyHarmonicOn`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.2.3, Theorem 6 (smoothness of
  harmonic functions).
-/

public section

open MeasureTheory TopologicalSpace
open scoped Gradient

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F}

/-- **Derivatives of harmonic functions are harmonic.** If `f` is harmonic at `x`, then so is
the directional derivative `y ↦ Df(y) v`, for every direction `v`. -/
theorem HarmonicAt.fderiv_apply {x : E} (hf : HarmonicAt f x) (v : E) :
    HarmonicAt (fun y => fderiv ℝ f y v) x := by
  borelize E
  have := FiniteDimensional.completeSpace ℝ F
  -- `f` is harmonic on the open set of points at which it is harmonic.
  let U : Opens E := ⟨{y | HarmonicAt f y}, isOpen_setOfPred_harmonicAt f⟩
  have hU : HarmonicOnNhd f U := fun _ hy => hy
  have hc : ContDiffOn ℝ 2 f U := hU.contDiffOn
  have hd : ContinuousOn (fun y => fderiv ℝ f y v) U :=
    (hc.continuousOn_fderiv_of_isOpen U.isOpen (by norm_num)).clm_apply continuousOn_const
  have hw : TauCeti.HasWeakLineDerivOn (Measure.addHaar : Measure E) U f
      (fun y => fderiv ℝ f y v) v :=
    TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt
      (hc.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
      (hd.locallyIntegrableOn U.isOpen.measurableSet) fun y hy =>
        ((hc.differentiableOn (by norm_num)).differentiableAt
          (U.isOpen.mem_nhds hy)).hasFDerivAt.hasLineDerivAt v
  exact (TauCeti.harmonicOnNhd_iff_weaklyHarmonicOn hd).2
    (hw.weaklyHarmonicOn hU.weaklyHarmonicOn) x hf

/-- **Derivatives of harmonic functions are harmonic.** If `f` is harmonic on `s`, then so is
the directional derivative `y ↦ Df(y) v`, for every direction `v`. -/
theorem HarmonicOnNhd.fderiv_apply {s : Set E} (hf : HarmonicOnNhd f s) (v : E) :
    HarmonicOnNhd (fun y => fderiv ℝ f y v) s :=
  fun x hx => (hf x hx).fderiv_apply v

/-- **The gradient of a harmonic function is harmonic.** If `f` is harmonic at `x`, then so is
its gradient `∇f`, as a vector-valued function: in an orthonormal basis its coordinates are the
directional derivatives of `f`. -/
theorem HarmonicAt.gradient {f : E → ℝ} {x : E} (hf : HarmonicAt f x) : HarmonicAt (∇ f) x := by
  set b := stdOrthonormalBasis ℝ E
  have h : ∇ f = fun y => ∑ i, fderiv ℝ f y (b i) • b i := by
    funext y
    conv_lhs => rw [← b.sum_repr' (∇ f y)]
    simp only [real_inner_comm _ (b _), inner_gradient_left]
  rw [h]
  exact HarmonicAt.sum fun i _ =>
    (hf.fderiv_apply (b i)).comp_CLM ((1 : ℝ →L[ℝ] ℝ).smulRight (b i))

/-- **The gradient of a harmonic function is harmonic.** If `f` is harmonic on `s`, then so is
its gradient `∇f`. -/
theorem HarmonicOnNhd.gradient {f : E → ℝ} {s : Set E} (hf : HarmonicOnNhd f s) :
    HarmonicOnNhd (∇ f) s :=
  fun x hx => (hf x hx).gradient

/-- **The derivative of a harmonic function is harmonic.** If `f` is harmonic at `x`, then so is
its Fréchet derivative `y ↦ Df(y)`, as a function with values in `E →L[ℝ] F`: in an orthonormal
basis `(bᵢ)` of `E`, `Df(y) = ∑ᵢ ⟪bᵢ, ·⟫ Df(y) bᵢ`, and each `y ↦ Df(y) bᵢ` is harmonic. -/
protected theorem HarmonicAt.fderiv {x : E} (hf : HarmonicAt f x) :
    HarmonicAt (fderiv ℝ f) x := by
  set b := stdOrthonormalBasis ℝ E
  have h : fderiv ℝ f = fun y => ∑ i, (innerSL ℝ (b i)).smulRight (fderiv ℝ f y (b i)) := by
    funext y
    ext v
    conv_lhs => rw [← b.sum_repr' v]
    simp
  rw [h]
  exact HarmonicAt.sum fun i _ =>
    (hf.fderiv_apply (b i)).comp_CLM
      (ContinuousLinearMap.smulRightL (𝕜 := ℝ) (𝕜₂ := ℝ) (S := ℝ) (E := E) (F := F)
        (innerSL ℝ (b i)))

/-- **The derivative of a harmonic function is harmonic.** If `f` is harmonic on `s`, then so is
its Fréchet derivative `y ↦ Df(y)`, with values in `E →L[ℝ] F`. -/
protected theorem HarmonicOnNhd.fderiv {s : Set E} (hf : HarmonicOnNhd f s) :
    HarmonicOnNhd (fderiv ℝ f) s :=
  fun x hx => (hf x hx).fderiv

end InnerProductSpace
