/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl

/-!
# Derivatives of harmonic functions are harmonic

Let `E` be a finite-dimensional real inner product space and `F` a finite-dimensional real normed
space. If `f : E → F` is harmonic at `x`, then so is each of its directional derivatives
`y ↦ Df(y) v` (`InnerProductSpace.HarmonicAt.fderiv_apply`) and each iterated directional
derivative `TauCeti.iteratedFDerivAlong ℝ vs f`
(`InnerProductSpace.HarmonicAt.iteratedFDerivAlong`). For a real-valued harmonic function
`f : E → ℝ`, its gradient `∇f`, whose coordinates in an orthonormal basis are directional
derivatives, is also harmonic (`InnerProductSpace.HarmonicAt.gradient`). Consequently every
estimate proved for harmonic functions, such as the decay of their oscillation and of their
integrals on shrinking balls, applies verbatim to the partial derivatives and to the gradient of a
harmonic function. This is how gradient decay estimates for solutions of constant-coefficient
elliptic equations are reduced to the harmonic case.

## Main declarations

* `InnerProductSpace.HarmonicAt.fderiv_apply`: a directional derivative of a function harmonic at
  `x` is harmonic at `x`.
* `InnerProductSpace.HarmonicOnNhd.fderiv_apply`: the same on a set.
* `InnerProductSpace.HarmonicAt.iteratedFDerivAlong` and
  `InnerProductSpace.HarmonicOnNhd.iteratedFDerivAlong`: iterated directional derivatives of a
  harmonic function are harmonic.
* `InnerProductSpace.HarmonicAt.iteratedFDerivAlong_sub_right` and
  `InnerProductSpace.HarmonicOnNhd.iteratedFDerivAlong_sub_right`: reflected translates
  `y ↦ (∂_{vs} f)(x - y)` of iterated directional derivatives are harmonic.
* `InnerProductSpace.HarmonicOnNhd.contDiffOn_sub_right`: for `f` harmonic on `{0}ᶜ`,
  `y ↦ f (x - y)` is smooth on `{x}ᶜ`.
* `InnerProductSpace.HarmonicAt.gradient` and `InnerProductSpace.HarmonicOnNhd.gradient`: the
  gradient of a real-valued harmonic function is harmonic.

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
open scoped ContDiff Gradient

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section VectorValued

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F}

/-- **Derivatives of harmonic functions are harmonic.** If `f` is harmonic at `x`, then so is
the directional derivative `y ↦ Df(y) v`, for every direction `v`. -/
theorem HarmonicAt.fderiv_apply {x : E} (hf : HarmonicAt f x) (v : E) :
    HarmonicAt (fun y => fderiv ℝ f y v) x := by
  borelize E
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

/-- **Iterated directional derivatives of harmonic functions are harmonic.** If `f` is harmonic at
`x`, then so is `TauCeti.iteratedFDerivAlong ℝ vs f`, for every list of directions `vs`. -/
theorem HarmonicAt.iteratedFDerivAlong {x : E} (hf : HarmonicAt f x) (vs : List E) :
    HarmonicAt (TauCeti.iteratedFDerivAlong ℝ vs f) x := by
  induction vs with
  | nil => simpa using hf
  | cons v vs ih =>
    rw [TauCeti.iteratedFDerivAlong_cons]
    exact ih.fderiv_apply v

/-- **Iterated directional derivatives of harmonic functions are harmonic.** If `f` is harmonic on
`s`, then so is `TauCeti.iteratedFDerivAlong ℝ vs f`, for every list of directions `vs`. -/
theorem HarmonicOnNhd.iteratedFDerivAlong {s : Set E} (hf : HarmonicOnNhd f s) (vs : List E) :
    HarmonicOnNhd (TauCeti.iteratedFDerivAlong ℝ vs f) s :=
  fun x hx => (hf x hx).iteratedFDerivAlong vs

/-- If `f` is harmonic at `x - y`, then `z ↦ (∂_{vs} f)(x - z)` is harmonic at `y`. -/
theorem HarmonicAt.iteratedFDerivAlong_sub_right {x y : E} (hf : HarmonicAt f (x - y))
    (vs : List E) :
    HarmonicAt (fun z ↦ TauCeti.iteratedFDerivAlong ℝ vs f (x - z)) y := by
  simpa [Function.comp_def] using (TauCeti.harmonicAt_comp_affineIsometryEquiv_right_iff
    (AffineIsometryEquiv.constVSub ℝ x)).2 (hf.iteratedFDerivAlong vs)

/-- If `f` is harmonic away from `0`, then for any `x` and list of directions `vs`,
`y ↦ (∂_{vs} f)(x - y)` is harmonic away from `x`. -/
theorem HarmonicOnNhd.iteratedFDerivAlong_sub_right (hf : HarmonicOnNhd f {0}ᶜ) (vs : List E)
    (x : E) :
    HarmonicOnNhd (fun y ↦ TauCeti.iteratedFDerivAlong ℝ vs f (x - y)) {x}ᶜ :=
  fun _ hy ↦
    (hf _ (sub_ne_zero.2 (Ne.symm (Set.mem_compl_singleton_iff.1 hy)))
      ).iteratedFDerivAlong_sub_right vs

/-- If `f` is harmonic away from `0`, then for any `x`, `y ↦ f (x - y)` is smooth away from `x`. -/
theorem HarmonicOnNhd.contDiffOn_sub_right (hf : HarmonicOnNhd f {0}ᶜ) (x : E) :
    ContDiffOn ℝ ∞ (fun y ↦ f (x - y)) {x}ᶜ := by
  simpa using (hf.iteratedFDerivAlong_sub_right [] x).analyticOnNhd.contDiffOn
    isOpen_compl_singleton.uniqueDiffOn

end VectorValued

section Gradient

variable {f : E → ℝ}

/-- **The gradient of a harmonic function is harmonic.** If `f` is harmonic at `x`, then so is
its gradient `∇f`, as a vector-valued function: in an orthonormal basis its coordinates are the
directional derivatives of `f`. -/
theorem HarmonicAt.gradient {x : E} (hf : HarmonicAt f x) : HarmonicAt (∇ f) x := by
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
theorem HarmonicOnNhd.gradient {s : Set E} (hf : HarmonicOnNhd f s) : HarmonicOnNhd (∇ f) s :=
  fun x hx => (hf x hx).gradient

end Gradient

end InnerProductSpace
