/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl

/-!
# Derivatives of harmonic functions are harmonic

Let `E` be a finite-dimensional real inner product space. If `f : E → ℝ` is harmonic at `x`, then
so is each of its directional derivatives `y ↦ Df(y) v`
(`InnerProductSpace.HarmonicAt.fderiv_apply`). Since harmonicity only asks for two continuous
derivatives, the identity `Δ (∂ᵥf) = ∂ᵥ(Δf)` is not available classically. Instead, `∂ᵥf` is a
weak derivative of the weakly harmonic function `f`, hence weakly harmonic
(`TauCeti.HasWeakLineDerivOn.weaklyHarmonicOn`), and being continuous it is harmonic by Weyl's
lemma (`TauCeti.harmonicOnNhd_iff_weaklyHarmonicOn`).

## Main declarations

* `InnerProductSpace.HarmonicAt.fderiv_apply`: a directional derivative of a function harmonic at
  `x` is harmonic at `x`.
* `InnerProductSpace.HarmonicOnNhd.fderiv_apply`: the same on a set.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.2.3, Theorem 6 (smoothness of
  harmonic functions).
-/

public section

open MeasureTheory TopologicalSpace

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ}

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

end InnerProductSpace
