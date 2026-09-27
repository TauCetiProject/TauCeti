/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
public import TauCeti.MeasureTheory.Function.Lp.MollificationBridge

/-!
# Local convergence of mollifications after zero extension

For a subset `t ⊆ s` of a measurable set `s`, extend an `Lᵖ(s)` function by zero to the
ambient space,
average it against a normalized smooth bump, and restrict the result to `t`. As the radius
shrinks, this converges in `Lᵖ(t)` to the original function restricted to `t` whenever
`1 ≤ p < ∞`. The result applies to every Banach-valued field, including all weak derivative
fields of a Sobolev function, and requires no regularity of the boundary of `s`.

This is the local form of the strong approximate-identity theorem. It does not assert that
the zero extension is weakly differentiable across the boundary.

The zero-extension convolution is also identified almost everywhere with the abstract `Lᵖ`
average.  Thus the same mollification can be used through its norm-convergent `Lᵖ` class or
through its smooth pointwise representative.

## Main declarations

* `TauCeti.normedBumpLp_extendByZero_ae_eq_convolution`: the abstract mollification of a zero
  extension has the classical convolution as a representative.
* `TauCeti.tendsto_normedBumpLp_extendByZero_restrict`: zero-extension mollifications converge
  locally in `Lᵖ`.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Set
open scoped Convolution ENNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]
  {s t : Set E}

local instance : FiniteDimensional ℝ E := .of_locallyCompactSpace ℝ

local instance : (mu.restrict (univ : Set E)).IsAddHaarMeasure := by
  rw [Measure.restrict_univ]
  infer_instance

/-- Mollifying a zero extension is represented almost everywhere by convolving the pointwise
zero extension with the normalized bump.  This identifies the abstract `Lᵖ` average used for
norm convergence with the classical smooth convolution used for differentiation. -/
theorem normedBumpLp_extendByZero_ae_eq_convolution (hp : p ≠ ∞)
    (phi : ContDiffBump (0 : E)) (hs : MeasurableSet s)
    (f : Lp F p (mu.restrict s)) :
    normedBumpLp hp phi (mu.restrict (univ : Set E))
        (extendByZeroLpₗᵢ ℝ mu hs (subset_univ s) f) =ᵐ[mu.restrict (univ : Set E)]
      (phi.normed (mu.restrict (univ : Set E)) ⋆[lsmul ℝ ℝ,
        mu.restrict (univ : Set E)] s.indicator (f : E → F)) := by
  let f₀ : E → F := s.indicator (f : E → F)
  have hf₀ : MemLp f₀ p (mu.restrict (univ : Set E)) := by
    simpa only [f₀, Measure.restrict_univ] using
      (memLp_indicator_iff_restrict hs).2 (Lp.memLp f)
  have hext : hf₀.toLp f₀ = extendByZeroLpₗᵢ ℝ mu hs (subset_univ s) f := by
    apply Lp.ext
    exact hf₀.coeFn_toLp.trans (coeFn_extendByZeroLpₗᵢ ℝ hs (subset_univ s) f).symm
  rw [← hext]
  simpa only [f₀] using normedBumpLp_ae_eq_convolution hp phi hf₀

/-- Zero-extend an `Lᵖ(s)` field, mollify it, and restrict to `t ⊆ s`. For `p < ∞`, this
converges in `Lᵖ(t)` to the original field restricted to `t`. -/
theorem tendsto_normedBumpLp_extendByZero_restrict (hp : p ≠ ∞)
    (hs : MeasurableSet s) (hts : t ⊆ s)
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (nhds 0))
    (f : Lp F p (mu.restrict s)) :
    Tendsto (fun i =>
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using Measure.restrict_mono_set mu (subset_univ t)) <|
        normedBumpLp hp (phi i) (mu.restrict (univ : Set E))
          (extendByZeroLpₗᵢ ℝ mu hs (subset_univ s) f))
      l (nhds (Lp.LpToLpOfMeasureLeSMul (E := F) (μ := mu.restrict t)
        (ν := mu.restrict s) (c := 1) (by simp) (by
        simpa only [one_smul] using Measure.restrict_mono_set mu hts) f)) := by
  let r : Lp F p (mu.restrict (univ : Set E)) →L[ℝ] Lp F p (mu.restrict t) :=
    Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
      simpa only [one_smul] using Measure.restrict_mono_set mu (subset_univ t))
  let e : Lp F p (mu.restrict s) →ₗᵢ[ℝ] Lp F p (mu.restrict (univ : Set E)) :=
    extendByZeroLpₗᵢ ℝ mu hs (subset_univ s)
  have hlimit := (r.continuous.tendsto (e f)).comp
    (tendsto_normedBumpLp hp hphi (e f))
  have hre : r (e f) = Lp.LpToLpOfMeasureLeSMul (E := F) (μ := mu.restrict t)
      (ν := mu.restrict s) (c := 1) (by simp) (by
      simpa only [one_smul] using Measure.restrict_mono_set mu hts) f := by
    apply Lp.ext
    have he := (coeFn_extendByZeroLpₗᵢ ℝ hs (subset_univ s) f).filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (subset_univ t)))
    have hmem : ∀ᵐ x ∂mu.restrict t, x ∈ s :=
      ((ae_restrict_mem hs).filter_mono
        (MeasureTheory.ae_mono (Measure.restrict_mono_set mu hts)))
    have he' : e f =ᵐ[mu.restrict t] f := by
      filter_upwards [he, hmem] with x he hx
      simpa only [Set.indicator_of_mem hx] using he
    exact ((Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _).trans he').trans
      (Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _).symm
  simpa only [Function.comp_def, r, e, hre] using hlimit

end TauCeti
