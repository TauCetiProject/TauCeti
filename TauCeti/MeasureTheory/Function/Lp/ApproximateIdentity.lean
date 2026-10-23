/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Average
public import TauCeti.MeasureTheory.Function.Lp.Convolution
public import TauCeti.MeasureTheory.Function.Lp.Translation

import TauCeti.Analysis.Convolution

/-!
# Smooth approximate identities in `Lᵖ`

Let `φ` be a smooth bump function centred at the origin and normalized to have integral one.
This file defines the corresponding averaging operator on `Lᵖ` by the Bochner integral

`f ↦ ∫ t, φ(t) f(· - t)`

as a continuous linear map of norm at most one, and proves that these operators converge strongly
to the identity when the outer radii of the bumps tend to zero.  The result holds for `1 ≤ p < ∞`,
for functions with values in an arbitrary real Banach space, and for every additive Haar measure
on a finite-dimensional real normed space.

The integral is taken directly in `Lᵖ`.  This avoids choosing pointwise representatives: translation
is continuous in `Lᵖ`, so the average is a Bochner integral of a continuous compactly supported
`Lᵖ`-valued function.  The proof is the standard approximate-identity estimate

`‖∫ φ(t) (f(· - t) - f) dt‖ₚ ≤ sup_{t ∈ supp φ} ‖f(· - t) - f‖ₚ`.

This is the `Lᵖ` convergence input for mollification in Sobolev spaces.  Together with commutation
of mollification and weak differentiation, it approximates both the value and every weak derivative
by the same smooth kernel.

The averaging operator is represented almost everywhere by the classical convolution with
the normalized bump. This formula applies to every `MemLp` representative, with no global
integrability or compact support assumption on the function.

## Main declarations

* `TauCeti.normedBumpLp`: averaging an `Lᵖ` function against a normalized smooth bump, as a
  continuous linear operator on `Lᵖ`.
* `TauCeti.normedBumpLp_apply`: the defining Bochner integral of that operator.
* `TauCeti.normedBumpLp_eq_normedBumpAverageL`: this operator is the normalized-bump average of
  the `Lᵖ` translation action.
* `TauCeti.normedBumpLp_eq_convolutionLp`: this operator is convolution with the normalized bump.
* `TauCeti.normedBumpLp_ae_eq_convolution`: its pointwise representative is the classical
  convolution with the normalized bump.
* `TauCeti.compLpL_normedBumpLp`: this operator commutes with postcomposition by a continuous
  linear map.
* `TauCeti.norm_normedBumpLp_le_one`: this averaging operator is an `Lᵖ` contraction.
* `TauCeti.tendsto_normedBumpLp`: normalized bumps whose radii shrink to zero converge strongly
  to the identity on `Lᵖ`.
* `TauCeti.tendsto_eLpNorm_normed_convolution_sub`: the same convergence for the classical
  convolution of a function in `Lᵖ` with these bumps.
* `TauCeti.tendsto_setLIntegral_enorm_normed_convolution_sub`: for a locally integrable function
  these convolutions converge in `L¹(K)` on every compact set `K`.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1; H. Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Proposition 4.21.

The pointwise representative formula follows LeanPool's
`RellichKondrachov/L2Compactness/Smoothing.lean`, especially its `smoothFun` and `smoothL2`
constructions, and Tau Ceti's `RepresentationTheory/Compact/Convolution.lean`, especially
`convolutionCLM_toLp_apply`.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Metric Set
open scoped Convolution ENNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

/-- Averaging an `Lᵖ` function against the normalized form of a smooth bump centred at zero, as a
continuous linear operator on `Lᵖ`.

The average is a Bochner integral in `Lᵖ`, so it is independent of all choices of pointwise
representative. The restriction `p < ∞` ensures that translation is strongly continuous, hence
that the `Lᵖ`-valued integrand is integrable; that integrability is what makes the average
additive, and the operator is a contraction by `TauCeti.norm_normedBumpLp_le_one`.

Completeness of `F` is not part of the definition, exactly as for `MeasureTheory.average` and
`convolution`: the Bochner integral is formed in whatever normed space is at hand, and it is `0`
unless that space is complete. So this operator is the advertised average of the translates of
its argument precisely when `F` is a Banach space, which is the setting of
`TauCeti.tendsto_normedBumpLp`; the contraction bound holds in either case. -/
def normedBumpLp (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [mu.IsAddHaarMeasure] : Lp F p mu →L[ℝ] Lp F p mu :=
  normedBumpAverageL phi mu (mu.translateLp p) (Measure.continuous_translateLp hp)

/-- The defining Bochner-integral formula for `normedBumpLp`. -/
theorem normedBumpLp_apply (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (f : Lp F p mu) :
    normedBumpLp hp phi mu f =
      ∫ t, phi.normed mu t • mu.translateLp p (-t) f ∂mu := by
  exact normedBumpAverageL_apply (F := Lp F p mu) phi mu (mu.translateLp p)
    (Measure.continuous_translateLp hp) f

/-- `normedBumpLp` is the normalized-bump average of the `Lᵖ` translation action. -/
theorem normedBumpLp_eq_normedBumpAverageL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    normedBumpLp (F := F) hp phi mu =
      normedBumpAverageL phi mu (mu.translateLp p) (Measure.continuous_translateLp hp) :=
  (rfl)

/-- Averaging against a normalized bump is convolution with the normalized bump, as an operator
on `Lᵖ`. -/
theorem normedBumpLp_eq_convolutionLp (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    normedBumpLp (F := F) hp phi mu = convolutionLp hp (phi.normed mu) mu := by
  ext1 f
  rw [normedBumpLp_apply, convolutionLp_apply hp phi.integrable_normed]

/-- The `Lᵖ` approximate identity is represented almost everywhere by the usual pointwise
convolution of any `MemLp` representative. -/
theorem normedBumpLp_ae_eq_convolution [CompleteSpace F] (hp : p ≠ ∞)
    (phi : ContDiffBump (0 : E)) {f : E → F} (hf : MemLp f p mu) :
    normedBumpLp hp phi mu (hf.toLp f) =ᵐ[mu] phi.normed mu ⋆[lsmul ℝ ℝ, mu] f := by
  rw [normedBumpLp_eq_convolutionLp]
  exact convolutionLp_ae_eq_convolution hp phi.integrable_normed hf

/-- Averaging against a normalized bump commutes with postcomposition by a continuous linear map
between Banach spaces. -/
theorem compLpL_normedBumpLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace F] [CompleteSpace G] (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (L : F →L[ℝ] G) (f : Lp F p mu) :
    L.compLpL p mu (normedBumpLp hp phi mu f) = normedBumpLp hp phi mu (L.compLpL p mu f) :=
  normedBumpAverageL_comm _ _ _ _ _ _ _ L.compLpL_translateLp f

/-- Averaging against a normalized nonnegative bump does not increase the `Lᵖ` norm when
`p < ∞`. -/
theorem norm_normedBumpLp_le_one (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    ‖normedBumpLp (F := F) hp phi mu‖ ≤ 1 := by
  exact norm_normedBumpAverageL_le_one (F := Lp F p mu) phi mu (mu.translateLp p)
    (Measure.continuous_translateLp hp)

/-- **Smooth approximate identity in `Lᵖ`.** Let `phi i` be normalized smooth bumps centred at
zero. If their outer radii tend to zero, then averaging any `f ∈ Lᵖ` against these bumps converges
to `f` in the `Lᵖ` norm.

The hypothesis `p < ∞` is used to obtain strong translation continuity in this general setting, and
`F` is assumed complete so that the `Lᵖ`-valued Bochner integral defining the average is the limit
of its approximating sums. No positivity or normalization hypotheses are exposed because they are
already supplied by `ContDiffBump.normed`. -/
theorem tendsto_normedBumpLp [CompleteSpace F] {I : Type*} {l : Filter I}
    (hp : p ≠ ∞) {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) (f : Lp F p mu) :
    Tendsto (fun i ↦ normedBumpLp hp (phi i) mu f) l (nhds f) := by
  simpa only [normedBumpLp, Measure.translateLp_zero] using
    tendsto_normedBumpAverageL (F := Lp F p mu) hphi mu (mu.translateLp p)
      (Measure.continuous_translateLp hp) f

/-- **Mollification converges in `Lᵖ`.** For `f ∈ Lᵖ` with `1 ≤ p < ∞` and normalized smooth bumps
`phi i` centred at zero whose outer radii tend to zero, the classical convolutions
`(phi i).normed mu ⋆ f` converge to `f` in `Lᵖ`. This is `TauCeti.tendsto_normedBumpLp` read on
functions rather than on `Lᵖ` classes. -/
theorem tendsto_eLpNorm_normed_convolution_sub [CompleteSpace F] {I : Type*} {l : Filter I}
    (hp : p ≠ ∞) {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) {f : E → F} (hf : MemLp f p mu) :
    Tendsto (fun i ↦ eLpNorm ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f - f) p mu) l (nhds 0) := by
  refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1
    (tendsto_normedBumpLp hp hphi (hf.toLp f))).congr fun i ↦ eLpNorm_congr_ae ?_
  filter_upwards [normedBumpLp_ae_eq_convolution hp (phi i) hf, hf.coeFn_toLp]
    with x h₁ h₂
  rw [Pi.sub_apply, Pi.sub_apply, h₁, h₂]

/-- **Mollification converges in `L¹_loc`.** For a locally integrable `f` and normalized smooth
bumps `phi i` centred at zero whose outer radii tend to zero, the classical convolutions
`(phi i).normed mu ⋆ f` converge to `f` in `L¹(K)` for every compact set `K`. -/
theorem tendsto_setLIntegral_enorm_normed_convolution_sub [CompleteSpace F] {I : Type*}
    {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) {f : E → F} (hf : LocallyIntegrable f mu)
    {K : Set E} (hK : IsCompact K) :
    Tendsto (fun i ↦ ∫⁻ x in K, ‖((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x - f x‖ₑ ∂mu) l
      (nhds 0) := by
  -- On `K`, bumps of radius less than one only see `f` on the compact set `cthickening 1 K`,
  -- where `f` is integrable, so the whole-space `L¹` convergence applies.
  set s := cthickening 1 K
  have hs : IsCompact s := hK.cthickening
  have hfs : MemLp (s.indicator f) 1 mu := memLp_one_iff_integrable.2 <|
    (hf.integrableOn_isCompact hs).integrable_indicator hs.measurableSet
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_eLpNorm_normed_convolution_sub ENNReal.one_ne_top hphi hfs)
    (.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hphi.eventually (gt_mem_nhds one_pos)] with i hi
  have hKs (x : E) (hx : x ∈ K) :
      ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x - f x =
        ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] s.indicator f) x - s.indicator f x := by
    rw [indicator_of_mem (self_subset_cthickening K hx)]
    refine congrArg (· - f x) (convolution_indicator_eq_of_forall_sub_mem _ fun t ht ↦ ?_).symm
    rw [(phi i).support_normed_eq, mem_ball_zero_iff] at ht
    refine mem_cthickening_of_dist_le _ x _ _ hx ?_
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact ht.le.trans hi.le
  rw [setLIntegral_congr_fun hK.measurableSet fun x hx ↦ by rw [hKs x hx]]
  exact (setLIntegral_le_lintegral _ _).trans lintegral_enorm_le_eLpNorm_one

end TauCeti
