/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Average
public import TauCeti.MeasureTheory.Function.Lp.Convolution
public import TauCeti.MeasureTheory.Function.Lp.Translation

import TauCeti.Analysis.Convolution.Basic
import TauCeti.MeasureTheory.Function.Lp.Holder
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

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

At the infinite exponent, mollifications converge against integrable test fields through
continuous bilinear maps. This weak-star endpoint is obtained by transferring convolution
to the test field and using its strong `L¹` convergence, not by claiming `L^∞` norm convergence.
Local finite-`Lᵖ` convergence only requires `Lᵖ` integrability on a positive thickening of
the set where convergence is measured.

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
* `ContinuousLinearMap.tendsto_integral_bilin_normed_convolution_top`: weak-star convergence
  for bounded fields tested against integrable fields through a continuous bilinear map.
* `TauCeti.tendsto_eLpNorm_normed_convolution_sub_restrict`: finite-`Lᵖ` convergence on a set
  from `Lᵖ` integrability on a positive thickening.
* `TauCeti.tendsto_lintegral_enorm_normed_convolution_sub`: for an integrable function these
  convolutions converge in `L¹`, written with lower Lebesgue integrals.
* `TauCeti.tendsto_setLIntegral_enorm_normed_convolution_sub`: for a locally integrable function
  these convolutions converge in `L¹(K)` on every compact set `K`.
* `ContinuousLinearMap.tendsto_setLIntegral_enorm_bilin_normedBump_sub`: mollifying both factors
  of a bilinear product of `Lᵖ` and `Lᵠ` functions converges in `L¹(W)` to the product of the
  limits.

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

open ContinuousLinearMap Filter MeasureTheory Metric Set
open scoped Convolution ENNReal

namespace TauCeti

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
      normedBumpAverageL (F := Lp F p mu) phi mu (mu.translateLp p)
        (Measure.continuous_translateLp hp) :=
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

/-- Convolution with a normalized smooth bump does not increase the `Lᵖ` seminorm,
for `1 ≤ p < ∞`. -/
theorem eLpNorm_normed_convolution_le [CompleteSpace F] (hp : p ≠ ∞)
    (phi : ContDiffBump (0 : E)) {f : E → F} (hf : MemLp f p mu) :
    eLpNorm (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) p mu ≤ eLpNorm f p mu := by
  have h := (normedBumpLp (F := F) hp phi mu).le_of_opNorm_le
    (norm_normedBumpLp_le_one hp phi) (hf.toLp f)
  have hn : ‖normedBumpLp hp phi mu (hf.toLp f)‖ ≤ ‖hf.toLp f‖ := by simpa using h
  calc eLpNorm (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) p mu =
      ‖normedBumpLp hp phi mu (hf.toLp f)‖ₑ := by
        rw [Lp.eNorm_def]
        exact eLpNorm_congr_ae (normedBumpLp_ae_eq_convolution hp phi hf).symm
    _ ≤ ‖hf.toLp f‖ₑ := by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hn
    _ = eLpNorm f p mu := by
        rw [Lp.eNorm_def]
        exact eLpNorm_congr_ae hf.coeFn_toLp

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

/-- Pairing mollifications of a bounded function with any integrable field through a
continuous bilinear map converges in norm. This is the `L¹`–`L^∞` weak-star endpoint. -/
theorem _root_.ContinuousLinearMap.tendsto_integral_bilin_normed_convolution_top
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [CompleteSpace F]
    (B : G →L[ℝ] F →L[ℝ] H) {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0))
    {a : E → G} (ha : Integrable a mu) {f : E → F} (hf : MemLp f ∞ mu) :
    Tendsto (fun i ↦ ∫ x, B (a x) (((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x) ∂mu)
      l (nhds (∫ x, B (a x) (f x) ∂mu)) := by
  -- Reflect the test field to express the pairing as convolution evaluated at zero.
  let b : E → G := fun x ↦ a (-x)
  have hb : Integrable b mu := ha.comp_neg
  have hbmem : MemLp b 1 mu := memLp_one_iff_integrable.mpr hb
  have hfn : MemLp (fun x ↦ f (-x)) ∞ mu :=
    hf.comp_measurePreserving (Measure.measurePreserving_neg mu)
  let L : Lp G 1 mu →L[ℝ] H := B.flip.lpPairing mu ∞ 1 (hfn.toLp (fun x ↦ f (-x)))
  have hL (v : Lp G 1 mu) (g : E → G) (hv : v =ᵐ[mu] g) :
      L v = ∫ x, B (g x) (f (-x)) ∂mu := by
    dsimp only [L]
    rw [lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hfn.coeFn_toLp, hv] with x hx hx'
    simp only [flip_apply, hx, hx']
  -- Strong L¹ convergence of the test field gives convergence through the L¹–L∞ pairing.
  have hlim := L.continuous.tendsto (hbmem.toLp b) |>.comp
    (tendsto_normedBumpLp ENNReal.one_ne_top hphi (hbmem.toLp b))
  have htarget : L (hbmem.toLp b) = ∫ x, B (a x) (f x) ∂mu := by
    rw [hL _ _ hbmem.coeFn_toLp]
    exact integral_neg_eq_self (fun x ↦ B (a x) (f x)) mu
  have hsource (i : I) : L (normedBumpLp ENNReal.one_ne_top (phi i) mu (hbmem.toLp b)) =
      ∫ x, B (a x) (((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x) ∂mu := by
    rw [hL _ _ (normedBumpLp_ae_eq_convolution ENNReal.one_ne_top (phi i) hbmem)]
    -- The L¹–L∞ bound supplies the norm-integrability hypothesis for associativity.
    have hbound (x : E) : ‖((fun y ↦ ‖(phi i).normed mu y‖) ⋆[mul ℝ ℝ, mu]
        (fun y ↦ ‖f y‖)) x‖ ≤ (∫ y, ‖(phi i).normed mu y‖ ∂mu) * lpNorm f ∞ mu := by
      have h := norm_convolution_lsmul_le_integral_norm_mul_norm
        (phi i).integrable_normed.norm (hf.norm.toLp _) x
      rw [convolution_congr (lsmul ℝ ℝ) (EventuallyEq.refl _ _) hf.norm.coeFn_toLp] at h
      simpa only [convolution_def, lsmul_apply, smul_eq_mul, mul_apply', norm_norm,
        Lp.norm_toLp, eLpNorm_norm f hf.aestronglyMeasurable, toReal_eLpNorm] using h
    have hassoc := convolution_assoc (lsmul ℝ ℝ).flip B B (lsmul ℝ ℝ)
      (fun g r v ↦ by simp only [flip_apply, lsmul_apply, map_smul, smul_apply])
      hb.aestronglyMeasurable (phi i).integrable_normed.aestronglyMeasurable
      hf.aestronglyMeasurable (hb.ae_convolution_exists _ (phi i).integrable_normed)
      (ae_of_all _ (convolutionExists_of_integrable_of_ae_norm_le _
        (phi i).integrable_normed.norm hf.aestronglyMeasurable.norm
        ((ae_le_lpNorm_exponent_top hf).mono fun _ hx ↦ by
          simpa only [norm_norm] using hx)))
      (convolutionExists_of_integrable_of_ae_norm_le _ hb.norm
        ((phi i).integrable_normed.aestronglyMeasurable.norm.convolution _
          hf.aestronglyMeasurable.norm) (ae_of_all _ hbound) 0)
    rw [convolution_flip] at hassoc
    have hpair : (b ⋆[B, mu] ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f)) 0 =
        ∫ x, B (a x) (((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x) ∂mu := by
      rw [convolution_def]
      simpa only [zero_sub, b] using integral_neg_eq_self (fun x ↦
        B (a x) (((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x)) mu
    simpa only [convolution_def, zero_sub] using hassoc.trans hpair
  simpa only [Function.comp_def, hsource, htarget] using hlim

/-- Pairing an `Lᵖ` mollification with any fixed conjugate-`Lᵠ` scalar coefficient converges
in the Banach codomain. The bump family and convergence filter are arbitrary. -/
theorem tendsto_integral_smul_normed_convolution [CompleteSpace F] {q : ℝ≥0∞}
    [Fact (1 ≤ q)] [p.HolderConjugate q] {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) {a : E → ℝ} (ha : MemLp a q mu)
    {f : E → F} (hf : MemLp f p mu) :
    Tendsto (fun i ↦ ∫ x, a x • ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu)
      l (nhds (∫ x, a x • f x ∂mu)) := by
  by_cases hp : p = ∞
  · subst p
    have hq : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q).mp rfl
    subst q
    exact (lsmul ℝ ℝ).tendsto_integral_bilin_normed_convolution_top hphi
      (memLp_one_iff_integrable.mp ha) hf
  let L : Lp F p mu →L[ℝ] F := (lsmul ℝ ℝ).lpPairing mu q p (ha.toLp a)
  have hpair (g : Lp F p mu) (G : E → F) (hg : g =ᵐ[mu] G) :
      L g = ∫ x, a x • G x ∂mu := by
    dsimp only [L]
    rw [lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hg] with x hx hG
    simp only [lsmul_apply, hx, hG]
  have hlim := L.continuous.tendsto (hf.toLp f) |>.comp (tendsto_normedBumpLp hp hphi (hf.toLp f))
  have hpairphi (i : I) : L (normedBumpLp hp (phi i) mu (hf.toLp f)) =
      ∫ x, a x • ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu :=
    hpair _ _ (normedBumpLp_ae_eq_convolution hp (phi i) hf)
  simpa only [Function.comp_def, hpairphi, hpair _ _ hf.coeFn_toLp] using hlim

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

/-- **Mollification converges in `L¹`.** For an integrable `f` and normalized smooth bumps
`phi i` centred at zero whose outer radii tend to zero, `∫ ‖(phi i).normed mu ⋆ f - f‖ → 0`. This
is the case `p = 1` of `TauCeti.tendsto_eLpNorm_normed_convolution_sub`, written with lower
Lebesgue integrals. -/
theorem tendsto_lintegral_enorm_normed_convolution_sub [CompleteSpace F] {I : Type*}
    {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) {f : E → F} (hf : Integrable f mu) :
    Tendsto (fun i ↦ ∫⁻ x, ‖((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x - f x‖ₑ ∂mu) l
      (nhds 0) := by
  have h := tendsto_eLpNorm_normed_convolution_sub ENNReal.one_ne_top hphi
    (memLp_one_iff_integrable.mpr hf)
  have hi (i : I) : Integrable ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f - f) mu :=
    ((phi i).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hf).sub hf
  simp_rw [eLpNorm_one_eq_lintegral_eNorm (hi _).aestronglyMeasurable] at h
  exact h

/-- Mollifications converge in `Lᵖ(s)`, for `1 ≤ p < ∞`, if the function belongs to `Lᵖ`
on a fixed positive thickening of `s`. Neither compactness of `s` nor global local
integrability is required. -/
theorem tendsto_eLpNorm_normed_convolution_sub_restrict [CompleteSpace F] {I : Type*}
    {l : Filter I} (hp : p ≠ ∞) {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) {f : E → F}
    {s : Set E} {δ : ℝ} (hδ : 0 < δ)
    (hf : MemLp f p (mu.restrict (thickening δ s))) :
    Tendsto (fun i ↦ eLpNorm ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f - f) p
      (mu.restrict s)) l (nhds 0) := by
  -- Small bumps only see the function on this fixed neighborhood.
  set t := thickening δ s
  have ht : MeasurableSet t := isOpen_thickening.measurableSet
  have hfs : MemLp (t.indicator f) p mu :=
    (memLp_indicator_iff_restrict ht.nullMeasurableSet).2 hf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_eLpNorm_normed_convolution_sub hp hphi hfs)
    (.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hphi.eventually (gt_mem_nhds hδ)] with i hi
  have heq : ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f - f) =ᵐ[mu.restrict s]
      ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] t.indicator f - t.indicator f) := by
    filter_upwards [(ae_restrict_mem isClosed_closure.measurableSet).filter_mono
      (ae_mono (Measure.restrict_mono_set mu (subset_closure (s := s))))] with x hx
    have hxt : x ∈ t := by
      dsimp only [t]
      rw [← thickening_closure]
      exact self_subset_thickening hδ (closure s) hx
    simp only [Pi.sub_apply]
    rw [indicator_of_mem hxt]
    refine congrArg (· - f x) (convolution_indicator_eq_of_forall_sub_mem _ fun y hy ↦ ?_).symm
    rw [(phi i).support_normed_eq, mem_ball_zero_iff] at hy
    dsimp only [t]
    rw [← thickening_closure]
    apply mem_thickening_iff.mpr
    refine ⟨x, hx, ?_⟩
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact hy.trans hi
  exact (eLpNorm_congr_ae heq).trans_le (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- **Mollification converges in `L¹_loc`.** For a locally integrable `f` and normalized smooth
bumps `phi i` centred at zero whose outer radii tend to zero, the classical convolutions
`(phi i).normed mu ⋆ f` converge to `f` in `L¹(K)` for every compact set `K`. -/
theorem tendsto_setLIntegral_enorm_normed_convolution_sub [CompleteSpace F] {I : Type*}
    {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) {f : E → F} (hf : LocallyIntegrable f mu)
    {K : Set E} (hK : IsCompact K) :
    Tendsto (fun i ↦ ∫⁻ x in K, ‖((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x - f x‖ₑ ∂mu) l
      (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_eLpNorm_normed_convolution_sub_restrict ENNReal.one_ne_top hphi one_pos
      ((memLp_one_iff_integrable.mpr (hf.integrableOn_isCompact hK.cthickening)).mono_measure
        (Measure.restrict_mono_set mu (thickening_subset_cthickening 1 K))))
    (.of_forall fun _ ↦ zero_le) (.of_forall fun _ ↦ lintegral_eNorm_le_eLpNorm_one)

section Bilinear

open scoped Topology

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
  [NormedSpace ℝ H]

/-- Mollifying both factors of a product by a shrinking normalized bump converges in `L¹(W)` to
the product of their limits, when the limits are represented on `W` by the classes of `U` and
`V`. -/
theorem _root_.ContinuousLinearMap.tendsto_setLIntegral_enorm_bilin_normedBump_sub
    (B : F →L[ℝ] G →L[ℝ] H)
    {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r] (hp : p ≠ ⊤) (hq : q ≠ ⊤) [CompleteSpace F] [CompleteSpace G]
    {U : E → F} {V : E → G} (hU : MemLp U p mu) (hV : MemLp V q mu)
    {I : Type*} {l : Filter I} {φ : I → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {W : Set E} (hWmu : mu W < ⊤) {f : E → F} {g : E → G}
    (hUae : hU.toLp U =ᵐ[mu.restrict W] f) (hVae : hV.toLp V =ᵐ[mu.restrict W] g) :
    Tendsto (fun i => ∫⁻ x in W,
      ‖B (((φ i).normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] U) x)
        ((((φ i).normed mu) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] V) x) - B (f x) (g x)‖ₑ ∂mu)
      l (𝓝 0) :=
  tendsto_setLIntegral_enorm_bilin_sub (r := r) B hWmu
    (tendsto_normedBumpLp (mu := mu) hp hφ (hU.toLp U))
    (tendsto_normedBumpLp (mu := mu) hq hφ (hV.toLp V))
    (fun i => normedBumpLp_ae_eq_convolution hp (φ i) hU)
    hUae (fun i => normedBumpLp_ae_eq_convolution hq (φ i) hV) hVae

end Bilinear

end TauCeti
