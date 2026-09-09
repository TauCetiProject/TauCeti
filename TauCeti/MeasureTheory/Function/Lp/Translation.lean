/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.SegmentIncrement
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
public import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
public import TauCeti.Topology.Instances.ENNReal
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The `Lᵖ` translation estimate

This file defines translation of `Lᵖ` classes as a linear isometric equivalence, proves its strong
continuity for `p < ∞`, and proves the translation estimate for a `C¹` function on a
finite-dimensional real normed space carrying an additive Haar measure:

`‖u(· + h) - u‖_p ≤ ‖h‖ ‖Du‖_p`.

It is the quantitative form of continuity of translation in `Lᵖ`. The proof integrates the
segment increment estimate `TauCeti.enorm_sub_le_lintegral_enorm_fderiv_apply`, raises the
resulting bound to the power `p`, and uses translation invariance of Haar measure after
exchanging the order of integration.

## Main declarations

* `MeasureTheory.Measure.translateLp`: translation by a vector as a linear isometric equivalence
  of `Lᵖ`.
* `MeasureTheory.Measure.coeFn_translateLp`: translation is almost everywhere precomposition by
  addition.
* `MeasureTheory.Measure.translateLp_zero`, `MeasureTheory.Measure.translateLp_symm`,
  `MeasureTheory.Measure.translateLp_add`: translation is an action of the additive group of
  vectors.
* `MeasureTheory.Measure.continuous_translateLp`: strong continuity of translation for `p < ∞`.
* `MeasureTheory.Measure.enorm_translateLp_sub`: identifies the norm of an `Lᵖ` translation
  increment with its pointwise `eLpNorm`.
* `TauCeti.tendsto_eLpNorm_comp_add_sub_of_memLp`: translation increments of an `Lᵖ` function
  tend to zero.
* `TauCeti.lintegral_enorm_comp_add_sub_rpow_le`: the translation estimate in `∫⁻` form.
* `TauCeti.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv`: the `Lᵖ` translation estimate for a `C¹`
  function.
* `TauCeti.tendsto_eLpNorm_comp_add_sub`: continuity of translation in `Lᵖ` for a `C¹` function
  with `Lᵖ` derivative.

## References

Lane A.6 of `TauCetiRoadmap/PDE/README.md`; H. Brezis, *Functional Analysis, Sobolev Spaces and
Partial Differential Equations*, Proposition 9.3; L. C. Evans, *Partial Differential Equations*,
Chapter 5.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

section LpTranslation

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

/-- Translation by `h` on `Lᵖ`, as a linear isometric equivalence.

Precomposition by `· + h` is invertible, its inverse being precomposition by `· + -h`; carrying
that inverse makes the identity, inverse and composition laws
`MeasureTheory.Measure.translateLp_zero`, `MeasureTheory.Measure.translateLp_symm` and
`MeasureTheory.Measure.translateLp_add` available as an action of the additive group of vectors
on `Lᵖ`. -/
def translateLp (mu : Measure E) [mu.IsAddHaarMeasure] (p : ENNReal) [Fact (1 ≤ p)]
    (h : E) : Lp F p mu ≃ₗᵢ[ℝ] Lp F p mu :=
  Lp.compMeasurePreservingₗᵢEquiv ℝ (measurePreserving_add_right mu h)
    (measurePreserving_add_right mu (-h))
    (Filter.EventuallyEq.of_eq (funext fun x ↦ by simp))

omit [NormedSpace ℝ E] in
/-- Translation by `h` is almost everywhere precomposition by addition of `h`. -/
theorem coeFn_translateLp (h : E) (f : Lp F p mu) :
    ⇑(translateLp mu p h f) =ᵐ[mu] ⇑f ∘ (· + h) := by
  rw [translateLp]
  exact Lp.coeFn_compMeasurePreservingₗᵢEquiv ℝ _ _ _ f

omit [NormedSpace ℝ E] in
/-- Translating by `h₁ + h₂` is translating by `h₁` and then by `h₂`. -/
theorem translateLp_add (h₁ h₂ : E) :
    translateLp (F := F) mu p (h₁ + h₂) = (translateLp mu p h₁).trans (translateLp mu p h₂) := by
  refine LinearIsometryEquiv.ext fun f => Lp.ext ?_
  filter_upwards [coeFn_translateLp (mu := mu) (h₁ + h₂) f,
    coeFn_translateLp (mu := mu) h₂ (translateLp mu p h₁ f),
    (measurePreserving_add_right mu h₂).quasiMeasurePreserving.ae_eq_comp
      (coeFn_translateLp (mu := mu) h₁ f)] with x hx hy hz
  simp only [Function.comp_apply] at hx hy hz
  rw [hx, LinearIsometryEquiv.trans_apply, hy, hz]
  exact congrArg _ (by abel)

omit [NormedSpace ℝ E] in
/-- Translation by zero is the identity on `Lᵖ`. -/
@[simp]
theorem translateLp_zero (f : Lp F p mu) : translateLp mu p 0 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_translateLp (mu := mu) 0 f] with x hx
  simpa only [Function.comp_apply, add_zero] using hx

omit [NormedSpace ℝ E] in
/-- The inverse of translation by `h` is translation by `-h`. -/
@[simp]
theorem translateLp_symm (h : E) :
    (translateLp (F := F) mu p h).symm = translateLp mu p (-h) :=
  LinearIsometryEquiv.ext fun f => (LinearIsometryEquiv.symm_apply_eq _).2 <| by
    rw [← LinearIsometryEquiv.trans_apply, ← translateLp_add, neg_add_cancel, translateLp_zero]

omit [NormedSpace ℝ E] in
/-- Translation of a fixed `Lᵖ` class depends continuously on the translation vector when
`p < ∞`. -/
theorem continuous_translateLp [ProperSpace E] (hp : p ≠ ∞) (f : Lp F p mu) :
    Continuous fun h : E ↦ translateLp mu p h f := by
  let T : E → C(E, E) := fun h ↦ ⟨fun x ↦ x + h, continuous_id.add continuous_const⟩
  have hT : Continuous T := ContinuousMap.continuous_of_continuous_uncurry T <| by
    dsimp only [T, Function.uncurry_apply_pair, ContinuousMap.coe_mk]
    fun_prop
  have hpres : ∀ h, MeasurePreserving (T h) mu mu := fun h ↦ by
    simpa only [T, ContinuousMap.coe_mk] using measurePreserving_add_right mu h
  have hcont : Continuous (fun h : E ↦ Lp.compMeasurePreserving (T h) (hpres h) f) :=
    (continuous_const : Continuous fun _ : E ↦ f).compMeasurePreservingLp hT hpres hp
  simpa only [translateLp, T, ContinuousMap.coe_mk,
    Lp.compMeasurePreservingₗᵢEquiv_apply] using hcont

omit [NormedSpace ℝ E] in
/-- The `Lᵖ` extended norm of a translation increment is its pointwise `eLpNorm`. -/
theorem enorm_translateLp_sub (h : E) (f : Lp F p mu) :
    ‖translateLp mu p h f - f‖ₑ = eLpNorm (fun x ↦ f (x + h) - f x) p mu := by
  have hae : ⇑(translateLp mu p h f - f) =ᵐ[mu] fun x ↦ f (x + h) - f x := by
    filter_upwards [Lp.coeFn_sub (translateLp mu p h f) f,
      coeFn_translateLp (mu := mu) h f] with x hx hy
    rw [hx, Pi.sub_apply, hy]
    rfl
  rw [Lp.enorm_def, eLpNorm_congr_ae hae]

end LpTranslation

end MeasureTheory.Measure

namespace TauCeti

section MemLpTranslation

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal}

/-- Translation increments of an `Lᵖ` function tend to zero as the translation tends to zero. -/
theorem tendsto_eLpNorm_comp_add_sub_of_memLp [ProperSpace E] {u : E → F}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hu : MemLp u p mu) :
    Filter.Tendsto (fun h : E ↦ eLpNorm (fun x ↦ u (x + h) - u x) p mu)
      (nhds 0) (nhds 0) := by
  let _ : Fact (1 ≤ p) := ⟨hp⟩
  have hcont := (Measure.continuous_translateLp (mu := mu) hp' (hu.toLp u)).tendsto (0 : E)
  have htend : Filter.Tendsto (fun h : E ↦ mu.translateLp p h (hu.toLp u))
      (nhds 0) (nhds (hu.toLp u)) := by
    simpa only [Measure.translateLp_zero] using hcont
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at htend
  apply htend.congr'
  filter_upwards with h
  apply eLpNorm_congr_ae
  exact ((Measure.coeFn_translateLp (mu := mu) h (hu.toLp u)).trans
      ((measurePreserving_add_right mu h).quasiMeasurePreserving.ae_eq_comp hu.coeFn_toLp)).sub
    hu.coeFn_toLp

end MemLpTranslation

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F}

/-- The `r`-th power of the segment estimate. Raising to the power `r ≥ 1` costs nothing because
the segment is parametrized by the probability space `Set.Icc 0 1`; the operator norm then splits
off `‖h‖ ^ r`. -/
private theorem enorm_sub_rpow_le (hu : ContDiff ℝ 1 u) {r : ℝ} (hr : 1 ≤ r) (x h : E) :
    ‖u (x + h) - u x‖ₑ ^ r
      ≤ ‖h‖ₑ ^ r * ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h)‖ₑ ^ r := by
  have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
  have hmeas : AEMeasurable (fun t : ℝ => ‖fderiv ℝ u (x + t • h) h‖ₑ)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (((hu.continuous_fderiv one_ne_zero).comp
      (by fun_prop : Continuous fun t : ℝ => x + t • h)).clm_apply
      continuous_const).enorm.aemeasurable
  have huniv : (volume.restrict (Icc (0 : ℝ) 1)) univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  have hsegment := enorm_sub_le_lintegral_enorm_fderiv_apply x h
    (fun t _ => (hu.differentiable one_ne_zero) (x + t • h))
    (((hu.continuous_fderiv one_ne_zero).comp_continuousOn (by fun_prop)).clm_apply
      continuousOn_const)
  calc ‖u (x + h) - u x‖ₑ ^ r
      ≤ (∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ) ^ r :=
        ENNReal.rpow_le_rpow hsegment hr0.le
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ ^ r := by
        simpa [huniv] using rpow_lintegral_le_measure_univ_rpow_mul hmeas hr
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, (‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ) ^ r := by
        gcongr with t
        exact ContinuousLinearMap.le_opENorm _ _
    _ = ‖h‖ₑ ^ r * ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h)‖ₑ ^ r := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
        rw [lintegral_mul_const' _ _ (by finiteness), mul_comm]

end Calculus

section Translation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {u : E → F}

/-- **The translation estimate in `∫⁻` form**: for a `C¹` function and `1 ≤ r`,
`∫ ‖u(x + h) - u(x)‖ ^ r dx ≤ ‖h‖ ^ r ∫ ‖Du‖ ^ r`.

The segment estimate is integrated in `x`, the order of integration in `x` and in the segment
parameter is exchanged, and the inner integral is then independent of the parameter because the
measure is translation invariant. -/
theorem lintegral_enorm_comp_add_sub_rpow_le (hu : ContDiff ℝ 1 u) {r : ℝ} (hr : 1 ≤ r) (h : E) :
    ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ r ∂mu ≤ ‖h‖ₑ ^ r * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ r ∂mu := by
  have hjoint : Measurable fun z : E × ℝ => ‖fderiv ℝ u (z.1 + z.2 • h)‖ₑ ^ r :=
    (ENNReal.continuous_rpow_const.comp
      (((hu.continuous_fderiv one_ne_zero).comp (by fun_prop)).enorm)).measurable
  calc ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ r ∂mu
      ≤ ∫⁻ x, (‖h‖ₑ ^ r * ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h)‖ₑ ^ r) ∂mu :=
        lintegral_mono fun x => enorm_sub_rpow_le hu hr x h
    _ = ‖h‖ₑ ^ r * ∫⁻ x, (∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h)‖ₑ ^ r) ∂mu :=
        lintegral_const_mul' _ _ (by finiteness)
    _ = ‖h‖ₑ ^ r * ∫⁻ t in Icc (0 : ℝ) 1, (∫⁻ x, ‖fderiv ℝ u (x + t • h)‖ₑ ^ r ∂mu) := by
        rw [lintegral_lintegral_swap hjoint.aemeasurable]
    _ = ‖h‖ₑ ^ r * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ r ∂mu := by
        congr 1
        rw [setLIntegral_congr_fun measurableSet_Icc fun t _ =>
          lintegral_add_right_eq_self (fun y => ‖fderiv ℝ u y‖ₑ ^ r) (t • h),
          lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        simp

/-- **The `Lᵖ` translation estimate**: a `C¹` function moves in `Lᵖ` at most linearly in the
translation, at the rate given by the `Lᵖ` seminorm of its derivative,

`‖u(· + h) - u‖_p ≤ ‖h‖ ‖Du‖_p`, `1 ≤ p < ∞`.

No support, integrability or boundedness hypothesis is needed. For `h ≠ 0`, if `Du` is not in
`Lᵖ` the right-hand side is `∞` and the bound carries no information; at `h = 0` both sides are
`0`. -/
theorem eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (h : E) :
    eLpNorm (fun x => u (x + h) - u x) p mu ≤ ‖h‖ₑ * eLpNorm (fderiv ℝ u) p mu := by
  have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  rw [← ofReal_norm h]
  refine eLpNorm_le_eLpNorm_of_lintegral_rpow_le (norm_nonneg h) (zero_lt_one.trans_le hp).ne'
    hp' ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg h) (zero_lt_one.trans_le hr).le, ofReal_norm]
  exact lintegral_enorm_comp_add_sub_rpow_le hu hr h

/-- **Continuity of translation in `Lᵖ`** for a `C¹` function with `Lᵖ` derivative: the `Lᵖ`
distance between `u` and its translate tends to `0`. This is the qualitative corollary of
`TauCeti.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv`, which gives the linear modulus.

For a `u` that is itself in `Lᵖ` this is already Mathlib's
`Filter.Tendsto.compMeasurePreservingLp`, which needs no derivative; the content here is that a
`C¹` function with `Lᵖ` derivative translates continuously in `Lᵖ` even when it is not in `Lᵖ`. -/
theorem tendsto_eLpNorm_comp_add_sub (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hfin : eLpNorm (fderiv ℝ u) p mu ≠ ∞) :
    Filter.Tendsto (fun h : E => eLpNorm (fun x => u (x + h) - u x) p mu) (nhds 0) (nhds 0) :=
  tendsto_nhds_zero_of_le_enorm_mul hfin fun h =>
    eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv hu hp hp' h

end Translation

end TauCeti
