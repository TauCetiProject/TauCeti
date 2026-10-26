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
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The `Lᵖ` translation estimate

This file develops continuous translation of `Lᵖ` functions on a space with continuous addition
carrying a right-invariant measure, translation equivalences on additive groups, and the
quantitative translation estimate for `C¹` functions on a real normed space:

`‖u(· + h) - u‖_p ≤ ‖h‖ ‖Du‖_p`.

Translation of `Lᵖ` classes is a linear isometric equivalence, it is an action of the additive
group, and for `p < ∞` it is strongly continuous. Consequently, the translation increments of any
`Lᵖ` function tend to zero. The translation estimate is the quantitative form of this continuity
for a `C¹` function, and needs no integrability of the function itself.

## Main declarations

* `MeasureTheory.Lp.continuous_compMeasurePreserving_add_right`: strong continuity of translation
  of `Lᵖ` classes for `p < ∞`.
* `MeasureTheory.Measure.translateLp`: translation by a group element as a linear
  isometric equivalence of `Lᵖ`.
* `MeasureTheory.Measure.coeFn_translateLp`, `MeasureTheory.MemLp.coeFn_translateLp_toLp`:
  translation is almost everywhere precomposition by addition.
* `ContinuousLinearMap.compLpL_translateLp`: translation commutes with postcomposition by a
  continuous linear map.
* `MeasureTheory.Measure.translateLp_zero`, `MeasureTheory.Measure.translateLp_symm`,
  `MeasureTheory.Measure.translateLp_add`: translation is an action of the additive group.
* `MeasureTheory.Measure.continuous_translateLp`: strong continuity of `translateLp` for `p < ∞`.
* `MeasureTheory.Measure.enorm_translateLp_sub`: identifies the norm of an `Lᵖ` translation
  increment with its pointwise `eLpNorm`.
* `MeasureTheory.MemLp.comp_add_right_restrict_of_mapsTo`: translation preserves `Lᵖ` on a smaller
  domain whose translate stays in the original domain.
* `MeasureTheory.MemLp.tendsto_eLpNorm_comp_add_sub`: translation increments of an `Lᵖ` function
  tend to zero.
* `MeasureTheory.eLpNorm_comp_add_sub_le_two_mul`: a translation increment is at most twice the
  function.
* `ContDiff.setLIntegral_enorm_comp_add_sub_rpow_le`,
  `ContDiff.eLpNorm_comp_add_sub_le_eLpNorm_fderiv_apply`: the local translation estimate,
  bounding the increment on a set `K` by the directional derivative on a set containing the
  segments `[x, x + h]`, `x ∈ K`.
* `ContDiff.lintegral_enorm_comp_add_sub_rpow_le`,
  `ContDiff.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv`: the global translation estimate.
* `ContDiff.tendsto_eLpNorm_comp_add_sub`: continuity of translation in `Lᵖ` for a `C¹` function
  with `Lᵖ` derivative.
* `ContDiff.eLpNorm_comp_add_add_sub_sub_le_mul_eLpNorm_fderiv_fderiv`: the second-order
  translation estimate, bounding a mixed second difference by the second derivative.

## References

H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Proposition 9.3; L. C. Evans, *Partial Differential Equations*, Chapter 5.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

namespace Lp

variable {E F : Type*} [Add E] [MeasurableSpace E] [TopologicalSpace E] [ContinuousAdd E]
  [BorelSpace E] [R1Space E] [NormedAddCommGroup F] {mu : Measure E} [mu.IsAddRightInvariant]
  [mu.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure mu] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translation of a fixed `Lᵖ` class depends continuously on the translation parameter when
`p < ∞`. -/
theorem continuous_compMeasurePreserving_add_right (hp : p ≠ ∞) (f : Lp F p mu) :
    Continuous fun h : E ↦ compMeasurePreserving (· + h) (measurePreserving_add_right mu h) f := by
  let T : E → C(E, E) := fun h ↦ ⟨(· + h), by fun_prop⟩
  have hT : Continuous T := ContinuousMap.continuous_of_continuous_uncurry T <| by
    dsimp only [T, Function.uncurry_apply_pair, ContinuousMap.coe_mk]
    fun_prop
  exact continuous_const.compMeasurePreservingLp hT
    (fun h ↦ measurePreserving_add_right mu h) hp

end Lp

namespace Measure

section LpTranslation

variable {E F : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E} [mu.IsAddRightInvariant]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translation by `h` on `Lᵖ`, as a linear isometric equivalence: almost everywhere it sends `f`
to `f (· + h)`, and its inverse is translation by `-h`. -/
def translateLp (mu : Measure E) [mu.IsAddRightInvariant] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : E) : Lp F p mu ≃ₗᵢ[ℝ] Lp F p mu :=
  Lp.compMeasurePreservingₗᵢEquiv ℝ (measurePreserving_add_right mu h)
    (measurePreserving_add_right mu (-h))
    (Filter.EventuallyEq.of_eq (funext fun x ↦ by simp))

/-- Translation by `h` is almost everywhere precomposition by addition of `h`. -/
theorem coeFn_translateLp (h : E) (f : Lp F p mu) :
    ⇑(translateLp mu p h f) =ᵐ[mu] ⇑f ∘ (· + h) := by
  rw [translateLp]
  exact Lp.coeFn_compMeasurePreservingₗᵢEquiv ℝ _ _ _ f

/-- Translation commutes with postcomposition by a continuous linear map. -/
theorem _root_.ContinuousLinearMap.compLpL_translateLp {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (L : F →L[ℝ] G) (h : E) (f : Lp F p mu) :
    L.compLpL p mu (translateLp mu p h f) = translateLp mu p h (L.compLpL p mu f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (translateLp mu p h f), coeFn_translateLp (mu := mu) h f,
    coeFn_translateLp (mu := mu) h (L.compLpL p mu f),
    (measurePreserving_add_right mu h).quasiMeasurePreserving.tendsto_ae.eventually
      (L.coeFn_compLpL f)] with x hL htr htrL hLtr
  rw [hL, htr, htrL]
  exact hLtr.symm

/-- Translating by `h₁ + h₂` is translating by `h₂` and then by `h₁`, so these
equivalences give a left action even when addition is not commutative. -/
theorem translateLp_add (h₁ h₂ : E) :
    translateLp (F := F) mu p (h₁ + h₂) = (translateLp mu p h₂).trans (translateLp mu p h₁) := by
  refine LinearIsometryEquiv.ext fun f => Lp.ext ?_
  filter_upwards [coeFn_translateLp (mu := mu) (h₁ + h₂) f,
    coeFn_translateLp (mu := mu) h₁ (translateLp mu p h₂ f),
    (measurePreserving_add_right mu h₁).quasiMeasurePreserving.ae_eq_comp
      (coeFn_translateLp (mu := mu) h₂ f)] with x hx hy hz
  simp only [Function.comp_apply] at hx hy hz
  rw [hx, LinearIsometryEquiv.trans_apply, hy, hz]
  exact congrArg _ (add_assoc _ _ _).symm

/-- Translation by zero is the identity on `Lᵖ`. -/
@[simp]
theorem translateLp_zero (f : Lp F p mu) : translateLp mu p 0 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_translateLp (mu := mu) 0 f] with x hx
  simpa only [Function.comp_apply, add_zero] using hx

/-- The inverse of translation by `h` is translation by `-h`. -/
@[simp]
theorem translateLp_symm (h : E) :
    (translateLp (F := F) mu p h).symm = translateLp mu p (-h) :=
  LinearIsometryEquiv.ext fun f => (LinearIsometryEquiv.symm_apply_eq _).2 <| by
    rw [← LinearIsometryEquiv.trans_apply, ← translateLp_add, add_neg_cancel, translateLp_zero]

/-- Translation of a fixed `Lᵖ` class depends continuously on the translation parameter when
`p < ∞`. -/
theorem continuous_translateLp [TopologicalSpace E] [ContinuousAdd E] [BorelSpace E] [R1Space E]
    [mu.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure mu] (hp : p ≠ ∞) (f : Lp F p mu) :
    Continuous fun h : E ↦ translateLp mu p h f := by
  simpa only [translateLp, Lp.compMeasurePreservingₗᵢEquiv_apply] using
    Lp.continuous_compMeasurePreserving_add_right hp f

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

end Measure

namespace MemLp

/-- The translate of the `Lᵖ` class of `f` by `h` is almost everywhere `f (· + h)`. -/
theorem coeFn_translateLp_toLp {E F : Type*} [AddGroup E] [MeasurableSpace E]
    [MeasurableAdd E] [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E}
    [mu.IsAddRightInvariant] {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : E → F} (hf : MemLp f p mu) (h : E) :
    ⇑(mu.translateLp p h (hf.toLp f)) =ᵐ[mu] fun x ↦ f (x + h) :=
  (Measure.coeFn_translateLp h (hf.toLp f)).trans
    ((measurePreserving_add_right mu h).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp)

section

variable {E F : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E] {mu : Measure E}
  [mu.IsAddRightInvariant] {p : ℝ≥0∞}

/-- An `Lᵖ` function remains `Lᵖ` after translation on any set whose translate lies in the
original domain. This is the restricted-domain counterpart of precomposition by
`MeasureTheory.Measure.translateLp`. -/
theorem comp_add_right_restrict_of_mapsTo [TopologicalSpace F] [ContinuousENorm F]
    {Omega V : Set E} {h : E} {f : E → F}
    (hf : MemLp f p (mu.restrict Omega)) (hVO : MapsTo (· + h) V Omega) :
    MemLp (fun x => f (x + h)) p (mu.restrict V) :=
  (hf.comp_measurePreserving ((measurePreserving_add_right mu h).restrict_preimage_emb
    (measurableEmbedding_addRight h) Omega)).mono_measure
    (Measure.restrict_mono_set mu hVO.subset_preimage)

end

variable {E F : Type*} [AddZeroClass E] [MeasurableSpace E] {mu : Measure E}
  [mu.IsAddRightInvariant] {p : ℝ≥0∞}

/-- Translation increments of an `Lᵖ` function tend to zero as the translation tends to zero. -/
theorem tendsto_eLpNorm_comp_add_sub [TopologicalSpace E] [ContinuousAdd E] [BorelSpace E]
    [R1Space E] [mu.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure mu] [NormedAddCommGroup F]
    {u : E → F} (hu : MemLp u p mu) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    Filter.Tendsto (fun h : E ↦ eLpNorm (fun x ↦ u (x + h) - u x) p mu) (nhds 0) (nhds 0) := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  have htend := (Lp.continuous_compMeasurePreserving_add_right hp' (hu.toLp u)).tendsto 0
  have hzero : (fun x : E ↦ x + 0) = id := funext fun x ↦ add_zero x
  simp only [hzero, Lp.compMeasurePreserving_id_apply] at htend
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hu] at htend
  refine htend.congr' (Filter.Eventually.of_forall fun h ↦ eLpNorm_congr_ae ?_)
  exact ((Lp.coeFn_compMeasurePreserving _ _).trans
    ((measurePreserving_add_right mu h).quasiMeasurePreserving.ae_eq_comp hu.coeFn_toLp)).sub
      Filter.EventuallyEq.rfl

end MemLp

/-- A translation increment is at most twice the function: `‖u(· + h) - u‖_p ≤ 2 ‖u‖_p` for
`1 ≤ p` and a right-invariant measure. -/
theorem eLpNorm_comp_add_sub_le_two_mul {E F : Type*} [Add E] [MeasurableSpace E]
    [MeasurableAdd E] {mu : Measure E} [mu.IsAddRightInvariant] [NormedAddCommGroup F]
    {p : ℝ≥0∞} {u : E → F} (hu : AEStronglyMeasurable u mu) (hp : 1 ≤ p) (h : E) :
    eLpNorm (fun x => u (x + h) - u x) p mu ≤ 2 * eLpNorm u p mu := by
  have htr : eLpNorm (fun x => u (x + h)) p mu = eLpNorm u p mu :=
    eLpNorm_comp_measurePreserving hu (measurePreserving_add_right mu h)
  calc eLpNorm (fun x => u (x + h) - u x) p mu
      ≤ eLpNorm (fun x => u (x + h)) p mu + eLpNorm u p mu := eLpNorm_sub_le hp
    _ = 2 * eLpNorm u p mu := by rw [htr, two_mul]

/-- Translation is continuous in the `L¹` distance from a fixed translate. -/
theorem Integrable.continuous_integral_norm_translate_sub
    {G E : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] {μ : Measure G} [μ.IsAddRightInvariant]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    {k : G → E} (hk : Integrable k μ) (b : G) :
    Continuous (fun c : G ↦ ∫ z : G, ‖k (z - c) - k (z - b)‖ ∂μ) := by
  let f : G → Lp E 1 μ := fun c ↦
    Lp.compMeasurePreserving (· + -c) (measurePreserving_add_right μ (-c)) (hk.toL1 k)
  have hf : Continuous f :=
    (Lp.continuous_compMeasurePreserving_add_right (by simp) (hk.toL1 k)).comp continuous_neg
  have hae (c : G) : f c =ᵐ[μ] fun z ↦ k (z - c) := by
    simpa only [f, sub_eq_add_neg, Function.comp_def] using
      (Lp.coeFn_compMeasurePreserving (hk.toL1 k) (measurePreserving_add_right μ (-c))).trans
        ((measurePreserving_add_right μ (-c)).quasiMeasurePreserving.ae_eq_comp hk.coeFn_toL1)
  have heq (c : G) : ‖f c - f b‖ = ∫ z : G, ‖k (z - c) - k (z - b)‖ ∂μ := by
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae
      (((Lp.coeFn_sub (f c) (f b)).trans ((hae c).sub (hae b))).fun_comp (fun x : E ↦ ‖x‖))
  exact ((hf.sub continuous_const).norm).congr heq

/-- Convergent shifts of an integrable function converge in `L¹`. -/
theorem Integrable.tendsto_integral_norm_translate_sub
    {G E α : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] {μ : Measure G} [μ.IsAddRightInvariant]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    {k : G → E} (hk : Integrable k μ) {c : α → G} {b : G} {l : Filter α}
    (hc : Filter.Tendsto c l (nhds b)) :
    Filter.Tendsto (fun a ↦ ∫ z : G, ‖k (z - c a) - k (z - b)‖ ∂μ) l (nhds 0) := by
  simpa only [Function.comp_def, sub_self, norm_zero, integral_zero] using
    (hk.continuous_integral_norm_translate_sub b).continuousAt.tendsto.comp hc

end MeasureTheory

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F}

/-- **The powered segment estimate in the direction of the increment.** For a `C¹` function and
`r ≥ 1`, the `r`-th power of `‖u(x + h) - u(x)‖` is bounded by the integral along `[x, x + h]`
of the `r`-th power of the directional derivative `Du · h`. -/
theorem ContDiff.enorm_sub_rpow_le_lintegral_fderiv_apply (hu : ContDiff ℝ 1 u)
    {r : ℝ} (hr : 1 ≤ r) (x h : E) :
    ‖u (x + h) - u x‖ₑ ^ r ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ ^ r := by
  have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
  have hmeas : AEMeasurable (fun t : ℝ => ‖fderiv ℝ u (x + t • h) h‖ₑ)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (((hu.continuous_fderiv one_ne_zero).comp
      (by fun_prop : Continuous fun t : ℝ => x + t • h)).clm_apply
      continuous_const).enorm.aemeasurable
  have huniv : (volume.restrict (Icc (0 : ℝ) 1)) univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  have hsegment := TauCeti.enorm_sub_le_lintegral_enorm_fderiv_apply x h
    (fun t _ => (hu.differentiable one_ne_zero) (x + t • h))
    (((hu.continuous_fderiv one_ne_zero).comp_continuousOn (by fun_prop)).clm_apply
      continuousOn_const)
  -- Jensen's inequality costs no measure factor because `Icc 0 1` has volume one.
  calc ‖u (x + h) - u x‖ₑ ^ r
      ≤ (∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ) ^ r :=
        ENNReal.rpow_le_rpow hsegment hr0.le
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ ^ r := by
        simpa [huniv] using TauCeti.rpow_lintegral_le_measure_univ_rpow_mul hmeas hr

end Calculus

section Translation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E} [SFinite mu] [mu.IsAddRightInvariant]
  {u : E → F}

/-- **The local translation estimate in `∫⁻` form**: for a `C¹` function and `1 ≤ r`, if every
segment `[x, x + h]` starting in `K` lies in the measurable set `T`, then

`∫_K ‖u(x + h) - u(x)‖ ^ r dx ≤ ∫_T ‖Du(x) h‖ ^ r dx`.

Only the directional derivative `Du · h` enters, and only on `T`. -/
theorem ContDiff.setLIntegral_enorm_comp_add_sub_rpow_le (hu : ContDiff ℝ 1 u) {r : ℝ}
    (hr : 1 ≤ r) (h : E) {K T : Set E} (hT : MeasurableSet T)
    (hKT : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ T) :
    ∫⁻ x in K, ‖u (x + h) - u x‖ₑ ^ r ∂mu ≤ ∫⁻ x in T, ‖fderiv ℝ u x h‖ₑ ^ r ∂mu := by
  -- Cut the derivative off to `T` before exchanging the integrals over `x` and the segment.
  set g : E → ℝ≥0∞ := T.indicator fun y => ‖fderiv ℝ u y h‖ₑ ^ r
  have hg : Measurable g :=
    (ENNReal.continuous_rpow_const.comp (((hu.continuous_fderiv one_ne_zero).clm_apply
      continuous_const).enorm)).measurable.indicator hT
  have hjoint : Measurable fun z : E × ℝ => g (z.1 + z.2 • h) :=
    hg.comp (by fun_prop : Continuous fun z : E × ℝ => z.1 + z.2 • h).measurable
  calc ∫⁻ x in K, ‖u (x + h) - u x‖ₑ ^ r ∂mu
      ≤ ∫⁻ x in K, (∫⁻ t in Icc (0 : ℝ) 1, g (x + t • h)) ∂mu := by
        refine setLIntegral_mono hjoint.lintegral_prod_right' fun x hx => ?_
        refine (hu.enorm_sub_rpow_le_lintegral_fderiv_apply hr x h).trans
          (setLIntegral_mono' measurableSet_Icc fun t ht => ?_)
        simp [g, indicator_of_mem (hKT x hx t ht)]
    _ ≤ ∫⁻ x, (∫⁻ t in Icc (0 : ℝ) 1, g (x + t • h)) ∂mu := setLIntegral_le_lintegral _ _
    _ = ∫⁻ t in Icc (0 : ℝ) 1, (∫⁻ x, g (x + t • h) ∂mu) :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ x in T, ‖fderiv ℝ u x h‖ₑ ^ r ∂mu := by
        rw [setLIntegral_congr_fun measurableSet_Icc fun t _ =>
          lintegral_add_right_eq_self g (t • h), lintegral_const, Measure.restrict_apply_univ,
          Real.volume_Icc, lintegral_indicator hT]
        simp

/-- **The translation estimate in `∫⁻` form**: for a `C¹` function and `1 ≤ r`,
`∫ ‖u(x + h) - u(x)‖ ^ r dx ≤ ‖h‖ ^ r ∫ ‖Du‖ ^ r`. -/
theorem ContDiff.lintegral_enorm_comp_add_sub_rpow_le (hu : ContDiff ℝ 1 u) {r : ℝ} (hr : 1 ≤ r)
    (h : E) :
    ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ r ∂mu ≤ ‖h‖ₑ ^ r * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ r ∂mu := by
  have hr0 : (0 : ℝ) ≤ r := zero_le_one.trans hr
  calc ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ r ∂mu
      ≤ ∫⁻ x, ‖fderiv ℝ u x h‖ₑ ^ r ∂mu := by
        simpa only [Measure.restrict_univ] using
          hu.setLIntegral_enorm_comp_add_sub_rpow_le (mu := mu) (K := univ) hr h
            MeasurableSet.univ fun _ _ _ _ => mem_univ _
    _ ≤ ∫⁻ x, (‖fderiv ℝ u x‖ₑ * ‖h‖ₑ) ^ r ∂mu := by
        gcongr with x
        exact ContinuousLinearMap.le_opENorm _ _
    _ = ‖h‖ₑ ^ r * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ r ∂mu := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr0]
        rw [lintegral_mul_const' _ _ (by finiteness), mul_comm]

/-- **The local `Lᵖ` translation estimate**: for a `C¹` function and `1 ≤ p ≤ ∞`, if every
segment `[x, x + h]` starting in `K` lies in the measurable set `T`, then

`‖u(· + h) - u‖_{Lᵖ(K)} ≤ ‖Du · h‖_{Lᵖ(T)}`.

Unlike `ContDiff.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv`, the right-hand side sees only the
derivative in the direction `h`, and only on `T`: this is the form in which translation increments
of a function defined on a domain are controlled away from the boundary. -/
theorem ContDiff.eLpNorm_comp_add_sub_le_eLpNorm_fderiv_apply [SecondCountableTopology E]
    (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞} (hp : 1 ≤ p) (h : E) {K T : Set E}
    (hT : MeasurableSet T) (hKT : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ T) :
    eLpNorm (fun x => u (x + h) - u x) p (mu.restrict K)
      ≤ eLpNorm (fun x => fderiv ℝ u x h) p (mu.restrict T) := by
  have hsub : Continuous fun x => u (x + h) - u x := by fun_prop
  have hfd : Continuous fun x => fderiv ℝ u x h :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  by_cases hp' : p = ∞
  · subst p
    rw [eLpNorm_exponent_top hsub.aestronglyMeasurable,
      eLpNorm_exponent_top hfd.aestronglyMeasurable]
    let C := eLpNormEssSup (fun x => fderiv ℝ u x h) (mu.restrict T)
    let g : E → ℝ≥0∞ := T.indicator fun x => ‖fderiv ℝ u x h‖ₑ
    have hg : Measurable g := hfd.enorm.measurable.indicator hT
    have hgC : ∀ᵐ x ∂mu, g x ≤ C := by
      filter_upwards [(ae_restrict_iff' hT).1
        (ae_le_eLpNormEssSup (f := fun x => fderiv ℝ u x h))] with x hx
      by_cases hxT : x ∈ T
      · simpa only [g, indicator_of_mem hxT] using hx hxT
      · simp only [g, indicator_of_notMem hxT, zero_le]
    have hjoint : Measurable fun z : E × ℝ => g (z.1 + z.2 • h) :=
      hg.comp (by fun_prop : Continuous fun z : E × ℝ => z.1 + z.2 • h).measurable
    -- Fubini transports the essential bound to almost every segment starting point.
    have hsegments : ∀ᵐ x ∂mu, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        g (x + t • h) ≤ C :=
      (Measure.ae_ae_comm (μ := mu) (ν := volume.restrict (Icc (0 : ℝ) 1))
        (p := fun x t => g (x + t • h) ≤ C)
        (measurableSet_le hjoint measurable_const)).2
        (Filter.Eventually.of_forall fun t =>
          (measurePreserving_add_right mu (t • h)).quasiMeasurePreserving.tendsto_ae.eventually hgC)
    apply eLpNormEssSup_le_of_ae_enorm_bound
    refine (ae_restrict_iff (measurableSet_le hsub.enorm.measurable measurable_const)).2 ?_
    filter_upwards [hsegments] with x hx hxK
    calc ‖u (x + h) - u x‖ₑ
        ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ := by
          simpa only [ENNReal.rpow_one] using
            hu.enorm_sub_rpow_le_lintegral_fderiv_apply (r := 1) le_rfl x h
      _ = ∫⁻ t in Icc (0 : ℝ) 1, g (x + t • h) :=
        setLIntegral_congr_fun measurableSet_Icc fun t ht =>
          (indicator_of_mem (hKT x hxK t ht) (fun y => ‖fderiv ℝ u y h‖ₑ)).symm
      _ ≤ ∫⁻ _ in Icc (0 : ℝ) 1, C := lintegral_mono_ae hx
      _ = C := by simp [Real.volume_Icc]
  · have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hsub.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hfd.aestronglyMeasurable]
    exact ENNReal.rpow_le_rpow (hu.setLIntegral_enorm_comp_add_sub_rpow_le hr h hT hKT)
      (by positivity)

/-- **The `Lᵖ` translation estimate**: a `C¹` function moves in `Lᵖ` at most linearly in the
translation, at the rate given by the `Lᵖ` seminorm of its derivative,

`‖u(· + h) - u‖_p ≤ ‖h‖ ‖Du‖_p`, `1 ≤ p ≤ ∞`.

No support, integrability or boundedness hypothesis is needed. For `h ≠ 0`, if `Du` is not in
`Lᵖ` the right-hand side is `∞` and the bound carries no information; at `h = 0` both sides are
`0`. -/
theorem ContDiff.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv [SecondCountableTopology E]
    (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞} (hp : 1 ≤ p) (h : E) :
    eLpNorm (fun x => u (x + h) - u x) p mu ≤ ‖h‖ₑ * eLpNorm (fderiv ℝ u) p mu := by
  calc eLpNorm (fun x => u (x + h) - u x) p mu
      ≤ eLpNorm (fun x => fderiv ℝ u x h) p mu := by
        simpa only [Measure.restrict_univ] using
          hu.eLpNorm_comp_add_sub_le_eLpNorm_fderiv_apply (mu := mu) (K := univ) hp h
            MeasurableSet.univ fun _ _ _ _ => mem_univ _
    _ ≤ ‖h‖ₑ * eLpNorm (fderiv ℝ u) p mu :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
          ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => by
            rw [mul_comm]
            exact ContinuousLinearMap.le_opENorm _ _)

/-- **Continuity of translation in `Lᵖ`** for a `C¹` function with `Lᵖ` derivative: the `Lᵖ`
distance between `u` and its translate tends to `0`. This is the qualitative corollary of
`ContDiff.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv`, which gives the linear modulus.

When `p < ∞` and `u` is itself in `Lᵖ`, this follows from
`MeasureTheory.MemLp.tendsto_eLpNorm_comp_add_sub` without a derivative assumption. Here `u` need
not belong to `Lᵖ`, and `p = ∞` is allowed: an essentially bounded derivative gives a linear
modulus of translation continuity even though arbitrary `L∞` functions need not translate
continuously. -/
theorem ContDiff.tendsto_eLpNorm_comp_add_sub [SecondCountableTopology E] (hu : ContDiff ℝ 1 u)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hfin : eLpNorm (fderiv ℝ u) p mu ≠ ∞) :
    Filter.Tendsto (fun h : E => eLpNorm (fun x => u (x + h) - u x) p mu) (nhds 0) (nhds 0) :=
  TauCeti.tendsto_nhds_zero_of_le_enorm_mul hfin fun h =>
    hu.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv hp h

/-- **The second-order translation estimate**: the mixed second difference of a `C²` function is
controlled by its second derivative,

`‖u(· + h + k) - u(· + h) - (u(· + k) - u)‖_p ≤ ‖h‖ ‖k‖ ‖D²u‖_p`, `1 ≤ p ≤ ∞`.

As for `ContDiff.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv`, no support, integrability or
boundedness hypothesis is needed. -/
theorem ContDiff.eLpNorm_comp_add_add_sub_sub_le_mul_eLpNorm_fderiv_fderiv
    [SecondCountableTopology E] (hu : ContDiff ℝ 2 u) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (h k : E) :
    eLpNorm (fun x => u (x + h + k) - u (x + h) - (u (x + k) - u x)) p mu ≤
      ‖h‖ₑ * ‖k‖ₑ * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu := by
  -- The mixed difference is the `h`-increment of the `k`-increment `x ↦ u (x + k) - u x`.
  have hdiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hinc : ContDiff ℝ 1 fun x => u (x + k) - u x := by fun_prop
  have hd : fderiv ℝ (fun x => u (x + k) - u x) = fun x => fderiv ℝ u (x + k) - fderiv ℝ u x := by
    ext1 x
    rw [fderiv_fun_sub (by fun_prop) (hdiff x), fderiv_comp_add_right]
  calc eLpNorm (fun x => u (x + h + k) - u (x + h) - (u (x + k) - u x)) p mu
      ≤ ‖h‖ₑ * eLpNorm (fderiv ℝ fun x => u (x + k) - u x) p mu :=
        hinc.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv hp h
    _ ≤ ‖h‖ₑ * (‖k‖ₑ * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu) := by
        rw [hd]
        gcongr
        exact (hu.fderiv_right (m := 1) (by norm_num)).eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv
          hp k
    _ = ‖h‖ₑ * ‖k‖ₑ * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu := (mul_assoc _ _ _).symm

end Translation
