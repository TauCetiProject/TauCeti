/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import TauCeti.Analysis.Sobolev.GraphStep.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Paths in `W^{1,p}(ℝ, F)` are continuous and vanish at infinity

Let `F` be a real Banach space and `1 ≤ p < ∞`. A path `u` in the first-order weak-derivative
graph over `Lᵖ(ℝ, F)` (the domain of the trajectory operator `d/ds + A(s)`) has a unique
continuous representative, and this representative tends to zero at `±∞`. Every value is
controlled by the `Lᵖ` norms of the path and of its weak derivative on the unit interval to its
right:

`‖u t‖ ≤ ‖u‖_{Lᵖ(t, t + 1)} + ‖u'‖_{Lᵖ(t, t + 1)}`,

so `sup_t ‖u t‖ ≤ ‖u‖_{Lᵖ} + ‖u'‖_{Lᵖ} ≤ √2 ‖u‖_{W^{1,p}}`. Hence `u ↦ u` is a bounded linear
map `W^{1,p}(ℝ, F) →L[ℝ] C₀(ℝ, F)`. Its values satisfy the fundamental theorem of calculus
`∫ r in s..t, u' r = u t - u s`.

The supremum bound is what makes nonlinear superposition operators `ξ ↦ V(γ + ξ)` on Sobolev
paths tractable: a path `ξ` of small `W^{1,p}` norm stays uniformly close to zero, so `γ + ξ`
stays in a fixed neighbourhood of the reference path `γ`, where `V` and its derivatives are
uniformly controlled.

## Proof

On the line, the weak derivative identifies a path, almost everywhere, with a constant plus the
primitive of its weak derivative
(`TauCeti.HasWeakLineDerivOn.exists_ae_eq_add_intervalIntegral_top`), which is continuous. On
`(t, t + 1)` the `W^{1,1}` bound `TauCeti.HasWeakLineDerivOn.norm_le_setAverage_add_integral`
controls the value at `t` by the `L¹` norms of the path and its derivative, and on an interval of
length one the `L¹` norm is at most the `Lᵖ` norm. These local `Lᵖ` norms tend to zero as
`t → ±∞` by dominated convergence, because `p < ∞`.

## Main declarations

* `TauCeti.WeakDerivStep.toZeroAtInfty`: the embedding `W^{1,p}(ℝ, F) →L[ℝ] C₀(ℝ, F)`.
* `TauCeti.WeakDerivStep.prev_ae_eq_toZeroAtInfty`, `TauCeti.WeakDerivStep.toZeroAtInfty_eq_iff`:
  it sends a path to its unique continuous representative.
* `TauCeti.WeakDerivStep.toZeroAtInfty_injective`: the continuous representative determines the
  path.
* `TauCeti.WeakDerivStep.norm_toZeroAtInfty_apply_le_eLpNorm_Ioo`: the local bound on `(t, t + 1)`.
* `TauCeti.WeakDerivStep.norm_toZeroAtInfty_le`,
  `TauCeti.WeakDerivStep.norm_toZeroAtInfty_le_sqrt_two_mul_norm`: the supremum bounds
  `‖u‖_{Lᵖ} + ‖u'‖_{Lᵖ}` and `√2 ‖u‖_{W^{1,p}}`; `TauCeti.WeakDerivStep.opNorm_toZeroAtInfty_le`
  bounds the norm of the embedding by `√2`.
* `TauCeti.WeakDerivStep.integral_weakFDeriv_apply_one_eq_sub`: the fundamental theorem of
  calculus `∫ r in s..t, u' r = u t - u s`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Theorem 8.8 and Corollary 8.9 (`W^{1,p}(ℝ) ⊆ L^∞(ℝ)` with a continuous representative
  vanishing at infinity, for `1 ≤ p < ∞`; stated there for scalar functions).
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology ZeroAtInfty

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The weak derivative of the value -/

/-- On the line, the restricted measure `volume.restrict ⊤` of the graph space is `volume`. -/
private theorem volume_restrict_top :
    (volume : Measure ℝ).restrict ((⊤ : Opens ℝ) : Set ℝ) = volume := by
  rw [Opens.coe_top, Measure.restrict_univ]

/-- Almost-everywhere statements for `volume.restrict ⊤` hold for `volume`. -/
private theorem ae_le_ae_restrict_top :
    ae (volume : Measure ℝ) ≤ ae ((volume : Measure ℝ).restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  ae_mono volume_restrict_top.ge

/-- The value of a path has weak derivative `s ↦ u' s 1` on the whole line. -/
private theorem hasWeakLineDerivOn_prev
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    HasWeakLineDerivOn volume ⊤ ⇑(prev _ u) (fun s ↦ weakFDeriv _ u s 1) 1 := by
  simpa only [ContinuousLinearMap.id_apply] using
    (hasWeakFDerivOn_base_prev _ u).hasWeakLineDerivOn 1

/-- The weak derivative `s ↦ u' s 1` of a path is in `Lᵖ`. -/
private theorem memLp_weakFDeriv_apply_one
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    MemLp (fun s ↦ weakFDeriv _ u s 1) p volume := by
  simpa using ((Lp.memLp (weakFDeriv _ u)).continuousLinearMap_comp
    (ContinuousLinearMap.apply ℝ F (1 : ℝ))).mono_measure volume_restrict_top.ge

/-- The `Lᵖ` norm of `s ↦ u' s 1` is at most that of the weak Fréchet derivative. -/
private theorem eLpNorm_weakFDeriv_apply_one_le
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    eLpNorm (fun s ↦ weakFDeriv _ u s 1) p volume ≤ ‖weakFDeriv _ u‖ₑ := by
  rw [Lp.enorm_def]
  refine (eLpNorm_mono_measure _ volume_restrict_top.ge).trans (eLpNorm_mono
    ((memLp_weakFDeriv_apply_one u).aestronglyMeasurable.mono_measure volume_restrict_top.le)
    fun s ↦ ?_)
  simpa using (weakFDeriv _ u s).le_opNorm 1

/-! ### Local `Lᵖ` norms on unit intervals -/

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- On an interval of length one, the integral of the norm is at most the `Lᵖ` norm. -/
private theorem integral_Ioo_norm_le_eLpNorm {g : ℝ → F} (hg : MemLp g p volume) (t : ℝ) :
    ∫ s in Ioo t (t + 1), ‖g s‖ ≤ (eLpNorm g p (volume.restrict (Ioo t (t + 1)))).toReal := by
  have : IsProbabilityMeasure (volume.restrict (Ioo t (t + 1))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo, add_sub_cancel_left, ENNReal.ofReal_one]⟩
  rw [integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable.restrict,
    ← eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable.restrict]
  exact ENNReal.toReal_mono (hg.restrict _).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le Fact.out)

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- For `p < ∞`, the `Lᵖ` norm of a function on `(t, t + 1)` tends to zero as `t` tends to
infinity in either direction. -/
private theorem tendsto_eLpNorm_restrict_Ioo (hp : p ≠ ∞) {g : ℝ → F} (hg : MemLp g p volume) :
    Tendsto (fun t ↦ eLpNorm g p (volume.restrict (Ioo t (t + 1)))) (cocompact ℝ) (𝓝 0) := by
  have : (cocompact ℝ).IsCountablyGenerated := by
    rw [cocompact_eq_atBot_atTop]
    infer_instance
  -- Every point `x` leaves `(t, t + 1)` once `t ∉ [x - 1, x]`.
  have hout (x : ℝ) : ∀ᶠ t in cocompact ℝ, x ∉ Ioo t (t + 1) :=
    Filter.mem_of_superset (isCompact_Icc (a := x - 1) (b := x)).compl_mem_cocompact
      fun t ht hx ↦ ht ⟨by linarith [hx.2], hx.1.le⟩
  have h := tendsto_eLpNorm_sub_of_ae_tendsto (m := volume) (l := cocompact ℝ) (C := 1)
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
    (f := fun t ↦ (Ioo t (t + 1)).indicator g) (g := 0)
    (Eventually.of_forall fun t ↦ hg.aestronglyMeasurable.indicator measurableSet_Ioo)
    aestronglyMeasurable_zero hg
    (Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ by
      rw [Pi.zero_apply, sub_zero, ENNReal.coe_one, one_mul]
      exact enorm_indicator_le_enorm_self _ x)
    (Eventually.of_forall fun x ↦ tendsto_const_nhds.congr' <|
      (hout x).mono fun t ht ↦ (indicator_of_notMem ht g).symm)
  simpa only [sub_zero,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo.nullMeasurableSet] using h

/-! ### The local bound -/

variable {u : WeakDerivStep volume ⊤ p
  (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))} {v : ℝ → F}

/-- Each value of a continuous representative `v` of a path is bounded by the `Lᵖ` norms of the
path and of its weak derivative on the unit interval to its right. -/
private theorem norm_le_eLpNorm_Ioo_of_ae_eq (hv : Continuous v)
    (hae : ⇑(prev _ u) =ᵐ[volume] v) (t : ℝ) :
    ‖v t‖ ≤ (eLpNorm ⇑(prev _ u) p (volume.restrict (Ioo t (t + 1)))).toReal +
      (eLpNorm (fun s ↦ weakFDeriv _ u s 1) p (volume.restrict (Ioo t (t + 1)))).toReal := by
  have hx : MemLp ⇑(prev _ u) p volume :=
    (Lp.memLp (prev _ u)).mono_measure volume_restrict_top.ge
  have hd := memLp_weakFDeriv_apply_one u
  have hdI : IntegrableOn (fun s ↦ weakFDeriv _ u s 1) (Ioo t (t + 1)) :=
    ((hd.locallyIntegrable Fact.out).integrableOn_isCompact isCompact_Icc).mono_set
      Ioo_subset_Icc_self
  have hb := ((hasWeakLineDerivOn_prev u).mono (Ω' := ⟨Ioo t (t + 1), isOpen_Ioo⟩)
    le_top).norm_le_setAverage_add_integral (lt_add_one t) hdI hv.continuousOn
    (ae_restrict_of_ae hae) (left_mem_Icc.2 (lt_add_one t).le)
  have havg : ⨍ s in Ioo t (t + 1), ‖⇑(prev _ u) s‖ =
      ∫ s in Ioo t (t + 1), ‖⇑(prev _ u) s‖ := by
    simp [setAverage_eq]
  rw [havg] at hb
  exact hb.trans (add_le_add (integral_Ioo_norm_le_eLpNorm hx t)
    (integral_Ioo_norm_le_eLpNorm hd t))

/-- A continuous representative of a path is bounded by `‖u‖_{Lᵖ} + ‖u'‖_{Lᵖ}`. -/
private theorem norm_le_of_ae_eq (hv : Continuous v) (hae : ⇑(prev _ u) =ᵐ[volume] v)
    (t : ℝ) : ‖v t‖ ≤ ‖prev _ u‖ + ‖weakFDeriv _ u‖ := by
  refine (norm_le_eLpNorm_Ioo_of_ae_eq hv hae t).trans (add_le_add ?_ ?_)
  · rw [Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) <|
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
        (eLpNorm_mono_measure _ volume_restrict_top.ge)
  · rw [← toReal_enorm]
    exact ENNReal.toReal_mono enorm_ne_top <|
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
        (eLpNorm_weakFDeriv_apply_one_le u)

/-- A continuous representative of a path tends to zero at infinity. -/
private theorem tendsto_cocompact_of_ae_eq (hp : p ≠ ∞) (hv : Continuous v)
    (hae : ⇑(prev _ u) =ᵐ[volume] v) : Tendsto v (cocompact ℝ) (𝓝 0) := by
  have hx : MemLp ⇑(prev _ u) p volume :=
    (Lp.memLp (prev _ u)).mono_measure volume_restrict_top.ge
  have hd := memLp_weakFDeriv_apply_one u
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun t ↦ norm_nonneg _) (norm_le_eLpNorm_Ioo_of_ae_eq hv hae) ?_
  simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_eLpNorm_restrict_Ioo hp hx)).add
    ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_eLpNorm_restrict_Ioo hp hd))

/-! ### The embedding into `C₀(ℝ, F)` -/

variable (u) in
/-- A path in `W^{1,p}(ℝ, F)`, `p < ∞`, agrees almost everywhere with a continuous function
vanishing at infinity. -/
private theorem exists_zeroAtInftyContinuousMap_ae_eq (hp : p ≠ ∞) :
    ∃ g : C₀(ℝ, F), ⇑(prev _ u) =ᵐ[volume] g := by
  obtain ⟨c, hc⟩ := (hasWeakLineDerivOn_prev u).exists_ae_eq_add_intervalIntegral_top 0
  have hloc := (memLp_weakFDeriv_apply_one u).locallyIntegrable Fact.out
  have hv : Continuous fun t ↦ c + ∫ s in (0 : ℝ)..t, weakFDeriv _ u s 1 :=
    continuous_const.add <| intervalIntegral.continuous_primitive
      (fun a b ↦ (hloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable) 0
  exact ⟨⟨⟨_, hv⟩, tendsto_cocompact_of_ae_eq hp hv hc⟩, hc⟩

private theorem eq_of_prev_ae_eq {g g' : C₀(ℝ, F)} (hg : ⇑(prev _ u) =ᵐ[volume] g)
    (hg' : ⇑(prev _ u) =ᵐ[volume] g') : g = g' :=
  ZeroAtInftyContinuousMap.ext <| congrFun <|
    (Continuous.ae_eq_iff_eq volume g.continuous g'.continuous).mp (hg.symm.trans hg')

/-- The continuous representative, as a linear map. -/
private def toZeroAtInftyₗ (hp : p ≠ ∞) :
    WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
      →ₗ[ℝ] C₀(ℝ, F) where
  toFun u := (exists_zeroAtInftyContinuousMap_ae_eq u hp).choose
  map_add' u w := by
    refine eq_of_prev_ae_eq (u := u + w)
      (exists_zeroAtInftyContinuousMap_ae_eq (u + w) hp).choose_spec ?_
    rw [prev_add, FunLike.coe_add]
    exact ((Lp.coeFn_add (prev _ u) (prev _ w)).filter_mono ae_le_ae_restrict_top).trans
      ((exists_zeroAtInftyContinuousMap_ae_eq u hp).choose_spec.add
      (exists_zeroAtInftyContinuousMap_ae_eq w hp).choose_spec)
  map_smul' c u := by
    refine eq_of_prev_ae_eq (u := c • u)
      (exists_zeroAtInftyContinuousMap_ae_eq (c • u) hp).choose_spec ?_
    rw [prev_smul, FunLike.coe_smul]
    exact ((Lp.coeFn_smul c (prev _ u)).filter_mono ae_le_ae_restrict_top).trans
      ((exists_zeroAtInftyContinuousMap_ae_eq u hp).choose_spec.const_smul c)

private theorem prev_ae_eq_toZeroAtInftyₗ (hp : p ≠ ∞)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ⇑(prev _ u) =ᵐ[volume] toZeroAtInftyₗ hp u :=
  (exists_zeroAtInftyContinuousMap_ae_eq u hp).choose_spec

/-- The sum of the component norms is at most `√2` times the graph norm. -/
private theorem norm_prev_add_norm_weakFDeriv_le :
    ‖prev _ u‖ + ‖weakFDeriv _ u‖ ≤ √2 * ‖u‖ := by
  have hsq := norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq _ u
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, Real.sq_sqrt zero_le_two, hsq]
  nlinarith [sq_nonneg (‖prev _ u‖ - ‖weakFDeriv _ u‖)]

/-- **The Sobolev embedding on the line.** For `1 ≤ p < ∞`, the map sending a path in
`W^{1,p}(ℝ, F)` to its continuous representative is a bounded linear map into the space
`C₀(ℝ, F)` of continuous functions vanishing at infinity, of norm at most `√2`
(`TauCeti.WeakDerivStep.opNorm_toZeroAtInfty_le`). -/
def toZeroAtInfty (hp : p ≠ ∞) :
    WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
      →L[ℝ] C₀(ℝ, F) :=
  (toZeroAtInftyₗ hp).mkContinuous √2 fun u ↦ by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine ((BoundedContinuousFunction.norm_le (by positivity)).2 fun t ↦ ?_).trans
      norm_prev_add_norm_weakFDeriv_le
    exact norm_le_of_ae_eq (toZeroAtInftyₗ hp u).continuous (prev_ae_eq_toZeroAtInftyₗ hp u) t

/-- The embedding sends a path to a representative of its value. -/
theorem prev_ae_eq_toZeroAtInfty (hp : p ≠ ∞)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ⇑(prev _ u) =ᵐ[volume] toZeroAtInfty hp u :=
  prev_ae_eq_toZeroAtInftyₗ hp u

/-- The embedding sends a path to its unique continuous representative vanishing at infinity. -/
theorem toZeroAtInfty_eq_iff (hp : p ≠ ∞)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (g : C₀(ℝ, F)) :
    toZeroAtInfty hp u = g ↔ ⇑(prev _ u) =ᵐ[volume] g :=
  ⟨fun h ↦ h ▸ prev_ae_eq_toZeroAtInfty hp u,
    fun h ↦ eq_of_prev_ae_eq (prev_ae_eq_toZeroAtInfty hp u) h⟩

/-- A continuous function agreeing almost everywhere with a path is the value of its embedding. -/
theorem coe_toZeroAtInfty_eq_of_ae_eq (hp : p ≠ ∞) (hv : Continuous v)
    (hae : ⇑(prev _ u) =ᵐ[volume] v) : ⇑(toZeroAtInfty hp u) = v :=
  (Continuous.ae_eq_iff_eq volume (toZeroAtInfty hp u).continuous hv).mp
    ((prev_ae_eq_toZeroAtInfty hp u).symm.trans hae)

/-- The continuous representative determines the path. -/
theorem toZeroAtInfty_injective (hp : p ≠ ∞) :
    Function.Injective (toZeroAtInfty (F := F) hp) := by
  intro u w huw
  apply ext
  apply Lp.ext
  refine ((prev_ae_eq_toZeroAtInfty hp u).trans ?_).filter_mono (ae_mono volume_restrict_top.le)
  rw [huw]
  exact (prev_ae_eq_toZeroAtInfty hp w).symm

/-- **The local bound.** The value at `t` of the continuous representative of a path is bounded by
the `Lᵖ` norms of the path and of its weak derivative on `(t, t + 1)`. -/
theorem norm_toZeroAtInfty_apply_le_eLpNorm_Ioo (hp : p ≠ ∞)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) (t : ℝ) :
    ‖toZeroAtInfty hp u t‖ ≤ (eLpNorm ⇑(prev _ u) p (volume.restrict (Ioo t (t + 1)))).toReal +
      (eLpNorm (fun s ↦ weakFDeriv _ u s 1) p (volume.restrict (Ioo t (t + 1)))).toReal :=
  norm_le_eLpNorm_Ioo_of_ae_eq (toZeroAtInfty hp u).continuous (prev_ae_eq_toZeroAtInfty hp u) t

/-- **The supremum bound.** The continuous representative of a path is bounded by the sum of the
`Lᵖ` norms of the path and of its weak derivative. -/
theorem norm_toZeroAtInfty_le (hp : p ≠ ∞)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖toZeroAtInfty hp u‖ ≤ ‖prev _ u‖ + ‖weakFDeriv _ u‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le (by positivity)).2 fun t ↦
    norm_le_of_ae_eq (toZeroAtInfty hp u).continuous (prev_ae_eq_toZeroAtInfty hp u) t

/-- The supremum of the continuous representative of a path is at most `√2` times its graph
norm. -/
theorem norm_toZeroAtInfty_le_sqrt_two_mul_norm (hp : p ≠ ∞)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖toZeroAtInfty hp u‖ ≤ √2 * ‖u‖ :=
  (norm_toZeroAtInfty_le hp u).trans norm_prev_add_norm_weakFDeriv_le

/-- The embedding `W^{1,p}(ℝ, F) →L[ℝ] C₀(ℝ, F)` has operator norm at most `√2`. -/
theorem opNorm_toZeroAtInfty_le (hp : p ≠ ∞) : ‖toZeroAtInfty (F := F) hp‖ ≤ √2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_toZeroAtInfty_le_sqrt_two_mul_norm hp)

/-- **The fundamental theorem of calculus.** The integrals of the weak derivative of a path are
the increments of its continuous representative. -/
theorem integral_weakFDeriv_apply_one_eq_sub (hp : p ≠ ∞)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) (s t : ℝ) :
    ∫ r in s..t, weakFDeriv _ u r 1 = toZeroAtInfty hp u t - toZeroAtInfty hp u s := by
  obtain ⟨a, b, hab, hs, ht⟩ : ∃ a b : ℝ, a < b ∧ s ∈ Icc a b ∧ t ∈ Icc a b :=
    ⟨min s t - 1, max s t + 1, by linarith [min_le_max (a := s) (b := t)],
      ⟨by linarith [min_le_left s t], by linarith [le_max_left s t]⟩,
      ⟨by linarith [min_le_right s t], by linarith [le_max_right s t]⟩⟩
  have hdI : IntegrableOn (fun r ↦ weakFDeriv _ u r 1) (Ioo a b) :=
    (((memLp_weakFDeriv_apply_one u).locallyIntegrable Fact.out).integrableOn_isCompact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  exact (((hasWeakLineDerivOn_prev u).mono (Ω' := ⟨Ioo a b, isOpen_Ioo⟩) le_top).integral_eq_sub
    hdI (toZeroAtInfty hp u).continuous.continuousOn
    (ae_restrict_of_ae (prev_ae_eq_toZeroAtInfty hp u)) hs ht)

end TauCeti.WeakDerivStep
