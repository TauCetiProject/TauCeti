/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.LeftRightLim
public import TauCeti.Probability.Quantile

/-!
# Atomless standard-Borel transport to the unit interval

This file proves that an atomless standard-Borel probability space is measure-preservingly
isomorphic modulo null sets to the unit interval with Lebesgue measure. The real-line
construction uses the cumulative distribution function and the generalized inverse already
provided by `MeasureTheory.Measure.quantile`, then transports a standard-Borel space to `ℝ`
by `embeddingReal`.

The CDF/quantile route is adapted from Cameron Freer's independent implementation in
`Graphon/MeasureIso.lean` at commit `9f7be59fa754d260a544b4cfd83d6a5b94f7552e`:
<https://github.com/cameronfreer/graphon/commit/9f7be59fa754d260a544b4cfd83d6a5b94f7552e>.
The graphon-specific packaging was removed. The original work is copyright Cameron Freer
and licensed under Apache 2.0. The underlying measure-preserving equivalence is also the
standard-Borel transport theorem in S. Janson, *Graphons, cut norm and distance, couplings
and rearrangements*, Theorem A.7.

Here `NullSingletonClass μ` is the formal hypothesis. On a standard-Borel space it gives the
atomlessness used by the CDF argument; the class itself only asserts that every singleton is
null. The module exports one theorem, `exists_mpModNull_equiv_unitInterval`; all construction
details are private.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Function
open scoped unitInterval

namespace MeasureTheory.Measure

noncomputable section

/-- **CDF continuity from null singletons.** The cumulative distribution function of a
null-singleton probability measure on `ℝ` is continuous. (A general CDF is only
right-continuous; the left jumps are exactly the singleton masses,
`cdf ν x − leftLim (cdf ν) x = ν {x}`, which vanish.) -/
private theorem continuous_cdf_of_noAtoms (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Continuous (cdf ν) := by
  have hleft : ∀ x, leftLim (cdf ν) x = cdf ν x := by
    intro x
    have hsing : (cdf ν).measure {x} = 0 := by rw [measure_cdf]; exact measure_singleton x
    rw [StieltjesFunction.measure_singleton] at hsing
    have hle : leftLim (cdf ν) x ≤ cdf ν x := (cdf ν).mono.leftLim_le le_rfl
    have hz : cdf ν x - leftLim (cdf ν) x ≤ 0 := ENNReal.ofReal_eq_zero.mp hsing
    exact le_antisymm hle (by linarith)
  rw [continuous_iff_continuousAt]
  intro x
  rw [(cdf ν).mono.continuousAt_iff_leftLim_eq_rightLim, hleft x,
    ((cdf ν).right_continuous x).rightLim_eq]

/-- The `ν`-measure of the sublevel set `{x | cdf ν x ≤ y}` is `y` (for `y < 1`). This is the
analytic heart of the probability integral transform: closedness of the sublevel set (CDF
continuity) plus the boundary value `cdf ν (sSup S) = y` (from the limit `cdf ν → 1`) pin the
set down to `Iic (sSup S)`, whose measure is `cdf ν (sSup S) = y` via `ofReal_cdf`. -/
private lemma cdf_sublevel_measure (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (y : ℝ) (hy1 : y < 1) :
    ν {x | cdf ν x ≤ y} = ENNReal.ofReal y := by
  set S : Set ℝ := {x | cdf ν x ≤ y}
  have hScl : IsClosed S := isClosed_Iic.preimage (continuous_cdf_of_noAtoms ν)
  have hevt : ∀ᶠ x in atTop, y < cdf ν x :=
    (tendsto_cdf_atTop ν).eventually (eventually_gt_nhds hy1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevt
  have hSbdd : BddAbove S := by
    refine ⟨M, fun x hx => ?_⟩
    by_contra hxM
    exact absurd (hM x (le_of_lt (not_le.mp hxM))) (not_lt.2 hx)
  by_cases hSne : S.Nonempty
  · set q := sSup S
    have hq_mem : q ∈ S := hScl.csSup_mem hSne hSbdd
    have hSeq : S = Iic q := by
      ext x
      constructor
      · intro hx; exact le_csSup hSbdd hx
      · intro hx
        exact le_trans ((cdf ν).mono hx) hq_mem
    have hcdfq : cdf ν q = y := by
      refine le_antisymm hq_mem ?_
      have htend : Tendsto (cdf ν) (𝓝[>] q) (𝓝 (cdf ν q)) :=
        ((continuous_cdf_of_noAtoms ν).tendsto q).mono_left nhdsWithin_le_nhds
      have hevt2 : ∀ᶠ x in 𝓝[>] q, y ≤ cdf ν x := by
        refine Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => ?_)
        have : x ∉ S := fun hxS => absurd (le_csSup hSbdd hxS) (not_le.2 hx)
        exact le_of_lt (not_le.mp this)
      exact ge_of_tendsto htend hevt2
    rw [hSeq, ← ofReal_cdf ν q, hcdfq]
  · rw [not_nonempty_iff_eq_empty] at hSne
    have hyle : y ≤ 0 := by
      have hfor : ∀ᶠ x in atBot, y ≤ cdf ν x := by
        refine Filter.Eventually.of_forall (fun x => ?_)
        have : x ∉ S := by rw [hSne]; simp
        exact le_of_lt (not_le.mp this)
      exact ge_of_tendsto (tendsto_cdf_atBot ν) hfor
    have hνS : ν S = 0 := by rw [hSne]; exact measure_empty
    rw [ENNReal.ofReal_eq_zero.mpr hyle]
    exact hνS

/-- **The probability integral transform.** For an atomless probability measure
`ν` on `ℝ`, its CDF pushes `ν` forward to Lebesgue measure on the unit interval:
`(cdf ν)_* ν = volume.restrict (Icc 0 1)`.

Proof: by `ext_of_Iic` it suffices to match `(cdf ν)_* ν (Iic y)` with `volume.restrict (Icc 0 1)
(Iic y)` for every `y`. The former is `ν {x | cdf ν x ≤ y}`; the latter is `volume (Iic y ∩ Icc 0
1)`. For `y < 1` both equal `ENNReal.ofReal y` (`cdf_sublevel_measure`, and `Iic y ∩ Icc 0 1 =
Icc 0 y`); for `y ≥ 1` both equal `1` (the sublevel set is `univ` since `cdf ≤ 1 ≤ y`, and
`Iic y ∩ Icc 0 1 = Icc 0 1`). -/
private theorem cdf_map_eq_volume_restrict (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] :
    Measure.map (cdf ν) ν = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hmeas : Measurable (cdf ν) := (cdf ν).mono.measurable
  refine Measure.ext_of_Iic _ _ (fun y => ?_)
  rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge y 1 with hy1 | hy1
  · -- `y < 1`: sublevel measure is `y`, and `Iic y ∩ Icc 0 1 = Icc 0 y` has volume `y`.
    have hrset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 y := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨hxy, hx0, _⟩; exact ⟨hx0, hxy⟩
      · rintro ⟨hx0, hxy⟩; exact ⟨hxy, hx0, le_of_lt (lt_of_le_of_lt hxy hy1)⟩
    rw [hrset, Real.volume_Icc, sub_zero]
    exact cdf_sublevel_measure ν y hy1
  · -- `y ≥ 1`: sublevel set is `univ` (`cdf ≤ 1 ≤ y`), and `Iic y ∩ Icc 0 1 = Icc 0 1`.
    have hset : cdf ν ⁻¹' Iic y = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact le_trans (cdf_le_one ν x) hy1
    have hrset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, and_iff_right_iff_imp]
      rintro ⟨_, hx1⟩; exact le_trans hx1 hy1
    rw [hset, hrset, measure_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]


/-! ### The atomless real-line isomorphism

The existing `Measure.quantile` in `TauCeti.Probability.Quantile` is the generalized inverse
used here. The following two lemmas add the atomless-specific facts needed on the closed
unit interval: the CDF transports the law to Lebesgue measure, and the quantile is its
inverse modulo the null endpoints. -/

private theorem map_quantile_volume_Icc (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measure.map ν.quantile (volume.restrict (Set.Icc (0 : ℝ) 1)) = ν := by
  simpa only [MeasureTheory.restrict_Ioo_eq_restrict_Icc] using
    (map_quantile_volume_Ioo ν)

private theorem cdf_quantile_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    (fun u => cdf ν (ν.quantile u)) =ᵐ[volume.restrict (Set.Icc 0 1)] id := by
  refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [Set.Countable.ae_notMem
      ((Set.countable_singleton (1 : ℝ)).insert 0) volume] with u hu huIcc
  have hu0 : u ≠ 0 := fun h => hu (by simp [h])
  have hu1 : u ≠ 1 := fun h => hu (by simp [h])
  have h0 : 0 < u := lt_of_le_of_ne huIcc.1 (Ne.symm hu0)
  have h1 : u < 1 := lt_of_le_of_ne huIcc.2 hu1
  have hlower : u ≤ cdf ν (ν.quantile u) := le_cdf_quantile ν h1
  have hupper : cdf ν (ν.quantile u) ≤ u := by
    have htend : Tendsto (cdf ν) (𝓝[<] (ν.quantile u))
        (𝓝 (cdf ν (ν.quantile u))) :=
      ((continuous_cdf_of_noAtoms ν).tendsto _).mono_left nhdsWithin_le_nhds
    have hevt : ∀ᶠ x in 𝓝[<] (ν.quantile u), cdf ν x ≤ u := by
      refine eventually_of_mem self_mem_nhdsWithin (fun x hx => ?_)
      have hxlt : x < ν.quantile u := hx
      have hqnot : ¬ ν.quantile u ≤ x := not_le_of_gt hxlt
      have hnot : ¬ u ≤ cdf ν x := by
        intro hcdf
        exact hqnot ((quantile_le_iff ν h0 h1).mpr hcdf)
      exact le_of_lt (not_le.mp hnot)
    exact le_of_tendsto htend hevt
  exact le_antisymm hupper hlower

private theorem quantile_cdf_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    (fun x => ν.quantile (cdf ν x)) =ᵐ[ν] id := by
  have hq : Measurable ν.quantile := measurable_quantile ν
  have hcdf : Measurable (cdf ν) := (cdf ν).mono.measurable
  have hpos : ∀ᵐ x ∂ν, 0 < cdf ν x := by
    have h0 : ν {x | cdf ν x ≤ 0} = 0 := by
      have h := cdf_sublevel_measure ν 0 (by norm_num)
      simpa using h
    rw [ae_iff]
    simp only [not_lt]
    exact h0
  have hle : ∀ᵐ x ∂ν, ν.quantile (cdf ν x) ≤ x := by
    filter_upwards [hpos] with x hx
    rw [quantile_def]
    exact csInf_le (bddBelow_setOf_le_cdf ν hx) (le_refl (cdf ν x))
  have hmap : Measure.map (fun x => ν.quantile (cdf ν x)) ν = ν := by
    have hcomp : (fun x => ν.quantile (cdf ν x)) = ν.quantile ∘ cdf ν := rfl
    rw [hcomp, ← Measure.map_map hq hcdf, cdf_map_eq_volume_restrict ν,
      map_quantile_volume_Icc ν]
  have habs : ∀ y : ℝ, ‖Real.arctan y‖ ≤ Real.pi / 2 := fun y => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan y),
      le_of_lt (Real.arctan_lt_pi_div_two y)⟩
  have hIg : Integrable (fun x => Real.arctan (ν.quantile (cdf ν x))) ν :=
    Integrable.of_bound
      ((Real.continuous_arctan.measurable.comp (hq.comp hcdf)).aestronglyMeasurable)
      (Real.pi / 2) (Filter.Eventually.of_forall (fun x => habs _))
  have hIid : Integrable (fun x => Real.arctan x) ν :=
    Integrable.of_bound Real.continuous_arctan.aestronglyMeasurable (Real.pi / 2)
      (Filter.Eventually.of_forall (fun x => habs x))
  have hInt : ∫ x, Real.arctan (ν.quantile (cdf ν x)) ∂ν = ∫ x, Real.arctan x ∂ν := by
    have hm := integral_map (μ := ν) (φ := fun x => ν.quantile (cdf ν x))
      (f := Real.arctan) (hq.comp hcdf).aemeasurable
      Real.continuous_arctan.aestronglyMeasurable
    rw [hmap] at hm
    rw [← hm]
  have hmono : ∀ᵐ x ∂ν, Real.arctan (ν.quantile (cdf ν x)) ≤ Real.arctan x := by
    filter_upwards [hle] with x hx
    exact Real.arctan_strictMono.monotone hx
  have hnonneg : 0 ≤ᵐ[ν] (fun x => Real.arctan x - Real.arctan (ν.quantile (cdf ν x))) := by
    filter_upwards [hmono] with x hx
    simp only [Pi.zero_apply]
    linarith
  have hzero : ∫ x, (Real.arctan x - Real.arctan (ν.quantile (cdf ν x))) ∂ν = 0 := by
    rw [integral_sub hIid hIg, hInt, sub_self]
  have hvanish := (integral_eq_zero_iff_of_nonneg_ae hnonneg (hIid.sub hIg)).mp hzero
  filter_upwards [hvanish] with x hx
  have heq : Real.arctan (ν.quantile (cdf ν x)) = Real.arctan x := by
    simp only [Pi.zero_apply] at hx
    linarith
  exact Real.arctan_injective heq



private structure Mod0MeasureIso (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) where
  toFun : α → β
  invFun : β → α
  measurable_toFun : Measurable toFun
  measurable_invFun : Measurable invFun
  map_toFun : Measure.map toFun μ = ν
  map_invFun : Measure.map invFun ν = μ
  left_inv_ae : (fun x => invFun (toFun x)) =ᵐ[μ] id
  right_inv_ae : (fun y => toFun (invFun y)) =ᵐ[ν] id

private def Mod0MeasureIso.trans {α β γ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    (e : Mod0MeasureIso α β μ ν) (f : Mod0MeasureIso β γ ν ξ) :
    Mod0MeasureIso α γ μ ξ where
  toFun := f.toFun ∘ e.toFun
  invFun := e.invFun ∘ f.invFun
  measurable_toFun := f.measurable_toFun.comp e.measurable_toFun
  measurable_invFun := e.measurable_invFun.comp f.measurable_invFun
  map_toFun := by
    rw [← Measure.map_map f.measurable_toFun e.measurable_toFun, e.map_toFun, f.map_toFun]
  map_invFun := by
    rw [← Measure.map_map e.measurable_invFun f.measurable_invFun, f.map_invFun, e.map_invFun]
  left_inv_ae := by
    have hqmp : Measure.QuasiMeasurePreserving e.toFun μ ν := by
      refine ⟨e.measurable_toFun, ?_⟩
      rw [e.map_toFun]
    have h1 := hqmp.ae_eq_comp f.left_inv_ae
    filter_upwards [h1, e.left_inv_ae] with x hx1 hx2
    simp only [Function.comp_apply, id_eq] at hx1 hx2 ⊢
    rw [hx1]
    exact hx2
  right_inv_ae := by
    have hqmp : Measure.QuasiMeasurePreserving f.invFun ξ ν := by
      refine ⟨f.measurable_invFun, ?_⟩
      rw [f.map_invFun]
    have h2 := hqmp.ae_eq_comp e.right_inv_ae
    filter_upwards [h2, f.right_inv_ae] with y hy1 hy2
    simp only [Function.comp_apply, id_eq] at hy1 hy2 ⊢
    rw [hy1]
    exact hy2

private noncomputable def realMod0MeasureIso (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Mod0MeasureIso ℝ ℝ ν (volume.restrict (Set.Icc 0 1)) where
  toFun := cdf ν
  invFun := ν.quantile
  measurable_toFun := (cdf ν).mono.measurable
  measurable_invFun := measurable_quantile ν
  map_toFun := cdf_map_eq_volume_restrict ν
  map_invFun := map_quantile_volume_Icc ν
  left_inv_ae := quantile_cdf_ae ν
  right_inv_ae := cdf_quantile_ae ν

private lemma noAtoms_map_of_injective {α β} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [NullSingletonClass μ] {f : α → β} (hf : MeasurableEmbedding f) :
    NullSingletonClass (Measure.map f μ) := by
  refine ⟨fun y => ?_⟩
  rw [hf.map_apply]
  have hsub : (f ⁻¹' {y}).Subsingleton := by
    intro a ha b hb
    simp only [mem_preimage, mem_singleton_iff] at ha hb
    exact hf.injective (ha.trans hb.symm)
  exact hsub.measure_zero μ

private noncomputable def embeddingRealMod0MeasureIso (α) [MeasurableSpace α]
    [StandardBorelSpace α] (μ : Measure α) [IsProbabilityMeasure μ] [Nonempty α] :
    Mod0MeasureIso α ℝ μ (Measure.map (embeddingReal α) μ) :=
  let he := measurableEmbedding_embeddingReal α
  { toFun := embeddingReal α
    invFun := he.invFun
    measurable_toFun := he.measurable
    measurable_invFun := he.measurable_invFun
    map_toFun := rfl
    map_invFun := by
      rw [Measure.map_map he.measurable_invFun he.measurable]
      have h : he.invFun ∘ embeddingReal α = id := funext he.leftInverse_invFun
      rw [h, Measure.map_id]
    left_inv_ae := ae_of_all _ he.leftInverse_invFun
    right_inv_ae := by
      have hrange : Measure.map (embeddingReal α) μ (range (embeddingReal α))ᶜ = 0 := by
        have h1 : Measure.map (embeddingReal α) μ (range (embeddingReal α)) = 1 := by
          rw [he.map_apply, preimage_range, measure_univ]
        rw [measure_compl he.measurableSet_range (measure_ne_top _ _), h1, measure_univ,
          tsub_self]
      have hmem : ∀ᵐ y ∂(Measure.map (embeddingReal α) μ), y ∈ range (embeddingReal α) := by
        rw [ae_iff]
        exact hrange
      filter_upwards [hmem] with y hy
      obtain ⟨x, rfl⟩ := hy
      simp only [id_eq]
      rw [he.leftInverse_invFun x] }

private noncomputable def atomless_standardBorel_mod0MeasureIso (α) [MeasurableSpace α]
    [StandardBorelSpace α] (μ : Measure α) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    Mod0MeasureIso α ℝ μ (volume.restrict (Set.Icc 0 1)) := by
  have hne : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hprob : IsProbabilityMeasure (Measure.map (embeddingReal α) μ) := inferInstance
  have hnull : NullSingletonClass (Measure.map (embeddingReal α) μ) :=
    noAtoms_map_of_injective (measurableEmbedding_embeddingReal α)
  exact (@embeddingRealMod0MeasureIso α _ _ μ inferInstance hne).trans
    (@realMod0MeasureIso (Measure.map (embeddingReal α) μ) hprob hnull)

private theorem atomless_standardBorel_toFun_mem (α) [MeasurableSpace α]
    [StandardBorelSpace α] (μ : Measure α) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (x : α) : (atomless_standardBorel_mod0MeasureIso α μ).toFun x ∈ I := by
  -- The composed construction sends `x` to the CDF of its real-line embedding.
  change cdf (Measure.map (embeddingReal α) μ) (embeddingReal α x) ∈ I
  exact ⟨ProbabilityTheory.cdf_nonneg _ _, ProbabilityTheory.cdf_le_one _ _⟩

private lemma mod0MeasureIso_to_unitInterval
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (e : Mod0MeasureIso α ℝ μ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hp : ∀ x, e.toFun x ∈ I) :
    ∃ (f : α → I) (g : I → α),
      MeasurePreserving f μ volume ∧ MeasurePreserving g volume μ ∧
      (∀ᵐ x ∂μ, g (f x) = x) ∧ (∀ᵐ y ∂(volume : Measure I), f (g y) = y) := by
  let f : α → I := fun x => (⟨e.toFun x, hp x⟩ : (I : Set ℝ))
  let g : I → α := fun y => e.invFun y.1
  have hfmeas : Measurable f := by
    dsimp [f]
    exact @Measurable.subtype_mk α ℝ _ _ _ e.toFun e.measurable_toFun hp
  have hgmeas : Measurable g := by
    dsimp [g]
    exact e.measurable_invFun.comp measurable_subtype_coe
  have hgf : (g ∘ f) =ᵐ[μ] id := by
    simpa [f, g, Function.comp_def] using e.left_inv_ae
  have hval : (fun y : I => e.toFun (e.invFun (y : ℝ))) =ᵐ[(volume : Measure I)]
      (fun y : I => (y : ℝ)) := by
    simpa [Function.comp_def] using
      (unitInterval.measurePreserving_coe.quasiMeasurePreserving.ae_eq_comp e.right_inv_ae)
  have hfg : (f ∘ g) =ᵐ[(volume : Measure I)] id := by
    filter_upwards [hval] with y hy
    apply Subtype.ext
    exact hy
  have hmapf : Measure.map f μ = volume := by
    apply Measure.ext
    intro t ht
    have hvalt : MeasurableSet ((Subtype.val : I → ℝ) '' t) :=
      unitInterval.measurableEmbedding_coe.measurableSet_image' ht
    rw [Measure.map_apply hfmeas ht]
    rw [unitInterval.volume_def, comap_subtype_coe_apply measurableSet_Icc volume t]
    calc
      μ (f ⁻¹' t) = μ (e.toFun ⁻¹' ((Subtype.val : I → ℝ) '' t)) := by
        congr 1
        apply Set.ext
        intro x
        -- The subtype constructor is definitionally the inverse of `Subtype.val`.
        change (⟨e.toFun x, hp x⟩ : (I : Set ℝ)) ∈ t ↔
          e.toFun x ∈ ((Subtype.val : I → ℝ) '' t)
        constructor
        · intro hx
          exact ⟨⟨e.toFun x, hp x⟩, hx, rfl⟩
        · rintro ⟨y, hy, hvaly⟩
          have hy' : y = (⟨e.toFun x, hp x⟩ : (I : Set ℝ)) := Subtype.ext hvaly
          simpa [hy'] using hy
      _ = Measure.map e.toFun μ ((Subtype.val : I → ℝ) '' t) :=
        (Measure.map_apply e.measurable_toFun hvalt).symm
      _ = (volume.restrict (I : Set ℝ)) ((Subtype.val : I → ℝ) '' t) := by
        rw [e.map_toFun]
      _ = volume ((Subtype.val : I → ℝ) '' t) := by
        rw [Measure.restrict_apply hvalt]
        congr 1
        apply Set.Subset.antisymm
        · exact Set.inter_subset_left
        · intro z hz
          rcases (Set.mem_image _ _ _).mp hz with ⟨y, hy, rfl⟩
          exact ⟨hz, y.2⟩
  have hmapg : Measure.map g volume = μ := by
    apply Measure.ext
    intro t ht
    have hqt : MeasurableSet (e.invFun ⁻¹' t) := e.measurable_invFun ht
    have hqI : Measurable g := hgmeas
    rw [Measure.map_apply hqI ht]
    have hpre : g ⁻¹' t = (Subtype.val : I → ℝ) ⁻¹' (e.invFun ⁻¹' t) := by
      ext y
      simp [g]
    rw [hpre, unitInterval.measurePreserving_coe.measure_preimage
      (hqt.nullMeasurableSet : NullMeasurableSet (e.invFun ⁻¹' t)
        (volume.restrict (I : Set ℝ)))]
    rw [← Measure.map_apply e.measurable_invFun ht, e.map_invFun]
  exact ⟨f, g, ⟨hfmeas, hmapf⟩, ⟨hgmeas, hmapg⟩, hgf, hfg⟩

end

public section

/-- A measure-preserving map in each direction between an atomless standard-Borel
probability space and the unit interval, with the two maps mutually inverse almost everywhere. -/
theorem exists_mpModNull_equiv_unitInterval
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∃ (f : Ω → I) (g : I → Ω),
      MeasurePreserving f μ (volume : Measure I) ∧
      MeasurePreserving g (volume : Measure I) μ ∧
      (∀ᵐ x ∂μ, g (f x) = x) ∧
      (∀ᵐ y ∂(volume : Measure I), f (g y) = y) := by
  let e := atomless_standardBorel_mod0MeasureIso Ω μ
  apply mod0MeasureIso_to_unitInterval e
  intro x
  simpa [e] using atomless_standardBorel_toFun_mem Ω μ x

end
end MeasureTheory.Measure
