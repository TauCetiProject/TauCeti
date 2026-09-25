/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import TauCeti.MeasureTheory.Measure.Atom
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

/-! ### The atomless real-line isomorphism

The CDF/quantile transport and inverse identities are supplied by
`TauCeti.Probability.Quantile`. The private construction below composes them with the
standard-Borel embedding into `ℝ`. -/

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
  map_invFun := by
    simpa only [MeasureTheory.restrict_Ioo_eq_restrict_Icc] using
      (map_quantile_volume_Ioo ν)
  left_inv_ae := quantile_cdf_ae ν
  right_inv_ae := cdf_quantile_ae ν

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
  have htoFun :
      (atomless_standardBorel_mod0MeasureIso α μ).toFun x =
        cdf (Measure.map (embeddingReal α) μ) (embeddingReal α x) := rfl
  rw [htoFun]
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
    apply unitInterval.measurableEmbedding_coe.map_injective
    have hcomp : (Subtype.val : I → ℝ) ∘ f = e.toFun := by
      funext x
      rfl
    rw [Measure.map_map unitInterval.measurePreserving_coe.measurable hfmeas, hcomp]
    rw [unitInterval.measurePreserving_coe.map_eq]
    exact e.map_toFun
  have hmapg : Measure.map g volume = μ := by
    have hcomp : g = e.invFun ∘ (Subtype.val : I → ℝ) := by
      funext y
      rfl
    rw [hcomp, ← Measure.map_map e.measurable_invFun measurable_subtype_coe,
      unitInterval.measurePreserving_coe.map_eq, e.map_invFun]
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
