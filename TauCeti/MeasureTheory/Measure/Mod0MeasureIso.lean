/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Measure-preserving isomorphisms modulo null sets

`Mod0MeasureIso` bundles two measurable maps between measured spaces which push the two measures
forward onto one another and which are mutually inverse outside a null set. It is the
modulo-null-set counterpart of `MeasurePreserving`, for the situation in which two spaces carry
the same law only up to null sets, as happens when standard transport constructions are composed.

The packaging is adapted from Cameron Freer's independent implementation in
`Graphon/MeasureIso.lean` at commit `9f7be59fa754d260a544b4cfd83d6a5b94f7552e`:
<https://github.com/cameronfreer/graphon/commit/9f7be59fa754d260a544b4cfd83d6a5b94f7552e>.
The original work is copyright Cameron Freer and licensed under Apache 2.0.

## Main results

* `MeasureTheory.Measure.Mod0MeasureIso` is the structure;
  `Mod0MeasureIso.measurePreserving` and `Mod0MeasureIso.measurePreserving_invFun` read off the
  two measure-preserving maps, `Mod0MeasureIso.symm` inverts an isomorphism, and
  `Mod0MeasureIso.trans` composes two of them;
* `MeasureTheory.Measure.embeddingRealMod0MeasureIso` transports a standard-Borel space into `ℝ`
  by `embeddingReal`;
* `MeasureTheory.Measure.mod0MeasureIso_to_unitInterval` turns a mod-zero isomorphism into `ℝ`
  carrying the unit interval measure into measure-preserving maps in both directions between
  that space and the unit interval.

The instance built from the cumulative distribution function and the quantile of an atomless
real law is `MeasureTheory.Measure.realMod0MeasureIso`, in `TauCeti.Probability.Quantile`.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped unitInterval

namespace MeasureTheory.Measure

/-- Two measurable maps that push `μ` and `ν` forward onto one another and that are mutually
inverse outside a null set: a measure-preserving isomorphism of the two measured spaces modulo
null sets. -/
structure Mod0MeasureIso (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) where
  /-- The forward map, which pushes `μ` forward to `ν`. -/
  toFun : α → β
  /-- The backward map, which pushes `ν` forward to `μ`. -/
  invFun : β → α
  measurable_toFun : Measurable toFun
  measurable_invFun : Measurable invFun
  map_toFun : Measure.map toFun μ = ν
  map_invFun : Measure.map invFun ν = μ
  left_inv_ae : (fun x => invFun (toFun x)) =ᵐ[μ] id
  right_inv_ae : (fun y => toFun (invFun y)) =ᵐ[ν] id

/-- The forward map of a mod-zero isomorphism preserves the measure. -/
theorem Mod0MeasureIso.measurePreserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : Mod0MeasureIso α β μ ν) :
    MeasurePreserving e.toFun μ ν :=
  ⟨e.measurable_toFun, e.map_toFun⟩

/-- The backward map of a mod-zero isomorphism preserves the measure. -/
theorem Mod0MeasureIso.measurePreserving_invFun {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} (e : Mod0MeasureIso α β μ ν) :
    MeasurePreserving e.invFun ν μ :=
  ⟨e.measurable_invFun, e.map_invFun⟩

/-- The inverse of a mod-zero isomorphism is a mod-zero isomorphism between the reversed spaces,
with the two maps interchanged. -/
def Mod0MeasureIso.symm {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : Mod0MeasureIso α β μ ν) : Mod0MeasureIso β α ν μ where
  toFun := e.invFun
  invFun := e.toFun
  measurable_toFun := e.measurable_invFun
  measurable_invFun := e.measurable_toFun
  map_toFun := e.map_invFun
  map_invFun := e.map_toFun
  left_inv_ae := e.right_inv_ae
  right_inv_ae := e.left_inv_ae

@[simp]
theorem Mod0MeasureIso.symm_toFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : Mod0MeasureIso α β μ ν) :
    e.symm.toFun = e.invFun :=
  (rfl)

@[simp]
theorem Mod0MeasureIso.symm_invFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : Mod0MeasureIso α β μ ν) :
    e.symm.invFun = e.toFun :=
  (rfl)

/-- The composition of two mod-zero isomorphisms is again a mod-zero isomorphism. -/
def Mod0MeasureIso.trans {α β γ} [MeasurableSpace α] [MeasurableSpace β]
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

@[simp]
theorem Mod0MeasureIso.trans_toFun {α β γ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    (e : Mod0MeasureIso α β μ ν) (f : Mod0MeasureIso β γ ν ξ) :
    (e.trans f).toFun = f.toFun ∘ e.toFun :=
  (rfl)

@[simp]
theorem Mod0MeasureIso.trans_invFun {α β γ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    (e : Mod0MeasureIso α β μ ν) (f : Mod0MeasureIso β γ ν ξ) :
    (e.trans f).invFun = e.invFun ∘ f.invFun :=
  (rfl)

/-- Transporting a standard-Borel space into `ℝ` by `embeddingReal` is a mod-zero isomorphism
onto the pushforward of the measure. -/
def embeddingRealMod0MeasureIso (α) [MeasurableSpace α] [StandardBorelSpace α] (μ : Measure α)
    [Nonempty α] : Mod0MeasureIso α ℝ μ (Measure.map (embeddingReal α) μ) :=
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
      have hmem : ∀ᵐ y ∂(Measure.map (embeddingReal α) μ), y ∈ range (embeddingReal α) :=
        ae_map_mem_range he.measurableSet_range he.measurable.aemeasurable
      filter_upwards [hmem] with y hy
      obtain ⟨x, rfl⟩ := hy
      simp only [id_eq]
      rw [he.leftInverse_invFun x] }

@[simp]
theorem embeddingRealMod0MeasureIso_toFun (α) [MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [Nonempty α] :
    (embeddingRealMod0MeasureIso α μ).toFun = embeddingReal α :=
  (rfl)

@[simp]
theorem embeddingRealMod0MeasureIso_invFun (α) [MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [Nonempty α] :
    (embeddingRealMod0MeasureIso α μ).invFun = (measurableEmbedding_embeddingReal α).invFun :=
  (rfl)

/-- A mod-zero isomorphism into `ℝ` carrying the unit interval measure gives measure-preserving
maps in both directions between the space and the unit interval: the forward map clipped to the
unit interval, and the backward map composed with the coercion. Since the forward map takes
values in the unit interval outside a null set, the two maps are mutually inverse almost
everywhere. -/
theorem mod0MeasureIso_to_unitInterval
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (e : Mod0MeasureIso α ℝ μ (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∃ (f : α → I) (g : I → α),
      MeasurePreserving f μ volume ∧ MeasurePreserving g volume μ ∧
      (∀ᵐ x ∂μ, g (f x) = x) ∧ (∀ᵐ y ∂(volume : Measure I), f (g y) = y) := by
  have hempty : (I : Set ℝ)ᶜ ∩ Set.Icc (0 : ℝ) 1 = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Icc]
    grind
  have hnull : (volume.restrict (Set.Icc (0 : ℝ) 1)) (I : Set ℝ)ᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Icc.compl, hempty, measure_empty]
  have hmem : ∀ᵐ x ∂μ, e.toFun x ∈ I := by
    have hpre : {x | e.toFun x ∉ I} = e.toFun ⁻¹' (I : Set ℝ)ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff]
    rw [ae_iff, hpre]
    exact e.measurePreserving.preimage_null hnull
  have hclip : ∀ x : α, max (0 : ℝ) (min 1 (e.toFun x)) ∈ I := by
    intro x
    exact ⟨by grind, by grind⟩
  let f : α → I := fun x => ⟨max (0 : ℝ) (min 1 (e.toFun x)), hclip x⟩
  let g : I → α := fun y => e.invFun y.1
  have hfmeas : Measurable f := by
    dsimp [f]
    exact Measurable.subtype_mk
      (measurable_const.max (measurable_const.min e.measurable_toFun)) (h := hclip)
  have hgmeas : Measurable g := by
    dsimp [g]
    exact e.measurable_invFun.comp measurable_subtype_coe
  have hclip_id : ∀ᵐ x ∂μ, max (0 : ℝ) (min 1 (e.toFun x)) = e.toFun x := by
    filter_upwards [hmem] with x hx
    grind
  have hgf : (g ∘ f) =ᵐ[μ] id := by
    filter_upwards [hclip_id, e.left_inv_ae] with x hx hx'
    simp [f, g, hx, hx']
  have hval : (fun y : I => e.toFun (e.invFun (y : ℝ))) =ᵐ[(volume : Measure I)]
      (fun y : I => (y : ℝ)) := by
    simpa [Function.comp_def] using
      (unitInterval.measurePreserving_coe.quasiMeasurePreserving.ae_eq_comp e.right_inv_ae)
  have hfg : (f ∘ g) =ᵐ[(volume : Measure I)] id := by
    filter_upwards [hval] with y hy
    apply Subtype.ext
    simp only [Function.comp_apply, f, g, id_eq]
    rw [hy]
    grind [y.2.1, y.2.2]
  have hmapf : Measure.map f μ = volume := by
    apply unitInterval.measurableEmbedding_coe.map_injective
    have hcomp : (Subtype.val : I → ℝ) ∘ f =ᵐ[μ] e.toFun := hclip_id
    rw [Measure.map_map unitInterval.measurePreserving_coe.measurable hfmeas,
      Measure.map_congr hcomp, unitInterval.measurePreserving_coe.map_eq]
    exact e.map_toFun
  have hmapg : Measure.map g volume = μ := by
    have hcomp : g = e.invFun ∘ (Subtype.val : I → ℝ) := by
      funext y
      rfl
    rw [hcomp, ← Measure.map_map e.measurable_invFun measurable_subtype_coe,
      unitInterval.measurePreserving_coe.map_eq, e.map_invFun]
  exact ⟨f, g, ⟨hfmeas, hmapf⟩, ⟨hgmeas, hmapg⟩, hgf, hfg⟩

end MeasureTheory.Measure
