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

* `MeasureTheory.Measure.Mod0MeasureIso` is the structure, `Mod0MeasureIso.measurePreserving`
  reads off the measure-preserving forward map, and `Mod0MeasureIso.trans` composes two of them;
* `MeasureTheory.Measure.embeddingRealMod0MeasureIso` transports a standard-Borel space into `ℝ`
  by `embeddingReal`;
* `MeasureTheory.Measure.mod0MeasureIso_to_unitInterval` turns a mod-zero isomorphism into `ℝ`
  whose image lies in the unit interval into measure-preserving maps in both directions between
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

/-- The composition of two mod-zero isomorphisms is again a mod-zero isomorphism.

It is `@[expose]`d so that the maps of a composite hold by `rfl` downstream. -/
@[expose]
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

/-- Transporting a standard-Borel space into `ℝ` by `embeddingReal` is a mod-zero isomorphism
onto the pushforward of the measure. It is `@[expose]`d so that its forward map, `embeddingReal`,
holds by `rfl` downstream. -/
@[expose]
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

/-- A mod-zero isomorphism into `ℝ` whose image lies in the unit interval gives measure-preserving
maps in both directions between the space and the unit interval, obtained by restricting the
forward map to the unit interval and composing the backward map with the coercion, and the two
maps are mutually inverse almost everywhere. -/
theorem mod0MeasureIso_to_unitInterval
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

end MeasureTheory.Measure
