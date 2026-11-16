/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

* `TauCeti.Mod0MeasureIso` is the structure; `TauCeti.Mod0MeasureIso.measurePreserving` and
  `TauCeti.Mod0MeasureIso.measurePreserving_invFun` read off the two measure-preserving maps,
  `TauCeti.Mod0MeasureIso.symm` inverts an isomorphism, and `TauCeti.Mod0MeasureIso.trans`
  composes two of them;
* `MeasurableEmbedding.mod0MeasureIso` makes a measurable embedding of a nonempty space that
  pushes `μ` forward to `ν` into a mod-zero isomorphism, with `MeasurableEmbedding.invFun` as
  the backward map;
* `TauCeti.Mod0MeasureIso.exists_measurePreserving_unitInterval` turns a mod-zero isomorphism
  into `ℝ` carrying the unit interval measure into measure-preserving maps in both directions
  between that space and the unit interval.

The instance built from the cumulative distribution function and the quantile of an atomless
real law is `MeasureTheory.Measure.realMod0MeasureIso`, in `TauCeti.Probability.Quantile`.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped unitInterval

namespace TauCeti

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

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {ν : Measure β} {ξ : Measure γ}

/-- The forward map of a mod-zero isomorphism preserves the measure. -/
theorem Mod0MeasureIso.measurePreserving (e : Mod0MeasureIso α β μ ν) :
    MeasurePreserving e.toFun μ ν :=
  ⟨e.measurable_toFun, e.map_toFun⟩

/-- The backward map of a mod-zero isomorphism preserves the measure. -/
theorem Mod0MeasureIso.measurePreserving_invFun (e : Mod0MeasureIso α β μ ν) :
    MeasurePreserving e.invFun ν μ :=
  ⟨e.measurable_invFun, e.map_invFun⟩

/-- The inverse of a mod-zero isomorphism is a mod-zero isomorphism between the reversed spaces,
with the two maps interchanged. -/
def Mod0MeasureIso.symm (e : Mod0MeasureIso α β μ ν) : Mod0MeasureIso β α ν μ where
  toFun := e.invFun
  invFun := e.toFun
  measurable_toFun := e.measurable_invFun
  measurable_invFun := e.measurable_toFun
  map_toFun := e.map_invFun
  map_invFun := e.map_toFun
  left_inv_ae := e.right_inv_ae
  right_inv_ae := e.left_inv_ae

@[simp]
theorem Mod0MeasureIso.symm_toFun (e : Mod0MeasureIso α β μ ν) : e.symm.toFun = e.invFun :=
  (rfl)

@[simp]
theorem Mod0MeasureIso.symm_invFun (e : Mod0MeasureIso α β μ ν) : e.symm.invFun = e.toFun :=
  (rfl)

/-- The composition of two mod-zero isomorphisms is again a mod-zero isomorphism. -/
def Mod0MeasureIso.trans (e : Mod0MeasureIso α β μ ν) (f : Mod0MeasureIso β γ ν ξ) :
    Mod0MeasureIso α γ μ ξ where
  toFun := f.toFun ∘ e.toFun
  invFun := e.invFun ∘ f.invFun
  measurable_toFun := f.measurable_toFun.comp e.measurable_toFun
  measurable_invFun := e.measurable_invFun.comp f.measurable_invFun
  map_toFun := (f.measurePreserving.comp e.measurePreserving).map_eq
  map_invFun := (e.measurePreserving_invFun.comp f.measurePreserving_invFun).map_eq
  left_inv_ae := by
    filter_upwards [e.measurePreserving.quasiMeasurePreserving.ae_eq_comp f.left_inv_ae,
      e.left_inv_ae] with x hx hx'
    simp_all
  right_inv_ae := by
    filter_upwards [f.measurePreserving_invFun.quasiMeasurePreserving.ae_eq_comp e.right_inv_ae,
      f.right_inv_ae] with y hy hy'
    simp_all

@[simp]
theorem Mod0MeasureIso.trans_toFun (e : Mod0MeasureIso α β μ ν) (f : Mod0MeasureIso β γ ν ξ) :
    (e.trans f).toFun = f.toFun ∘ e.toFun :=
  (rfl)

@[simp]
theorem Mod0MeasureIso.trans_invFun (e : Mod0MeasureIso α β μ ν) (f : Mod0MeasureIso β γ ν ξ) :
    (e.trans f).invFun = e.invFun ∘ f.invFun :=
  (rfl)

/-- A measurable embedding of a nonempty space that pushes `μ` forward to `ν` is a mod-zero
isomorphism, with `MeasurableEmbedding.invFun` as the backward map: the two maps are mutually
inverse on the range of the embedding, which carries all of `ν`. -/
def _root_.MeasurableEmbedding.mod0MeasureIso [Nonempty α] {f : α → β}
    (hf : MeasurableEmbedding f) (hμ : μ.map f = ν) : Mod0MeasureIso α β μ ν where
  toFun := f
  invFun := hf.invFun
  measurable_toFun := hf.measurable
  measurable_invFun := hf.measurable_invFun
  map_toFun := hμ
  map_invFun := by
    rw [← hμ, Measure.map_map hf.measurable_invFun hf.measurable,
      hf.leftInverse_invFun.comp_eq_id, Measure.map_id]
  left_inv_ae := ae_of_all _ hf.leftInverse_invFun
  right_inv_ae := by
    have hmem : ∀ᵐ y ∂ν, y ∈ range f :=
      hμ ▸ ae_map_mem_range hf.measurableSet_range hf.measurable.aemeasurable
    filter_upwards [hmem] with _ ⟨x, hx⟩
    rw [← hx, hf.leftInverse_invFun x, id_eq]

@[simp]
theorem _root_.MeasurableEmbedding.mod0MeasureIso_toFun [Nonempty α] {f : α → β}
    (hf : MeasurableEmbedding f) (hμ : μ.map f = ν) : (hf.mod0MeasureIso hμ).toFun = f :=
  (rfl)

@[simp]
theorem _root_.MeasurableEmbedding.mod0MeasureIso_invFun [Nonempty α] {f : α → β}
    (hf : MeasurableEmbedding f) (hμ : μ.map f = ν) :
    (hf.mod0MeasureIso hμ).invFun = hf.invFun :=
  (rfl)

/-- A mod-zero isomorphism into `ℝ` carrying the unit interval measure gives measure-preserving
maps in both directions between the space and the unit interval which are mutually inverse
almost everywhere. -/
theorem Mod0MeasureIso.exists_measurePreserving_unitInterval
    (e : Mod0MeasureIso α ℝ μ (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∃ (f : α → I) (g : I → α),
      MeasurePreserving f μ volume ∧ MeasurePreserving g volume μ ∧
      (∀ᵐ x ∂μ, g (f x) = x) ∧ (∀ᵐ y ∂(volume : Measure I), f (g y) = y) :=
  -- Compose with the inverse of the coercion `I → ℝ`, itself a mod-zero isomorphism.
  let e' : Mod0MeasureIso α I μ volume := e.trans
    (unitInterval.measurableEmbedding_coe.mod0MeasureIso
      unitInterval.measurePreserving_coe.map_eq).symm
  ⟨e'.toFun, e'.invFun, e'.measurePreserving, e'.measurePreserving_invFun, e'.left_inv_ae,
    e'.right_inv_ae⟩

end TauCeti
