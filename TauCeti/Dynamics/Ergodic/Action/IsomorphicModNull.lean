/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.Factor
public import TauCeti.Dynamics.Ergodic.IsomorphicModNull
import TauCeti.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Isomorphism mod 0 through almost-everywhere inverse maps

`TauCeti.IsomorphismModNull` describes an isomorphism mod 0 of two systems through conull
invariant sets on which the maps are mutually inverse and conjugate the systems exactly. For
actions of arbitrary monoids, such as the `ℝ`-parameter of a flow, no common conull set can be
chosen for all parameters, so isomorphism mod 0 of actions is formulated almost everywhere:
`TauCeti.IsIsomorphismModNullSMul M f g μ ν` says that `f : X → Y` and `g : Y → X` are factor
maps of the `M`-actions (measure-preserving, intertwining each parameter almost everywhere) and
are mutually inverse almost everywhere.

For a single map, and for actions of countable monoids by measurable quasi-measure-preserving
maps, this agrees with the conull-set definition: the almost-everywhere identities hold exactly on
measurable conull sets that are forward invariant, mapped into each other by `f` and `g`
(`TauCeti.isIsomorphicModNull_iff_exists_ae`,
`TauCeti.isIsomorphismModNullSMul_iff_exists_measurableSet`). The construction starts from an
invariant conull set `X₁` on which `g ∘ f = id` and `f` intertwines, takes an invariant conull
`Y₀` on which `f ∘ g = id` and `g` lands in `X₁`, and sets `X₀ = X₁ ∩ f ⁻¹' Y₀`
(`MeasureTheory.exists_measurableSet_mapsTo_smul_of_ae`).

## Main definitions

* `TauCeti.IsIsomorphismModNullSMul M f g μ ν`, `TauCeti.IsIsomorphismModNullVAdd M f g μ ν`:
  `f` and `g` are almost-everywhere inverse factor maps of the actions.
* `TauCeti.IsIsomorphicModNullSMul M μ ν`, `TauCeti.IsIsomorphicModNullVAdd M μ ν`: such maps
  exist.

## Main results

* `TauCeti.IsIsomorphismModNullSMul.refl`, `.symm`, `.trans`, and the same for
  `IsIsomorphicModNullSMul`: an equivalence relation.
* `TauCeti.IsIsomorphismModNullSMul.ergodicSMul_iff`: ergodicity of measurable actions is
  invariant.
* `TauCeti.IsIsomorphismModNullSMul.of_invOn`: maps that are mutually inverse and intertwine every
  parameter on conull sets are almost-everywhere inverse factor maps.
* `TauCeti.IsIsomorphismModNullSMul.exists_measurableSet`: conversely, for a countable monoid
  acting by measurable quasi-measure-preserving maps, they are mutually inverse and intertwine
  every parameter exactly on measurable conull forward-invariant sets;
  `TauCeti.isIsomorphismModNullSMul_iff_exists_measurableSet` is the equivalence.
* `TauCeti.exists_isomorphismModNull_of_ae`, `TauCeti.isIsomorphicModNull_iff_exists_ae`: the
  single-map version, with the conull-set structure `TauCeti.IsomorphismModNull`.
-/

public section

namespace TauCeti

open MeasureTheory Filter Set Function

variable {M X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} {ρ : Measure Z} {f : X → Y} {g : Y → X}

section SingleMap

variable {T : X → X} {S : Y → Y}

namespace IsomorphismModNull

/-- The inverse map of an isomorphism mod 0 is a left inverse almost everywhere. -/
theorem invFun_comp_toFun_ae_eq (e : IsomorphismModNull T μ S ν) :
    e.invFun ∘ e.toFun =ᵐ[μ] id := by
  filter_upwards [mem_ae_iff.mpr e.measure_compl_source] with x hx using e.invFun_toFun x hx

/-- The inverse map of an isomorphism mod 0 is a right inverse almost everywhere. -/
theorem toFun_comp_invFun_ae_eq (e : IsomorphismModNull T μ S ν) :
    e.toFun ∘ e.invFun =ᵐ[ν] id :=
  e.symm.invFun_comp_toFun_ae_eq

end IsomorphismModNull

/-- **Conull realization of an almost-everywhere isomorphism.** For measurable
quasi-measure-preserving systems `T` and `S`, measure-preserving maps `f : X → Y` and
`g : Y → X` that are mutually inverse almost everywhere, with `f ∘ T = S ∘ f` almost everywhere,
are the maps of an isomorphism mod 0. -/
theorem exists_isomorphismModNull_of_ae (hTm : Measurable T) (hT : QuasiMeasurePreserving T μ μ)
    (hSm : Measurable S) (hS : QuasiMeasurePreserving S ν ν) (hf : MeasurePreserving f μ ν)
    (hg : MeasurePreserving g ν μ) (hgf : g ∘ f =ᵐ[μ] id) (hfg : f ∘ g =ᵐ[ν] id)
    (hfT : f ∘ T =ᵐ[μ] S ∘ f) :
    ∃ e : IsomorphismModNull T μ S ν, e.toFun = f ∧ e.invFun = g := by
  obtain ⟨X₁, hX₁m, hX₁0, hX₁T, hX₁⟩ := exists_measurableSet_mapsTo_of_ae hTm hT
    (p := fun x ↦ g (f x) = x ∧ f (T x) = S (f x))
    (by filter_upwards [hgf, hfT] with x h₁ h₂ using ⟨h₁, h₂⟩)
  have hY : ∀ᵐ y ∂ν, f (g y) = y ∧ g y ∈ X₁ := by
    filter_upwards [hfg, hg.quasiMeasurePreserving.ae (mem_ae_iff.mpr hX₁0)] with y h₁ h₂
      using ⟨h₁, h₂⟩
  obtain ⟨Y₀, hY₀m, hY₀0, hY₀S, hY₀⟩ := exists_measurableSet_mapsTo_of_ae hSm hS hY
  have hcompl : μ (X₁ ∩ f ⁻¹' Y₀)ᶜ = 0 := by
    rw [compl_inter, ← preimage_compl]
    refine measure_union_null hX₁0 ?_
    rw [hf.measure_preimage hY₀m.compl.nullMeasurableSet]
    exact hY₀0
  refine ⟨
    { toFun := f
      invFun := g
      source := X₁ ∩ f ⁻¹' Y₀
      target := Y₀
      measurableSet_source := hX₁m.inter (hf.measurable hY₀m)
      measurableSet_target := hY₀m
      measure_compl_source := hcompl
      measure_compl_target := hY₀0
      mapsTo_source := fun x hx ↦ ⟨hX₁T hx.1, by
        rw [mem_preimage, (hX₁ x hx.1).2]
        exact hY₀S hx.2⟩
      mapsTo_target := hY₀S
      mapsTo_toFun := fun _ hx ↦ hx.2
      mapsTo_invFun := fun y hy ↦ ⟨(hY₀ y hy).2, by rw [mem_preimage, (hY₀ y hy).1]; exact hy⟩
      invFun_toFun := fun x hx ↦ (hX₁ x hx.1).1
      toFun_invFun := fun y hy ↦ (hY₀ y hy).1
      measurePreserving_toFun := hf
      measurePreserving_invFun := hg
      toFun_comp := fun x hx ↦ (hX₁ x hx.1).2 }, rfl, rfl⟩

/-- For measurable quasi-measure-preserving systems, isomorphism mod 0 is the existence of
measure-preserving maps that are mutually inverse almost everywhere and conjugate the systems
almost everywhere. -/
theorem isIsomorphicModNull_iff_exists_ae (hTm : Measurable T)
    (hT : QuasiMeasurePreserving T μ μ) (hSm : Measurable S) (hS : QuasiMeasurePreserving S ν ν) :
    IsIsomorphicModNull T μ S ν ↔ ∃ (f : X → Y) (g : Y → X), MeasurePreserving f μ ν ∧
      MeasurePreserving g ν μ ∧ g ∘ f =ᵐ[μ] id ∧ f ∘ g =ᵐ[ν] id ∧ f ∘ T =ᵐ[μ] S ∘ f := by
  refine ⟨fun h ↦ (isIsomorphicModNull_iff_nonempty.mp h).elim fun e ↦ ⟨e.toFun, e.invFun,
    e.measurePreserving_toFun, e.measurePreserving_invFun, e.invFun_comp_toFun_ae_eq,
    e.toFun_comp_invFun_ae_eq, e.isFactorMap.comp_ae_eq⟩, ?_⟩
  rintro ⟨f, g, hf, hg, hgf, hfg, hfT⟩
  obtain ⟨e, -, -⟩ := exists_isomorphismModNull_of_ae hTm hT hSm hS hf hg hgf hfg hfT
  exact e.isIsomorphicModNull

end SingleMap

/-- `f : X → Y` and `g : Y → X` are an isomorphism mod 0 of the additive `M`-actions on `(X, μ)`
and `(Y, ν)`: both are factor maps of the actions, and they are mutually inverse almost
everywhere. -/
structure IsIsomorphismModNullVAdd (M : Type*) [VAdd M X] [VAdd M Y] (f : X → Y) (g : Y → X)
    (μ : Measure X) (ν : Measure Y) : Prop where
  /-- The forward map is a factor map. -/
  isFactorMapVAdd : IsFactorMapVAdd M f μ ν
  /-- The inverse map is a factor map. -/
  isFactorMapVAdd_symm : IsFactorMapVAdd M g ν μ
  /-- The inverse map is a left inverse almost everywhere. -/
  left_inv : g ∘ f =ᵐ[μ] id
  /-- The inverse map is a right inverse almost everywhere. -/
  right_inv : f ∘ g =ᵐ[ν] id

/-- `f : X → Y` and `g : Y → X` are an isomorphism mod 0 of the `M`-actions on `(X, μ)` and
`(Y, ν)`: both are factor maps of the actions, and they are mutually inverse almost everywhere. -/
@[to_additive existing]
structure IsIsomorphismModNullSMul (M : Type*) [SMul M X] [SMul M Y] (f : X → Y) (g : Y → X)
    (μ : Measure X) (ν : Measure Y) : Prop where
  /-- The forward map is a factor map. -/
  isFactorMapSMul : IsFactorMapSMul M f μ ν
  /-- The inverse map is a factor map. -/
  isFactorMapSMul_symm : IsFactorMapSMul M g ν μ
  /-- The inverse map is a left inverse almost everywhere. -/
  left_inv : g ∘ f =ᵐ[μ] id
  /-- The inverse map is a right inverse almost everywhere. -/
  right_inv : f ∘ g =ᵐ[ν] id

/-- The additive `M`-actions on `(X, μ)` and `(Y, ν)` are isomorphic mod 0: there are
almost-everywhere inverse factor maps between them. -/
def IsIsomorphicModNullVAdd (M : Type*) [VAdd M X] [VAdd M Y] (μ : Measure X)
    (ν : Measure Y) : Prop :=
  ∃ (f : X → Y) (g : Y → X), IsIsomorphismModNullVAdd M f g μ ν

/-- The `M`-actions on `(X, μ)` and `(Y, ν)` are isomorphic mod 0: there are almost-everywhere
inverse factor maps between them. -/
@[to_additive existing]
def IsIsomorphicModNullSMul (M : Type*) [SMul M X] [SMul M Y] (μ : Measure X)
    (ν : Measure Y) : Prop :=
  ∃ (f : X → Y) (g : Y → X), IsIsomorphismModNullSMul M f g μ ν

namespace IsIsomorphismModNullSMul

section SMul

variable [SMul M X] [SMul M Y] [SMul M Z] {f' : Y → Z} {g' : Z → Y}

/-- The identity is an isomorphism mod 0 of an action with itself. -/
@[to_additive /-- The identity is an isomorphism mod 0 of an additive action with itself. -/]
protected theorem refl (μ : Measure X) : IsIsomorphismModNullSMul M (id : X → X) id μ μ :=
  ⟨.id μ, .id μ, .rfl, .rfl⟩

/-- Exchanging the two maps of an isomorphism mod 0 gives an isomorphism mod 0 in the other
direction. -/
@[to_additive /-- Exchanging the two maps of an isomorphism mod 0 of additive actions gives an
isomorphism mod 0 in the other direction. -/]
protected theorem symm (h : IsIsomorphismModNullSMul M f g μ ν) :
    IsIsomorphismModNullSMul M g f ν μ :=
  ⟨h.isFactorMapSMul_symm, h.isFactorMapSMul, h.right_inv, h.left_inv⟩

/-- Isomorphisms mod 0 of actions compose. -/
@[to_additive /-- Isomorphisms mod 0 of additive actions compose. -/]
protected theorem trans (h : IsIsomorphismModNullSMul M f g μ ν)
    (h' : IsIsomorphismModNullSMul M f' g' ν ρ) :
    IsIsomorphismModNullSMul M (f' ∘ f) (g ∘ g') μ ρ := by
  refine ⟨h'.isFactorMapSMul.comp h.isFactorMapSMul,
    h.isFactorMapSMul_symm.comp h'.isFactorMapSMul_symm, ?_, ?_⟩
  · filter_upwards [h.isFactorMapSMul.measurePreserving.quasiMeasurePreserving.ae_eq_comp
      h'.left_inv, h.left_inv] with x h₁ h₂
    simp only [comp_apply, id_eq] at h₁ h₂ ⊢
    rw [h₁, h₂]
  · filter_upwards [h'.isFactorMapSMul_symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
      h.right_inv, h'.right_inv] with z h₁ h₂
    simp only [comp_apply, id_eq] at h₁ h₂ ⊢
    rw [h₁, h₂]

/-- The two actions of an isomorphism mod 0 are isomorphic mod 0. -/
@[to_additive /-- The two additive actions of an isomorphism mod 0 are isomorphic mod 0. -/]
theorem isIsomorphicModNullSMul (h : IsIsomorphismModNullSMul M f g μ ν) :
    IsIsomorphicModNullSMul M μ ν :=
  ⟨f, g, h⟩

/-- Ergodicity of measurable actions is invariant under isomorphism mod 0. -/
@[to_additive /-- Ergodicity of measurable additive actions is invariant under isomorphism
mod 0. -/]
theorem ergodicSMul_iff [MeasurableConstSMul M X] [MeasurableConstSMul M Y]
    (h : IsIsomorphismModNullSMul M f g μ ν) : ErgodicSMul M X μ ↔ ErgodicSMul M Y ν :=
  ⟨fun _ ↦ h.isFactorMapSMul.ergodicSMul, fun _ ↦ h.isFactorMapSMul_symm.ergodicSMul⟩

/-- Measure-preserving maps `f` and `g` that are mutually inverse on conull sets `X₀` and `Y₀`,
with `g` mapping `Y₀` into `X₀`, `X₀` forward invariant and `f` intertwining every parameter on
`X₀`, are an isomorphism mod 0 of the actions: `g` intertwines every parameter on `Y₀`. -/
@[to_additive /-- Measure-preserving maps `f` and `g` that are mutually inverse on conull sets
`X₀` and `Y₀`, with `g` mapping `Y₀` into `X₀`, `X₀` forward invariant and `f` intertwining every
parameter on `X₀`, are an isomorphism mod 0 of the additive actions. -/]
theorem of_invOn (hf : MeasurePreserving f μ ν) (hg : MeasurePreserving g ν μ) {X₀ : Set X}
    {Y₀ : Set Y} (hX₀ : μ X₀ᶜ = 0) (hY₀ : ν Y₀ᶜ = 0) (hX₀M : ∀ m : M, MapsTo (m • ·) X₀ X₀)
    (hgY : MapsTo g Y₀ X₀) (hinv : InvOn g f X₀ Y₀)
    (hfm : ∀ m : M, ∀ x ∈ X₀, f (m • x) = m • f x) : IsIsomorphismModNullSMul M f g μ ν := by
  refine ⟨.of_measure_compl_eq_zero hf hX₀ hfm, .of_measure_compl_eq_zero hg hY₀ fun m y hy ↦ ?_,
    ?_, ?_⟩
  · have hx := hgY hy
    calc g (m • y) = g (m • f (g y)) := by rw [hinv.2 hy]
      _ = g (f (m • g y)) := by rw [hfm m _ hx]
      _ = m • g y := hinv.1 (hX₀M m hx)
  · filter_upwards [mem_ae_iff.mpr hX₀] with x hx using hinv.1 hx
  · filter_upwards [mem_ae_iff.mpr hY₀] with y hy using hinv.2 hy

end SMul

section Monoid

variable [Monoid M] [MulAction M X] [MulAction M Y] [MeasurableConstSMul M X]
  [MeasurableConstSMul M Y] [Countable M]

/-- **Invariant conull realization of an isomorphism mod 0.** For a countable monoid acting by
measurable quasi-measure-preserving maps on both sides, the maps of an isomorphism mod 0 are
mutually inverse, and the forward map intertwines every parameter, exactly on measurable conull
forward-invariant sets `X₀` and `Y₀` with `f '' X₀ ⊆ Y₀` and `g '' Y₀ ⊆ X₀`. -/
@[to_additive /-- **Invariant conull realization of an isomorphism mod 0.** For a countable
additive monoid acting by measurable quasi-measure-preserving maps on both sides, the maps of an
isomorphism mod 0 are mutually inverse, and the forward map intertwines every parameter, exactly
on measurable conull forward-invariant sets `X₀` and `Y₀` with `f '' X₀ ⊆ Y₀` and
`g '' Y₀ ⊆ X₀`. -/]
theorem exists_measurableSet (h : IsIsomorphismModNullSMul M f g μ ν)
    (hMX : ∀ m : M, QuasiMeasurePreserving (m • ·) μ μ)
    (hMY : ∀ m : M, QuasiMeasurePreserving (m • ·) ν ν) :
    ∃ (X₀ : Set X) (Y₀ : Set Y), MeasurableSet X₀ ∧ MeasurableSet Y₀ ∧ μ X₀ᶜ = 0 ∧ ν Y₀ᶜ = 0 ∧
      (∀ m : M, MapsTo (m • ·) X₀ X₀) ∧ (∀ m : M, MapsTo (m • ·) Y₀ Y₀) ∧ MapsTo f X₀ Y₀ ∧
      MapsTo g Y₀ X₀ ∧ InvOn g f X₀ Y₀ ∧ ∀ m : M, ∀ x ∈ X₀, f (m • x) = m • f x := by
  have hf := h.isFactorMapSMul.measurePreserving
  obtain ⟨X₁, hX₁m, hX₁0, hX₁M, hX₁⟩ := exists_measurableSet_mapsTo_smul_of_ae hMX
    (p := fun x ↦ g (f x) = x ∧ ∀ m : M, f (m • x) = m • f x)
    (by filter_upwards [h.left_inv, ae_all_iff.mpr h.isFactorMapSMul.comp_smul_ae_eq]
          with x h₁ h₂ using ⟨h₁, h₂⟩)
  have hY : ∀ᵐ y ∂ν, f (g y) = y ∧ g y ∈ X₁ := by
    filter_upwards [h.right_inv, h.isFactorMapSMul_symm.measurePreserving.quasiMeasurePreserving.ae
      (mem_ae_iff.mpr hX₁0)] with y h₁ h₂ using ⟨h₁, h₂⟩
  obtain ⟨Y₀, hY₀m, hY₀0, hY₀M, hY₀⟩ := exists_measurableSet_mapsTo_smul_of_ae hMY hY
  refine ⟨X₁ ∩ f ⁻¹' Y₀, Y₀, hX₁m.inter (hf.measurable hY₀m), hY₀m, ?_, hY₀0,
    fun m x hx ↦ ⟨hX₁M m hx.1, ?_⟩, hY₀M, fun _ hx ↦ hx.2,
    fun y hy ↦ ⟨(hY₀ y hy).2, ?_⟩, ⟨fun x hx ↦ (hX₁ x hx.1).1, fun y hy ↦ (hY₀ y hy).1⟩,
    fun m x hx ↦ (hX₁ x hx.1).2 m⟩
  · rw [compl_inter, ← preimage_compl]
    refine measure_union_null hX₁0 ?_
    rw [hf.measure_preimage hY₀m.compl.nullMeasurableSet]
    exact hY₀0
  · rw [mem_preimage, (hX₁ x hx.1).2 m]
    exact hY₀M m hx.2
  · rw [mem_preimage, (hY₀ y hy).1]
    exact hy

end Monoid

end IsIsomorphismModNullSMul

namespace IsIsomorphicModNullSMul

variable [SMul M X] [SMul M Y] [SMul M Z]

/-- Isomorphism mod 0 of actions is reflexive. -/
@[to_additive /-- Isomorphism mod 0 of additive actions is reflexive. -/]
protected theorem refl (μ : Measure X) : IsIsomorphicModNullSMul M μ μ :=
  (IsIsomorphismModNullSMul.refl μ).isIsomorphicModNullSMul

/-- Isomorphism mod 0 of actions is symmetric. -/
@[to_additive /-- Isomorphism mod 0 of additive actions is symmetric. -/]
protected theorem symm (h : IsIsomorphicModNullSMul M μ ν) : IsIsomorphicModNullSMul M ν μ :=
  let ⟨_, _, h⟩ := h
  h.symm.isIsomorphicModNullSMul

/-- Isomorphism mod 0 of actions is transitive. -/
@[to_additive /-- Isomorphism mod 0 of additive actions is transitive. -/]
protected theorem trans (h : IsIsomorphicModNullSMul M μ ν) (h' : IsIsomorphicModNullSMul M ν ρ) :
    IsIsomorphicModNullSMul M μ ρ :=
  let ⟨_, _, h⟩ := h
  let ⟨_, _, h'⟩ := h'
  (h.trans h').isIsomorphicModNullSMul

end IsIsomorphicModNullSMul

/-- For a countable monoid acting by measurable quasi-measure-preserving maps, measure-preserving
maps `f` and `g` are an isomorphism mod 0 of the actions exactly when they are mutually inverse,
and `f` intertwines every parameter, on measurable conull forward-invariant sets mapped into each
other. -/
@[to_additive /-- For a countable additive monoid acting by measurable quasi-measure-preserving
maps, measure-preserving maps `f` and `g` are an isomorphism mod 0 of the additive actions exactly
when they are mutually inverse, and `f` intertwines every parameter, on measurable conull
forward-invariant sets mapped into each other. -/]
theorem isIsomorphismModNullSMul_iff_exists_measurableSet [Monoid M] [MulAction M X]
    [MulAction M Y] [MeasurableConstSMul M X] [MeasurableConstSMul M Y] [Countable M]
    (hMX : ∀ m : M, QuasiMeasurePreserving (m • ·) μ μ)
    (hMY : ∀ m : M, QuasiMeasurePreserving (m • ·) ν ν) (hf : MeasurePreserving f μ ν)
    (hg : MeasurePreserving g ν μ) :
    IsIsomorphismModNullSMul M f g μ ν ↔
      ∃ (X₀ : Set X) (Y₀ : Set Y), MeasurableSet X₀ ∧ MeasurableSet Y₀ ∧ μ X₀ᶜ = 0 ∧
        ν Y₀ᶜ = 0 ∧ (∀ m : M, MapsTo (m • ·) X₀ X₀) ∧ (∀ m : M, MapsTo (m • ·) Y₀ Y₀) ∧
        MapsTo f X₀ Y₀ ∧ MapsTo g Y₀ X₀ ∧ InvOn g f X₀ Y₀ ∧
        ∀ m : M, ∀ x ∈ X₀, f (m • x) = m • f x :=
  ⟨fun h ↦ h.exists_measurableSet hMX hMY, fun ⟨_, _, _, _, hX₀, hY₀, hX₀M, _, _, hgY, hinv,
    hfm⟩ ↦ .of_invOn hf hg hX₀ hY₀ hX₀M hgY hinv hfm⟩

end TauCeti
