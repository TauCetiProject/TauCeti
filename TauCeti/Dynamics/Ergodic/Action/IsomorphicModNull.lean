/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.Factor
public import TauCeti.MeasureTheory.Measure.Mod0MeasureIso
import TauCeti.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Isomorphism mod 0 of actions through almost-everywhere inverse maps

`TauCeti.IsomorphismModNull` describes an isomorphism mod 0 of two systems through conull
invariant sets on which the maps are mutually inverse and conjugate the systems exactly. For
actions of arbitrary monoids, such as the `ℝ`-parameter of a flow, a common conull set for all
parameters cannot be chosen in general, so isomorphism mod 0 of actions is formulated almost
everywhere: `TauCeti.IsIsomorphismModNullSMul M f g μ ν` says that `f : X → Y` and `g : Y → X`
are factor maps of the `M`-actions (measure-preserving, intertwining each parameter almost
everywhere) and are mutually inverse almost everywhere.

For actions of countable monoids by measurable quasi-measure-preserving maps, this agrees with
the conull-set definition: the almost-everywhere identities hold exactly on measurable conull sets
that are forward invariant, mapped into each other by `f` and `g`
(`TauCeti.isIsomorphismModNullSMul_iff_exists_measurableSet`). The construction starts from an
invariant conull set `X₁` on which `g ∘ f = id` and `f` intertwines, takes an invariant conull
`Y₀` on which `f ∘ g = id` and `g` lands in `X₁`
(`MeasureTheory.exists_measurableSet_mapsTo_smul_of_ae`), and sets `X₀ = X₁ ∩ f ⁻¹' Y₀`
(`MeasureTheory.QuasiMeasurePreserving.exists_measurableSet_invOn`).
The single-map version is `TauCeti.isIsomorphicModNull_iff_exists_ae`.

## Main definitions

* `TauCeti.IsIsomorphismModNullSMul M f g μ ν`, `TauCeti.IsIsomorphismModNullVAdd M f g μ ν`:
  `f` and `g` are almost-everywhere inverse factor maps of the actions.
* `TauCeti.IsIsomorphicModNullSMul M μ ν`, `TauCeti.IsIsomorphicModNullVAdd M μ ν`: such maps
  exist (`TauCeti.isIsomorphicModNullSMul_iff`).

## Main results

* `TauCeti.IsIsomorphismModNullSMul.toMod0MeasureIso`: the maps of an isomorphism mod 0 of
  actions are a `TauCeti.Mod0MeasureIso`.
* `TauCeti.IsIsomorphismModNullSMul.refl`, `.symm`, `.trans`, and the same for
  `IsIsomorphicModNullSMul`: an equivalence relation.
* `TauCeti.IsIsomorphismModNullSMul.ergodicSMul_iff`,
  `TauCeti.IsIsomorphicModNullSMul.ergodicSMul_iff`: ergodicity of measurable actions is invariant.
* `TauCeti.IsIsomorphismModNullSMul.of_invOn`: measure-preserving maps that are inverse on conull
  sets `X₀`, `Y₀`, with `X₀` forward invariant, `g` mapping `Y₀` into `X₀` and `f` intertwining
  every parameter on `X₀`, are almost-everywhere inverse factor maps.
* `TauCeti.IsIsomorphismModNullSMul.exists_measurableSet`: conversely, for a countable monoid
  acting by measurable quasi-measure-preserving maps, they are mutually inverse and intertwine
  every parameter exactly on measurable conull forward-invariant sets;
  `TauCeti.isIsomorphismModNullSMul_iff_exists_measurableSet` is the equivalence.
-/

public section

namespace TauCeti

open MeasureTheory Filter Set Function

variable {M X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} {ρ : Measure Z} {f : X → Y} {g : Y → X}

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

/-- Two actions are isomorphic mod 0 exactly when there are almost-everywhere inverse factor maps
between them. -/
@[to_additive /-- Two additive actions are isomorphic mod 0 exactly when there are
almost-everywhere inverse factor maps between them. -/]
theorem isIsomorphicModNullSMul_iff [SMul M X] [SMul M Y] :
    IsIsomorphicModNullSMul M μ ν ↔ ∃ (f : X → Y) (g : Y → X), IsIsomorphismModNullSMul M f g μ ν :=
  Iff.rfl

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

/-- The maps of an isomorphism mod 0 of actions, as a measure-preserving isomorphism modulo null
sets. -/
@[to_additive /-- The maps of an isomorphism mod 0 of additive actions, as a measure-preserving
isomorphism modulo null sets. -/]
def toMod0MeasureIso (h : IsIsomorphismModNullSMul M f g μ ν) : Mod0MeasureIso X Y μ ν :=
  .ofMeasurePreserving h.isFactorMapSMul.measurePreserving
    h.isFactorMapSMul_symm.measurePreserving h.left_inv h.right_inv

@[to_additive (attr := simp)]
theorem toMod0MeasureIso_toFun (h : IsIsomorphismModNullSMul M f g μ ν) :
    h.toMod0MeasureIso.toFun = f :=
  Mod0MeasureIso.ofMeasurePreserving_toFun ..

@[to_additive (attr := simp)]
theorem toMod0MeasureIso_invFun (h : IsIsomorphismModNullSMul M f g μ ν) :
    h.toMod0MeasureIso.invFun = g :=
  Mod0MeasureIso.ofMeasurePreserving_invFun ..

/-- Isomorphisms mod 0 of actions compose. -/
@[to_additive /-- Isomorphisms mod 0 of additive actions compose. -/]
protected theorem trans (h : IsIsomorphismModNullSMul M f g μ ν)
    (h' : IsIsomorphismModNullSMul M f' g' ν ρ) :
    IsIsomorphismModNullSMul M (f' ∘ f) (g ∘ g') μ ρ := by
  refine ⟨h'.isFactorMapSMul.comp h.isFactorMapSMul,
    h.isFactorMapSMul_symm.comp h'.isFactorMapSMul_symm, ?_, ?_⟩
  · simpa only [Mod0MeasureIso.trans_toFun, Mod0MeasureIso.trans_invFun, toMod0MeasureIso_toFun,
      toMod0MeasureIso_invFun, comp_def] using
      (h.toMod0MeasureIso.trans h'.toMod0MeasureIso).left_inv_ae
  · simpa only [Mod0MeasureIso.trans_toFun, Mod0MeasureIso.trans_invFun, toMod0MeasureIso_toFun,
      toMod0MeasureIso_invFun, comp_def] using
      (h.toMod0MeasureIso.trans h'.toMod0MeasureIso).right_inv_ae

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
  obtain ⟨X₀, hX₀₁, hX₀m, hX₀0, hX₀M, hfX, hgY, hinv⟩ :=
    hf.quasiMeasurePreserving.exists_measurableSet_invOn hf.measurable hX₁m hX₁0 hX₁M hX₁ hY₀m
      hY₀0 hY₀M hY₀
  exact ⟨X₀, Y₀, hX₀m, hY₀m, hX₀0, hY₀0, hX₀M, hY₀M, hfX, hgY, hinv,
    fun m x hx ↦ (hX₁ x (hX₀₁ hx)).2 m⟩

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
  let ⟨_, _, h⟩ := isIsomorphicModNullSMul_iff.mp h
  h.symm.isIsomorphicModNullSMul

/-- Isomorphism mod 0 of actions is transitive. -/
@[to_additive /-- Isomorphism mod 0 of additive actions is transitive. -/]
protected theorem trans (h : IsIsomorphicModNullSMul M μ ν) (h' : IsIsomorphicModNullSMul M ν ρ) :
    IsIsomorphicModNullSMul M μ ρ :=
  let ⟨_, _, h⟩ := isIsomorphicModNullSMul_iff.mp h
  let ⟨_, _, h'⟩ := isIsomorphicModNullSMul_iff.mp h'
  (h.trans h').isIsomorphicModNullSMul

/-- Ergodicity of measurable actions is invariant under isomorphism mod 0. -/
@[to_additive /-- Ergodicity of measurable additive actions is invariant under isomorphism
mod 0. -/]
theorem ergodicSMul_iff [MeasurableConstSMul M X] [MeasurableConstSMul M Y]
    (h : IsIsomorphicModNullSMul M μ ν) : ErgodicSMul M X μ ↔ ErgodicSMul M Y ν :=
  let ⟨_, _, h⟩ := isIsomorphicModNullSMul_iff.mp h
  h.ergodicSMul_iff

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
