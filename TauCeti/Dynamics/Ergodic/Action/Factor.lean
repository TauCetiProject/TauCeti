/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import TauCeti.Dynamics.Ergodic.Factor

/-!
# Factor maps of measure-preserving actions

Let a monoid `M` act on measurable spaces `X` and `Y`. A *factor map* of the actions from
`(X, μ)` to `(Y, ν)` is a measure-preserving map `π : X → Y` that intertwines each parameter
almost everywhere: `π ∘ (m • ·) =ᵐ[μ] (m • ·) ∘ π` for every `m : M`. This is the action interface
of `TauCeti.IsFactorMap`, which is the case of a single map; the additive version
`TauCeti.IsFactorMapVAdd` covers actions of additive monoids such as flows.

## Main definitions

* `TauCeti.IsFactorMapSMul M π μ ν`, `TauCeti.IsFactorMapVAdd M π μ ν`: `π` is a factor map of
  the `M`-actions.

## Main results

* `TauCeti.IsFactorMapSMul.toIsFactorMap`: each parameter of a factor map of actions gives a
  factor map of single systems.
* `TauCeti.IsFactorMapSMul.id`, `TauCeti.IsFactorMapSMul.comp`: factor maps contain the identity
  and compose.
* `TauCeti.IsFactorMapSMul.of_map_smul`: an equivariant measure-preserving map is a factor map.
  `TauCeti.IsFactorMapSMul.of_measurableEquiv_symm`: so is the inverse of an equivariant
  measure-preserving measurable equivalence. More generally,
  `TauCeti.IsFactorMapSMul.of_measure_compl_eq_zero` needs equivariance only on a conull set.
* `TauCeti.IsFactorMapSMul.exists_measurableSet_mapsTo_smul`: **invariant conull realization**.
  A factor map of actions of a countable monoid acting by measurable quasi-measure-preserving maps
  intertwines every parameter exactly on a measurable conull set that is forward invariant under
  the action; `TauCeti.isFactorMapSMul_iff_exists_measurableSet` is the equivalence with the
  conull-set definition. The invariant set comes from
  `MeasureTheory.exists_measurableSet_mapsTo_smul_of_ae`; the single-map version is
  `TauCeti.isFactorMap_iff_exists_measurableSet`. The realization needs a countable monoid, such as
  `ℕ` or `ℤ`; for uncountable ones, such as the `ℝ`-parameter of a flow, only the converse
  `TauCeti.IsFactorMapVAdd.of_measure_compl_eq_zero` applies.
* `TauCeti.IsFactorMapSMul.toPUnit`: the constant map to a point is a factor map onto the trivial
  action.
* `TauCeti.IsFactorMapSMul.prodMap`, `TauCeti.IsFactorMapSMul.fst`,
  `TauCeti.IsFactorMapSMul.snd`: products of factor maps are factor maps for the diagonal action,
  and the coordinate projections of a product are factor maps.
* `TauCeti.IsFactorMapSMul.of_smul_eq`: restriction of the parameters along a map `f : N → M`
  with `f n • x = n • x`, for instance a monoid homomorphism.
* `TauCeti.IsFactorMapSMul.smulInvariantMeasure`, `TauCeti.IsFactorMapSMul.ergodicSMul`:
  invariance of the measure and ergodicity pass to factors;
  `TauCeti.IsFactorMapSMul.aeconst_of_forall_preimage_smul_ae_eq` is the zero-one part of the
  latter, which needs no measurability of the target action.

The descent of ergodicity adapts the proof of `ErgodicSMul.map`
(`TauCeti/Dynamics/Ergodic/Action/Map.lean`) from everywhere-equivariant maps to
almost-everywhere intertwiners; `ErgodicSMul.map` is derived from it there.
-/

public section

namespace TauCeti

open MeasureTheory Filter

variable {M N X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} {ρ : Measure Z} {π : X → Y} {σ : Y → Z}

/-- `π : X → Y` is a factor map from the additive `M`-action on `(X, μ)` to the additive
`M`-action on `(Y, ν)`: it is measure-preserving and intertwines every parameter almost
everywhere, `π ∘ (m +ᵥ ·) =ᵐ[μ] (m +ᵥ ·) ∘ π`. -/
structure IsFactorMapVAdd (M : Type*) [VAdd M X] [VAdd M Y] (π : X → Y) (μ : Measure X)
    (ν : Measure Y) : Prop where
  /-- A factor map is measure-preserving. -/
  measurePreserving : MeasurePreserving π μ ν
  /-- A factor map intertwines every parameter almost everywhere. -/
  comp_vadd_ae_eq : ∀ m : M, π ∘ (m +ᵥ ·) =ᵐ[μ] (m +ᵥ ·) ∘ π

/-- `π : X → Y` is a factor map from the `M`-action on `(X, μ)` to the `M`-action on `(Y, ν)`: it
is measure-preserving and intertwines every parameter almost everywhere,
`π ∘ (m • ·) =ᵐ[μ] (m • ·) ∘ π`. -/
@[to_additive existing]
structure IsFactorMapSMul (M : Type*) [SMul M X] [SMul M Y] (π : X → Y) (μ : Measure X)
    (ν : Measure Y) : Prop where
  /-- A factor map is measure-preserving. -/
  measurePreserving : MeasurePreserving π μ ν
  /-- A factor map intertwines every parameter almost everywhere. -/
  comp_smul_ae_eq : ∀ m : M, π ∘ (m • ·) =ᵐ[μ] (m • ·) ∘ π

namespace IsFactorMapSMul

section SMul

variable [SMul M X] [SMul M Y] [SMul M Z]

/-- A factor map of actions is, for each parameter `m`, a factor map from the system `(m • ·)` on
`(X, μ)` to the system `(m • ·)` on `(Y, ν)`. -/
@[to_additive /-- A factor map of additive actions is, for each parameter `m`, a factor map from
the system `(m +ᵥ ·)` on `(X, μ)` to the system `(m +ᵥ ·)` on `(Y, ν)`. -/]
theorem toIsFactorMap (h : IsFactorMapSMul M π μ ν) (m : M) :
    IsFactorMap π (m • ·) (m • ·) μ ν :=
  ⟨h.measurePreserving, h.comp_smul_ae_eq m⟩

/-- The identity is a factor map from any action to itself. -/
@[to_additive /-- The identity is a factor map from any additive action to itself. -/]
protected theorem id (μ : Measure X) : IsFactorMapSMul M id μ μ :=
  ⟨.id μ, fun _ ↦ .rfl⟩

/-- A measure-preserving equivariant map is a factor map. -/
@[to_additive /-- A measure-preserving equivariant map is a factor map. -/]
theorem of_map_smul (hπ : MeasurePreserving π μ ν) (h : ∀ (m : M) (x : X), π (m • x) = m • π x) :
    IsFactorMapSMul M π μ ν :=
  ⟨hπ, fun m ↦ .of_eq (funext fun x ↦ h m x)⟩

/-- The inverse of an equivariant measure-preserving measurable equivalence is a factor map. -/
@[to_additive /-- The inverse of an equivariant measure-preserving measurable equivalence of
additive actions is a factor map. -/]
theorem of_measurableEquiv_symm {e : X ≃ᵐ Y} (he : MeasurePreserving e μ ν)
    (h : ∀ (m : M) (x : X), e (m • x) = m • e x) : IsFactorMapSMul M e.symm ν μ :=
  of_map_smul he.symm fun m y ↦ by
    rw [← e.symm_apply_apply (m • e.symm y), h, e.apply_symm_apply]

/-- A measure-preserving map that intertwines every parameter exactly on a conull set is a factor
map of the actions. -/
@[to_additive /-- A measure-preserving map that intertwines every parameter exactly on a conull
set is a factor map of the additive actions. -/]
theorem of_measure_compl_eq_zero (hπ : MeasurePreserving π μ ν) {X₀ : Set X} (h0 : μ X₀ᶜ = 0)
    (h : ∀ m : M, ∀ x ∈ X₀, π (m • x) = m • π x) : IsFactorMapSMul M π μ ν :=
  ⟨hπ, fun m ↦ by filter_upwards [mem_ae_iff.mpr h0] with x hx using h m x hx⟩

/-- Factor maps compose. -/
@[to_additive /-- Factor maps compose. -/]
protected theorem comp (hσ : IsFactorMapSMul M σ ν ρ) (hπ : IsFactorMapSMul M π μ ν) :
    IsFactorMapSMul M (σ ∘ π) μ ρ :=
  ⟨hσ.measurePreserving.comp hπ.measurePreserving,
    fun m ↦ ((hσ.toIsFactorMap m).comp (hπ.toIsFactorMap m)).comp_ae_eq⟩

/-- The constant map to a point is a factor map from an action on a probability space onto the
trivial action on a point. -/
@[to_additive /-- The constant map to a point is a factor map from an additive action on a
probability space onto the trivial action on a point. -/]
theorem toPUnit [IsProbabilityMeasure μ] :
    IsFactorMapSMul M (fun _ : X ↦ PUnit.unit) μ (Measure.dirac PUnit.unit) :=
  of_map_smul ⟨measurable_const, by simp [Measure.map_const]⟩ fun _ _ ↦ rfl

/-- Restriction of parameters: a factor map of `M`-actions is a factor map of `N`-actions for any
`f : N → M` with `f n • x = n • x` on both spaces, for instance a monoid homomorphism defining the
`N`-actions. -/
@[to_additive /-- Restriction of parameters: a factor map of additive `M`-actions is a factor map
of additive `N`-actions for any `f : N → M` with `f n +ᵥ x = n +ᵥ x` on both spaces. -/]
theorem of_smul_eq [SMul N X] [SMul N Y] (h : IsFactorMapSMul M π μ ν) (f : N → M)
    (hX : ∀ (n : N) (x : X), f n • x = n • x) (hY : ∀ (n : N) (y : Y), f n • y = n • y) :
    IsFactorMapSMul N π μ ν := by
  refine ⟨h.measurePreserving, fun n ↦ ?_⟩
  have hXf : (n • · : X → X) = (f n • ·) := funext fun x ↦ (hX n x).symm
  have hYf : (n • · : Y → Y) = (f n • ·) := funext fun y ↦ (hY n y).symm
  rw [hXf, hYf]
  exact h.comp_smul_ae_eq (f n)

/-- If `π` is a factor map of actions, the target action is measurable and `μ` is invariant, then
`ν` is invariant. -/
@[to_additive /-- If `π` is a factor map of additive actions, the target action is measurable and
`μ` is invariant, then `ν` is invariant. -/]
theorem smulInvariantMeasure [SMulInvariantMeasure M X μ] [MeasurableConstSMul M Y]
    (h : IsFactorMapSMul M π μ ν) : SMulInvariantMeasure M Y ν where
  measure_preimage_smul m s hs := by
    have hπ := h.measurePreserving
    rw [← hπ.measure_preimage (hs.preimage (measurable_const_smul m)).nullMeasurableSet,
      ← hπ.measure_preimage hs.nullMeasurableSet]
    calc μ (π ⁻¹' ((m • ·) ⁻¹' s)) = μ ((m • ·) ⁻¹' (π ⁻¹' s)) :=
          measure_congr ((h.comp_smul_ae_eq m).preimage s).symm
      _ = μ (π ⁻¹' s) :=
          measure_preimage_smul_of_nullMeasurableSet
            (hs.preimage hπ.measurable).nullMeasurableSet m

/-- **The zero-one law passes to factors.** If `π` is a factor map of actions and the source
action is ergodic, then every measurable set of the target that is almost invariant under every
parameter is null or conull. -/
@[to_additive /-- **The zero-one law passes to factors.** If `π` is a factor map of additive
actions and the source action is ergodic, then every measurable set of the target that is almost
invariant under every parameter is null or conull. -/]
theorem aeconst_of_forall_preimage_smul_ae_eq [ErgodicSMul M X μ] (h : IsFactorMapSMul M π μ ν)
    {s : Set Y} (hs : MeasurableSet s) (hinv : ∀ m : M, (m • ·) ⁻¹' s =ᵐ[ν] s) :
    EventuallyEmptyOrUniv s (ae ν) := by
  have hπ := h.measurePreserving
  rw [← hπ.aeconst_preimage hs.nullMeasurableSet]
  refine MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq M
    (hs.preimage hπ.measurable).nullMeasurableSet fun m ↦ ?_
  exact ((h.comp_smul_ae_eq m).preimage s).trans
    (hπ.quasiMeasurePreserving.preimage_ae_eq (hinv m))

/-- **Ergodicity passes to factors.** If `π` is a factor map of actions, the target action is
measurable and the source action is ergodic, then the target action is ergodic. -/
@[to_additive /-- **Ergodicity passes to factors.** If `π` is a factor map of additive actions,
the target action is measurable and the source action is ergodic, then the target action is
ergodic. -/]
theorem ergodicSMul [ErgodicSMul M X μ] [MeasurableConstSMul M Y]
    (h : IsFactorMapSMul M π μ ν) : ErgodicSMul M Y ν where
  toSMulInvariantMeasure := h.smulInvariantMeasure
  aeconst_of_forall_preimage_smul_ae_eq := h.aeconst_of_forall_preimage_smul_ae_eq

end SMul

section Monoid

variable [Monoid M] [MulAction M X] [MeasurableConstSMul M X] [SMul M Y] [Countable M]

/-- **Invariant conull realization.** A factor map of actions of a countable monoid acting by
measurable quasi-measure-preserving maps intertwines every parameter exactly on a measurable
conull set that is forward invariant under the action. -/
@[to_additive /-- **Invariant conull realization.** A factor map of additive actions of a
countable additive monoid acting by measurable quasi-measure-preserving maps intertwines every
parameter exactly on a measurable conull set that is forward invariant under the action. -/]
theorem exists_measurableSet_mapsTo_smul (h : IsFactorMapSMul M π μ ν)
    (hM : ∀ m : M, QuasiMeasurePreserving (m • ·) μ μ) :
    ∃ X₀ : Set X, MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧ (∀ m : M, Set.MapsTo (m • ·) X₀ X₀) ∧
      ∀ m : M, ∀ x ∈ X₀, π (m • x) = m • π x := by
  obtain ⟨X₀, hm, h0, hmaps, hX₀⟩ := exists_measurableSet_mapsTo_smul_of_ae hM
    (p := fun x ↦ ∀ m : M, π (m • x) = m • π x) (ae_all_iff.mpr h.comp_smul_ae_eq)
  exact ⟨X₀, hm, h0, hmaps, fun m x hx ↦ hX₀ x hx m⟩

end Monoid

section Prod

variable {X' Y' : Type*} [MeasurableSpace X'] [MeasurableSpace Y'] {μ' : Measure X'}
  {ν' : Measure Y'} {π' : X' → Y'} [SMul M X] [SMul M Y] [SMul M X'] [SMul M Y']

/-- The product of two factor maps is a factor map for the diagonal actions on the products. -/
@[to_additive prodMap /-- The product of two factor maps is a factor map for the diagonal additive
actions on the products. -/]
theorem prodMap [SFinite μ] [SFinite μ'] (h : IsFactorMapSMul M π μ ν)
    (h' : IsFactorMapSMul M π' μ' ν') :
    IsFactorMapSMul M (Prod.map π π') (μ.prod μ') (ν.prod ν') := by
  refine ⟨h.measurePreserving.prod h'.measurePreserving, fun m ↦ ?_⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp (h.comp_smul_ae_eq m),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (h'.comp_smul_ae_eq m)] with p h₁ h₂
  exact Prod.ext h₁ h₂

/-- The first coordinate projection is a factor map from the diagonal action on a product, the
second factor a probability space, to the first factor. -/
@[to_additive /-- The first coordinate projection is a factor map from the diagonal additive
action on a product, the second factor a probability space, to the first factor. -/]
protected theorem fst [IsProbabilityMeasure μ'] :
    IsFactorMapSMul M Prod.fst (μ.prod μ') μ :=
  of_map_smul measurePreserving_fst fun _ _ ↦ rfl

/-- The second coordinate projection is a factor map from the diagonal action on a product, the
first factor a probability space, to the second factor. -/
@[to_additive /-- The second coordinate projection is a factor map from the diagonal additive
action on a product, the first factor a probability space, to the second factor. -/]
protected theorem snd [IsProbabilityMeasure μ] [SFinite μ'] :
    IsFactorMapSMul M Prod.snd (μ.prod μ') μ' :=
  of_map_smul measurePreserving_snd fun _ _ ↦ rfl

end Prod

end IsFactorMapSMul

/-- For a countable monoid acting by measurable quasi-measure-preserving maps, a
measure-preserving map is a factor map of the actions exactly when it intertwines every parameter
on a measurable conull set that is forward invariant under the action. -/
@[to_additive /-- For a countable additive monoid acting by measurable quasi-measure-preserving
maps, a measure-preserving map is a factor map of the additive actions exactly when it intertwines
every parameter on a measurable conull set that is forward invariant under the action. -/]
theorem isFactorMapSMul_iff_exists_measurableSet [Monoid M] [MulAction M X]
    [MeasurableConstSMul M X] [SMul M Y] [Countable M]
    (hM : ∀ m : M, QuasiMeasurePreserving (m • ·) μ μ)
    (hπ : MeasurePreserving π μ ν) :
    IsFactorMapSMul M π μ ν ↔ ∃ X₀ : Set X, MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧
      (∀ m : M, Set.MapsTo (m • ·) X₀ X₀) ∧ ∀ m : M, ∀ x ∈ X₀, π (m • x) = m • π x :=
  ⟨fun h ↦ h.exists_measurableSet_mapsTo_smul hM, fun ⟨_, _, h0, _, h⟩ ↦
    .of_measure_compl_eq_zero hπ h0 h⟩

end TauCeti
