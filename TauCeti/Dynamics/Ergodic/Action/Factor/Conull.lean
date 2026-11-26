/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.Factor
public import TauCeti.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Invariant conull realizations of almost-everywhere intertwiners

A factor map intertwines each parameter of an action only almost everywhere, with a null set that
depends on the parameter. For a countable monoid acting by measurable quasi-measure-preserving
maps, these null sets can be removed at once: there is a measurable conull set `X₀`, forward
invariant under every parameter, on which the factor map intertwines every parameter exactly.
Conversely, a measure-preserving map that intertwines every parameter exactly on a conull set is a
factor map. The invariant set comes from `MeasureTheory.exists_measurableSet_mapsTo_smul_of_ae`;
the single-map version is `TauCeti.isFactorMap_iff_exists_measurableSet`.

## Main results

* `TauCeti.IsFactorMapSMul.exists_measurableSet_mapsTo_smul`: the common invariant conull
  realization of a factor map of actions of a countable monoid;
  `TauCeti.isFactorMapSMul_iff_exists_measurableSet` is the equivalence with the conull-set
  definition.
* `TauCeti.IsFactorMapSMul.of_measure_compl_eq_zero`: the converse, for actions of any parameter
  type.

The additive versions are generated for actions of additive monoids. The realization needs a
countable monoid, such as `ℕ` or `ℤ`; for uncountable ones, such as the `ℝ`-parameter of a flow,
only the converse `TauCeti.IsFactorMapVAdd.of_measure_compl_eq_zero` applies.
-/

public section

namespace TauCeti

open MeasureTheory Set

variable {M X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {π : X → Y}

section Action

variable [Monoid M] [MulAction M X] [MeasurableConstSMul M X]

/-- **Invariant conull realization.** A factor map of actions of a countable monoid acting by
measurable quasi-measure-preserving maps intertwines every parameter exactly on a measurable
conull set that is forward invariant under the action. -/
@[to_additive /-- **Invariant conull realization.** A factor map of additive actions of a
countable additive monoid acting by measurable quasi-measure-preserving maps intertwines every
parameter exactly on a measurable conull set that is forward invariant under the action. -/]
theorem IsFactorMapSMul.exists_measurableSet_mapsTo_smul [SMul M Y] [Countable M]
    (h : IsFactorMapSMul M π μ ν) (hM : ∀ m : M, QuasiMeasurePreserving (m • ·) μ μ) :
    ∃ X₀ : Set X, MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧ (∀ m : M, MapsTo (m • ·) X₀ X₀) ∧
      ∀ m : M, ∀ x ∈ X₀, π (m • x) = m • π x := by
  obtain ⟨X₀, hm, h0, hmaps, hX₀⟩ := exists_measurableSet_mapsTo_smul_of_ae hM
    (p := fun x ↦ ∀ m : M, π (m • x) = m • π x) (ae_all_iff.mpr h.comp_smul_ae_eq)
  exact ⟨X₀, hm, h0, hmaps, fun m x hx ↦ hX₀ x hx m⟩

end Action

/-- A measure-preserving map that intertwines every parameter exactly on a conull set is a factor
map of the actions. -/
@[to_additive /-- A measure-preserving map that intertwines every parameter exactly on a conull
set is a factor map of the additive actions. -/]
theorem IsFactorMapSMul.of_measure_compl_eq_zero [SMul M X] [SMul M Y]
    (hπ : MeasurePreserving π μ ν) {X₀ : Set X} (h0 : μ X₀ᶜ = 0)
    (h : ∀ m : M, ∀ x ∈ X₀, π (m • x) = m • π x) : IsFactorMapSMul M π μ ν :=
  ⟨hπ, fun m ↦ by filter_upwards [mem_ae_iff.mpr h0] with x hx using h m x hx⟩

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
      (∀ m : M, MapsTo (m • ·) X₀ X₀) ∧ ∀ m : M, ∀ x ∈ X₀, π (m • x) = m • π x :=
  ⟨fun h ↦ h.exists_measurableSet_mapsTo_smul hM, fun ⟨_, _, h0, _, h⟩ ↦
    .of_measure_compl_eq_zero hπ h0 h⟩

end TauCeti
