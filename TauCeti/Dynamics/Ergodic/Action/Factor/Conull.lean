/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.Factor
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Invariant conull realizations of almost-everywhere intertwiners

A factor map intertwines each parameter of an action only almost everywhere, with a null set that
depends on the parameter. For a countable monoid acting by measurable quasi-measure-preserving
maps, these null sets can be removed at once: there is a measurable conull set `X₀`, forward
invariant under every parameter, on which the factor map intertwines every parameter exactly.
Conversely, a measure-preserving map that intertwines every parameter exactly on a conull set is a
factor map.
The same holds for a single measurable quasi-measure-preserving map.

The invariant set is `⋂ m, (m • ·) ⁻¹' E`, for a measurable conull set `E` on which the
intertwining identities hold: if `x` lies in it then so does `m • x`, since
`m' • (m • x) = (m' * m) • x`.

## Main results

* `TauCeti.exists_measurableSet_mapsTo_smul_of_ae`: for a countable monoid acting by
  quasi-measure-preserving maps, an almost-everywhere property holds on a measurable conull set
  that is forward invariant under the action.
* `TauCeti.IsFactorMapSMul.exists_measurableSet_mapsTo_smul`: the common invariant conull
  realization of a factor map of actions of a countable monoid;
  `TauCeti.isFactorMapSMul_iff_exists_measurableSet` is the equivalence with the conull-set
  definition.
* `TauCeti.exists_measurableSet_mapsTo_of_ae`, `TauCeti.IsFactorMap.exists_measurableSet_mapsTo`,
  `TauCeti.isFactorMap_iff_exists_measurableSet`: the same for a single map.

The additive versions are generated for actions of additive monoids such as `ℕ`, `ℤ` and flows.
-/

public section

namespace TauCeti

open MeasureTheory Set

variable {M X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {π : X → Y}

section Action

variable [Monoid M] [MulAction M X] [MeasurableConstSMul M X]

/-- For a countable monoid acting by quasi-measure-preserving maps, an almost-everywhere property
holds on a measurable conull set that is forward invariant under every parameter. -/
@[to_additive /-- For a countable additive monoid acting by quasi-measure-preserving maps, an
almost-everywhere property holds on a measurable conull set that is forward invariant under every
parameter. -/]
theorem exists_measurableSet_mapsTo_smul_of_ae [Countable M]
    (hM : ∀ m : M, QuasiMeasurePreserving (m • ·) μ μ) {p : X → Prop}
    (hp : ∀ᵐ x ∂μ, p x) :
    ∃ X₀ : Set X, MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧ (∀ m : M, MapsTo (m • ·) X₀ X₀) ∧
      ∀ x ∈ X₀, p x := by
  obtain ⟨N, hpN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  refine ⟨⋂ m : M, (m • ·) ⁻¹' Nᶜ, .iInter fun m ↦ measurable_const_smul m hNm.compl, ?_,
    fun m x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [compl_iInter]
    exact measure_iUnion_null fun m ↦ by
      rw [← preimage_compl, compl_compl]
      exact (hM m).preimage_null hN0
  · simp only [mem_iInter, mem_preimage] at hx ⊢
    intro m'
    rw [smul_smul]
    exact hx (m' * m)
  · have hx1 := mem_iInter.mp hx 1
    simp only [mem_preimage, one_smul, mem_compl_iff] at hx1
    by_contra h
    exact hx1 (hpN h)

/-- **Invariant conull realization.** A factor map of actions of a countable monoid acting by
quasi-measure-preserving maps intertwines every parameter exactly on a measurable conull set that
is forward invariant under the action. -/
@[to_additive /-- **Invariant conull realization.** A factor map of additive actions of a
countable additive monoid acting by quasi-measure-preserving maps intertwines every parameter
exactly on a measurable conull set that is forward invariant under the action. -/]
theorem IsFactorMapSMul.exists_measurableSet_mapsTo_smul [MulAction M Y] [Countable M]
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

/-- For a countable monoid acting by quasi-measure-preserving maps, a measure-preserving map is a
factor map of the actions exactly when it intertwines every parameter on a measurable conull set
that is forward invariant under the action. -/
@[to_additive /-- For a countable additive monoid acting by quasi-measure-preserving maps, a
measure-preserving map is a factor map of the additive actions exactly when it intertwines every
parameter on a measurable conull set that is forward invariant under the action. -/]
theorem isFactorMapSMul_iff_exists_measurableSet [Monoid M] [MulAction M X]
    [MeasurableConstSMul M X] [MulAction M Y] [Countable M]
    (hM : ∀ m : M, QuasiMeasurePreserving (m • ·) μ μ)
    (hπ : MeasurePreserving π μ ν) :
    IsFactorMapSMul M π μ ν ↔ ∃ X₀ : Set X, MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧
      (∀ m : M, MapsTo (m • ·) X₀ X₀) ∧ ∀ m : M, ∀ x ∈ X₀, π (m • x) = m • π x :=
  ⟨fun h ↦ h.exists_measurableSet_mapsTo_smul hM, fun ⟨_, _, h0, _, h⟩ ↦
    .of_measure_compl_eq_zero hπ h0 h⟩

section Map

variable {T : X → X} {S : Y → Y}

/-- For a quasi-measure-preserving map `T`, an almost-everywhere property holds on a measurable
conull set that is forward invariant under `T`. -/
theorem exists_measurableSet_mapsTo_of_ae (hTm : Measurable T) (hT : QuasiMeasurePreserving T μ μ)
    {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∃ X₀ : Set X, MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧ MapsTo T X₀ X₀ ∧ ∀ x ∈ X₀, p x := by
  obtain ⟨N, hpN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  refine ⟨⋂ n : ℕ, T^[n] ⁻¹' Nᶜ, .iInter fun n ↦ hTm.iterate n hNm.compl, ?_,
    fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [compl_iInter]
    exact measure_iUnion_null fun n ↦ by
      rw [← preimage_compl, compl_compl]
      exact (hT.iterate n).preimage_null hN0
  · simp only [mem_iInter, mem_preimage] at hx ⊢
    intro n
    rw [← Function.iterate_succ_apply]
    exact hx (n + 1)
  · have hx0 := mem_iInter.mp hx 0
    simp only [Function.iterate_zero, preimage_id, mem_compl_iff] at hx0
    by_contra h
    exact hx0 (hpN h)

/-- **Invariant conull realization for a single map.** A factor map from a quasi-measure-preserving
system `T` satisfies `π ∘ T = S ∘ π` on a measurable conull set that is forward invariant under
`T`. -/
theorem IsFactorMap.exists_measurableSet_mapsTo (h : IsFactorMap π T S μ ν) (hTm : Measurable T)
    (hT : QuasiMeasurePreserving T μ μ) :
    ∃ X₀ : Set X, MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧ MapsTo T X₀ X₀ ∧
      ∀ x ∈ X₀, π (T x) = S (π x) :=
  exists_measurableSet_mapsTo_of_ae hTm hT h.comp_ae_eq

/-- For a quasi-measure-preserving map `T`, a measure-preserving map `π` is a factor map exactly
when `π ∘ T = S ∘ π` on a measurable conull set that is forward invariant under `T`. -/
theorem isFactorMap_iff_exists_measurableSet (hTm : Measurable T)
    (hT : QuasiMeasurePreserving T μ μ) (hπ : MeasurePreserving π μ ν) :
    IsFactorMap π T S μ ν ↔ ∃ X₀ : Set X, MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧ MapsTo T X₀ X₀ ∧
      ∀ x ∈ X₀, π (T x) = S (π x) :=
  ⟨fun h ↦ h.exists_measurableSet_mapsTo hTm hT, fun ⟨_, _, h0, _, h⟩ ↦
    ⟨hπ, by filter_upwards [mem_ae_iff.mpr h0] with x hx using h x hx⟩⟩

end Map

end TauCeti
