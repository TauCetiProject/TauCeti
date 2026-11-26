/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Membership
public import TauCeti.Dynamics.Ergodic.Action.Factor

/-!
# Factor maps of actions from generators

A measure-preserving map `π` that intertwines almost everywhere the parameters in a generating
set of a monoid `M` is a factor map of the `M`-actions, provided these generators act
quasi-measure-preservingly on the source (`TauCeti.IsFactorMapSMul.of_submonoidClosure_eq_top`).
For a group it suffices to intertwine a generating set of the group whose elements and their
inverses act quasi-measure-preservingly on the source
(`TauCeti.IsFactorMapSMul.of_subgroupClosure_eq_top`), since a map intertwining `g` also
intertwines `g⁻¹` (`MeasureTheory.QuasiMeasurePreserving.comp_inv_smul_ae_eq`).

This identifies the action interface for `ℕ` and `ℤ` with the interface for a single map
`TauCeti.IsFactorMap` applied to the generator `1 +ᵥ ·`
(`TauCeti.isFactorMapVAdd_nat_iff`, `TauCeti.isFactorMapVAdd_int_iff`): a map, through its
iterates, and an invertible map, through its integer powers.
-/

public section

open MeasureTheory Filter Function
open scoped Pointwise

variable {M G X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
  {ν : Measure Y} {π : X → Y}

namespace MeasureTheory.QuasiMeasurePreserving

omit [MeasurableSpace Y] in
/-- If `π` intertwines `g • ·` almost everywhere and `g⁻¹ • ·` is quasi-measure-preserving on the
source, then `π` intertwines `g⁻¹ • ·` almost everywhere. -/
@[to_additive /-- If `π` intertwines `g +ᵥ ·` almost everywhere and `-g +ᵥ ·` is
quasi-measure-preserving on the source, then `π` intertwines `-g +ᵥ ·` almost everywhere. -/]
theorem comp_inv_smul_ae_eq [Group G] [MulAction G X] [MulAction G Y] {g : G}
    (hg : QuasiMeasurePreserving (g⁻¹ • · : X → X) μ μ)
    (h : π ∘ (g • ·) =ᵐ[μ] (g • ·) ∘ π) :
    π ∘ (g⁻¹ • ·) =ᵐ[μ] (g⁻¹ • ·) ∘ π := by
  filter_upwards [(hg.ae_eq_comp h).fun_comp (g⁻¹ • ·)] with x hx
  simpa using hx.symm

end MeasureTheory.QuasiMeasurePreserving

namespace TauCeti

namespace IsFactorMapSMul

/-- **Factor maps from generators of a monoid.** A measure-preserving map that intertwines almost
everywhere every parameter of a set `s` generating the monoid `M` is a factor map of the
`M`-actions, if every parameter in `s` is quasi-measure-preserving on the source. -/
@[to_additive /-- **Factor maps from generators of an additive monoid.** A measure-preserving map
that intertwines almost everywhere every parameter of a set `s` generating the additive monoid
`M` is a factor map of the additive `M`-actions, if every parameter in `s` is
quasi-measure-preserving on the source. -/]
theorem of_submonoidClosure_eq_top [Monoid M] [MulAction M X] [MulAction M Y]
    (hπ : MeasurePreserving π μ ν) {s : Set M}
    (hX : ∀ m ∈ s, QuasiMeasurePreserving (m • · : X → X) μ μ)
    (hs : Submonoid.closure s = ⊤) (h : ∀ m ∈ s, π ∘ (m • ·) =ᵐ[μ] (m • ·) ∘ π) :
    IsFactorMapSMul M π μ ν := by
  refine ⟨hπ, fun m ↦ ?_⟩
  have hm : m ∈ Submonoid.closure s := hs ▸ Submonoid.mem_top m
  suffices QuasiMeasurePreserving (m • · : X → X) μ μ ∧ π ∘ (m • ·) =ᵐ[μ] (m • ·) ∘ π from this.2
  induction hm using Submonoid.closure_induction with
  | mem m hm => exact ⟨hX m hm, h m hm⟩
  | one => exact ⟨by simp only [one_smul]; exact .id μ, .of_eq (funext fun x ↦ by simp)⟩
  | mul a b _ _ ha hb =>
    have hX' : (fun x : X ↦ (a * b) • x) = (a • ·) ∘ (b • ·) := funext fun x ↦ mul_smul a b x
    have hY' : (fun y : Y ↦ (a * b) • y) = (a • ·) ∘ (b • ·) := funext fun y ↦ mul_smul a b y
    rw [hX', hY']
    exact ⟨ha.1.comp hb.1, (hb.1.ae_eq_comp ha.2).trans (hb.2.fun_comp (a • ·))⟩

/-- **Factor maps from generators of a group.** A measure-preserving map that intertwines almost
everywhere every parameter of a set `s` generating the group `G` is a factor map of the
`G`-actions, if every parameter in `s` and its inverse are quasi-measure-preserving on the
source. -/
@[to_additive /-- **Factor maps from generators of an additive group.** A measure-preserving map
that intertwines almost everywhere every parameter of a set `s` generating the additive group `G`
is a factor map of the additive `G`-actions, if every parameter in `s` and its negative are
quasi-measure-preserving on the source. -/]
theorem of_subgroupClosure_eq_top [Group G] [MulAction G X] [MulAction G Y]
    (hπ : MeasurePreserving π μ ν) {s : Set G}
    (hX : ∀ g ∈ s, QuasiMeasurePreserving (g • · : X → X) μ μ ∧
      QuasiMeasurePreserving (g⁻¹ • · : X → X) μ μ)
    (hs : Subgroup.closure s = ⊤) (h : ∀ g ∈ s, π ∘ (g • ·) =ᵐ[μ] (g • ·) ∘ π) :
    IsFactorMapSMul G π μ ν := by
  refine of_submonoidClosure_eq_top hπ (s := s ∪ s⁻¹) (fun g hg ↦ ?_) ?_ fun g hg ↦ ?_
  · rcases hg with hg | hg
    · exact (hX g hg).1
    · simpa using (hX g⁻¹ hg).2
  · rw [← Subgroup.closure_toSubmonoid, hs, Subgroup.top_toSubmonoid]
  · rcases hg with hg | hg
    · exact h g hg
    · simpa using (hX g⁻¹ hg).2.comp_inv_smul_ae_eq (h g⁻¹ hg)

end IsFactorMapSMul

/-- **Factor maps of `ℕ`-actions.** For additive actions of `ℕ` whose generator `1 +ᵥ ·` is
quasi-measure-preserving on the source, a measure-preserving map is a factor map of the actions
exactly when it is a factor map of the single systems `1 +ᵥ ·`. -/
theorem isFactorMapVAdd_nat_iff [AddAction ℕ X] [AddAction ℕ Y]
    (hX : QuasiMeasurePreserving ((1 : ℕ) +ᵥ · : X → X) μ μ) :
    IsFactorMapVAdd ℕ π μ ν ↔ IsFactorMap π ((1 : ℕ) +ᵥ ·) ((1 : ℕ) +ᵥ ·) μ ν :=
  ⟨fun h ↦ h.toIsFactorMap 1, fun h ↦ IsFactorMapVAdd.of_addSubmonoidClosure_eq_top
    h.measurePreserving (s := {1}) (fun _ hn ↦ hn ▸ hX) (by simp) fun _ hn ↦ hn ▸ h.comp_ae_eq⟩

/-- **Factor maps of `ℤ`-actions.** For additive actions of `ℤ` whose parameters `1 +ᵥ ·` and
`-1 +ᵥ ·` are quasi-measure-preserving on the source, a measure-preserving map is a factor map of
the actions exactly when it is a factor map of the single systems `1 +ᵥ ·`. -/
theorem isFactorMapVAdd_int_iff [AddAction ℤ X] [AddAction ℤ Y]
    (hX : QuasiMeasurePreserving ((1 : ℤ) +ᵥ · : X → X) μ μ)
    (hX' : QuasiMeasurePreserving ((-1 : ℤ) +ᵥ · : X → X) μ μ) :
    IsFactorMapVAdd ℤ π μ ν ↔ IsFactorMap π ((1 : ℤ) +ᵥ ·) ((1 : ℤ) +ᵥ ·) μ ν :=
  ⟨fun h ↦ h.toIsFactorMap 1, fun h ↦ IsFactorMapVAdd.of_addSubgroupClosure_eq_top
    h.measurePreserving (s := {1}) (fun _ hn ↦ hn ▸ ⟨hX, hX'⟩)
    (by rw [← AddSubgroup.zmultiples_eq_closure, Int.zmultiples_one])
    fun _ hn ↦ hn ▸ h.comp_ae_eq⟩

end TauCeti
