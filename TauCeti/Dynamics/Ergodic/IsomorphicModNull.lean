/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Dynamics.Ergodic.Factor
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Isomorphism of measure-preserving systems mod 0

Two systems `T : X → X` on `(X, μ)` and `S : Y → Y` on `(Y, ν)` are *isomorphic mod 0* when, after
discarding null sets, they are conjugate by a measure-preserving bijection. Here an
`IsomorphismModNull T μ S ν` records measurable conull sets `X₀ ⊆ X`, `Y₀ ⊆ Y` invariant under `T`
and `S`, and measure-preserving maps `X → Y`, `Y → X` that restrict to mutually inverse bijections
`X₀ ≃ Y₀` and conjugate `T` to `S` on `X₀`. The restricted bijection is a measurable equivalence
`X₀ ≃ᵐ Y₀` preserving the restricted measures and conjugating the restrictions of `T` and `S`
(`IsomorphismModNull.toMeasurableEquiv`); recording it through maps on the whole spaces makes the
composition of isomorphisms a matter of intersecting conull sets.

## Main definitions

* `TauCeti.IsomorphismModNull T μ S ν`: an isomorphism mod 0 of the two systems.
* `TauCeti.IsIsomorphicModNull T μ S ν`: there is an isomorphism mod 0.

## Main results

* `TauCeti.IsIsomorphicModNull.refl`, `.symm`, `.trans`: isomorphism mod 0 is an equivalence
  relation.
* `TauCeti.IsomorphismModNull.ofMeasurableEquiv`: a measure-preserving conjugacy `X ≃ᵐ Y` is an
  isomorphism mod 0.
* `TauCeti.IsomorphismModNull.toMeasurableEquiv`: the measurable equivalence `X₀ ≃ᵐ Y₀` of the
  conull invariant sets, which preserves the restricted measures
  (`IsomorphismModNull.measurePreserving_toMeasurableEquiv`) and conjugates the restricted systems
  (`IsomorphismModNull.toMeasurableEquiv_restrict`).
* `TauCeti.IsomorphismModNull.isFactorMap`: both maps of an isomorphism mod 0 are factor maps.
* `TauCeti.IsIsomorphicModNull.ergodic_iff`: ergodicity is invariant under isomorphism mod 0.
* `TauCeti.not_isIsomorphicModNull_id_not`: on two points of equal mass the identity and the
  swap are not isomorphic mod 0 (the swap is ergodic, the identity is not), although both preserve
  the measure.

## References

This is the isomorphism part of §0.1 of the Tau Ceti roadmap `ClassicalErgodicTheory`.
-/

public section

namespace TauCeti

open MeasureTheory Function Set

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} {ρ : Measure Z} {T : X → X} {S : Y → Y} {R : Z → Z}

/-- An isomorphism mod 0 from the system `T` on `(X, μ)` to the system `S` on `(Y, ν)`: measurable
conull sets `source ⊆ X`, `target ⊆ Y` invariant under `T` and `S`, and measure-preserving maps
`toFun : X → Y`, `invFun : Y → X` restricting to mutually inverse bijections between `source` and
`target`, with `toFun ∘ T = S ∘ toFun` on `source`. -/
structure IsomorphismModNull (T : X → X) (μ : Measure X) (S : Y → Y) (ν : Measure Y) where
  /-- The forward map. -/
  toFun : X → Y
  /-- The inverse map. -/
  invFun : Y → X
  /-- The conull invariant set of `X` on which `toFun` is a bijection. -/
  source : Set X
  /-- The conull invariant set of `Y` on which `invFun` is a bijection. -/
  target : Set Y
  /-- The source is measurable. -/
  measurableSet_source : MeasurableSet source
  /-- The target is measurable. -/
  measurableSet_target : MeasurableSet target
  /-- The source is conull. -/
  measure_compl_source : μ sourceᶜ = 0
  /-- The target is conull. -/
  measure_compl_target : ν targetᶜ = 0
  /-- The source is invariant under `T`. -/
  mapsTo_source : MapsTo T source source
  /-- The target is invariant under `S`. -/
  mapsTo_target : MapsTo S target target
  /-- The forward map sends the source to the target. -/
  mapsTo_toFun : MapsTo toFun source target
  /-- The inverse map sends the target to the source. -/
  mapsTo_invFun : MapsTo invFun target source
  /-- The inverse map is a left inverse on the source. -/
  invFun_toFun : ∀ x ∈ source, invFun (toFun x) = x
  /-- The inverse map is a right inverse on the target. -/
  toFun_invFun : ∀ y ∈ target, toFun (invFun y) = y
  /-- The forward map is measure-preserving. -/
  measurePreserving_toFun : MeasurePreserving toFun μ ν
  /-- The inverse map is measure-preserving. -/
  measurePreserving_invFun : MeasurePreserving invFun ν μ
  /-- The forward map conjugates `T` to `S` on the source. -/
  toFun_comp : ∀ x ∈ source, toFun (T x) = S (toFun x)

/-- The systems `T` on `(X, μ)` and `S` on `(Y, ν)` are isomorphic mod 0: there is an
`IsomorphismModNull T μ S ν`. -/
def IsIsomorphicModNull (T : X → X) (μ : Measure X) (S : Y → Y) (ν : Measure Y) : Prop :=
  Nonempty (IsomorphismModNull T μ S ν)

namespace IsomorphismModNull

/-- The inverse map conjugates `S` to `T` on the target. -/
theorem invFun_comp (e : IsomorphismModNull T μ S ν) {y : Y} (hy : y ∈ e.target) :
    e.invFun (S y) = T (e.invFun y) := by
  have hx := e.mapsTo_invFun hy
  rw [← e.invFun_toFun _ (e.mapsTo_source hx), e.toFun_comp _ hx, e.toFun_invFun _ hy]

/-- The identity isomorphism mod 0 of a system. -/
@[expose, simps]
protected def refl (T : X → X) (μ : Measure X) : IsomorphismModNull T μ T μ where
  toFun := id
  invFun := id
  source := univ
  target := univ
  measurableSet_source := .univ
  measurableSet_target := .univ
  measure_compl_source := by simp
  measure_compl_target := by simp
  mapsTo_source := mapsTo_univ _ _
  mapsTo_target := mapsTo_univ _ _
  mapsTo_toFun := mapsTo_univ _ _
  mapsTo_invFun := mapsTo_univ _ _
  invFun_toFun _ _ := rfl
  toFun_invFun _ _ := rfl
  measurePreserving_toFun := .id μ
  measurePreserving_invFun := .id μ
  toFun_comp _ _ := rfl

/-- The inverse of an isomorphism mod 0. -/
@[expose, simps]
protected def symm (e : IsomorphismModNull T μ S ν) : IsomorphismModNull S ν T μ where
  toFun := e.invFun
  invFun := e.toFun
  source := e.target
  target := e.source
  measurableSet_source := e.measurableSet_target
  measurableSet_target := e.measurableSet_source
  measure_compl_source := e.measure_compl_target
  measure_compl_target := e.measure_compl_source
  mapsTo_source := e.mapsTo_target
  mapsTo_target := e.mapsTo_source
  mapsTo_toFun := e.mapsTo_invFun
  mapsTo_invFun := e.mapsTo_toFun
  invFun_toFun := e.toFun_invFun
  toFun_invFun := e.invFun_toFun
  measurePreserving_toFun := e.measurePreserving_invFun
  measurePreserving_invFun := e.measurePreserving_toFun
  toFun_comp _ hy := e.invFun_comp hy

/-- The composition of two isomorphisms mod 0. The new conull sets are the points of `source` whose
image lies in the second source, and the points of the second target whose inverse image lies in
`target`. -/
@[expose, simps]
protected def trans (e : IsomorphismModNull T μ S ν) (f : IsomorphismModNull S ν R ρ) :
    IsomorphismModNull T μ R ρ where
  toFun := f.toFun ∘ e.toFun
  invFun := e.invFun ∘ f.invFun
  source := e.source ∩ e.toFun ⁻¹' f.source
  target := f.target ∩ f.invFun ⁻¹' e.target
  measurableSet_source :=
    e.measurableSet_source.inter (e.measurePreserving_toFun.measurable f.measurableSet_source)
  measurableSet_target :=
    f.measurableSet_target.inter (f.measurePreserving_invFun.measurable e.measurableSet_target)
  measure_compl_source := by
    rw [compl_inter, ← preimage_compl]
    refine measure_union_null e.measure_compl_source ?_
    rw [e.measurePreserving_toFun.measure_preimage f.measurableSet_source.compl.nullMeasurableSet]
    exact f.measure_compl_source
  measure_compl_target := by
    rw [compl_inter, ← preimage_compl]
    refine measure_union_null f.measure_compl_target ?_
    rw [f.measurePreserving_invFun.measure_preimage e.measurableSet_target.compl.nullMeasurableSet]
    exact e.measure_compl_target
  mapsTo_source x hx :=
    ⟨e.mapsTo_source hx.1, by
      rw [mem_preimage, e.toFun_comp _ hx.1]
      exact f.mapsTo_source hx.2⟩
  mapsTo_target y hy :=
    ⟨f.mapsTo_target hy.1, by
      rw [mem_preimage, f.invFun_comp hy.1]
      exact e.mapsTo_target hy.2⟩
  mapsTo_toFun x hx :=
    ⟨f.mapsTo_toFun hx.2, by
      rw [mem_preimage, comp_apply, f.invFun_toFun _ hx.2]
      exact e.mapsTo_toFun hx.1⟩
  mapsTo_invFun y hy :=
    ⟨e.mapsTo_invFun hy.2, by
      rw [mem_preimage, comp_apply, e.toFun_invFun _ hy.2]
      exact f.mapsTo_invFun hy.1⟩
  invFun_toFun x hx := by
    simp only [comp_apply, f.invFun_toFun _ hx.2, e.invFun_toFun _ hx.1]
  toFun_invFun y hy := by
    simp only [comp_apply, e.toFun_invFun _ hy.2, f.toFun_invFun _ hy.1]
  measurePreserving_toFun := f.measurePreserving_toFun.comp e.measurePreserving_toFun
  measurePreserving_invFun := e.measurePreserving_invFun.comp f.measurePreserving_invFun
  toFun_comp x hx := by
    rw [comp_apply, comp_apply, e.toFun_comp _ hx.1, f.toFun_comp _ hx.2]

/-- A measure-preserving measurable equivalence conjugating `T` to `S` is an isomorphism mod 0,
with full source and target. -/
@[expose, simps]
def ofMeasurableEquiv (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (h : Semiconj e T S) :
    IsomorphismModNull T μ S ν where
  toFun := e
  invFun := e.symm
  source := univ
  target := univ
  measurableSet_source := .univ
  measurableSet_target := .univ
  measure_compl_source := by simp
  measure_compl_target := by simp
  mapsTo_source := mapsTo_univ _ _
  mapsTo_target := mapsTo_univ _ _
  mapsTo_toFun := mapsTo_univ _ _
  mapsTo_invFun := mapsTo_univ _ _
  invFun_toFun x _ := e.symm_apply_apply x
  toFun_invFun y _ := e.apply_symm_apply y
  measurePreserving_toFun := he
  measurePreserving_invFun := he.symm e
  toFun_comp x _ := h x

/-- The forward map of an isomorphism mod 0 is a factor map. -/
theorem isFactorMap (e : IsomorphismModNull T μ S ν) : IsFactorMap e.toFun T S μ ν where
  measurePreserving := e.measurePreserving_toFun
  comp_ae_eq := by
    filter_upwards [mem_ae_iff.mpr e.measure_compl_source] with x hx
    exact e.toFun_comp x hx

/-- The inverse map of an isomorphism mod 0 is a factor map. -/
theorem isFactorMap_invFun (e : IsomorphismModNull T μ S ν) : IsFactorMap e.invFun S T ν μ :=
  e.symm.isFactorMap

/-- The forward map of an isomorphism mod 0 is measurable. -/
theorem measurable_toFun (e : IsomorphismModNull T μ S ν) : Measurable e.toFun :=
  e.measurePreserving_toFun.measurable

/-- The inverse map of an isomorphism mod 0 is measurable. -/
theorem measurable_invFun (e : IsomorphismModNull T μ S ν) : Measurable e.invFun :=
  e.measurePreserving_invFun.measurable

/-- The measurable equivalence between the conull invariant sets given by an isomorphism mod 0. -/
@[expose] def toMeasurableEquiv (e : IsomorphismModNull T μ S ν) : e.source ≃ᵐ e.target where
  toFun := e.mapsTo_toFun.restrict
  invFun := e.mapsTo_invFun.restrict
  left_inv x := Subtype.ext (e.invFun_toFun x x.property)
  right_inv y := Subtype.ext (e.toFun_invFun y y.property)
  measurable_toFun := (e.measurable_toFun.comp measurable_subtypeVal).subtype_mk
  measurable_invFun := (e.measurable_invFun.comp measurable_subtypeVal).subtype_mk

@[simp]
theorem coe_toMeasurableEquiv_apply (e : IsomorphismModNull T μ S ν) (x : e.source) :
    (e.toMeasurableEquiv x : Y) = e.toFun x :=
  rfl

@[simp]
theorem coe_toMeasurableEquiv_symm_apply (e : IsomorphismModNull T μ S ν) (y : e.target) :
    (e.toMeasurableEquiv.symm y : X) = e.invFun y :=
  rfl

/-- The measurable equivalence of an isomorphism mod 0 preserves the measures restricted to the
conull invariant sets. -/
theorem measurePreserving_toMeasurableEquiv (e : IsomorphismModNull T μ S ν) :
    MeasurePreserving e.toMeasurableEquiv (μ.comap (↑)) (ν.comap (↑)) := by
  refine ⟨e.toMeasurableEquiv.measurable, Measure.ext fun A hA ↦ ?_⟩
  have hA' : MeasurableSet ((↑) '' A : Set Y) :=
    (MeasurableEmbedding.subtypeVal e.measurableSet_target).measurableSet_image.mpr hA
  rw [Measure.map_apply e.toMeasurableEquiv.measurable hA,
    comap_subtypeVal_apply e.measurableSet_source,
    comap_subtypeVal_apply e.measurableSet_target,
    ← e.measurePreserving_toFun.measure_preimage hA'.nullMeasurableSet]
  have hset : ((↑) '' (e.toMeasurableEquiv ⁻¹' A) : Set X) =
      e.toFun ⁻¹' ((↑) '' A) ∩ e.source := by
    ext x
    constructor
    · rintro ⟨⟨x, hx⟩, hA, rfl⟩
      exact ⟨⟨e.toMeasurableEquiv ⟨x, hx⟩, hA, rfl⟩, hx⟩
    · rintro ⟨⟨y, hy, hyx⟩, hx⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      have : e.toMeasurableEquiv ⟨x, hx⟩ = y := Subtype.ext hyx.symm
      rwa [mem_preimage, this]
  rw [hset]
  exact measure_inter_conull e.measure_compl_source

/-- The measurable equivalence of an isomorphism mod 0 conjugates the restrictions of the two
systems to the conull invariant sets. -/
theorem toMeasurableEquiv_restrict (e : IsomorphismModNull T μ S ν) (x : e.source) :
    e.toMeasurableEquiv (MapsTo.restrict T e.source e.source e.mapsTo_source x) =
      MapsTo.restrict S e.target e.target e.mapsTo_target (e.toMeasurableEquiv x) :=
  Subtype.ext (e.toFun_comp x x.property)

end IsomorphismModNull

namespace IsIsomorphicModNull

/-- Every system is isomorphic mod 0 to itself. -/
protected theorem refl (T : X → X) (μ : Measure X) : IsIsomorphicModNull T μ T μ :=
  ⟨.refl T μ⟩

/-- Isomorphism mod 0 is symmetric. -/
protected theorem symm (h : IsIsomorphicModNull T μ S ν) : IsIsomorphicModNull S ν T μ :=
  h.map IsomorphismModNull.symm

/-- Isomorphism mod 0 is transitive. -/
protected theorem trans (h : IsIsomorphicModNull T μ S ν) (h' : IsIsomorphicModNull S ν R ρ) :
    IsIsomorphicModNull T μ R ρ :=
  h.elim fun e ↦ h'.elim fun f ↦ ⟨e.trans f⟩

/-- Systems that are conjugate by a measure-preserving measurable equivalence are isomorphic
mod 0. -/
theorem of_measurableEquiv (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (h : Semiconj e T S) :
    IsIsomorphicModNull T μ S ν :=
  ⟨.ofMeasurableEquiv e he h⟩

/-- Pre-ergodicity is invariant under isomorphism mod 0. -/
theorem preErgodic_iff (h : IsIsomorphicModNull T μ S ν) : PreErgodic T μ ↔ PreErgodic S ν :=
  h.elim fun e ↦ ⟨e.isFactorMap.preErgodic, e.isFactorMap_invFun.preErgodic⟩

/-- Ergodicity is invariant under isomorphism mod 0 of systems given by measurable maps. -/
theorem ergodic_iff (h : IsIsomorphicModNull T μ S ν) (hT : Measurable T) (hS : Measurable S) :
    Ergodic T μ ↔ Ergodic S ν :=
  h.elim fun e ↦ ⟨fun h ↦ e.isFactorMap.ergodic h hS, fun h ↦ e.isFactorMap_invFun.ergodic h hT⟩

end IsIsomorphicModNull

section Check

/-- The swap of two points of equal mass is ergodic. -/
theorem ergodic_not_count : Ergodic not (Measure.count : Measure Bool) := by
  have hmp : MeasurePreserving not (Measure.count : Measure Bool) Measure.count := by
    refine ⟨measurable_from_top, Measure.ext_iff_singleton.mpr fun b ↦ ?_⟩
    rw [Measure.map_apply measurable_from_top (measurableSet_singleton b),
      show not ⁻¹' {b} = {!b} by ext c; cases b <;> cases c <;> simp]
    simp
  refine ⟨hmp, ⟨fun s _ hs ↦ ?_⟩⟩
  have hs' : ∀ b, b ∈ s ↔ (!b) ∈ s := fun b ↦ by
    have := Measure.ae_count_iff.mp hs b
    simpa [eq_comm] using this.symm
  by_cases htrue : true ∈ s
  · have hfalse : false ∈ s := (hs' true).mp htrue
    have : s = univ := eq_univ_of_forall fun b ↦ by cases b <;> assumption
    rw [this]
    exact Filter.EventuallyConst.const _
  · have hfalse : false ∉ s := fun h ↦ htrue ((hs' false).mp h)
    have : s = ∅ := eq_empty_of_forall_notMem fun b ↦ by cases b <;> assumption
    rw [this]
    exact Filter.EventuallyConst.const _

/-- The identity of two points of equal mass is not ergodic. -/
theorem not_ergodic_id_count : ¬ Ergodic id (Measure.count : Measure Bool) := by
  intro h
  rcases h.measure_self_or_compl_eq_zero (s := {true}) (measurableSet_singleton _).nullMeasurableSet
    (by simp) with h₁ | h₁
  · simp at h₁
  · rw [show ({true} : Set Bool)ᶜ = {false} by ext b; cases b <;> simp] at h₁
    simp at h₁

/-- On two points of equal mass, the identity and the swap both preserve the measure but are not
isomorphic mod 0: the swap is ergodic and the identity is not. -/
theorem not_isIsomorphicModNull_id_not :
    ¬ IsIsomorphicModNull id (Measure.count : Measure Bool) not Measure.count := fun h ↦
  not_ergodic_id_count ((h.ergodic_iff measurable_id measurable_from_top).mpr ergodic_not_count)

end Check

end TauCeti
