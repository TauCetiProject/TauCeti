/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Quasi-measure-preserving maps

An almost everywhere measurable map `f` with `μ.map f ≤ C • ν` is quasi-measure preserving from `μ`
to `ν`, since domination by a multiple implies absolute continuity
(`MeasureTheory.Measure.absolutelyContinuous_of_le_smul`).

An almost-everywhere property holds on a measurable conull set that is forward invariant under a
countable monoid acting by measurable quasi-measure-preserving maps: the set is
`⋂ m, (m • ·) ⁻¹' E` for a measurable conull set `E` on which the property holds, and if `x` lies in
it then so does `m • x`, since `m' • (m • x) = (m' * m) • x`. A single map is the case of the
action of its iterates, `IterateMulAct`.

## Main declarations

* `MeasureTheory.QuasiMeasurePreserving.of_map_le_smul`: an almost everywhere measurable map whose
  pushforward is dominated by a multiple of `ν` is quasi-measure preserving.
* `MeasureTheory.exists_measurableSet_mapsTo_smul_of_ae`: for a countable monoid acting by
  measurable quasi-measure-preserving maps, an almost-everywhere property holds on a measurable
  conull set that is forward invariant under the action; the additive version is
  `MeasureTheory.exists_measurableSet_mapsTo_vadd_of_ae`.
* `MeasureTheory.exists_measurableSet_mapsTo_of_ae`: the same for a single measurable
  quasi-measure-preserving map.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {f : α → β} {C : ℝ≥0∞}

/-- An almost everywhere measurable map whose pushforward is dominated by a multiple of `ν` is
quasi-measure preserving. -/
theorem QuasiMeasurePreserving.of_map_le_smul (hf : AEMeasurable f μ) (hmap : μ.map f ≤ C • ν) :
    QuasiMeasurePreserving f μ ν :=
  ⟨hf, Measure.absolutelyContinuous_of_le_smul hmap⟩

section Invariant

open Set

variable {M X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- For a countable monoid acting by measurable quasi-measure-preserving maps, an
almost-everywhere property holds on a measurable conull set that is forward invariant under every
parameter. -/
@[to_additive /-- For a countable additive monoid acting by measurable quasi-measure-preserving
maps, an almost-everywhere property holds on a measurable conull set that is forward invariant
under every parameter. -/]
theorem exists_measurableSet_mapsTo_smul_of_ae [Monoid M] [MulAction M X]
    [MeasurableConstSMul M X] [Countable M] (hM : ∀ m : M, QuasiMeasurePreserving (m • ·) μ μ)
    {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) :
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

/-- For a measurable quasi-measure-preserving map `T`, an almost-everywhere property holds on a
measurable conull set that is forward invariant under `T`. -/
theorem exists_measurableSet_mapsTo_of_ae {T : X → X} (hTm : Measurable T)
    (hT : QuasiMeasurePreserving T μ μ) {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∃ X₀ : Set X, MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧ MapsTo T X₀ X₀ ∧ ∀ x ∈ X₀, p x := by
  have := measurableSMul_iterateMulAct.mpr hTm
  obtain ⟨X₀, hm, h0, hmaps, hp⟩ :=
    exists_measurableSet_mapsTo_smul_of_ae (M := IterateMulAct T)
      (fun ⟨n⟩ ↦ by simpa only [IterateMulAct.mk_smul] using hT.iterate n) hp
  refine ⟨X₀, hm, h0, ?_, hp⟩
  simpa only [IterateMulAct.mk_smul, Function.iterate_one] using hmaps (.mk 1)

end Invariant

end MeasureTheory
