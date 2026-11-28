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

Maps `f : α → β` and `g : β → α` that are mutually inverse almost everywhere are inverse on
measurable conull sets mapped into each other: take a conull set `X₁` on which `g ∘ f = id` and a
conull set `Y₀` on which `f ∘ g = id` and which `g` maps into `X₁`; then `X₁ ∩ f ⁻¹' Y₀` and `Y₀`
work.

## Main declarations

* `MeasureTheory.QuasiMeasurePreserving.of_map_le_smul`: an almost everywhere measurable map whose
  pushforward is dominated by a multiple of `ν` is quasi-measure preserving.
* `MeasureTheory.exists_measurableSet_mapsTo_smul_of_ae`: for a countable monoid acting by
  measurable quasi-measure-preserving maps, an almost-everywhere property holds on a measurable
  conull set that is forward invariant under the action; the additive version is
  `MeasureTheory.exists_measurableSet_mapsTo_vadd_of_ae`.
* `MeasureTheory.exists_measurableSet_mapsTo_of_ae`: the same for a single measurable
  quasi-measure-preserving map.
* `MeasureTheory.QuasiMeasurePreserving.measure_compl_inter_preimage_eq_zero`: `A ∩ f ⁻¹' B` is
  conull when `A` and `B` are.
* `MeasureTheory.QuasiMeasurePreserving.exists_measurableSet_invOn`: the common conull set
  `X₁ ∩ f ⁻¹' Y₀` of an almost-everywhere inverse pair, forward invariant under the maps that
  preserve `X₁` and that `f` intertwines on `X₁` with maps preserving `Y₀`.
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

open Set in
/-- For a quasi-measure-preserving `f`, the set `A ∩ f ⁻¹' B` is conull when `A` and `B` are. -/
theorem QuasiMeasurePreserving.measure_compl_inter_preimage_eq_zero
    (hf : QuasiMeasurePreserving f μ ν) {A : Set α} {B : Set β} (hA : μ Aᶜ = 0) (hB : ν Bᶜ = 0) :
    μ (A ∩ f ⁻¹' B)ᶜ = 0 := by
  rw [compl_inter, ← preimage_compl]
  exact measure_union_null hA (hf.preimage_null hB)

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

section InvOn

open Set

/-- **Common conull set of an almost-everywhere inverse pair.** Let `f` be measurable and
quasi-measure preserving, `X₁` a measurable conull set on which `g ∘ f = id`, and `Y₀` a
measurable conull set on which `f ∘ g = id` and which `g` maps into `X₁`. Then `X₁` contains a
measurable conull set `X₀` (namely `X₁ ∩ f ⁻¹' Y₀`) such that `f` maps `X₀` into `Y₀`, `g` maps
`Y₀` into `X₀`, and `f`, `g` are inverse there. If moreover maps `φ i` preserve `X₁`, maps `ψ i`
preserve `Y₀`, and `f ∘ φ i = ψ i ∘ f` on `X₁`, then every `φ i` preserves `X₀`. -/
theorem QuasiMeasurePreserving.exists_measurableSet_invOn {ι : Type*} {g : β → α}
    {φ : ι → α → α} {ψ : ι → β → β} (hf : QuasiMeasurePreserving f μ ν) (hfm : Measurable f)
    {X₁ : Set α} {Y₀ : Set β} (hX₁m : MeasurableSet X₁) (hX₁0 : μ X₁ᶜ = 0)
    (hX₁φ : ∀ i, MapsTo (φ i) X₁ X₁)
    (hX₁ : ∀ x ∈ X₁, g (f x) = x ∧ ∀ i, f (φ i x) = ψ i (f x)) (hY₀m : MeasurableSet Y₀)
    (hY₀0 : ν Y₀ᶜ = 0) (hY₀ψ : ∀ i, MapsTo (ψ i) Y₀ Y₀) (hY₀ : ∀ y ∈ Y₀, f (g y) = y ∧ g y ∈ X₁) :
    ∃ X₀ ⊆ X₁, MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧ (∀ i, MapsTo (φ i) X₀ X₀) ∧ MapsTo f X₀ Y₀ ∧
      MapsTo g Y₀ X₀ ∧ InvOn g f X₀ Y₀ := by
  refine ⟨X₁ ∩ f ⁻¹' Y₀, inter_subset_left, hX₁m.inter (hfm hY₀m),
    hf.measure_compl_inter_preimage_eq_zero hX₁0 hY₀0, fun i x hx ↦ ⟨hX₁φ i hx.1, ?_⟩,
    fun _ hx ↦ hx.2, fun y hy ↦ ⟨(hY₀ y hy).2, ?_⟩,
    ⟨fun x hx ↦ (hX₁ x hx.1).1, fun y hy ↦ (hY₀ y hy).1⟩⟩
  · rw [mem_preimage, (hX₁ x hx.1).2 i]
    exact hY₀ψ i hx.2
  · rw [mem_preimage, (hY₀ y hy).1]
    exact hy

end InvOn

end MeasureTheory
