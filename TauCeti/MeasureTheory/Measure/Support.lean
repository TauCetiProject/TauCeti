/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Topological support under products, scalar multiplication and continuous maps

This file identifies the support of a nonzero scalar multiple of a measure and the support of a
pushforward by a continuous map. It also shows that pushing a measure forward along a
homeomorphism transports its topological support onto the image of the original support.
Finite products have the product of the supports of their factors. A measurable map that is
continuous at a source support point sends that point into the support of the pushforward;
global continuity is unnecessary for this inclusion.

## Main result

* `MeasureTheory.Measure.support_smul_measure` — multiplying a measure by a nonzero scalar
  preserves its support.
* `MeasureTheory.Measure.support_map_eq_closure_image` — a continuous pushforward has support
  equal to the closure of the image of the support, when the source support has full measure.
* `MeasureTheory.Measure.support_map_eq_closure_range` — a continuous image of a full-support
  measure has support equal to the closure of the map's range.
* `MeasureTheory.Measure.support_map_homeomorph` — the support of a pushforward by a homeomorphism
  is the image of the original support.
-/

public section

open Set
open scoped ENNReal Topology

namespace MeasureTheory.Measure

/-- The support of a finite product of sigma-finite measures is the product of their supports.
No compatibility between the topologies and measurable structures is needed. -/
@[simp]
theorem support_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, TopologicalSpace (α i)] [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    (Measure.pi μ).support = Set.univ.pi (fun i ↦ (μ i).support) := by
  classical
  ext x
  simp only [Set.mem_univ_pi, mem_support_iff_forall]
  constructor
  · intro hx i U hU
    let V : ∀ j, Set (α j) := Function.update (fun _ ↦ Set.univ) i U
    have hV : ∀ j, V j ∈ 𝓝 (x j) := by
      intro j
      by_cases h : j = i
      · subst j
        simpa [V] using hU
      · simp [V, h]
    have hpos := hx (Set.univ.pi V) (set_pi_mem_nhds Set.finite_univ fun j _ ↦ hV j)
    rw [Measure.pi_pi] at hpos
    have hi := Finset.prod_ne_zero_iff.mp hpos.ne' i (Finset.mem_univ i)
    exact pos_iff_ne_zero.mpr (by simpa [V] using hi)
  · intro hx U hU
    rw [nhds_pi] at hU
    obtain ⟨I, _, V, hV, hsub⟩ := Filter.mem_pi.mp hU
    have hpos : 0 < Measure.pi μ (Set.univ.pi V) := by
      rw [Measure.pi_pi]
      exact pos_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun i _ ↦
        (hx i (V i) (hV i)).ne'
    exact hpos.trans_le (measure_mono fun y hy ↦ hsub fun i _ ↦ hy i (Set.mem_univ i))

/-- A measurable map continuous at a source support point sends it into the support of the
pushforward, even if the map is discontinuous elsewhere. -/
theorem mem_support_map_of_continuousAt {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    {μ : Measure X} {f : X → Y} {x : X}
    (hf : AEMeasurable f μ) (hfx : ContinuousAt f x) (hx : x ∈ μ.support) :
    f x ∈ (μ.map f).support := by
  rw [mem_support_iff_forall]
  intro U hU
  exact ((mem_support_iff_forall x).mp hx _ (hfx hU)).trans_le (Measure.le_map_apply hf U)

/-- Multiplying a measure by a nonzero `ℝ≥0∞` scalar preserves its topological support. -/
theorem support_smul_measure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (c : ℝ≥0∞) (μ : Measure X) (hc : c ≠ 0) :
    (c • μ).support = μ.support := by
  rw [support_eq_forall_isOpen, support_eq_forall_isOpen]
  ext x
  simp only [Set.mem_ofPred_eq, smul_apply, smul_eq_mul]
  constructor <;> intro h U hxU hU
  · exact (ENNReal.mul_pos_iff.mp (h U hxU hU)).2
  · exact ENNReal.mul_pos_iff.mpr ⟨pos_iff_ne_zero.mpr hc, h U hxU hU⟩

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The support of a continuous pushforward is the closure of the image of the support,
provided that the source support has full measure. -/
theorem support_map_eq_closure_image (μ : Measure X) (hμ : μ.support ∈ ae μ)
    {f : X → Y} (hf : Continuous f) :
    (μ.map f).support = closure (f '' μ.support) := by
  apply Set.Subset.antisymm
  · apply support_subset_of_isClosed isClosed_closure
    exact (ae_map_iff hf.measurable.aemeasurable isClosed_closure.measurableSet).2 <|
      (Filter.eventually_mem_set.mpr hμ).mono fun x hx ↦ subset_closure (mem_image_of_mem f hx)
  · refine closure_minimal ?_ isClosed_support
    rintro _ ⟨x, hx, rfl⟩
    rw [support_eq_forall_isOpen]
    intro U hxU hU
    rw [Measure.map_apply hf.measurable hU.measurableSet]
    exact (mem_support_iff_forall x).mp hx (f ⁻¹' U)
      ((hU.preimage hf).mem_nhds hxU)

/-- The support of the pushforward of a full-support measure by a continuous map is the closure of
the map's range. No injectivity, surjectivity, or properness hypothesis is needed. -/
theorem support_map_eq_closure_range (μ : Measure X) {f : X → Y} (hμ : μ.support = Set.univ)
    (hf : Continuous f) : (μ.map f).support = closure (Set.range f) := by
  rw [support_map_eq_closure_image μ (by simp [hμ]) hf, hμ, image_univ]

/-- A homeomorphism carries the support of a measure onto the support of its pushforward. -/
theorem support_map_homeomorph (μ : Measure X) (e : X ≃ₜ Y) :
    (μ.map e).support = e '' μ.support := by
  ext y
  rw [Measure.support_eq_forall_isOpen, e.image_eq_preimage_symm, Set.mem_preimage,
    Measure.support_eq_forall_isOpen]
  constructor
  · intro hy U hyU hU
    have hey : y ∈ e '' U := ⟨e.symm y, hyU, e.apply_symm_apply y⟩
    have heU : IsOpen (e '' U) := e.isOpenMap U hU
    have hpos := hy (e '' U) hey heU
    rw [Measure.map_apply e.measurable heU.measurableSet, e.preimage_image] at hpos
    exact hpos
  · intro hx U hyU hU
    rw [Measure.map_apply e.measurable hU.measurableSet]
    exact hx (e ⁻¹' U) (by simpa) (hU.preimage e.continuous)

end MeasureTheory.Measure
