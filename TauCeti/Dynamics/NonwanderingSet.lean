/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Homeomorph.Defs

/-!
# The non-wandering set of a self-map

A point `x` of a topological space is *non-wandering* for a self-map `f` when every neighbourhood
`U` of `x` meets its image `f^[n] '' U` under some iterate with `n ≥ 1`. This file defines the set
of non-wandering points and proves its basic properties.

## Main definitions

* `TauCeti.nonwanderingSet f`: the set of non-wandering points of `f`.

## Main results

* `TauCeti.isClosed_nonwanderingSet`: the non-wandering set is closed.
* `Function.IsPeriodicPt.mem_nonwanderingSet`: every periodic point is non-wandering.
* `Continuous.mapsTo_nonwanderingSet`: a continuous map sends the non-wandering set into itself;
  `Homeomorph.image_nonwanderingSet`: a homeomorphism maps it onto itself.
* `Homeomorph.nonwanderingSet_symm`: a homeomorphism and its inverse have the same non-wandering
  set.
* `MeasureTheory.Conservative.nonwanderingSet_eq_univ` and
  `MeasureTheory.MeasurePreserving.nonwanderingSet_eq_univ`: if `f` is conservative for a measure
  that is positive on nonempty open sets, for instance if it preserves a finite measure of full
  support, every point is non-wandering (topological Poincaré recurrence).
* `TauCeti.nonwanderingSet_eq_univ_of_dense`: if every point of a dense set is non-wandering, so
  is every point.

## References

* M. R. Herman, *Sur les courbes invariantes par les difféomorphismes de l'anneau*, Vol. 1,
  Astérisque 103-104, 1983, Chapitre I, 3.4.3 and 3.4.4.
-/

public section

open Set Filter Function MeasureTheory
open scoped Topology

variable {X : Type*} [TopologicalSpace X] {f g : X → X} {x : X} {s : Set X}

namespace TauCeti

/-- The non-wandering set of a self-map `f` of a topological space: the points `x` such that every
neighbourhood `U` of `x` meets its image `f^[n] '' U` under some iterate with `n ≥ 1`. -/
def nonwanderingSet (f : X → X) : Set X :=
  {x | ∀ U ∈ 𝓝 x, ∃ n : ℕ, 0 < n ∧ (f^[n] '' U ∩ U).Nonempty}

/-- Unfolding lemma for `nonwanderingSet`. -/
theorem mem_nonwanderingSet_iff :
    x ∈ nonwanderingSet f ↔ ∀ U ∈ 𝓝 x, ∃ n : ℕ, 0 < n ∧ (f^[n] '' U ∩ U).Nonempty :=
  Iff.rfl

/-- It suffices to test the open neighbourhoods. -/
theorem mem_nonwanderingSet_iff_isOpen :
    x ∈ nonwanderingSet f ↔
      ∀ U : Set X, IsOpen U → x ∈ U → ∃ n : ℕ, 0 < n ∧ (f^[n] '' U ∩ U).Nonempty := by
  refine ⟨fun h U hU hx ↦ h U (hU.mem_nhds hx), fun h U hU ↦ ?_⟩
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
  obtain ⟨n, hn, y, hy⟩ := h V hV hxV
  exact ⟨n, hn, y, image_mono hVU hy.1, hVU hy.2⟩

/-- A point is non-wandering when every neighbourhood `U` contains a point `y` with
`f^[n] y ∈ U` for some `n ≥ 1`. -/
theorem mem_nonwanderingSet_iff_exists_iterate_mem :
    x ∈ nonwanderingSet f ↔ ∀ U ∈ 𝓝 x, ∃ n : ℕ, 0 < n ∧ ∃ y ∈ U, f^[n] y ∈ U := by
  simp only [mem_nonwanderingSet_iff, Set.Nonempty, mem_inter_iff, mem_image]
  refine forall₂_congr fun U _ ↦ exists_congr fun n ↦ and_congr_right fun _ ↦ ?_
  exact ⟨fun ⟨_, ⟨y, hy, rfl⟩, h⟩ ↦ ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ ↦ ⟨_, ⟨y, hy, rfl⟩, h⟩⟩

/-- The non-wandering set is closed. -/
theorem isClosed_nonwanderingSet (f : X → X) : IsClosed (nonwanderingSet f) := by
  refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_)
  simp only [mem_compl_iff, mem_nonwanderingSet_iff, not_forall, not_exists, not_and,
    exists_prop] at hx
  obtain ⟨U, hU, hUf⟩ := hx
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
  refine ⟨V, fun y hyV hy ↦ ?_, hV, hxV⟩
  obtain ⟨n, hn, z, hz⟩ := hy V (hV.mem_nhds hyV)
  exact hUf n hn ⟨z, image_mono hVU hz.1, hVU hz.2⟩

/-- A set of non-wandering points has non-wandering closure. -/
theorem closure_subset_nonwanderingSet (h : s ⊆ nonwanderingSet f) :
    closure s ⊆ nonwanderingSet f :=
  (isClosed_nonwanderingSet f).closure_subset_iff.2 h

/-- If every point of a dense set is non-wandering, then every point is non-wandering. -/
theorem nonwanderingSet_eq_univ_of_dense (hs : Dense s) (h : s ⊆ nonwanderingSet f) :
    nonwanderingSet f = univ :=
  univ_subset_iff.1 (hs.closure_eq ▸ closure_subset_nonwanderingSet h)

end TauCeti

open TauCeti

/-- Every periodic point is non-wandering. -/
theorem Function.IsPeriodicPt.mem_nonwanderingSet {n : ℕ} (hx : IsPeriodicPt f n x)
    (hn : 0 < n) : x ∈ nonwanderingSet f :=
  fun _ hU ↦ ⟨n, hn, x, ⟨x, mem_of_mem_nhds hU, hx.eq⟩, mem_of_mem_nhds hU⟩

/-- Every fixed point is non-wandering. -/
theorem Function.IsFixedPt.mem_nonwanderingSet (hx : IsFixedPt f x) :
    x ∈ nonwanderingSet f :=
  (hx.isPeriodicPt 1).mem_nonwanderingSet one_pos

/-- A continuous map sends its non-wandering set into itself. -/
theorem Continuous.mapsTo_nonwanderingSet (hf : Continuous f) :
    MapsTo f (nonwanderingSet f) (nonwanderingSet f) := by
  intro x hx
  rw [mem_nonwanderingSet_iff_exists_iterate_mem] at hx ⊢
  intro U hU
  obtain ⟨n, hn, y, hy, hny⟩ := hx _ (hf.continuousAt hU)
  refine ⟨n, hn, f y, hy, ?_⟩
  rw [← iterate_succ_apply, iterate_succ_apply']
  exact hny

/-- If `g` is a left inverse of `f`, every non-wandering point of `f` is non-wandering for `g`. -/
theorem Function.LeftInverse.nonwanderingSet_subset (h : LeftInverse g f) :
    nonwanderingSet f ⊆ nonwanderingSet g := by
  intro x hx
  rw [mem_nonwanderingSet_iff_exists_iterate_mem] at hx ⊢
  intro U hU
  obtain ⟨n, hn, y, hy, hny⟩ := hx U hU
  exact ⟨n, hn, f^[n] y, hny, by rwa [(h.iterate n) y]⟩

namespace TauCeti

/-- The periodic points of `f` are non-wandering. -/
theorem periodicPts_subset_nonwanderingSet : periodicPts f ⊆ nonwanderingSet f :=
  fun _ ⟨_, hn, hx⟩ ↦ hx.mem_nonwanderingSet hn

/-- Every point is non-wandering for the identity map. -/
@[simp]
theorem nonwanderingSet_id : nonwanderingSet (id : X → X) = univ :=
  eq_univ_of_forall fun _ ↦ (isFixedPt_id _).mem_nonwanderingSet

end TauCeti

namespace Homeomorph

/-- A homeomorphism and its inverse have the same non-wandering set. -/
@[simp]
theorem nonwanderingSet_symm (e : X ≃ₜ X) : nonwanderingSet e.symm = nonwanderingSet e :=
  e.left_inv.nonwanderingSet_subset.antisymm
    e.right_inv.nonwanderingSet_subset |>.symm

/-- A homeomorphism maps its non-wandering set onto itself. -/
@[simp]
theorem image_nonwanderingSet (e : X ≃ₜ X) : e '' nonwanderingSet e = nonwanderingSet e := by
  refine e.continuous.mapsTo_nonwanderingSet.image_subset.antisymm fun x hx ↦ ?_
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  rw [← nonwanderingSet_symm] at hx ⊢
  exact e.symm.continuous.mapsTo_nonwanderingSet hx

/-- The preimage of the non-wandering set under the homeomorphism is the set itself. -/
@[simp]
theorem preimage_nonwanderingSet (e : X ≃ₜ X) : e ⁻¹' nonwanderingSet e = nonwanderingSet e := by
  calc e ⁻¹' nonwanderingSet e = e ⁻¹' (e '' nonwanderingSet e) := by
        rw [image_nonwanderingSet]
    _ = nonwanderingSet e := e.preimage_image _

end Homeomorph

namespace MeasureTheory

variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure]

/-- Topological Poincaré recurrence: if `f` is conservative for a measure that is positive on
nonempty open sets, every point is non-wandering. -/
theorem Conservative.nonwanderingSet_eq_univ (hf : Conservative f μ) :
    nonwanderingSet f = univ := by
  refine eq_univ_of_forall fun x ↦ mem_nonwanderingSet_iff_isOpen.2 fun U hU hxU ↦ ?_
  obtain ⟨y, hy, m, hm, hmy⟩ :=
    hf.exists_mem_iterate_mem hU.measurableSet.nullMeasurableSet (hU.measure_ne_zero μ ⟨x, hxU⟩)
  exact ⟨m, Nat.pos_of_ne_zero hm, f^[m] y, mem_image_of_mem _ hy, hmy⟩

/-- If `f` preserves a finite measure of full support (positive on nonempty open sets), every
point is non-wandering. -/
theorem MeasurePreserving.nonwanderingSet_eq_univ [IsFiniteMeasure μ]
    (hf : MeasurePreserving f μ μ) : nonwanderingSet f = univ :=
  hf.conservative.nonwanderingSet_eq_univ

end MeasureTheory
