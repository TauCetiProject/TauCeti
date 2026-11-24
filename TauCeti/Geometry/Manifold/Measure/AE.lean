/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure
public import Mathlib.Order.Filter.CountableInter

/-!
# The almost-everywhere filter on a manifold

A property holds almost everywhere on a manifold `M` when the set where it fails is chartwise null
(`TauCeti.IsNullSet`). This file packages these sets as a filter `TauCeti.Manifold.ae I M`, with
the countable intersection property. Like `TauCeti.IsNullSet`, the filter needs no metric, no
measurable structure on `M` and no choice of Haar measure on the model.

With a finite-dimensional model, sets in the filter are dense, so continuous maps to a Hausdorff
space that agree almost everywhere are equal. Reading the filter in charts of the maximal atlas is
in `TauCeti.Geometry.Manifold.Measure.Atlas`.

## Main definitions and results

* `TauCeti.Manifold.ae I M`: the filter of subsets of `M` with null complement.
* `TauCeti.Manifold.ae_eq_iff_forall_measure_eq_zero_iff`: a measure on `M` has
  `TauCeti.Manifold.ae I M` as its almost-everywhere filter exactly when its null sets are the
  chartwise null sets.
* `TauCeti.Manifold.dense_of_mem_ae`, `TauCeti.Manifold.eq_of_ae_eq`: with a finite-dimensional
  model, sets in the filter are dense, and continuous maps agreeing almost everywhere are equal.
-/

public section

open Filter Module Set
open scoped Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace Manifold

variable (I M) in
/-- The almost-everywhere filter on a manifold: a set belongs to it when its complement is
chartwise null. It needs no measurable structure on the manifold. -/
def ae : Filter M :=
  Filter.ofCountableUnion {s | IsNullSet I s}
    (fun _ hS h ↦ by rw [sUnion_eq_biUnion]; exact IsNullSet.biUnion hS h)
    fun _ ht _ hst ↦ IsNullSet.mono ht hst

theorem mem_ae_iff {s : Set M} : s ∈ ae I M ↔ IsNullSet I sᶜ :=
  Iff.rfl

theorem ae_iff {p : M → Prop} : (∀ᶠ x in ae I M, p x) ↔ IsNullSet I {x | ¬p x} :=
  Iff.rfl

theorem compl_mem_ae_iff {s : Set M} : sᶜ ∈ ae I M ↔ IsNullSet I s := by
  rw [mem_ae_iff, compl_compl]

instance : CountableInterFilter (ae I M) :=
  Filter.countableInter_ofCountableUnion _ _ _

/-- On a nonempty manifold with a finite-dimensional model, the almost-everywhere filter is
proper: the whole manifold is not null. -/
instance [FiniteDimensional ℝ E] [Nonempty M] : (ae I M).NeBot := by
  refine ⟨fun h ↦ ?_⟩
  have hnull : IsNullSet I (univ : Set M) := compl_mem_ae_iff.1 (h ▸ mem_bot)
  have := hnull.interior_eq_empty
  rw [interior_univ] at this
  exact univ_nonempty.ne_empty this

/-- On a manifold with a nontrivial finite-dimensional model, almost every point differs from a
given point. -/
theorem ae_ne [FiniteDimensional ℝ E] [Nontrivial E] (x : M) : ∀ᶠ y in ae I M, y ≠ x := by
  rw [ae_iff]
  simpa using (countable_singleton x).isNullSet (I := I)

/-- With a finite-dimensional model, a set in the almost-everywhere filter is dense. -/
theorem dense_of_mem_ae [FiniteDimensional ℝ E] {s : Set M} (hs : s ∈ ae I M) : Dense s := by
  simpa using (mem_ae_iff.1 hs).dense_compl

/-- With a finite-dimensional model, continuous maps to a Hausdorff space that agree almost
everywhere are equal. -/
theorem eq_of_ae_eq [FiniteDimensional ℝ E] {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : M → Y} (h : f =ᶠ[ae I M] g) (hf : Continuous f) (hg : Continuous g) : f = g :=
  hf.ext_on (dense_of_mem_ae h) hg fun _ hx ↦ hx

/-- A measure on `M` has the manifold almost-everywhere filter as its almost-everywhere filter
exactly when its null sets are the chartwise null sets. -/
theorem ae_eq_iff_forall_measure_eq_zero_iff [MeasurableSpace M] {μ : MeasureTheory.Measure M} :
    MeasureTheory.ae μ = ae I M ↔ ∀ s : Set M, μ s = 0 ↔ IsNullSet I s := by
  refine ⟨fun h s ↦ ?_, fun h ↦ Filter.ext fun _ ↦ by rw [MeasureTheory.mem_ae_iff, mem_ae_iff, h]⟩
  rw [← MeasureTheory.compl_mem_ae_iff, h, compl_mem_ae_iff]

end Manifold

theorem IsNullSet.compl_mem_ae {s : Set M} (hs : IsNullSet I s) : sᶜ ∈ Manifold.ae I M :=
  Manifold.compl_mem_ae_iff.2 hs

end TauCeti
