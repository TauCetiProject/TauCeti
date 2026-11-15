/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic

/-!
# Continuous sections with almost everywhere equal chart expressions

Let `A` be a finite bundle atlas of a fibre bundle `V → M` whose model space carries a measure
charging every nonempty open set, such as Lebesgue measure. Two continuous sections of `V` whose
chart expressions in every chart of `A` agree almost everywhere on the chart image are equal
(`TauCeti.FiniteBundleAtlas.eq_of_continuous_of_coord_ae_eq`): the chart expressions are continuous
on the open chart images (`TauCeti.FiniteBundleAtlas.continuousOn_coord`), hence agree everywhere
there, and the trivializations are injective.
-/

public section

open Bundle MeasureTheory

namespace TauCeti

variable {E : Type*} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas E M F V)

/-- **Continuous sections are determined by their chart expressions almost everywhere.** Two
continuous sections whose chart expressions in every chart `i` agree almost everywhere on
`A.image i`, for a measure charging nonempty open sets, are equal. -/
theorem eq_of_continuous_of_coord_ae_eq [T2Space F] [MeasurableSpace E] {μ : Measure E}
    [μ.IsOpenPosMeasure] {s t : ∀ x, V x} (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (ht : Continuous fun x ↦ TotalSpace.mk' F x (t x))
    (h : ∀ i, A.coord i s =ᵐ[μ.restrict (A.image i)] A.coord i t) : s = t := by
  funext x
  obtain ⟨i, hx⟩ := A.exists_mem_dom x
  have hy : A.chart i x ∈ A.image i := A.mem_image.2 ⟨x, hx, rfl⟩
  have heq := Measure.eqOn_open_of_ae_eq (h i) (A.image i).isOpen (A.continuousOn_coord hs i)
    (A.continuousOn_coord ht i) hy
  rw [← (A.chart i).left_inv (A.dom_subset_chart_source i hx)]
  exact (A.coord_eq_coord_iff hy).1 heq

end FiniteBundleAtlas

end TauCeti
