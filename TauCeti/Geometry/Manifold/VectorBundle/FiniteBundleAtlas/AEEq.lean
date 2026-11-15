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
  have heq := Measure.eqOn_open_of_ae_eq (h i) (A.image i).isOpen (A.continuousOn_coord hs i)
    (A.continuousOn_coord ht i) (A.mem_image.2 ⟨x, hx, rfl⟩)
  rw [A.coord_chart s hx, A.coord_chart t hx] at heq
  have hb : x ∈ (A.triv i).baseSet := A.dom_subset_baseSet i hx
  have himage : A.triv i ⟨x, s x⟩ = A.triv i ⟨x, t x⟩ := by
    rw [← (A.triv i).mk_proj_snd' (x := ⟨x, s x⟩) hb,
      ← (A.triv i).mk_proj_snd' (x := ⟨x, t x⟩) hb, heq]
  exact TotalSpace.mk_inj.1 ((A.triv i).injOn ((A.triv i).mem_source.2 hb)
    ((A.triv i).mem_source.2 hb) himage)

end FiniteBundleAtlas

end TauCeti
