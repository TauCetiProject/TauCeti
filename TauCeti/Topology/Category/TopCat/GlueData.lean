/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Gluing
public import Mathlib.Topology.Bases
public import TauCeti.Topology.Compactness.LocallyCompact

/-!
# Separation, countability, and local compactness of glued spaces

A space obtained by gluing open charts is second countable when the chart family is countable
and every chart is second countable. It is locally compact when every chart is locally compact.
It is Hausdorff exactly when the gluing relation between each pair of charts is closed in their
product. The latter criterion isolates the mathematical separation argument needed in applications:
for example, toric charts must prove that their monomial overlap relation is closed.
-/

public section

open CategoryTheory Set Topology

namespace TopCat.GlueData

variable (D : TopCat.GlueData)

/-- The relation between the `i`-th and `j`-th charts: two points are related when the gluing
identifies their images. -/
def chartRel (i j : D.J) : Set (D.U i × D.U j) :=
  {p | D.Rel ⟨i, p.1⟩ ⟨j, p.2⟩}

/-- Two points in different charts are related exactly when they come from a point in their
overlap via the two transition maps. -/
theorem mem_chartRel_iff_exists (i j : D.J) (x : D.U i) (y : D.U j) :
    (x, y) ∈ D.chartRel i j ↔
      ∃ z : D.V (i, j), D.f i j z = x ∧ D.f j i (D.t i j z) = y :=
  Iff.rfl

/-- Membership in the relation between two charts is equivalent to equality of their images in
the glued space. -/
@[simp]
theorem mem_chartRel_iff (i j : D.J) (x : D.U i) (y : D.U j) :
    (x, y) ∈ D.chartRel i j ↔ D.toGlueData.ι i x = D.toGlueData.ι j y :=
  (D.ι_eq_iff_rel i j x y).symm

/-- The space obtained by gluing open charts is Hausdorff exactly when the gluing relation between
every pair of charts is closed in the product of those charts. -/
theorem t2Space_iff_isClosed_chartRel :
    T2Space D.toGlueData.glued ↔ ∀ i j, IsClosed (D.chartRel i j) := by
  let π : (Σ i, D.U i) → D.toGlueData.glued := fun x ↦ D.toGlueData.ι x.1 x.2
  have hπ : IsOpenQuotientMap π := {
    surjective := by
      intro x
      obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
      exact ⟨⟨i, y⟩, rfl⟩
    continuous := continuous_sigma fun i ↦ (D.toGlueData.ι i).hom.continuous_toFun
    isOpenMap := by
      intro s hs
      rw [isOpen_sigma_iff] at hs
      rw [show π '' s = ⋃ i, D.toGlueData.ι i '' ((fun y : D.U i ↦ ⟨i, y⟩) ⁻¹' s) by
        ext x
        simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
        constructor
        · rintro ⟨⟨i, y⟩, hy, rfl⟩
          exact ⟨i, y, hy, rfl⟩
        · rintro ⟨i, y, hy, rfl⟩
          exact ⟨⟨i, y⟩, hy, rfl⟩]
      exact isOpen_iUnion fun i ↦ D.open_image_open i ⟨_, hs i⟩ }
  rw [t2Space_iff_of_isOpenQuotientMap hπ]
  rw [show (∀ i j, IsClosed (D.chartRel i j)) ↔
      ∀ i j, IsClosed (D.chartRel j i) by
    constructor <;> intro h i j <;> exact h _ _]
  let e₁ : ((Σ i, D.U i) × (Σ i, D.U i)) ≃ₜ Σ i, D.U i × (Σ i, D.U i) :=
    Homeomorph.sigmaProdDistrib
  rw [← e₁.symm.isClosed_preimage, isClosed_sigma_iff]
  apply forall_congr' fun i ↦ ?_
  let e₂ : (D.U i × (Σ j, D.U j)) ≃ₜ Σ j, D.U j × D.U i :=
    (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib
  rw [← e₂.symm.isClosed_preimage, isClosed_sigma_iff]
  apply forall_congr' fun j ↦ ?_
  change IsClosed {p : D.U j × D.U i | π ⟨i, p.2⟩ = π ⟨j, p.1⟩} ↔
    IsClosed (D.chartRel j i)
  rw [show {p : D.U j × D.U i | π ⟨i, p.2⟩ = π ⟨j, p.1⟩} = D.chartRel j i by
    ext p
    exact eq_comm.trans (D.mem_chartRel_iff j i p.1 p.2).symm]

/-- A glued space with countably many second-countable charts is second countable. -/
instance secondCountableTopology [Countable D.J]
    [∀ i, SecondCountableTopology (D.U i)] : SecondCountableTopology D.toGlueData.glued := by
  let U : D.J → Set D.toGlueData.glued := fun i ↦ range (D.toGlueData.ι i)
  have hU (i : D.J) : IsOpen (U i) := (D.ι_isOpenEmbedding i).isOpen_range
  have hcover : ⋃ i, U i = univ := iUnion_eq_univ_iff.2 fun x ↦ D.ι_jointly_surjective x
  let hCount : ∀ i : D.J, SecondCountableTopology (U i) := fun i ↦
    (D.ι_isOpenEmbedding i).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hU hcover

/-- A glued space with locally compact charts is locally compact. -/
instance locallyCompactSpace [∀ i, LocallyCompactSpace (D.U i)] :
    LocallyCompactSpace D.toGlueData.glued := by
  let U : D.J → Set D.toGlueData.glued := fun i ↦ range (D.toGlueData.ι i)
  have hU (i : D.J) : IsOpen (U i) := (D.ι_isOpenEmbedding i).isOpen_range
  have hcover : ⋃ i, U i = univ := iUnion_eq_univ_iff.2 fun x ↦ D.ι_jointly_surjective x
  let hCompact : ∀ i : D.J, LocallyCompactSpace (U i) := fun i ↦
    (D.ι_isOpenEmbedding i).isEmbedding.toHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  exact TauCeti.locallyCompactSpace_of_isOpen_cover hU hcover

end TopCat.GlueData
