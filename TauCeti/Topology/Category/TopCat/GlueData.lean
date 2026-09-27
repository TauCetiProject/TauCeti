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
  constructor
  · intro h i j
    let _ := h
    rw [show D.chartRel i j = {p | D.toGlueData.ι i p.1 = D.toGlueData.ι j p.2} by
      ext p
      exact D.mem_chartRel_iff i j p.1 p.2]
    exact isClosed_eq
      ((D.toGlueData.ι i).hom.continuous_toFun.comp continuous_fst)
      ((D.toGlueData.ι j).hom.continuous_toFun.comp continuous_snd)
  · intro h
    rw [t2Space_iff]
    intro x y hxy
    obtain ⟨i, a, rfl⟩ := D.ι_jointly_surjective x
    obtain ⟨j, b, rfl⟩ := D.ι_jointly_surjective y
    have hab : (a, b) ∈ (D.chartRel i j)ᶜ := by
      simpa only [Set.mem_compl_iff, D.mem_chartRel_iff] using hxy
    obtain ⟨u, v, hu, hv, ha, hb, huv⟩ :=
      isOpen_prod_iff.mp (h i j).isOpen_compl a b hab
    refine ⟨D.toGlueData.ι i '' u, D.toGlueData.ι j '' v,
      D.open_image_open i ⟨u, hu⟩, D.open_image_open j ⟨v, hv⟩,
      ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro z ⟨a', ha', rfl⟩ ⟨b', hb', hab'⟩
    have hrel : (a', b') ∈ D.chartRel i j :=
      (D.mem_chartRel_iff i j a' b').2 hab'.symm
    exact (huv ⟨ha', hb'⟩) hrel

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
