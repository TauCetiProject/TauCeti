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

universe u

variable (D : TopCat.GlueData.{u})

/-- The relation between the `i`-th and `j`-th charts: two points are related when the gluing
identifies their images. -/
def chartRel (i j : D.J) : Set (D.U i × D.U j) :=
  {p | D.Rel ⟨i, p.1⟩ ⟨j, p.2⟩}

/-- A point of the `i`-th chart and a point of the `j`-th chart are related exactly when they are
the images of a single point of the overlap `V (i, j)` under `f i j` and under `f j i` composed
with the transition `t i j`. -/
theorem mem_chartRel_iff_exists {i j : D.J} {p : D.U i × D.U j} :
    p ∈ D.chartRel i j ↔
      ∃ z : D.V (i, j), D.f i j z = p.1 ∧ D.f j i (D.t i j z) = p.2 :=
  Iff.rfl

/-- Membership in the relation between two charts is equivalent to equality of their images in
the glued space. -/
@[simp, grind =]
theorem mem_chartRel_iff {i j : D.J} {p : D.U i × D.U j} :
    p ∈ D.chartRel i j ↔ D.toGlueData.ι i p.1 = D.toGlueData.ι j p.2 :=
  (D.ι_eq_iff_rel i j p.1 p.2).symm

/-- The map from the disjoint union of the charts to the glued space is an open quotient map. -/
theorem isOpenQuotientMap_sigma_ι :
    IsOpenQuotientMap fun x : Σ i, D.U i ↦ D.toGlueData.ι x.1 x.2 := {
  surjective := by
    intro x
    obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
    exact ⟨⟨i, y⟩, rfl⟩
  continuous := continuous_sigma fun i ↦ (D.toGlueData.ι i).hom.continuous_toFun
  isOpenMap := isOpenMap_sigma.2 fun i ↦ (D.ι_isOpenEmbedding i).isOpenMap }

/-- The space obtained by gluing open charts is Hausdorff exactly when the gluing relation between
every pair of charts is closed in the product of those charts. -/
theorem t2Space_iff_isClosed_chartRel :
    T2Space D.toGlueData.glued ↔ ∀ i j, IsClosed (D.chartRel i j) := by
  let π : (Σ i, D.U i) → D.toGlueData.glued := fun x ↦ D.toGlueData.ι x.1 x.2
  rw [t2Space_iff_of_isOpenQuotientMap D.isOpenQuotientMap_sigma_ι]
  rw [forall_comm]
  let e₁ : ((Σ i, D.U i) × (Σ i, D.U i)) ≃ₜ Σ i, D.U i × (Σ i, D.U i) :=
    Homeomorph.sigmaProdDistrib
  rw [← e₁.symm.isClosed_preimage, isClosed_sigma_iff]
  apply forall_congr' fun i ↦ ?_
  let e₂ : (D.U i × (Σ j, D.U j)) ≃ₜ Σ j, D.U j × D.U i :=
    (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib
  rw [← e₂.symm.isClosed_preimage, isClosed_sigma_iff]
  apply forall_congr' fun j ↦ ?_
  congr! 1
  ext ⟨x, y⟩
  simp only [e₁, e₂, Set.mem_preimage, Set.mem_ofPred_eq,
    Homeomorph.symm_trans_apply, Homeomorph.sigmaProdDistrib_symm_apply,
    Homeomorph.prodComm_symm, Homeomorph.coe_prodComm, Prod.swap, mem_chartRel_iff, eq_comm]

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
