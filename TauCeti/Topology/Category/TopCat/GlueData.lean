/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Gluing
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.Basic
public import TauCeti.Topology.Compactness.LocallyCompact

/-!
# Separation, countability, and local compactness of glued spaces

A space obtained by gluing open charts is second countable when the chart family is countable
and every chart is second countable. It is locally compact when every chart is locally compact.
It is Hausdorff exactly when the gluing relation between each pair of charts is closed in their
product. The latter criterion isolates the mathematical separation argument needed in applications:
for example, toric charts must prove that their monomial overlap relation is closed.

Connectedness is controlled by the overlap graph, whose vertices are the charts and in which `i`
and `j` are adjacent when the overlap `V (i, j)` is nonempty. A space glued from preconnected
charts is preconnected exactly when any two nonempty charts are joined by a path in this graph,
and a space glued from a nonempty family of connected charts is connected exactly when the
overlap graph is connected. Paths may pass through charts which are not adjacent to their
endpoints: the criterion uses the generated relation, not a single overlap.
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

/-! ### Connectedness and the overlap graph -/

/-- The images of two charts in the glued space meet exactly when their overlap is nonempty. -/
theorem range_ι_inter_range_ι_nonempty_iff (i j : D.J) :
    (range (D.toGlueData.ι i) ∩ range (D.toGlueData.ι j)).Nonempty ↔ Nonempty (D.V (i, j)) := by
  rw [D.image_inter, range_nonempty_iff_nonempty]

/-- If the glued space is preconnected, then any two nonempty charts are joined by a nonempty
chain of charts with consecutive nonempty overlaps. -/
theorem transGen_of_preconnectedSpace [PreconnectedSpace D.toGlueData.glued] {i j : D.J}
    (hi : Nonempty (D.U i)) (hj : Nonempty (D.U j)) :
    Relation.TransGen (fun i j ↦ Nonempty (D.V (i, j))) i j := by
  have hcover : ⋃ i, range (D.toGlueData.ι i) = univ :=
    iUnion_eq_univ_iff.2 fun x ↦ D.ι_jointly_surjective x
  refine Relation.TransGen.mono (fun i j h ↦ (D.range_ι_inter_range_ι_nonempty_iff i j).1 h) _ _ <|
    IsPreconnected.transGen_of_iUnion (hcover ▸ isPreconnected_univ)
      (fun i ↦ (D.ι_isOpenEmbedding i).isOpen_range) i j ?_ ?_
  · exact range_nonempty_iff_nonempty.2 hi
  · exact range_nonempty_iff_nonempty.2 hj

/-- A space glued from preconnected charts is preconnected exactly when any two nonempty charts
are joined by a chain of charts with consecutive nonempty overlaps. Empty charts impose no
condition. -/
theorem preconnectedSpace_iff_reflTransGen [∀ i, PreconnectedSpace (D.U i)] :
    PreconnectedSpace D.toGlueData.glued ↔ ∀ i j, Nonempty (D.U i) → Nonempty (D.U j) →
      Relation.ReflTransGen (fun i j ↦ Nonempty (D.V (i, j))) i j := by
  refine ⟨fun _ i j hi hj ↦ (D.transGen_of_preconnectedSpace hi hj).to_reflTransGen,
    fun h ↦ ⟨?_⟩⟩
  -- The nonempty charts cover the glued space, and their images form a family of preconnected
  -- sets whose intersection graph is preconnected.
  let t : Set D.J := {i | Nonempty (D.U i)}
  have hcover : ⋃ i ∈ t, range (D.toGlueData.ι i) = univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
    exact mem_biUnion (x := i) ⟨y⟩ (mem_range_self y)
  rw [← hcover]
  refine IsPreconnected.biUnion_of_reflTransGen
    (fun i _ ↦ isPreconnected_range (D.toGlueData.ι i).hom.continuous) fun i hi j hj ↦ ?_
  refine Relation.ReflTransGen.mono (fun k l hkl ↦ ?_) _ _ (h i j hi hj)
  exact ⟨(D.range_ι_inter_range_ι_nonempty_iff k l).2 hkl,
    hkl.map (D.f k l)⟩

/-- A space glued from a nonempty family of connected charts is connected exactly when the
overlap graph is connected: any two charts are joined by a chain of charts with consecutive
nonempty overlaps. -/
theorem connectedSpace_iff_reflTransGen [Nonempty D.J] [∀ i, ConnectedSpace (D.U i)] :
    ConnectedSpace D.toGlueData.glued ↔
      ∀ i j, Relation.ReflTransGen (fun i j ↦ Nonempty (D.V (i, j))) i j := by
  refine ⟨fun _ i j ↦
    (D.transGen_of_preconnectedSpace inferInstance inferInstance).to_reflTransGen, fun h ↦ ?_⟩
  obtain ⟨i⟩ := ‹Nonempty D.J›
  exact { toPreconnectedSpace := D.preconnectedSpace_iff_reflTransGen.2 fun i j _ _ ↦ h i j
          toNonempty := ⟨D.toGlueData.ι i (Classical.arbitrary _)⟩ }

end TopCat.GlueData
