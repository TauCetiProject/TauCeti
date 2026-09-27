/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Representability.ConnectionMatrix
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Structural
import TauCeti.LinearAlgebra.Matrix.PosSemidef
import TauCeti.MeasureTheory.Integral.Pi
import TauCeti.MeasureTheory.Integral.PosSemidef

/-!
# Homomorphism densities satisfy the representability axioms

The homomorphism density `t(·, W)` of a graphon `W` is a graph parameter
(`TauCeti.DenseGraphLimits.homDensityParam`) that is isomorphism invariant, multiplicative,
normalized and reflection positive.  These are the four structural conditions of the
Lovász–Szegedy characterization of homomorphism densities, so this is its easy direction.

The first three conditions are structural laws of `homDensity`. Reflection positivity follows from
the gluing formula for labeled graphs and positivity of the resulting connection matrices.

## Main definitions

* `TauCeti.DenseGraphLimits.homDensityParam` — the graph parameter `t(·, W)`.

## Main results

* `TauCeti.DenseGraphLimits.isIsoInvariant_homDensityParam`,
  `TauCeti.DenseGraphLimits.isMultiplicative_homDensityParam` and
  `TauCeti.DenseGraphLimits.isNormalized_homDensityParam` — the three structural laws;
* `TauCeti.DenseGraphLimits.isReflectionPositive_homDensityParam` — **`t(·, W)` is reflection
  positive**.

## References

* L. Lovász, B. Szegedy, *Limits of dense graph sequences*, JCTB 96 (2006), 933–957, Section 2 —
  connection matrices and the reflection positivity of homomorphism densities.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Section 7.1.
-/

public section

noncomputable section

open MeasureTheory SimpleGraph

open scoped Matrix

namespace TauCeti.DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The homomorphism density `t(·, W)` of a graphon, as a graph parameter. -/
def homDensityParam (W : Graphon Ω μ) : GraphParam :=
  fun _ F => by classical exact homDensity F W

/-- The value of `homDensityParam W` at `F` is `t(F, W)`, for any decidability instance on the
adjacency of `F`. -/
@[simp]
theorem homDensityParam_apply (W : Graphon Ω μ) {n : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] : homDensityParam W n F = homDensity F W := by
  simp only [homDensityParam]
  congr

/-- `t(·, W)` is isomorphism invariant. -/
theorem isIsoInvariant_homDensityParam (W : Graphon Ω μ) : IsIsoInvariant (homDensityParam W) := by
  classical
  rw [isIsoInvariant_iff]
  rintro n₁ n₂ F₁ F₂ ⟨φ⟩
  rw [homDensityParam_apply, homDensityParam_apply]
  exact (homDensity_eq_of_iso φ W).symm

/-- `t(·, W)` is multiplicative over disjoint unions. -/
theorem isMultiplicative_homDensityParam (W : Graphon Ω μ) :
    IsMultiplicative (homDensityParam W) := by
  classical
  rw [isMultiplicative_iff]
  intro n₁ n₂ F₁ F₂
  rw [homDensityParam_apply, homDensityParam_apply, homDensityParam_apply,
    homDensity_map_embedding, homDensity_sum]

/-- `t(·, W)` is normalized: `t(K₁, W) = 1`. -/
theorem isNormalized_homDensityParam (W : Graphon Ω μ) : IsNormalized (homDensityParam W) := by
  classical
  rw [isNormalized_iff, homDensityParam_apply, homDensity_bot]

/-! ### Reflection positivity -/

section ReflectionPositive

variable (W : Graphon Ω μ) {k : ℕ}

/-- The labels of a `k`-labeled graph, as an embedding. -/
private def labelEmb (A : LabeledGraph k) : Fin k ↪ Fin A.n := ⟨A.label, A.label_injective⟩

open Classical in
/-- The pairs of labels joined in `A`. -/
private def labelEdges (A : LabeledGraph k) : Finset (Sym2 (Fin k)) :=
  (A.graph.comap A.label).edgeFinset

open Classical in
/-- The product of `W` along the edges of `A` that meet an unlabeled vertex. -/
private def outerEdgeProd (A : LabeledGraph k) (z : Fin A.n → Ω) : ℝ :=
  ∏ e ∈ A.graph.edgeFinset \ (Finset.univ.map (labelEmb A)).sym2, edgeFactor W z e

/-- The density of the edges of `A` meeting an unlabeled vertex, with the labels held at `x`. -/
private def outerDensity (A : LabeledGraph k) (x : Fin k → Ω) : ℝ :=
  ∫ y : A.Unlabeled → Ω, outerEdgeProd W A (Sum.elim x y ∘ A.labelSumUnlabeledEquiv.symm)
    ∂Measure.pi fun _ => μ

/-- The edges of `G` inside the range of an embedding `f` are the image of the edges of the pulled
back graph, so their product of edge factors is read in the pulled back assignment. -/
private theorem prod_edgeFactor_inter_sym2 {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (f : U ↪ V)
    [DecidableRel (G.comap f).Adj] (z : V → Ω) :
    ∏ e ∈ G.edgeFinset ∩ (Finset.univ.map f).sym2, edgeFactor W z e =
      ∏ e ∈ (G.comap f).edgeFinset, edgeFactor W (z ∘ f) e := by
  have h : (G.comap f).edgeFinset.map f.sym2Map = G.edgeFinset ∩ (Finset.univ.map f).sym2 := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_map, mem_edgeFinset, Function.Embedding.sym2Map_apply,
        Finset.mem_inter, Finset.mem_sym2_iff, Sym2.mem_iff, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨e, he, hmap⟩
        induction e using Sym2.ind with
        | _ a b =>
          rw [Sym2.map_mk, Sym2.eq_iff] at hmap
          rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨he, by rintro _ (rfl | rfl) <;> simp⟩
          · exact ⟨(comap_adj.1 he).symm, by rintro _ (rfl | rfl) <;> simp⟩
      · rintro ⟨huv, hsub⟩
        obtain ⟨a, rfl⟩ := hsub u (Or.inl rfl)
        obtain ⟨b, rfl⟩ := hsub _ (Or.inr rfl)
        exact ⟨s(a, b), comap_adj.2 huv, rfl⟩
  rw [← h, Finset.prod_map]
  exact Finset.prod_congr rfl fun e _ => edgeFactor_map W f z e

/-- **The edge product of a gluing splits** into the edges between labels, which form the union of
the labeled edge sets of the two sides, and the edges of each side meeting an unlabeled
vertex. -/
private theorem prod_edgeFactor_glue (A B : LabeledGraph k) [DecidableRel (A.glue B).graph.Adj]
    (z : Fin (A.glue B).n → Ω) :
    ∏ e ∈ (A.glue B).graph.edgeFinset, edgeFactor W z e =
      (∏ e ∈ labelEdges A ∪ labelEdges B, edgeFactor W (z ∘ (A.glue B).label) e) *
        (outerEdgeProd W A (z ∘ A.glueInl B) * outerEdgeProd W B (z ∘ A.glueInr B)) := by
  classical
  rw [← Finset.prod_inter_mul_prod_sdiff _ (Finset.univ.map (labelEmb (A.glue B))).sym2]
  congr 1
  · rw [prod_edgeFactor_inter_sym2 W _ (labelEmb (A.glue B))]
    have hL : ((A.glue B).graph.comap (labelEmb (A.glue B))).edgeFinset =
        labelEdges A ∪ labelEdges B := by
      ext e
      induction e using Sym2.ind with
      | _ i j =>
        rw [mem_edgeFinset]
        simp only [labelEdges, labelEmb, Finset.mem_union, mem_edgeFinset, mem_edgeSet,
          comap_adj, Function.Embedding.coeFn_mk, LabeledGraph.glue_adj_label]
    rw [hL]
    rfl
  · -- The edges of a gluing are the images of the edges of the two sides.
    have hE : (A.glue B).graph.edgeFinset =
        A.graph.edgeFinset.map (A.glueInl B).sym2Map ∪
          B.graph.edgeFinset.map (A.glueInr B).sym2Map := by
      ext e
      simp [LabeledGraph.glue_graph, edgeSet_map]
    -- The labels of the gluing are the images of the labels of either side, so removing the
    -- pairs of labels commutes with pushing the edges of a side into the gluing.
    have hl : (A.graph.edgeFinset.map (A.glueInl B).sym2Map) \
          (Finset.univ.map (labelEmb (A.glue B))).sym2 =
        (A.graph.edgeFinset \ (Finset.univ.map (labelEmb A)).sym2).map (A.glueInl B).sym2Map := by
      have h : (labelEmb A).trans (A.glueInl B) = labelEmb (A.glue B) := by
        refine Function.Embedding.ext fun i => ?_
        rw [Function.Embedding.trans_apply]
        exact (congrFun (LabeledGraph.glueInl_label A B) i).symm
      rw [← h, ← Finset.map_map, Finset.sym2_map, Finset.map_sdiff]
    have hr : (B.graph.edgeFinset.map (A.glueInr B).sym2Map) \
          (Finset.univ.map (labelEmb (A.glue B))).sym2 =
        (B.graph.edgeFinset \ (Finset.univ.map (labelEmb B)).sym2).map (A.glueInr B).sym2Map := by
      have h : (labelEmb B).trans (A.glueInr B) = labelEmb (A.glue B) := by
        refine Function.Embedding.ext fun i => ?_
        rw [Function.Embedding.trans_apply]
        exact (congrFun (LabeledGraph.glueInr_label A B) i).symm
      rw [← h, ← Finset.map_map, Finset.sym2_map, Finset.map_sdiff]
    -- An edge meeting an unlabeled vertex comes from only one side.
    have hdisj : Disjoint ((A.graph.edgeFinset \ (Finset.univ.map (labelEmb A)).sym2).map
        (A.glueInl B).sym2Map)
        ((B.graph.edgeFinset \ (Finset.univ.map (labelEmb B)).sym2).map
          (A.glueInr B).sym2Map) := by
      refine Finset.disjoint_left.2 fun e he he' => ?_
      simp only [Finset.mem_map, Finset.mem_sdiff, Finset.mem_sym2_iff, not_forall,
        Function.Embedding.sym2Map_apply] at he he'
      obtain ⟨e₁, ⟨-, a, ha, hna⟩, rfl⟩ := he
      obtain ⟨e₂, -, he₂⟩ := he'
      have hmem : A.glueInl B a ∈ Sym2.map (A.glueInr B) e₂ := he₂ ▸ Sym2.mem_map.2 ⟨a, ha, rfl⟩
      obtain ⟨b, -, hb⟩ := Sym2.mem_map.1 hmem
      obtain ⟨i, rfl, -⟩ := (LabeledGraph.glueInl_eq_glueInr_iff A B a b).1 hb.symm
      exact hna ⟨i, Finset.mem_univ _, rfl⟩
    rw [hE, Finset.union_sdiff_distrib, hl, hr, Finset.prod_union hdisj, Finset.prod_map,
      Finset.prod_map]
    simp only [outerEdgeProd, Function.Embedding.sym2Map_apply, edgeFactor_map]

/-- In the coordinates of a gluing, the labels read off the label coordinates. -/
private theorem comp_glue_label {β : Type*} (A B : LabeledGraph k) (x : Fin k → β)
    (y : A.Unlabeled ⊕ B.Unlabeled → β) :
    (Sum.elim x y ∘ (A.glueEquiv B).symm) ∘ (A.glue B).label = x := by
  funext i
  simp only [Function.comp_apply, ← LabeledGraph.glueEquiv_inl, Equiv.symm_apply_apply,
    Sum.elim_inl]

/-- In the coordinates of a gluing, the left side reads the label coordinates and its private
coordinates. -/
private theorem comp_glueInl {β : Type*} (A B : LabeledGraph k) (x : Fin k → β)
    (y : A.Unlabeled ⊕ B.Unlabeled → β) :
    (Sum.elim x y ∘ (A.glueEquiv B).symm) ∘ A.glueInl B =
      Sum.elim x (y ∘ Sum.inl) ∘ A.labelSumUnlabeledEquiv.symm := by
  funext v
  obtain ⟨s, rfl⟩ := A.labelSumUnlabeledEquiv.surjective v
  simp only [Function.comp_apply, LabeledGraph.glueInl_labelSumUnlabeledEquiv,
    Equiv.symm_apply_apply]
  rcases s with i | a <;> simp

/-- In the coordinates of a gluing, the right side reads the label coordinates and its private
coordinates. -/
private theorem comp_glueInr {β : Type*} (A B : LabeledGraph k) (x : Fin k → β)
    (y : A.Unlabeled ⊕ B.Unlabeled → β) :
    (Sum.elim x y ∘ (A.glueEquiv B).symm) ∘ A.glueInr B =
      Sum.elim x (y ∘ Sum.inr) ∘ B.labelSumUnlabeledEquiv.symm := by
  funext v
  obtain ⟨s, rfl⟩ := B.labelSumUnlabeledEquiv.surjective v
  simp only [Function.comp_apply, LabeledGraph.glueInr_labelSumUnlabeledEquiv,
    Equiv.symm_apply_apply]
  rcases s with i | b <;> simp

/-- The coordinates of a gluing: an assignment of the labels and of the unlabeled vertices of the
two sides. -/
private def glueCoord (A B : LabeledGraph k) :
    (Fin k → Ω) × (A.Unlabeled ⊕ B.Unlabeled → Ω) ≃ᵐ (Fin (A.glue B).n → Ω) :=
  (MeasurableEquiv.sumPiEquivProdPi fun _ => Ω).symm.trans
    (MeasurableEquiv.arrowCongr' (A.glueEquiv B) (MeasurableEquiv.refl Ω))

-- `glueCoord` is a composite of two measurable equivalences whose underlying maps are, by
-- definition, `Sum.elim` (as `Sum.rec`) and precomposition with `(glueEquiv A B).symm`; Mathlib
-- states no application lemma for their composite, so it is read off definitionally here.
private theorem glueCoord_apply (A B : LabeledGraph k)
    (p : (Fin k → Ω) × (A.Unlabeled ⊕ B.Unlabeled → Ω)) :
    glueCoord A B p = Sum.elim p.1 p.2 ∘ (A.glueEquiv B).symm := (rfl)

private theorem measurePreserving_glueCoord (A B : LabeledGraph k) :
    MeasurePreserving (glueCoord A B)
      ((Measure.pi fun _ : Fin k => μ).prod (Measure.pi fun _ : A.Unlabeled ⊕ B.Unlabeled => μ))
      (Measure.pi fun _ : Fin (A.glue B).n => μ) :=
  (measurePreserving_arrowCongr' (fun _ => μ) (fun _ => μ) (A.glueEquiv B)
      (MeasurableEquiv.refl Ω) fun _ => MeasurePreserving.id μ).comp
    (measurePreserving_sumPiEquivProdPi_symm fun _ => μ)

/-- With the labels held at `x`, integrating out the unlabeled vertices of a gluing gives the
labeled edge product times the two outer densities. -/
private theorem integral_prod_edgeFactor_glueCoord (A B : LabeledGraph k)
    [DecidableRel (A.glue B).graph.Adj] (x : Fin k → Ω) :
    ∫ y, (∏ e ∈ (A.glue B).graph.edgeFinset, edgeFactor W (glueCoord A B (x, y)) e)
        ∂(Measure.pi fun _ => μ) =
      (∏ e ∈ labelEdges A ∪ labelEdges B, edgeFactor W x e) *
        (outerDensity W A x * outerDensity W B x) := by
  simp_rw [glueCoord_apply, prod_edgeFactor_glue, comp_glue_label, comp_glueInl, comp_glueInr]
  rw [integral_const_mul, outerDensity, outerDensity,
    ← integral_pi_sum_mul (fun _ : A.Unlabeled ⊕ B.Unlabeled => μ)]
  simp only [Function.comp_def]

/-- The integrand of `t(A B, W)` in the coordinates of the gluing. -/
private theorem integrable_prod_edgeFactor_glueCoord (A B : LabeledGraph k)
    [DecidableRel (A.glue B).graph.Adj] :
    Integrable (fun p => ∏ e ∈ (A.glue B).graph.edgeFinset, edgeFactor W (glueCoord A B p) e)
      ((Measure.pi fun _ : Fin k => μ).prod
        (Measure.pi fun _ : A.Unlabeled ⊕ B.Unlabeled => μ)) :=
  ((measurePreserving_glueCoord A B).integrable_comp_emb
    (glueCoord A B).measurableEmbedding).2 (integrable_homDensity_integrand _ W)

/-- The integrand of the gluing formula is integrable. -/
private theorem integrable_glue (A B : LabeledGraph k) :
    Integrable (fun x => (∏ e ∈ labelEdges A ∪ labelEdges B, edgeFactor W x e) *
      (outerDensity W A x * outerDensity W B x)) (Measure.pi fun _ => μ) := by
  classical
  refine (integrable_prod_edgeFactor_glueCoord W A B).integral_prod_left.congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact integral_prod_edgeFactor_glueCoord W A B x

/-- **The gluing formula.** The density of a gluing is the integral, over the positions of the
labels, of the labeled edge product times the two outer densities. -/
private theorem homDensity_glue (A B : LabeledGraph k) [DecidableRel (A.glue B).graph.Adj] :
    homDensity (A.glue B).graph W =
      ∫ x, (∏ e ∈ labelEdges A ∪ labelEdges B, edgeFactor W x e) *
        (outerDensity W A x * outerDensity W B x) ∂Measure.pi fun _ => μ := by
  rw [homDensity_def, ← (measurePreserving_glueCoord A B).integral_comp',
    integral_prod _ (integrable_prod_edgeFactor_glueCoord W A B)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    integral_prod_edgeFactor_glueCoord W A B x)

/-- **Homomorphism densities are reflection positive**: every connection matrix of `t(·, W)` is
positive semidefinite. -/
theorem isReflectionPositive_homDensityParam : IsReflectionPositive (homDensityParam W) := by
  classical
  rw [isReflectionPositive_iff]
  intro k n A
  have hM : connectionMatrix (homDensityParam W) A = Matrix.of fun i j =>
      ∫ x, (∏ e ∈ labelEdges (A i) ∪ labelEdges (A j), edgeFactor W x e) *
        (outerDensity W (A i) x * outerDensity W (A j) x) ∂Measure.pi fun _ => μ := by
    ext i j
    rw [connectionMatrix_apply, LabeledGraph.forgetLabels_def, homDensityParam_apply,
      homDensity_glue, Matrix.of_apply]
  rw [hM]
  refine posSemidef_integral (Filter.Eventually.of_forall fun x => ?_)
    fun i j => integrable_glue W (A i) (A j)
  have h := (posSemidef_prod_union (fun i => labelEdges (A i)) (edgeFactor_nonneg W x)
    (edgeFactor_le_one W x)).hadamard (posSemidef_rankOne fun i => outerDensity W (A i) x)
  have heq : (Matrix.of fun i j => ∏ e ∈ labelEdges (A i) ∪ labelEdges (A j), edgeFactor W x e) ⊙
      (Matrix.of fun i j => star (outerDensity W (A i) x) * outerDensity W (A j) x) =
      fun i j => (∏ e ∈ labelEdges (A i) ∪ labelEdges (A j), edgeFactor W x e) *
        (outerDensity W (A i) x * outerDensity W (A j) x) := by
    ext i j
    rw [Matrix.hadamard_apply, Matrix.of_apply, Matrix.of_apply, star_trivial]
  exact heq ▸ h

end ReflectionPositive

end TauCeti.DenseGraphLimits
