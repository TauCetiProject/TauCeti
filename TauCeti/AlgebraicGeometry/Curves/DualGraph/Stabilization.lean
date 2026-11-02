/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Iso
import TauCeti.Data.Fin.Rev
import TauCeti.Logic.Equiv.Basic

/-!
# Stabilization of dual graphs is independent of the order of contractions

A pointed nodal curve in the stable range `2g - 2 + n > 0` is stabilized by repeatedly contracting
a rational tail carrying at most one marking or an unmarked rational bridge, recomputing the
special points after every contraction. On dual graphs these are the stabilization steps
`TauCeti.DualGraph.StabilizationStep`, and iterating them from any graph reaches a stable graph
(`TauCeti.DualGraph.exists_reflTransGen_stabilizationStep_isStable`). This file shows that the
stable graph reached does not depend on the order in which the contractions are performed: any
two stable graphs obtained from the same graph by stabilization steps are isomorphic.

Since each step removes a vertex, this follows, as in Newman's lemma, from the diamond property
up to isomorphism: two different steps from the same graph can each be followed by at most one
further step so that the results are isomorphic. If the two contracted components are far apart,
each remains contractible after the other is contracted, and contracting both in either order
gives isomorphic graphs. The cases where they meet are the following.

* A tail attached to a bridge: after contracting the tail, the bridge becomes a tail carrying the
  marking of the old tail, if any; contracting it, or contracting the bridge and then the tail,
  deletes both components and moves that marking to the other neighbour of the bridge.
* Two adjacent bridges: either order replaces the chain of the two bridges by a single node
  joining their outer neighbours.
* Two tails attached to each other, or two bridges joined by two nodes, would form the whole
  curve, of genus at most one with at most two markings, outside the stable range.

The argument is carried out for labelled graphs (`TauCeti.DualGraph.LabelledStabilizationStep`),
whose vertices carry labels that are kept by the remaining vertices and of which a predicate `P`
singles out the contractible ones. Both contractions of a diamond delete the same two vertices, so
the isomorphisms above preserve the labels. The stable range is only needed when every label
satisfies `P`, for otherwise some vertex is never contracted and the two contracted components
cannot form the whole curve. With the degrees of a map on the components as labels, this is the
order independence of map-aware stabilization; with labels in `Unit`, it is the statement for
graphs.

## Main results

* `TauCeti.DualGraph.LabelledStabilizationStep.exists_reflGen_iso`: the diamond property of
  labelled stabilization steps up to isomorphism preserving the labels.
* `TauCeti.DualGraph.exists_iso_of_reflTransGen_labelledStabilizationStep`: any two labelled
  graphs reached from the same labelled graph by labelled stabilization steps, and admitting no
  further step, are isomorphic by an isomorphism preserving the labels.
* `TauCeti.DualGraph.StabilizationStep.exists_reflGen_iso`: the diamond property of
  stabilization steps up to isomorphism, in the stable range.
* `TauCeti.DualGraph.nonempty_iso_of_reflTransGen_of_isStable`: any two stable graphs reached
  from the same graph by stabilization steps are isomorphic.

## References

* [Stacks, Tag 0E7N](https://stacks.math.columbia.edu/tag/0E7N), contracting rational tails and
  rational bridges.
* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161–199, §2, for stabilization of pointed curves.
* M. H. A. Newman, *On theories with a combinatorial definition of “equivalence”*, Ann. of Math.
  43 (1942), 223–243, for the passage from the diamond property to uniqueness of normal forms.
-/

public section

namespace TauCeti

namespace DualGraph

open Finset Function

universe u v w

variable {ι : Type v} {G : DualGraph.{u} ι}

/-! ### Isomorphisms of double contractions -/

section SubtypeSubtype

variable {v₁ v₂ : G.Vertex} {hne₁ : v₂ ≠ v₁} {hne₂ : v₁ ≠ v₂}
  [Fintype {w : {w : G.Vertex // w ≠ v₁} // w ≠ ⟨v₂, hne₁⟩}]
  [DecidableEq {w : {w : G.Vertex // w ≠ v₁} // w ≠ ⟨v₂, hne₁⟩}]
  {n₁ : Nonempty {w : {w : G.Vertex // w ≠ v₁} // w ≠ ⟨v₂, hne₁⟩}}
  [Fintype {w : {w : G.Vertex // w ≠ v₂} // w ≠ ⟨v₁, hne₂⟩}]
  [DecidableEq {w : {w : G.Vertex // w ≠ v₂} // w ≠ ⟨v₁, hne₂⟩}]
  {n₂ : Nonempty {w : {w : G.Vertex // w ≠ v₂} // w ≠ ⟨v₁, hne₂⟩}}
  {E₁ E₂ : Type u} [Fintype E₁] [DecidableEq E₁] [Fintype E₂] [DecidableEq E₂]
  {f₁ : E₁ → Fin 2 → {w : {w : G.Vertex // w ≠ v₁} // w ≠ ⟨v₂, hne₁⟩}}
  {f₂ : E₂ → Fin 2 → {w : {w : G.Vertex // w ≠ v₂} // w ≠ ⟨v₁, hne₂⟩}}
  {m₁ : ι → {w : {w : G.Vertex // w ≠ v₁} // w ≠ ⟨v₂, hne₁⟩}}
  {m₂ : ι → {w : {w : G.Vertex // w ≠ v₂} // w ≠ ⟨v₁, hne₂⟩}} {c₁ c₂}

/-- An isomorphism between a graph obtained from `G` by deleting `v₁` and then `v₂` and one
obtained by deleting `v₂` and then `v₁`, both keeping the genera of the remaining vertices, from a
bijection of their edges compatible with the ends and the markings in `G`. Contracting tails and
bridges deletes a vertex in this way, so this applies to any two double contractions of `G`, in
either order. -/
private def Iso.ofSubtypeSubtype (τ : E₁ ≃ E₂)
    (hτ : ∀ e, s((f₂ (τ e) 0).1.1, (f₂ (τ e) 1).1.1) = s((f₁ e 0).1.1, (f₁ e 1).1.1))
    (hm : ∀ i, (m₂ i).1.1 = (m₁ i).1.1) :
    Iso ⟨_, E₁, f₁, fun w ↦ G.genus w.1.1, m₁, c₁⟩ ⟨_, E₂, f₂, fun w ↦ G.genus w.1.1, m₂, c₂⟩ :=
  Iso.ofInjective (Subtype.val ∘ Subtype.val) (Subtype.val ∘ Subtype.val)
    (Subtype.val_injective.comp Subtype.val_injective)
    (Equiv.subtypeSubtypeComm (fun _ _ ↦ by simp [Subtype.ext_iff])
      fun _ _ ↦ by simp [Subtype.ext_iff])
    (fun _ ↦ Equiv.coe_coe_subtypeSubtypeComm_apply _ _ _) τ
    (fun e ↦ by simpa [ends_def] using hτ e)
    (fun _ ↦ congrArg G.genus (Equiv.coe_coe_subtypeSubtypeComm_apply _ _ _)) hm

/-- The isomorphism `Iso.ofSubtypeSubtype` fixes the underlying vertices of `G`. -/
private lemma Iso.coe_coe_ofSubtypeSubtype_vertexEquiv_apply (τ : E₁ ≃ E₂)
    (hτ : ∀ e, s((f₂ (τ e) 0).1.1, (f₂ (τ e) 1).1.1) = s((f₁ e 0).1.1, (f₁ e 1).1.1))
    (hm : ∀ i, (m₂ i).1.1 = (m₁ i).1.1) (w : {w : {w : G.Vertex // w ≠ v₁} // w ≠ ⟨v₂, hne₁⟩}) :
    ((Iso.ofSubtypeSubtype (n₁ := n₁) (n₂ := n₂) (c₁ := c₁) (c₂ := c₂) τ hτ hm).vertexEquiv w).1.1 =
      w.1.1 := by
  simp [Iso.ofSubtypeSubtype]

end SubtypeSubtype

/-! ### Auxiliary facts in the stable range -/

variable [Fintype ι]

/-- Two vertices of nonpositive log-canonical degree cannot carry all branches of the nodes
meeting them when the graph they would make up is in the stable range: its log-canonical degrees
add up to `2g - 2 + n > 0`. -/
private lemma false_of_forall_endpoint_mem_pair {v₁ v₂ : G.Vertex}
    (hrange : (∀ w, w = v₁ ∨ w = v₂) → 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι)
    (hne : v₁ ≠ v₂) (h₁ : G.logCanonicalDegree v₁ ≤ 0) (h₂ : G.logCanonicalDegree v₂ ≤ 0)
    (hclosed : ∀ e i, G.endpoint e i = v₁ ∨ G.endpoint e i = v₂ →
      G.endpoint e i.rev = v₁ ∨ G.endpoint e i.rev = v₂) : False := by
  have hall (w : G.Vertex) : w = v₁ ∨ w = v₂ := by
    induction G.reflTransGen_adj v₁ w with
    | refl => exact .inl rfl
    | @tail b c _ hbc ih =>
      obtain ⟨e, ⟨he₀, he₁⟩ | ⟨he₀, he₁⟩⟩ := adj_iff.mp hbc
      · have := hclosed e 0 (by rw [he₀]; exact ih)
        rwa [show (0 : Fin 2).rev = 1 from rfl, he₁] at this
      · have := hclosed e 1 (by rw [he₁]; exact ih)
        rwa [show (1 : Fin 2).rev = 0 from rfl, he₀] at this
  have hrange := hrange hall
  have huniv : (univ : Finset G.Vertex) = {v₁, v₂} := by
    ext w
    simpa using hall w
  have := G.sum_logCanonicalDegree
  rw [huniv, sum_pair hne] at this
  omega

/-- Two unmarked rational bridges are not joined by two nodes when the graph they would make up is
in the stable range. -/
private lemma bridgeNeighbor_rev_ne_of_bridgeNeighbor_eq {u w : G.Vertex}
    (hrange : (∀ x, x = u ∨ x = w) → 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι)
    (huw : u ≠ w)
    (hgu : G.genus u = 0) (hu : G.valence u = 2)
    (hloopu : ∀ e, G.endpoint e 0 = u → G.endpoint e 1 ≠ u) (hmu : ∀ i, G.marking i ≠ u)
    (hgw : G.genus w = 0) (hw : G.valence w = 2) (hmw : ∀ i, G.marking i ≠ w) {k : Fin 2}
    (hk : G.bridgeNeighbor hu k = w) : G.bridgeNeighbor hu k.rev ≠ w := by
  intro hk'
  have hnb (l : Fin 2) : G.bridgeNeighbor hu l = w := by
    rcases Fin.fin_two_eq_or_eq_rev k l with rfl | rfl
    exacts [hk, hk']
  have hlog {x : G.Vertex} (hgx : G.genus x = 0) (hx : G.valence x = 2)
      (hmx : ∀ i, G.marking i ≠ x) : G.logCanonicalDegree x ≤ 0 := by
    have : G.numMarkings x = 0 := by simp [numMarkings_def, hmx]
    rw [logCanonicalDegree_def, hgx, hx, this]
    omega
  refine false_of_forall_endpoint_mem_pair hrange huw (hlog hgu hu hmu) (hlog hgw hw hmw)
    fun e i hi ↦ ?_
  rcases hi with hi | hi
  · obtain ⟨l, hl⟩ := exists_eq_halfEdgeOfValenceEqTwo hu (h := (e, i)) hi
    refine .inr ?_
    rw [← hnb l, ← endpoint_halfEdgeOfValenceEqTwo_rev, hl]
  · -- The other branches of the two nodes at `u` are two distinct half-edges at `w`, hence all of
    -- them.
    refine .inl ?_
    have hx (l : Fin 2) : G.endpoint (G.halfEdgeOfValenceEqTwo hu l).1.1
        (G.halfEdgeOfValenceEqTwo hu l).1.2.rev = w :=
      (endpoint_halfEdgeOfValenceEqTwo_rev hu l).trans (hnb l)
    obtain ⟨m, hm⟩ := exists_eq_halfEdgeOfValenceEqTwo hw (h := (e, i)) hi
    obtain ⟨m₀, hm₀⟩ := exists_eq_halfEdgeOfValenceEqTwo hw
      (h := ((G.halfEdgeOfValenceEqTwo hu 0).1.1, (G.halfEdgeOfValenceEqTwo hu 0).1.2.rev)) (hx 0)
    obtain ⟨m₁, hm₁⟩ := exists_eq_halfEdgeOfValenceEqTwo hw
      (h := ((G.halfEdgeOfValenceEqTwo hu 1).1.1, (G.halfEdgeOfValenceEqTwo hu 1).1.2.rev)) (hx 1)
    have h01 : m₀ ≠ m₁ := by
      rintro rfl
      exact halfEdgeOfValenceEqTwo_fst_ne hu hloopu (Prod.ext_iff.mp (hm₀.symm.trans hm₁)).1
    obtain ⟨l, hl⟩ : ∃ l, (e, i) = ((G.halfEdgeOfValenceEqTwo hu l).1.1,
        (G.halfEdgeOfValenceEqTwo hu l).1.2.rev) := by
      rcases Fin.fin_two_eq_or_eq_rev m₀ m with rfl | rfl
      · exact ⟨0, hm.symm.trans hm₀⟩
      · obtain rfl : m₁ = m₀.rev := (Fin.fin_two_eq_or_eq_rev m₀ m₁).resolve_left (Ne.symm h01)
        exact ⟨1, hm.symm.trans hm₁⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hl
    rw [Fin.rev_rev]
    exact (G.halfEdgeOfValenceEqTwo hu l).2

/-! ### The diamond property -/

variable {α : Type w} {P : α → Prop}

/-- Two distinct rational tails with at most one marking each can be contracted in either
order, with isomorphic labelled results. -/
private lemma exists_iso_contractTail_contractTail (c : G.Vertex → α)
    (hrange : (∀ v, P (c v)) → 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι)
    {v₁ v₂ : G.Vertex} (hne : v₁ ≠ v₂) (hc₁ : P (c v₁)) (hg₁ : G.genus v₁ = 0)
    (hv₁ : G.valence v₁ = 1) (hm₁ : G.numMarkings v₁ ≤ 1) (hc₂ : P (c v₂)) (hg₂ : G.genus v₂ = 0)
    (hv₂ : G.valence v₂ = 1) (hm₂ : G.numMarkings v₂ ≤ 1) :
    ∃ y₁ y₂, LabelledStabilizationStep P ⟨G.contractTail hv₁, fun w ↦ c w.1⟩ y₁ ∧
      LabelledStabilizationStep P ⟨G.contractTail hv₂, fun w ↦ c w.1⟩ y₂ ∧
      ∃ f : y₁.1.Iso y₂.1, ∀ w, y₂.2 (f.vertexEquiv w) = y₁.2 w := by
  -- The two tails are not attached to each other: otherwise they would make up the whole graph.
  have hatt₁ : G.attachment hv₁ ≠ v₂ := by
    intro hatt
    have hatt' := attachment_eq_of_attachment_eq hv₁ hv₂ hatt
    refine false_of_forall_endpoint_mem_pair
      (fun hall ↦ hrange fun w ↦ (hall w).elim (· ▸ hc₁) (· ▸ hc₂)) hne ?_ ?_ fun e i hi ↦ ?_
    · rw [(G.isRationalTail_iff.mpr ⟨hg₁, hv₁⟩).logCanonicalDegree_eq]
      omega
    · rw [(G.isRationalTail_iff.mpr ⟨hg₂, hv₂⟩).logCanonicalDegree_eq]
      omega
    · rcases hi with hi | hi
      · exact .inr ((endpoint_rev_eq_attachment hv₁ hi).trans hatt)
      · exact .inl ((endpoint_rev_eq_attachment hv₂ hi).trans hatt')
  have hatt₂ : G.attachment hv₂ ≠ v₁ := fun h ↦ hatt₁ (attachment_eq_of_attachment_eq hv₂ hv₁ h)
  have hval₁ : (G.contractTail hv₂).valence ⟨v₁, hne⟩ = 1 :=
    (valence_contractTail_of_attachment_ne hv₂ hne hatt₂).trans hv₁
  have hval₂ : (G.contractTail hv₁).valence ⟨v₂, hne.symm⟩ = 1 :=
    (valence_contractTail_of_attachment_ne hv₁ hne.symm hatt₁).trans hv₂
  have hmark₁ : (G.contractTail hv₂).numMarkings ⟨v₁, hne⟩ ≤ 1 := by
    rw [numMarkings_contractTail, ite_eq_right hatt₂]
    omega
  have hmark₂ : (G.contractTail hv₁).numMarkings ⟨v₂, hne.symm⟩ ≤ 1 := by
    rw [numMarkings_contractTail, ite_eq_right hatt₁]
    omega
  have ha₁ := coe_attachment_contractTail hv₂ hv₁ hne hatt₁ hval₁
  have ha₂ := coe_attachment_contractTail hv₁ hv₂ hne.symm hatt₂ hval₂
  refine ⟨_, _,
    .contractTail _ ((G.contractTail hv₁).isRationalTail_iff.mpr ⟨hg₂, hval₂⟩) hmark₂ hc₂,
    .contractTail _ ((G.contractTail hv₂).isRationalTail_iff.mpr ⟨hg₁, hval₁⟩) hmark₁ hc₁,
    Iso.ofSubtypeSubtype (Equiv.subtypeSubtypeComm (fun _ _ ↦ by simp [Subtype.ext_iff])
      fun _ _ ↦ by simp [Subtype.ext_iff]) (fun _ ↦ by simp) (fun i ↦ ?_),
    fun _ ↦ congrArg c (Iso.coe_coe_ofSubtypeSubtype_vertexEquiv_apply ..)⟩
  by_cases h₁ : G.marking i = v₁ <;> by_cases h₂ : G.marking i = v₂ <;>
    simp [Subtype.ext_iff, h₁, h₂, hatt₁, hatt₂, ha₁, ha₂, hne, hne.symm]

/-- A rational tail `v₁` with at most one marking and an unmarked rational bridge `v₂` to which it
is not attached can be contracted in either order, with isomorphic labelled results. -/
private lemma exists_iso_contractTail_contractBridge_of_ne (c : G.Vertex → α) {v₁ v₂ : G.Vertex}
    (hne : v₁ ≠ v₂) (hc₁ : P (c v₁)) (hg₁ : G.genus v₁ = 0) (hv₁ : G.valence v₁ = 1)
    (hm₁ : G.numMarkings v₁ ≤ 1) (hc₂ : P (c v₂)) (hg₂ : G.genus v₂ = 0) (hv₂ : G.valence v₂ = 2)
    (hloop₂ : ∀ e, G.endpoint e 0 = v₂ → G.endpoint e 1 ≠ v₂) (hm₂ : ∀ i, G.marking i ≠ v₂)
    (hatt : G.attachment hv₁ ≠ v₂) :
    ∃ y₁ y₂, LabelledStabilizationStep P ⟨G.contractTail hv₁, fun w ↦ c w.1⟩ y₁ ∧
      LabelledStabilizationStep P ⟨G.contractBridge hv₂ hloop₂ hm₂, fun w ↦ c w.1⟩ y₂ ∧
      ∃ f : y₁.1.Iso y₂.1, ∀ w, y₂.2 (f.vertexEquiv w) = y₁.2 w := by
  -- The tail is attached elsewhere, so it is not a neighbour of the bridge.
  have hnb (k : Fin 2) : G.bridgeNeighbor hv₂ k ≠ v₁ := by
    intro hk
    rw [← endpoint_halfEdgeOfValenceEqTwo_rev] at hk
    have := endpoint_rev_eq_attachment hv₁ hk
    rw [Fin.rev_rev, (G.halfEdgeOfValenceEqTwo hv₂ k).2] at this
    exact hatt this.symm
  have hval₂ : (G.contractTail hv₁).valence ⟨v₂, hne.symm⟩ = 2 :=
    (valence_contractTail_of_attachment_ne hv₁ hne.symm hatt).trans hv₂
  have hval₁ : (G.contractBridge hv₂ hloop₂ hm₂).valence ⟨v₁, hne⟩ = 1 :=
    (valence_contractBridge hv₂ hloop₂ hm₂ v₁ hne).trans hv₁
  have hmark₁ : (G.contractBridge hv₂ hloop₂ hm₂).numMarkings ⟨v₁, hne⟩ ≤ 1 :=
    (numMarkings_contractBridge hv₂ hloop₂ hm₂ v₁ hne).trans_le hm₁
  have ha := coe_attachment_contractBridge hv₂ hloop₂ hm₂ hv₁ hne hatt hval₁
  refine ⟨_, _,
    .contractBridge _ ((G.contractTail hv₁).isRationalBridge_iff.mpr
      ⟨hg₂, hval₂, forall_endpoint_one_ne_contractTail hv₁ hne.symm hloop₂⟩)
      (marking_contractTail_ne hv₁ hne.symm hm₂ hatt) hc₂,
    .contractTail _ ((G.contractBridge hv₂ hloop₂ hm₂).isRationalTail_iff.mpr ⟨hg₁, hval₁⟩) hmark₁
      hc₁,
    Iso.ofSubtypeSubtype
      { toFun := fun
          | none => ⟨none, fun k h ↦ hnb k (congrArg Subtype.val h)⟩
          | some e => ⟨some ⟨e.1.1, fun i h ↦ e.2 i (Subtype.ext h)⟩,
              fun i h ↦ e.1.2 i (congrArg Subtype.val h)⟩
        invFun := fun
          | ⟨none, _⟩ => none
          | ⟨some e, h⟩ => some ⟨⟨e.1, fun i h' ↦ h i (Subtype.ext h')⟩,
              fun i h' ↦ e.2 i (congrArg Subtype.val h')⟩
        left_inv := by rintro (_ | _) <;> rfl
        right_inv := by rintro ⟨_ | _, _⟩ <;> rfl }
      (fun e ↦ ?_) (fun i ↦ ?_),
    fun _ ↦ congrArg c (Iso.coe_coe_ofSubtypeSubtype_vertexEquiv_apply ..)⟩
  · cases e with
    | none =>
      simpa using (sym2_coe_bridgeNeighbor_contractTail hv₁ hv₂ hne.symm hnb hval₂).symm
    | some e => simp
  · by_cases h₁ : G.marking i = v₁ <;>
      simp [Subtype.ext_iff, h₁, ha]

/-- A rational tail `v₁` with at most one marking attached to an unmarked rational bridge `v₂` can
be contracted together with the bridge in either order: both orders delete the two components and
move the marking of the tail to the other neighbour of the bridge. -/
private lemma exists_iso_contractTail_contractBridge_of_eq (c : G.Vertex → α) {v₁ v₂ : G.Vertex}
    (hne : v₁ ≠ v₂) (hc₁ : P (c v₁)) (hg₁ : G.genus v₁ = 0) (hv₁ : G.valence v₁ = 1)
    (hm₁ : G.numMarkings v₁ ≤ 1) (hc₂ : P (c v₂)) (hg₂ : G.genus v₂ = 0) (hv₂ : G.valence v₂ = 2)
    (hloop₂ : ∀ e, G.endpoint e 0 = v₂ → G.endpoint e 1 ≠ v₂) (hm₂ : ∀ i, G.marking i ≠ v₂)
    (hatt : G.attachment hv₁ = v₂) :
    ∃ y₁ y₂, LabelledStabilizationStep P ⟨G.contractTail hv₁, fun w ↦ c w.1⟩ y₁ ∧
      LabelledStabilizationStep P ⟨G.contractBridge hv₂ hloop₂ hm₂, fun w ↦ c w.1⟩ y₂ ∧
      ∃ f : y₁.1.Iso y₂.1, ∀ w, y₂.2 (f.vertexEquiv w) = y₁.2 w := by
  -- The tail is one of the two neighbours of the bridge, and is not the other one.
  obtain ⟨k, hk⟩ : ∃ k, G.bridgeNeighbor hv₂ k = v₁ := by
    obtain ⟨⟨e, i⟩, he⟩ := exists_endpoint_eq_of_valence_pos (G := G) (by omega : 0 < G.valence v₁)
    have h' : G.endpoint e i.rev = v₂ := (endpoint_rev_eq_attachment hv₁ he).trans hatt
    obtain ⟨k, hk⟩ := exists_eq_halfEdgeOfValenceEqTwo hv₂ (h := (e, i.rev)) h'
    refine ⟨k, ?_⟩
    rw [← endpoint_halfEdgeOfValenceEqTwo_rev, hk, Fin.rev_rev, he]
  have hk' := bridgeNeighbor_rev_ne hv₂ hloop₂ hv₁ hk
  have hval₂ : (G.contractTail hv₁).valence ⟨v₂, hne.symm⟩ = 1 := by
    have := valence_contractTail hv₁ v₂ hne.symm
    rw [ite_eq_left hatt] at this
    omega
  have hmark₂ : (G.contractTail hv₁).numMarkings ⟨v₂, hne.symm⟩ ≤ 1 := by
    have : G.numMarkings v₂ = 0 := by simp [numMarkings_def, hm₂]
    rw [numMarkings_contractTail, ite_eq_left hatt]
    omega
  have hval₁ : (G.contractBridge hv₂ hloop₂ hm₂).valence ⟨v₁, hne⟩ = 1 :=
    (valence_contractBridge hv₂ hloop₂ hm₂ v₁ hne).trans hv₁
  have hmark₁ : (G.contractBridge hv₂ hloop₂ hm₂).numMarkings ⟨v₁, hne⟩ ≤ 1 :=
    (numMarkings_contractBridge hv₂ hloop₂ hm₂ v₁ hne).trans_le hm₁
  -- After either contraction, the remaining component is attached to the other neighbour of the
  -- bridge.
  have ha₂ : ((G.contractTail hv₁).attachment hval₂).1 = G.bridgeNeighbor hv₂ k.rev := by
    rw [← endpoint_rev_eq_attachment hval₂
      (e := ⟨_, forall_endpoint_halfEdgeOfValenceEqTwo_ne hv₂ hne.symm hk'⟩)
      (i := (G.halfEdgeOfValenceEqTwo hv₂ k.rev).1.2)
      (Subtype.ext (G.halfEdgeOfValenceEqTwo hv₂ k.rev).2)]
    exact endpoint_halfEdgeOfValenceEqTwo_rev hv₂ k.rev
  have ha₁ : ((G.contractBridge hv₂ hloop₂ hm₂).attachment hval₁).1 =
      G.bridgeNeighbor hv₂ k.rev := by
    rw [← endpoint_rev_eq_attachment hval₁ (e := none) (i := k) (Subtype.ext hk),
      endpoint_contractBridge_none]
  -- The node replacing the bridge meets the tail, so it is deleted with the tail.
  have hnone : ¬ ∀ i, (G.contractBridge hv₂ hloop₂ hm₂).endpoint none i ≠ ⟨v₁, hne⟩ :=
    fun h ↦ h k (Subtype.ext hk)
  refine ⟨_, _,
    .contractTail _ ((G.contractTail hv₁).isRationalTail_iff.mpr ⟨hg₂, hval₂⟩) hmark₂ hc₂,
    .contractTail _ ((G.contractBridge hv₂ hloop₂ hm₂).isRationalTail_iff.mpr ⟨hg₁, hval₁⟩) hmark₁
      hc₁,
    Iso.ofSubtypeSubtype
      { toFun := fun e ↦ ⟨some ⟨e.1.1, fun i h ↦ e.2 i (Subtype.ext h)⟩,
          fun i h ↦ e.1.2 i (congrArg Subtype.val h)⟩
        invFun := fun
          | ⟨none, h⟩ => (hnone h).elim
          | ⟨some e, h⟩ => ⟨⟨e.1, fun i h' ↦ h i (Subtype.ext h')⟩,
              fun i h' ↦ e.2 i (congrArg Subtype.val h')⟩
        left_inv _ := rfl
        right_inv := by
          rintro ⟨_ | _, h⟩
          · exact (hnone h).elim
          · rfl }
      (fun _ ↦ by simp) (fun i ↦ ?_),
    fun _ ↦ congrArg c (Iso.coe_coe_ofSubtypeSubtype_vertexEquiv_apply ..)⟩
  by_cases h₁ : G.marking i = v₁ <;>
    simp [Subtype.ext_iff, h₁, hm₂ i, ha₁, ha₂, hatt]

/-- Two unmarked rational bridges which are not adjacent can be contracted in either order, with
isomorphic results. -/
private lemma exists_iso_contractBridge_contractBridge_of_forall_ne (c : G.Vertex → α)
    {v₁ v₂ : G.Vertex} (hne : v₁ ≠ v₂) (hc₁ : P (c v₁)) (hg₁ : G.genus v₁ = 0)
    (hv₁ : G.valence v₁ = 2) (hloop₁ : ∀ e, G.endpoint e 0 = v₁ → G.endpoint e 1 ≠ v₁)
    (hm₁ : ∀ i, G.marking i ≠ v₁) (hc₂ : P (c v₂)) (hg₂ : G.genus v₂ = 0) (hv₂ : G.valence v₂ = 2)
    (hloop₂ : ∀ e, G.endpoint e 0 = v₂ → G.endpoint e 1 ≠ v₂) (hm₂ : ∀ i, G.marking i ≠ v₂)
    (hnb₁ : ∀ k, G.bridgeNeighbor hv₁ k ≠ v₂) :
    ∃ y₁ y₂, LabelledStabilizationStep P ⟨G.contractBridge hv₁ hloop₁ hm₁, fun w ↦ c w.1⟩ y₁ ∧
      LabelledStabilizationStep P ⟨G.contractBridge hv₂ hloop₂ hm₂, fun w ↦ c w.1⟩ y₂ ∧
      ∃ f : y₁.1.Iso y₂.1, ∀ w, y₂.2 (f.vertexEquiv w) = y₁.2 w := by
  have hnb₂ (k : Fin 2) : G.bridgeNeighbor hv₂ k ≠ v₁ := fun hk ↦ by
    obtain ⟨l, hl⟩ := exists_bridgeNeighbor_eq hv₂ hv₁ hk
    exact hnb₁ l hl
  have hval₂ : (G.contractBridge hv₁ hloop₁ hm₁).valence ⟨v₂, hne.symm⟩ = 2 :=
    (valence_contractBridge hv₁ hloop₁ hm₁ v₂ hne.symm).trans hv₂
  have hval₁ : (G.contractBridge hv₂ hloop₂ hm₂).valence ⟨v₁, hne⟩ = 2 :=
    (valence_contractBridge hv₂ hloop₂ hm₂ v₁ hne).trans hv₁
  refine ⟨_, _,
    .contractBridge _ ((G.contractBridge hv₁ hloop₁ hm₁).isRationalBridge_iff.mpr
      ⟨hg₂, hval₂, forall_endpoint_one_ne_contractBridge hv₁ hloop₁ hm₁ hne.symm hloop₂ (hnb₁ 0)⟩)
      (marking_contractBridge_ne hv₁ hloop₁ hm₁ hne.symm hm₂) hc₂,
    .contractBridge _ ((G.contractBridge hv₂ hloop₂ hm₂).isRationalBridge_iff.mpr
      ⟨hg₁, hval₁, forall_endpoint_one_ne_contractBridge hv₂ hloop₂ hm₂ hne hloop₁ (hnb₂ 0)⟩)
      (marking_contractBridge_ne hv₂ hloop₂ hm₂ hne hm₁) hc₁,
    Iso.ofSubtypeSubtype
      -- The node replacing either bridge is the node replacing it in the other order.
      { toFun := fun
          | none => some ⟨none, fun k h ↦ hnb₂ k (congrArg Subtype.val h)⟩
          | some ⟨none, _⟩ => none
          | some ⟨some e, h⟩ => some ⟨some ⟨e.1, fun i h' ↦ h i (Subtype.ext h')⟩,
              fun i h' ↦ e.2 i (congrArg Subtype.val h')⟩
        invFun := fun
          | none => some ⟨none, fun k h ↦ hnb₁ k (congrArg Subtype.val h)⟩
          | some ⟨none, _⟩ => none
          | some ⟨some e, h⟩ => some ⟨some ⟨e.1, fun i h' ↦ h i (Subtype.ext h')⟩,
              fun i h' ↦ e.2 i (congrArg Subtype.val h')⟩
        left_inv := by rintro (_ | ⟨_ | _, _⟩) <;> rfl
        right_inv := by rintro (_ | ⟨_ | _, _⟩) <;> rfl }
      (fun e ↦ ?_) (fun _ ↦ by simp),
    fun _ ↦ congrArg c (Iso.coe_coe_ofSubtypeSubtype_vertexEquiv_apply ..)⟩
  rcases e with _ | ⟨_ | e, _⟩
  · simpa using (sym2_coe_bridgeNeighbor_contractBridge hv₁ hloop₁ hm₁ hv₂ hne.symm hnb₂
      hval₂).symm
  · simpa using sym2_coe_bridgeNeighbor_contractBridge hv₂ hloop₂ hm₂ hv₁ hne hnb₁ hval₁
  · simp

/-- Two unmarked rational bridges joined by a node can be contracted in either order: both orders
replace the chain of the two bridges by a single node joining their other neighbours. -/
private lemma exists_iso_contractBridge_contractBridge_of_eq (c : G.Vertex → α)
    (hrange : (∀ v, P (c v)) → 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι)
    {v₁ v₂ : G.Vertex} (hne : v₁ ≠ v₂) (hc₁ : P (c v₁)) (hg₁ : G.genus v₁ = 0)
    (hv₁ : G.valence v₁ = 2) (hloop₁ : ∀ e, G.endpoint e 0 = v₁ → G.endpoint e 1 ≠ v₁)
    (hm₁ : ∀ i, G.marking i ≠ v₁) (hc₂ : P (c v₂)) (hg₂ : G.genus v₂ = 0) (hv₂ : G.valence v₂ = 2)
    (hloop₂ : ∀ e, G.endpoint e 0 = v₂ → G.endpoint e 1 ≠ v₂) (hm₂ : ∀ i, G.marking i ≠ v₂)
    {k : Fin 2} (hk : G.bridgeNeighbor hv₁ k = v₂) :
    ∃ y₁ y₂, LabelledStabilizationStep P ⟨G.contractBridge hv₁ hloop₁ hm₁, fun w ↦ c w.1⟩ y₁ ∧
      LabelledStabilizationStep P ⟨G.contractBridge hv₂ hloop₂ hm₂, fun w ↦ c w.1⟩ y₂ ∧
      ∃ f : y₁.1.Iso y₂.1, ∀ w, y₂.2 (f.vertexEquiv w) = y₁.2 w := by
  obtain ⟨l, hl⟩ := exists_bridgeNeighbor_eq hv₁ hv₂ hk
  have hk' := bridgeNeighbor_rev_ne_of_bridgeNeighbor_eq
    (fun hall ↦ hrange fun w ↦ (hall w).elim (· ▸ hc₁) (· ▸ hc₂)) hne hg₁ hv₁ hloop₁ hm₁ hg₂ hv₂
    hm₂ hk
  have hl' := bridgeNeighbor_rev_ne_of_bridgeNeighbor_eq
    (fun hall ↦ hrange fun w ↦ (hall w).elim (· ▸ hc₂) (· ▸ hc₁)) hne.symm hg₂ hv₂ hloop₂ hm₂ hg₁
    hv₁ hm₁ hl
  have hval₂ : (G.contractBridge hv₁ hloop₁ hm₁).valence ⟨v₂, hne.symm⟩ = 2 :=
    (valence_contractBridge hv₁ hloop₁ hm₁ v₂ hne.symm).trans hv₂
  have hval₁ : (G.contractBridge hv₂ hloop₂ hm₂).valence ⟨v₁, hne⟩ = 2 :=
    (valence_contractBridge hv₂ hloop₂ hm₂ v₁ hne).trans hv₁
  -- The node replacing the first bridge meets the second one, so it is replaced in turn.
  have hnone₁ : ¬ ∀ i, (G.contractBridge hv₁ hloop₁ hm₁).endpoint none i ≠ ⟨v₂, hne.symm⟩ :=
    fun h ↦ h k (Subtype.ext hk)
  have hnone₂ : ¬ ∀ i, (G.contractBridge hv₂ hloop₂ hm₂).endpoint none i ≠ ⟨v₁, hne⟩ :=
    fun h ↦ h l (Subtype.ext hl)
  refine ⟨_, _,
    -- The node replacing one bridge is not a loop at the other bridge.
    .contractBridge _ ((G.contractBridge hv₁ hloop₁ hm₁).isRationalBridge_iff.mpr
      ⟨hg₂, hval₂, forall_endpoint_one_ne_contractBridge hv₁ hloop₁ hm₁ hne.symm hloop₂ hk'⟩)
      (marking_contractBridge_ne hv₁ hloop₁ hm₁ hne.symm hm₂) hc₂,
    .contractBridge _ ((G.contractBridge hv₂ hloop₂ hm₂).isRationalBridge_iff.mpr
      ⟨hg₁, hval₁, forall_endpoint_one_ne_contractBridge hv₂ hloop₂ hm₂ hne hloop₁ hl'⟩)
      (marking_contractBridge_ne hv₂ hloop₂ hm₂ hne hm₁) hc₁,
    Iso.ofSubtypeSubtype
      { toFun := fun
          | none => none
          | some ⟨none, h⟩ => (hnone₁ h).elim
          | some ⟨some e, h⟩ => some ⟨some ⟨e.1, fun i h' ↦ h i (Subtype.ext h')⟩,
              fun i h' ↦ e.2 i (congrArg Subtype.val h')⟩
        invFun := fun
          | none => none
          | some ⟨none, h⟩ => (hnone₂ h).elim
          | some ⟨some e, h⟩ => some ⟨some ⟨e.1, fun i h' ↦ h i (Subtype.ext h')⟩,
              fun i h' ↦ e.2 i (congrArg Subtype.val h')⟩
        left_inv := by
          rintro (_ | ⟨_ | _, h⟩)
          · rfl
          · exact (hnone₁ h).elim
          · rfl
        right_inv := by
          rintro (_ | ⟨_ | _, h⟩)
          · rfl
          · exact (hnone₂ h).elim
          · rfl }
      (fun e ↦ ?_) (fun _ ↦ by simp),
    fun _ ↦ congrArg c (Iso.coe_coe_ofSubtypeSubtype_vertexEquiv_apply ..)⟩
  rcases e with _ | ⟨_ | e, h⟩
  · have h₁ := sym2_coe_bridgeNeighbor_contractBridge_of_bridgeNeighbor_eq hv₂ hloop₂ hm₂ hv₁
      hne.symm hl hk' hval₁
    have h₂ := sym2_coe_bridgeNeighbor_contractBridge_of_bridgeNeighbor_eq hv₁ hloop₁ hm₁ hv₂ hne hk
      hl' hval₂
    simp [h₁, h₂]
  · exact (hnone₁ h).elim
  · simp

/-- **The diamond property up to isomorphism.** Two labelled stabilization steps from the same
labelled graph can each be followed by at most one further step so that the results are isomorphic
by an isomorphism preserving the labels. The stable range `2g - 2 + n > 0` is needed only when
every label satisfies `P`. -/
theorem LabelledStabilizationStep.exists_reflGen_iso
    {x y₁ y₂ : Σ G : DualGraph.{u} ι, G.Vertex → α}
    (hrange : (∀ v, P (x.2 v)) → 0 < 2 * (x.1.arithmeticGenus : ℤ) - 2 + Fintype.card ι)
    (h₁ : LabelledStabilizationStep P x y₁) (h₂ : LabelledStabilizationStep P x y₂) :
    ∃ z₁ z₂, Relation.ReflGen (LabelledStabilizationStep P) y₁ z₁ ∧
      Relation.ReflGen (LabelledStabilizationStep P) y₂ z₂ ∧
      ∃ f : z₁.1.Iso z₂.1, ∀ w, z₂.2 (f.vertexEquiv w) = z₁.2 w := by
  have single {z₁ z₂ : Σ G : DualGraph.{u} ι, G.Vertex → α}
      (hz₁ : LabelledStabilizationStep P y₁ z₁) (hz₂ : LabelledStabilizationStep P y₂ z₂)
      (f : ∃ f : z₁.1.Iso z₂.1, ∀ w, z₂.2 (f.vertexEquiv w) = z₁.2 w) :
      ∃ z₁ z₂, Relation.ReflGen (LabelledStabilizationStep P) y₁ z₁ ∧
        Relation.ReflGen (LabelledStabilizationStep P) y₂ z₂ ∧
        ∃ f : z₁.1.Iso z₂.1, ∀ w, z₂.2 (f.vertexEquiv w) = z₁.2 w :=
    ⟨z₁, z₂, .single hz₁, .single hz₂, f⟩
  obtain ⟨G, c⟩ := x
  cases h₁ with
  | @contractTail _ _ v₁ hv₁ hm₁ hc₁ =>
    obtain ⟨hg₁, hv₁⟩ := G.isRationalTail_iff.mp hv₁
    cases h₂ with
    | @contractTail _ _ v₂ hv₂ hm₂ hc₂ =>
      obtain ⟨hg₂, hv₂⟩ := G.isRationalTail_iff.mp hv₂
      by_cases hne : v₁ = v₂
      · subst hne
        exact ⟨_, _, .refl, .refl, .refl _, fun _ ↦ by simp⟩
      · obtain ⟨z₁, z₂, hz₁, hz₂, f⟩ :=
          exists_iso_contractTail_contractTail c hrange hne hc₁ hg₁ hv₁ hm₁ hc₂ hg₂ hv₂ hm₂
        exact single hz₁ hz₂ f
    | @contractBridge _ _ v₂ hv₂ hm₂ hc₂ =>
      obtain ⟨hg₂, hv₂, hloop₂⟩ := G.isRationalBridge_iff.mp hv₂
      have hne : v₁ ≠ v₂ := by
        rintro rfl
        omega
      by_cases hatt : G.attachment hv₁ = v₂
      · obtain ⟨z₁, z₂, hz₁, hz₂, f⟩ := exists_iso_contractTail_contractBridge_of_eq c hne hc₁ hg₁
          hv₁ hm₁ hc₂ hg₂ hv₂ hloop₂ hm₂ hatt
        exact single hz₁ hz₂ f
      · obtain ⟨z₁, z₂, hz₁, hz₂, f⟩ := exists_iso_contractTail_contractBridge_of_ne c hne hc₁ hg₁
          hv₁ hm₁ hc₂ hg₂ hv₂ hloop₂ hm₂ hatt
        exact single hz₁ hz₂ f
  | @contractBridge _ _ v₁ hv₁ hm₁ hc₁ =>
    obtain ⟨hg₁, hv₁, hloop₁⟩ := G.isRationalBridge_iff.mp hv₁
    cases h₂ with
    | @contractTail _ _ v₂ hv₂ hm₂ hc₂ =>
      obtain ⟨hg₂, hv₂⟩ := G.isRationalTail_iff.mp hv₂
      have hne : v₂ ≠ v₁ := by
        rintro rfl
        omega
      by_cases hatt : G.attachment hv₂ = v₁
      · obtain ⟨z₂, z₁, hz₂, hz₁, f⟩ := exists_iso_contractTail_contractBridge_of_eq c hne hc₂ hg₂
          hv₂ hm₂ hc₁ hg₁ hv₁ hloop₁ hm₁ hatt
        exact single hz₁ hz₂ (exists_iso_symm f)
      · obtain ⟨z₂, z₁, hz₂, hz₁, f⟩ := exists_iso_contractTail_contractBridge_of_ne c hne hc₂ hg₂
          hv₂ hm₂ hc₁ hg₁ hv₁ hloop₁ hm₁ hatt
        exact single hz₁ hz₂ (exists_iso_symm f)
    | @contractBridge _ _ v₂ hv₂ hm₂ hc₂ =>
      obtain ⟨hg₂, hv₂, hloop₂⟩ := G.isRationalBridge_iff.mp hv₂
      by_cases hne : v₁ = v₂
      · subst hne
        exact ⟨_, _, .refl, .refl, .refl _, fun _ ↦ by simp⟩
      by_cases hadj : ∃ k, G.bridgeNeighbor hv₁ k = v₂
      · obtain ⟨k, hk⟩ := hadj
        obtain ⟨z₁, z₂, hz₁, hz₂, f⟩ := exists_iso_contractBridge_contractBridge_of_eq c hrange hne
          hc₁ hg₁ hv₁ hloop₁ hm₁ hc₂ hg₂ hv₂ hloop₂ hm₂ hk
        exact single hz₁ hz₂ f
      · obtain ⟨z₁, z₂, hz₁, hz₂, f⟩ := exists_iso_contractBridge_contractBridge_of_forall_ne c hne
          hc₁ hg₁ hv₁ hloop₁ hm₁ hc₂ hg₂ hv₂ hloop₂ hm₂ fun k hk ↦ hadj ⟨k, hk⟩
        exact single hz₁ hz₂ f

/-- **The diamond property up to isomorphism.** In the stable range, two stabilization steps from
the same graph can each be followed by at most one further step so that the results are
isomorphic. -/
theorem StabilizationStep.exists_reflGen_iso
    (hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι) {H₁ H₂ : DualGraph.{u} ι}
    (h₁ : StabilizationStep G H₁) (h₂ : StabilizationStep G H₂) :
    ∃ K₁ K₂, Relation.ReflGen StabilizationStep H₁ K₁ ∧
      Relation.ReflGen StabilizationStep H₂ K₂ ∧ Nonempty (K₁.Iso K₂) := by
  obtain ⟨z₁, z₂, hz₁, hz₂, f, -⟩ := h₁.labelledStabilizationStep.exists_reflGen_iso
    (fun _ ↦ hrange) h₂.labelledStabilizationStep
  refine ⟨z₁.1, z₂.1, ?_, ?_, ⟨f⟩⟩
  · cases hz₁ with
    | refl => exact .refl
    | single h => exact .single h.fst
  · cases hz₂ with
    | refl => exact .refl
    | single h => exact .single h.fst

/-- **Labelled stabilization is independent of the order of contractions.** Any two labelled
graphs reached from the same labelled graph by labelled stabilization steps, and admitting no
further step, are isomorphic by an isomorphism preserving the labels. The stable range
`2g - 2 + n > 0` is needed only when every label satisfies `P`. -/
theorem exists_iso_of_reflTransGen_labelledStabilizationStep
    {x y₁ y₂ : Σ G : DualGraph.{u} ι, G.Vertex → α}
    (hrange : (∀ v, P (x.2 v)) → 0 < 2 * (x.1.arithmeticGenus : ℤ) - 2 + Fintype.card ι)
    (h₁ : Relation.ReflTransGen (LabelledStabilizationStep P) x y₁)
    (h₂ : Relation.ReflTransGen (LabelledStabilizationStep P) x y₂)
    (hy₁ : ∀ z, ¬ LabelledStabilizationStep P y₁ z)
    (hy₂ : ∀ z, ¬ LabelledStabilizationStep P y₂ z) :
    ∃ f : y₁.1.Iso y₂.1, ∀ w, y₂.2 (f.vertexEquiv w) = y₁.2 w := by
  induction hn : Fintype.card x.1.Vertex using Nat.strong_induction_on generalizing x y₁ y₂ with
  | _ n ih =>
  rcases h₁.cases_head with rfl | ⟨z₁, hxz₁, hz₁y₁⟩
  · rcases h₂.cases_head with rfl | ⟨z₂, hxz₂, -⟩
    · exact ⟨.refl _, fun _ ↦ by simp⟩
    · exact (hy₁ _ hxz₂).elim
  rcases h₂.cases_head with rfl | ⟨z₂, hxz₂, hz₂y₂⟩
  · exact (hy₂ _ hxz₁).elim
  -- Complete the diamond from `x`, then reduce one corner as far as possible and transport the
  -- result along the isomorphism to the other corner.
  obtain ⟨l₁, l₂, hzl₁, hzl₂, f, hf⟩ := hxz₁.exists_reflGen_iso hrange hxz₂
  obtain ⟨s, hl₁s, hs⟩ := exists_reflTransGen_labelledStabilizationStep_forall_not (P := P) l₁
  obtain ⟨s', hl₂s', g⟩ := exists_reflTransGen_labelledStabilizationStep_iso hl₁s f hf
  have hs' (z) : ¬ LabelledStabilizationStep P s' z := fun hz ↦ by
    obtain ⟨g', hg'⟩ := exists_iso_symm g
    obtain ⟨z', hz', -⟩ := hz.exists_iso g' hg'
    exact hs z' hz'
  have a := ih _ (hn ▸ hxz₁.fst.card_vertex_lt)
    (hxz₁.two_mul_arithmeticGenus_sub_two_add_card_pos hrange) hz₁y₁
    (hzl₁.to_reflTransGen.trans hl₁s) hy₁ hs rfl
  have b := ih _ (hn ▸ hxz₂.fst.card_vertex_lt)
    (hxz₂.two_mul_arithmeticGenus_sub_two_add_card_pos hrange) hz₂y₂
    (hzl₂.to_reflTransGen.trans hl₂s') hy₂ hs' rfl
  exact exists_iso_trans a (exists_iso_trans g (exists_iso_symm b))

/-- **Stabilization is independent of the order of contractions.** Any two stable graphs reached
from the same graph by stabilization steps are isomorphic. The starting graph is then in the stable
range `2g - 2 + n > 0`, since the steps preserve `g` and `n`. -/
theorem nonempty_iso_of_reflTransGen_of_isStable {H₁ H₂ : DualGraph.{u} ι}
    (h₁ : Relation.ReflTransGen StabilizationStep G H₁)
    (h₂ : Relation.ReflTransGen StabilizationStep G H₂) (hH₁ : H₁.IsStable) (hH₂ : H₂.IsStable) :
    Nonempty (H₁.Iso H₂) := by
  have hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι := by
    simpa [arithmeticGenus_eq_of_reflTransGen h₁] using
      hH₁.two_mul_arithmeticGenus_sub_two_add_card_pos
  obtain ⟨f, -⟩ := exists_iso_of_reflTransGen_labelledStabilizationStep (fun _ ↦ hrange)
    (reflTransGen_labelledStabilizationStep_of_reflTransGen h₁)
    (reflTransGen_labelledStabilizationStep_of_reflTransGen h₂)
    (fun _ h ↦ hH₁.not_stabilizationStep h.fst) (fun _ h ↦ hH₂.not_stabilizationStep h.fst)
  exact ⟨f⟩

end DualGraph

end TauCeti
