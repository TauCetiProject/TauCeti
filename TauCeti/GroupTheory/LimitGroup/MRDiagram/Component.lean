/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Zariski
public import TauCeti.GroupTheory.LimitGroup.MRDiagram.Basic
import TauCeti.Topology.NoetherianSpace.Decomposition

/-!
# Makanin–Razborov diagrams and irreducible components

Let `D` be a Makanin–Razborov diagram over the coefficient group `A`, let `L` be a target
receiving the coefficients, and let `x` be a tuple of the root group of `D` such that the values
at `x` of the `A`-homomorphisms from the root group to `L` are the solutions in `L` of a system
`S` of equations (for instance the variables in the coordinate group of `S`). Each edge at the
root then contributes a set of solutions of `S`: the values at `x` of the branch composites
through this edge. If the diagram is complete, these finitely many sets cover the solution set
of `S`; if moreover they are Zariski irreducible, the irreducible components of the solution set
are among their Zariski closures.

The sets of solutions obtained through the edges at the root (`MRDiagram.edgeImage`) and their
covering of the solution set (`MRDiagram.iUnion_edgeImage_eq_V_of_isComplete`) are in
`TauCeti.GroupTheory.LimitGroup.MRDiagram.Basic`.

## Main definitions

* `MRDiagram.IsComponentNormalized`: the Zariski closures of the sets of solutions obtained
  through the individual edges at the root are pairwise distinct and are exactly the irreducible
  components of the solution set of `S`.

## Main results

* `MRDiagram.maximal_isIrreducible_iff_exists_closure_edgeImage`: for a complete diagram whose
  edges at the root have Zariski irreducible sets of solutions, the irreducible components of the
  solution set are the inclusion-maximal Zariski closures of these sets.
* `MRDiagram.isComponentNormalized_node_iff_of_isComplete`: such a diagram is
  component-normalized exactly when no closure is contained in another one.
* `MRDiagram.isComponentNormalized_edge_iff_of_isComplete`,
  `MRDiagram.isComponentNormalized_freeRoot_iff_isIrreducible`: a complete diagram with a single
  edge at its root, for instance the one-edge diagram of a free `A`-group, is
  component-normalized exactly when the solution set is irreducible.
* `MRDiagram.IsComponentNormalized.ncard_setOf_maximal_isIrreducible_eq`: in a
  component-normalized diagram whose root is not a leaf, the number of edges at the root is the
  number of irreducible components of the solution set; so it is one for an irreducible solution
  set (`MRDiagram.IsComponentNormalized.eq_one_of_isIrreducible`).

Completeness does not imply component-normalization: the root may carry an edge whose solutions
are already obtained through another one, or two edges with the same closure. The canonical
diagram of a limit group, whose root carries the modular group and has one proper quotient edge
for each maximal shortening quotient, is in general not component-normalized either: the
condition is meant for diagrams whose edges at the root go to the coordinate groups of the
irreducible components of the solution set.

## References

* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, in: Groups, Languages,
  Algorithms, Contemp. Math. 378 (2005), Theorem 3.9 (irreducible components), §11.1 (canonical
  hom-diagrams) and Theorem 11.3.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.6, Theorem 6.
-/

public section

namespace TauCeti.LimitGroup

open GroupAlgGeom

universe u v w

namespace MRDiagram

variable {A : Type v} [Group A] {H : Type u} [Group H] {ι : A →* H} {L : Type w} [Group L]
  {ιL : A →* L}

/-! ### The components of a complete diagram -/

section node

variable {X : Type*} {M : Subgroup (MulAut H)} {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)}
  {n : ℕ} {K : Fin n → Type u} [∀ i, Group (K i)] {κ : ∀ i, A →* K i} {π : ∀ i, GHom ι (κ i)}
  {child : ∀ i, MRDiagram (κ i)}

/-- **Components of a complete diagram.** Suppose that the values at the tuple `x` of the
homomorphisms from the root group to the target fixing the coefficients are the solutions of
`S`, that the diagram is complete, and that the set of solutions obtained through each edge at
the root is Zariski irreducible. Then the maximal irreducible subsets of the solution set of `S`
are the inclusion-maximal Zariski closures of these sets. -/
theorem maximal_isIrreducible_iff_exists_closure_edgeImage {S : Set (GX A X)} {x : X → H}
    (hx : Set.range (fun (φ : GHom ι ιL) (j : X) => φ (x j)) = V ιL S)
    (hc : (node M hM π child).IsComplete ιL)
    (hirr : ∀ i, @IsIrreducible (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i)))
    {Z : Set (X → L)} :
    Maximal (fun Z ↦ @IsIrreducible (X → L) (zariskiTopology ιL X) Z ∧ Z ⊆ V ιL S) Z ↔
      ∃ i, Z = @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i)) ∧
        ∀ j, @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i)) ⊆
            @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π j) (child j)) →
          @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π j) (child j)) ⊆
            @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i)) := by
  let := zariskiTopology ιL X
  have hU := iUnion_edgeImage_eq_V_of_isComplete hx hc
  have hV : V ιL S = ⋃ i, closure (edgeImage ιL x M (π i) (child i)) :=
    (hU.symm.trans_subset (Set.iUnion_mono fun i => subset_closure)).antisymm <|
      Set.iUnion_subset fun i =>
        closure_minimal ((Set.subset_iUnion _ i).trans hU.subset) (isClosed_V S)
  rw [hV]
  exact maximal_isIrreducible_subset_iUnion_iff (fun i => isClosed_closure)
    fun i => (hirr i).closure

end node

/-! ### Component-normalized diagrams -/

section Normalized

variable {X : Type*}

variable (ιL) in
/-- A diagram is *component-normalized* for the system `S` at the tuple `x` of its root group
when the Zariski closures of the sets of solutions obtained through the edges at its root are
pairwise distinct and are exactly the maximal irreducible subsets of the solution set of `S`.
For a diagram reduced to a leaf, the single set of values at `x` of the homomorphisms out of
the leaf plays the role of these sets. -/
def IsComponentNormalized (S : Set (GX A X)) (x : X → H) : MRDiagram ι → Prop
  | leaf _ =>
    {Z | Maximal (fun Z ↦ @IsIrreducible (X → L) (zariskiTopology ιL X) Z ∧ Z ⊆ V ιL S) Z} =
      {@closure (X → L) (zariskiTopology ιL X) (Set.range fun (φ : GHom ι ιL) (j : X) => φ (x j))}
  | node M _ π child =>
    Function.Injective (fun i =>
        @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i))) ∧
      Set.range (fun i =>
        @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i))) =
      {Z | Maximal (fun Z ↦ @IsIrreducible (X → L) (zariskiTopology ιL X) Z ∧ Z ⊆ V ιL S) Z}

variable {S : Set (GX A X)} {x : X → H}

/-- A diagram reduced to a leaf is component-normalized when the only maximal irreducible subset
of the solution set is the closure of the set of values at `x` of the homomorphisms out of the
leaf. -/
@[simp]
theorem isComponentNormalized_leaf {free : IsFreeGGroup ι} :
    (leaf free).IsComponentNormalized ιL S x ↔
      {Z | Maximal (fun Z ↦ @IsIrreducible (X → L) (zariskiTopology ιL X) Z ∧ Z ⊆ V ιL S) Z} =
        {@closure (X → L) (zariskiTopology ιL X)
          (Set.range fun (φ : GHom ι ιL) (j : X) => φ (x j))} :=
  Iff.rfl

/-- If the values at the tuple `x` of the homomorphisms from the leaf to the target fixing the
coefficients are the solutions of the system `S`, then a diagram reduced to this leaf is
component-normalized exactly when the solution set of `S` is Zariski irreducible. -/
theorem isComponentNormalized_leaf_iff_isIrreducible {free : IsFreeGGroup ι}
    (hx : Set.range (fun (φ : GHom ι ιL) (j : X) => φ (x j)) = V ιL S) :
    (leaf free).IsComponentNormalized ιL S x ↔
      @IsIrreducible (X → L) (zariskiTopology ιL X) (V ιL S) := by
  let := zariskiTopology ιL X
  rw [isComponentNormalized_leaf, hx, (isClosed_V S).closure_eq]
  refine ⟨fun h => ?_, fun hS => Set.ext fun Z =>
    maximal_iff_eq (P := fun Z ↦ IsIrreducible Z ∧ Z ⊆ V ιL S) ⟨hS, subset_rfl⟩ fun _ h => h.2⟩
  have hV : Maximal (fun Z ↦ IsIrreducible Z ∧ Z ⊆ V ιL S) (V ιL S) :=
    h.superset (Set.mem_singleton _)
  exact hV.prop.1

variable {M : Subgroup (MulAut H)} {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)}

section node

variable {n : ℕ} {K : Fin n → Type u} [∀ i, Group (K i)] {κ : ∀ i, A →* K i} {π : ∀ i, GHom ι (κ i)}
  {child : ∀ i, MRDiagram (κ i)}

/-- A diagram is component-normalized when the closures of the sets of solutions obtained through
the edges at its root are pairwise distinct and are exactly the maximal irreducible subsets of the
solution set. -/
@[simp]
theorem isComponentNormalized_node :
    (node M hM π child).IsComponentNormalized ιL S x ↔
      Function.Injective (fun i =>
          @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i))) ∧
        Set.range (fun i =>
          @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i))) =
        {Z | Maximal (fun Z ↦ @IsIrreducible (X → L) (zariskiTopology ιL X) Z ∧ Z ⊆ V ιL S) Z} :=
  Iff.rfl

/-- In a component-normalized diagram, the closure of the solutions obtained through an edge at
the root is a maximal irreducible subset of the solution set. -/
theorem IsComponentNormalized.maximal_closure_edgeImage
    (h : (node M hM π child).IsComponentNormalized ιL S x) (i : Fin n) :
    Maximal (fun Z ↦ @IsIrreducible (X → L) (zariskiTopology ιL X) Z ∧ Z ⊆ V ιL S)
      (@closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i))) :=
  (isComponentNormalized_node.1 h).2.subset (Set.mem_range_self i)

/-- In a component-normalized diagram no edge at the root is redundant: if the closure of the
solutions obtained through one edge is contained in the closure of those obtained through
another, the two edges coincide. -/
theorem IsComponentNormalized.eq_of_closure_edgeImage_subset
    (h : (node M hM π child).IsComponentNormalized ιL S x) {i j : Fin n}
    (hij : @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i)) ⊆
      @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π j) (child j))) : i = j :=
  (isComponentNormalized_node.1 h).1 <|
    (h.maximal_closure_edgeImage i).eq_of_le (h.maximal_closure_edgeImage j).prop hij

/-- In a component-normalized diagram whose root is not a leaf, the number of edges at the root
is the number of maximal irreducible subsets of the solution set. -/
theorem IsComponentNormalized.ncard_setOf_maximal_isIrreducible_eq
    (h : (node M hM π child).IsComponentNormalized ιL S x) :
    {Z | Maximal (fun Z ↦ @IsIrreducible (X → L) (zariskiTopology ιL X) Z ∧ Z ⊆ V ιL S) Z}.ncard =
      n := by
  rw [← (isComponentNormalized_node.1 h).2,
    Set.ncard_range_of_injective (isComponentNormalized_node.1 h).1, Nat.card_fin]

/-- A component-normalized diagram of a Zariski irreducible solution set whose root is not a leaf
has exactly one edge at its root. -/
theorem IsComponentNormalized.eq_one_of_isIrreducible
    (h : (node M hM π child).IsComponentNormalized ιL S x)
    (hS : @IsIrreducible (X → L) (zariskiTopology ιL X) (V ιL S)) : n = 1 := by
  let := zariskiTopology ιL X
  have hV : {Z | Maximal (fun Z ↦ IsIrreducible Z ∧ Z ⊆ V ιL S) Z} = {V ιL S} :=
    Set.ext fun Z =>
      maximal_iff_eq (P := fun Z ↦ IsIrreducible Z ∧ Z ⊆ V ιL S) ⟨hS, subset_rfl⟩ fun _ h => h.2
  rw [← h.ncard_setOf_maximal_isIrreducible_eq, hV, Set.ncard_singleton]

/-- Suppose that the values at the tuple `x` of the homomorphisms from the root group to the target
fixing the coefficients are the solutions of the system `S`. Then a complete diagram whose edges
at the root have Zariski irreducible sets of solutions is component-normalized exactly when the
closure of the solutions obtained through one edge at the root is never contained in the closure
of those obtained through another edge. -/
theorem isComponentNormalized_node_iff_of_isComplete
    (hx : Set.range (fun (φ : GHom ι ιL) (j : X) => φ (x j)) = V ιL S)
    (hc : (node M hM π child).IsComplete ιL)
    (hirr : ∀ i, @IsIrreducible (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i))) :
    (node M hM π child).IsComponentNormalized ιL S x ↔
      ∀ i j, @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π i) (child i)) ⊆
        @closure (X → L) (zariskiTopology ιL X) (edgeImage ιL x M (π j) (child j)) → i = j := by
  refine ⟨fun h i j => h.eq_of_closure_edgeImage_subset, fun h => ?_⟩
  refine isComponentNormalized_node.2 ⟨fun i j hij => h i j hij.subset, Set.ext fun Z => ?_⟩
  rw [Set.mem_range, Set.mem_ofPred_eq, maximal_isIrreducible_iff_exists_closure_edgeImage hx hc
    hirr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm, fun j hj => h i j hj ▸ subset_rfl⟩,
    fun ⟨i, hi, _⟩ => ⟨i, hi.symm⟩⟩

end node

/-- Suppose that the values at the tuple `x` of the homomorphisms from the root group to the target
fixing the coefficients are the solutions of the system `S`. Then a complete diagram with a
single edge at its root is component-normalized exactly when the solution set of `S` is Zariski
irreducible. -/
theorem isComponentNormalized_edge_iff_of_isComplete {K : Type u} [Group K] {κ : A →* K}
    {π : GHom ι κ} {D : MRDiagram κ}
    (hx : Set.range (fun (φ : GHom ι ιL) (j : X) => φ (x j)) = V ιL S)
    (hc : (edge M hM π D).IsComplete ιL) :
    (edge M hM π D).IsComponentNormalized ιL S x ↔
      @IsIrreducible (X → L) (zariskiTopology ιL X) (V ιL S) := by
  rw [edge_def] at hc ⊢
  let := zariskiTopology ιL X
  have hU : edgeImage ιL x M π D = V ιL S := by
    rw [← iUnion_edgeImage_eq_V_of_isComplete hx hc, Set.iUnion_const]
  refine ⟨fun h => ?_, fun hS => ?_⟩
  · simpa [hU, (isClosed_V S).closure_eq] using (h.maximal_closure_edgeImage 0).prop.1
  · exact (isComponentNormalized_node_iff_of_isComplete hx hc fun _ => hU ▸ hS).2
      fun i j _ => Subsingleton.elim i j

/-- Suppose that the values at the tuple `x` of the homomorphisms from a free `A`-group to the
target fixing the coefficients are the solutions of the system `S`. Then the one-edge diagram of
this free `A`-group is component-normalized exactly when the solution set of `S` is Zariski
irreducible. -/
theorem isComponentNormalized_freeRoot_iff_isIrreducible {free : IsFreeGGroup ι}
    (hx : Set.range (fun (φ : GHom ι ιL) (j : X) => φ (x j)) = V ιL S) :
    (freeRoot free).IsComponentNormalized ιL S x ↔
      @IsIrreducible (X → L) (zariskiTopology ιL X) (V ιL S) := by
  rw [freeRoot_def]
  exact isComponentNormalized_edge_iff_of_isComplete hx
    (freeRoot_def free ▸ isComplete_freeRoot free)

end Normalized

end MRDiagram

end TauCeti.LimitGroup
