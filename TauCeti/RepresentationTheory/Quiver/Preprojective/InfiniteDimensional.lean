/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GolodShafarevich
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation

/-!
# Infinite-dimensional preprojective algebras

The additive preprojective algebra `Π_k(Q)` of a finite quiver is presented on the doubled quiver
by the local relators `ρ_v`, one at each vertex, homogeneous of path length two and lying in the
corner of `v`. The growth bound
`TauCeti.PathAlgebra.not_module_finite_quotient_span_range_of_two_mul_le_sum` therefore applies to
it. The arrows of the doubled quiver from `i` to `j` are the arrows of `Q`
between `i` and `j` in either direction, so the condition on a nonzero nonnegative weight `δ` on the
vertices reads

```text
2 δ_i ≤ ∑_j (#(i ⟶ j) + #(j ⟶ i)) δ_j,
```

that is `(2I - A) δ ≤ 0` for the adjacency matrix `A` of the underlying multigraph of `Q`, a loop
counting twice. Under it `Π_k(Q)` is infinite-dimensional over every field `k`.

For an orientation of a finite simple graph `G` the condition is `2 δ_i ≤ ∑_{j ∼ i} δ_j`. The marks
of an affine simply-laced diagram satisfy it with equality, so the preprojective algebra of every
orientation of a graphical affine diagram is infinite-dimensional. The affine diagrams of types
`D_n`, `E6`, `E7` and `E8` are trees, so all their orientations are acyclic and the oriented-cycle
argument of `TauCeti.not_module_finite_preprojectiveAlgebra_of_length_pos` does not reach them. More
generally the condition holds, with the marks extended by zero, for every graph containing a
graphical affine diagram as a subgraph.

## Main results

* `TauCeti.not_module_finite_preprojectiveAlgebra_of_two_mul_le_sum`: **a preprojective algebra
  whose underlying multigraph carries a nonzero nonnegative weight `δ` with `(2I - A) δ ≤ 0` is
  infinite-dimensional.**
* `TauCeti.not_module_finite_preprojectiveAlgebra_orientedQuiver_of_two_mul_le_sum`: the same for
  an orientation of a finite simple graph, with the condition `2 δ_i ≤ ∑_{j ∼ i} δ_j`.
* `TauCeti.AffineDynkinType.not_module_finite_preprojectiveAlgebra`: **the preprojective algebra
  of any orientation of a graphical affine simply-laced diagram is infinite-dimensional.**

## Implementation notes

The oriented quiver of a graph has `Finite` vertex and arrow types; as in
`TauCeti.RepresentationTheory.Quiver.Zigzag.Preprojective`, the `Fintype` structures its
preprojective algebra needs are supplied by `Fintype.ofFinite`.

## References

* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the preprojective algebra and its local relations.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, for the
  infinite-dimensionality of the preprojective algebras of non-Dynkin quivers.
* V. Kac, *Infinite dimensional Lie algebras*, Chapter 4, for the marks of the affine diagrams.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Quiver

variable (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **A preprojective algebra whose underlying multigraph carries a suitable weight is
infinite-dimensional.** If a nonzero nonnegative weight `δ` on the vertices of `Q` satisfies
`2 δ_i ≤ ∑_j (#(i ⟶ j) + #(j ⟶ i)) δ_j` at every vertex, that is `(2I - A) δ ≤ 0` for the adjacency
matrix `A` of the underlying multigraph, then `Π_k(Q)` is not a finite-dimensional `k`-vector
space. -/
theorem not_module_finite_preprojectiveAlgebra_of_two_mul_le_sum {S : Type*} [CommRing S]
    [LinearOrder S] [IsStrictOrderedRing S] {δ : Q → S} (hδ0 : 0 ≤ δ) (hδ : δ ≠ 0)
    (hδle : ∀ i, 2 * δ i ≤
      ∑ j, ((Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) : ℕ) : S) * δ j) :
    ¬ Module.Finite k (preprojectiveAlgebra k Q) := by
  let e : Q ≃ Symmetrify Q :=
    { toFun := Symmetrify.of.obj
      invFun := fun v => v
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  -- The relators are read on the vertices of the doubled quiver, which are those of `Q`.
  have hl (v : Symmetrify Q) : vertexIdempotent k v * localPreprojectiveRelator k (Q := Q) v =
      localPreprojectiveRelator k (Q := Q) v := by
    have h := doubledVertexIdempotent_mul_localPreprojectiveRelator k (Q := Q) v
    rw [doubledVertexIdempotent_def k (Q := Q) v] at h
    -- `Symmetrify.of.obj v` is `v` itself (`TauCeti.symmetrify_of_obj`).
    exact h
  have hr (v : Symmetrify Q) : localPreprojectiveRelator k (Q := Q) v * vertexIdempotent k v =
      localPreprojectiveRelator k (Q := Q) v := by
    have h := localPreprojectiveRelator_mul_doubledVertexIdempotent k (Q := Q) v
    rw [doubledVertexIdempotent_def k (Q := Q) v] at h
    -- `Symmetrify.of.obj v` is `v` itself (`TauCeti.symmetrify_of_obj`).
    exact h
  -- The hom type of the doubled quiver is explicitly equivalent to the sum of both directions.
  have hcard (i j : Q) : Fintype.card (Symmetrify.of.obj i ⟶ Symmetrify.of.obj j) =
      Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) := by
    let f : (Symmetrify.of.obj i ⟶ Symmetrify.of.obj j) ≃
        ((i ⟶ j) ⊕ (j ⟶ i)) := Equiv.refl _
    exact (Fintype.card_congr f).trans Fintype.card_sum
  have hI : preprojectiveIdeal k Q = TwoSidedIdeal.span (Set.range
      (localPreprojectiveRelator k (Q := Q) : Symmetrify Q → pathAlgebra k (Symmetrify Q))) :=
    preprojectiveIdeal_eq_span_range_localPreprojectiveRelator k Q
  have hδle' (v : Symmetrify Q) :
      2 * δ (e.symm v) ≤ ∑ w : Symmetrify Q,
        (Fintype.card (v ⟶ w) : S) * δ (e.symm w) := by
    obtain ⟨i, rfl⟩ := e.surjective v
    have hsum := Fintype.sum_equiv e
      (fun j : Q => ((Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) : ℕ) : S) * δ j)
      (fun w : Symmetrify Q => (Fintype.card (e i ⟶ w) : S) * δ (e.symm w))
      (fun j => by
        simp only [e.symm_apply_apply]
        exact congrArg (fun n : ℕ => (n : S) * δ j) (hcard i j).symm)
    simpa only [e.symm_apply_apply] using (hδle i).trans_eq hsum
  have h := not_module_finite_quotient_span_range_of_two_mul_le_sum (R := Symmetrify Q)
    (localPreprojectiveRelator k (Q := Q)) (localPreprojectiveRelator_mem_grade_two k (Q := Q))
    hl hr (fun v => hδ0 (e.symm v))
    (fun h => hδ (funext fun i => by simpa using congrFun h (e i))) hδle'
  -- `h` is about the same quotient, with the finiteness instances of the doubled quiver.
  convert h using 4 <;> exact hI

end Quiver

section Graph

open DoubledQuiver

attribute [local instance] Fintype.ofFinite

variable {V : Type u} {G : SimpleGraph V}

/-- Between two vertices an orientation keeps exactly one of the two darts of an edge, and nothing
when they are not adjacent: the oriented quiver has, in the two directions together, one arrow
between adjacent vertices and none between non-adjacent ones. -/
private theorem card_hom_add_card_hom_orientedQuiver [DecidableRel G.Adj] (o : Orientation G)
    (i j : V) :
    Nat.card (OrientedQuiver.vertex G o i ⟶ OrientedQuiver.vertex G o j) +
        Nat.card (OrientedQuiver.vertex G o j ⟶ OrientedQuiver.vertex G o i) =
      if G.Adj i j then 1 else 0 := by
  rw [Nat.card_congr (OrientedQuiver.homEquiv G o i j),
    Nat.card_congr (OrientedQuiver.homEquiv G o j i)]
  split_ifs with h
  · by_cases ho : (⟨(i, j), h⟩ : G.Dart) ∈ o
    · have ho' : (⟨(j, i), h.symm⟩ : G.Dart) ∉ o := (o.symm_notMem_iff_mem G _).2 ho
      have h1 : Nat.card {h' : G.Adj i j // (⟨(i, j), h'⟩ : G.Dart) ∈ o} = 1 :=
        Nat.card_eq_one_iff_unique.2 ⟨⟨fun _ _ => Subtype.ext rfl⟩, ⟨⟨h, ho⟩⟩⟩
      have h2 : Nat.card {h' : G.Adj j i // (⟨(j, i), h'⟩ : G.Dart) ∈ o} = 0 :=
        @Nat.card_of_isEmpty _ ⟨fun p => ho' p.2⟩
      rw [h1, h2]
    · have ho' : (⟨(j, i), h.symm⟩ : G.Dart) ∈ o := (o.symm_mem_iff_not_mem _).2 ho
      have h1 : Nat.card {h' : G.Adj i j // (⟨(i, j), h'⟩ : G.Dart) ∈ o} = 0 :=
        @Nat.card_of_isEmpty _ ⟨fun p => ho p.2⟩
      have h2 : Nat.card {h' : G.Adj j i // (⟨(j, i), h'⟩ : G.Dart) ∈ o} = 1 :=
        Nat.card_eq_one_iff_unique.2 ⟨⟨fun _ _ => Subtype.ext rfl⟩, ⟨⟨h.symm, ho'⟩⟩⟩
      rw [h1, h2]
  · have h1 : Nat.card {h' : G.Adj i j // (⟨(i, j), h'⟩ : G.Dart) ∈ o} = 0 :=
      @Nat.card_of_isEmpty _ ⟨fun p => h p.1⟩
    have h2 : Nat.card {h' : G.Adj j i // (⟨(j, i), h'⟩ : G.Dart) ∈ o} = 0 :=
      @Nat.card_of_isEmpty _ ⟨fun p => h p.1.symm⟩
    rw [h1, h2]

variable (k : Type w) [Field k] [Fintype V] [DecidableRel G.Adj]

/-- **The preprojective algebra of an oriented graph carrying a suitable weight is
infinite-dimensional.** If a nonzero nonnegative weight `δ` on the vertices of a finite simple graph
`G` satisfies `2 δ_i ≤ ∑_{j ∼ i} δ_j` at every vertex, then the preprojective algebra of every
orientation of `G` is not a finite-dimensional `k`-vector space. -/
theorem not_module_finite_preprojectiveAlgebra_orientedQuiver_of_two_mul_le_sum
    (o : Orientation G) {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    {δ : V → S} (hδ0 : 0 ≤ δ) (hδ : δ ≠ 0) (hδle : ∀ i, 2 * δ i ≤ ∑ j ∈ G.neighborFinset i, δ j) :
    ¬ Module.Finite k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hc (i j : V) :
      ((Fintype.card (OrientedQuiver.vertex G o i ⟶ OrientedQuiver.vertex G o j) +
        Fintype.card (OrientedQuiver.vertex G o j ⟶ OrientedQuiver.vertex G o i) : ℕ) : S) =
          if G.Adj i j then 1 else 0 := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
      card_hom_add_card_hom_orientedQuiver o i j]
    split_ifs <;> simp
  set e := OrientedQuiver.vertexEquiv G o
  refine not_module_finite_preprojectiveAlgebra_of_two_mul_le_sum k (Q := OrientedQuiver G o)
    (δ := fun i => δ (e.symm i)) (fun i => hδ0 (e.symm i))
    (fun h => hδ (funext fun v => by simpa using congrFun h (e v))) fun i => ?_
  obtain ⟨i, rfl⟩ := e.surjective i
  have hsum :
      ∑ j ∈ G.neighborFinset i, δ j = ∑ j : V, (if G.Adj i j then (1 : S) else 0) * δ j := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    exact Finset.sum_congr (by ext j; simp) fun _ _ => rfl
  simp only [Equiv.symm_apply_apply]
  refine (hδle i).trans_eq (hsum.trans (Fintype.sum_equiv e _ _ fun j => ?_))
  simp only [e, OrientedQuiver.vertexEquiv_apply, OrientedQuiver.vertexEquiv_symm_vertex, hc i j]

/-- **The preprojective algebra of an affine simply-laced diagram is infinite-dimensional**, for
every orientation of a valid graphical affine diagram and over every field. The multiplicity-two
diagram `Ã₁`, which is not a simple graph, is excluded by `IsGraphical`. -/
theorem AffineDynkinType.not_module_finite_preprojectiveAlgebra {t : AffineDynkinType}
    (ht : t.Valid) (hg : t.IsGraphical) (o : Orientation t.graph) :
    ¬ Module.Finite k (preprojectiveAlgebra k (OrientedQuiver t.graph o)) :=
  not_module_finite_preprojectiveAlgebra_orientedQuiver_of_two_mul_le_sum k o (δ := t.marks)
    (fun i => (AffineDynkinType.marks_pos i).le)
    (fun h => (AffineDynkinType.marks_pos (0 : Fin t.nodes)).ne' (congrFun h 0))
    (fun i => (AffineDynkinType.sum_marks_neighborFinset_eq_two_mul ht hg i).ge)

end Graph

end TauCeti
