/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimpleGraph
public import TauCeti.RepresentationTheory.Quiver.EulerForm
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GolodShafarevich
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation
import TauCeti.LinearAlgebra.Matrix.ZMatrix

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
argument of `TauCeti.not_module_finite_preprojectiveAlgebra_of_length_pos` does not reach them.

A weight exists as soon as the form of `2I - A` is not positive definite: a symmetric matrix with
nonpositive off-diagonal entries and a nonpositive value of its form has a nonzero nonnegative
vector `δ` with `(2I - A) δ ≤ 0` (`Matrix.exists_nonneg_mulVec_nonpos_of_dotProduct_mulVec_nonpos`).
Twice the Tits form of `Q` is the form of `2I - A`, so `Π_k(Q)` is infinite-dimensional whenever
the Tits form is not positive definite. For a connected simple graph, a positive definite `2I - A`
makes the graph a Dynkin diagram by the classification of finite-type Cartan matrices, so the
preprojective algebra of every orientation of a connected graph which is not a Dynkin diagram is
infinite-dimensional.

## Main results

* `TauCeti.not_module_finite_preprojectiveAlgebra_of_two_mul_le_sum`: **a preprojective algebra
  whose underlying multigraph carries a nonzero nonnegative weight `δ` with `(2I - A) δ ≤ 0` is
  infinite-dimensional.**
* `TauCeti.not_module_finite_preprojectiveAlgebra_orientedQuiver_of_two_mul_le_sum`: the same for
  an orientation of a finite simple graph, with the condition `2 δ_i ≤ ∑_{j ∼ i} δ_j`.
* `TauCeti.not_module_finite_preprojectiveAlgebra_of_not_posDef_titsForm`: **a preprojective
  algebra whose Tits form is not positive definite is infinite-dimensional.**
* `TauCeti.not_module_finite_preprojectiveAlgebra_orientedQuiver_of_not_posDef`: the same for an
  orientation of a finite simple graph whose matrix `2I - A` is not positive definite.
* `TauCeti.not_module_finite_preprojectiveAlgebra_orientedQuiver_of_not_exists_dynkinType_iso`:
  **the preprojective algebra of any orientation of a connected non-Dynkin graph is
  infinite-dimensional.**
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
* V. Kac, *Infinite dimensional Lie algebras*, Chapter 4, for the marks of the affine diagrams
  and the separation of finite from non-finite types by nonnegative vectors.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

open scoped _root_.Matrix

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
  let e : Q ≃ Symmetrify Q := Equiv.ofBijective _ symmetrify_of_obj_bijective
  -- The relators are read on the vertices of the doubled quiver, which are those of `Q`.
  have hl (v : Symmetrify Q) : vertexIdempotent k v * localPreprojectiveRelator k (Q := Q) v =
      localPreprojectiveRelator k (Q := Q) v := by
    have h := doubledVertexIdempotent_mul_localPreprojectiveRelator k (Q := Q) v
    rw [doubledVertexIdempotent_def k (Q := Q) v] at h
    exact (congrArg
      (fun x : Symmetrify Q => vertexIdempotent k x * localPreprojectiveRelator k (Q := Q) v)
      (symmetrify_of_obj (Q := Q) v)).symm.trans h
  have hr (v : Symmetrify Q) : localPreprojectiveRelator k (Q := Q) v * vertexIdempotent k v =
      localPreprojectiveRelator k (Q := Q) v := by
    have h := localPreprojectiveRelator_mul_doubledVertexIdempotent k (Q := Q) v
    rw [doubledVertexIdempotent_def k (Q := Q) v] at h
    exact (congrArg
      (fun x : Symmetrify Q => localPreprojectiveRelator k (Q := Q) v * vertexIdempotent k x)
      (symmetrify_of_obj (Q := Q) v)).symm.trans h
  -- Mathlib defines the arrows of `Symmetrify Q` as a sum, built by `Hom.toPos` and `Hom.toNeg`.
  have hcard (i j : Q) : Fintype.card (Symmetrify.of.obj i ⟶ Symmetrify.of.obj j) =
      Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) := by
    let f : (Symmetrify.of.obj i ⟶ Symmetrify.of.obj j) ≃
        ((i ⟶ j) ⊕ (j ⟶ i)) :=
      { toFun := fun e => match e with
          | .inl a => .inl a
          | .inr a => .inr a
        invFun := Sum.elim Hom.toPos Hom.toNeg
        left_inv := by intro e; cases e <;> rfl
        right_inv := by intro e; cases e <;> rfl }
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

/-- **A preprojective algebra whose Tits form is not positive definite is infinite-dimensional.**
If the Tits form of the finite quiver `Q` is not positive definite, then `Π_k(Q)` is not a
finite-dimensional `k`-vector space. In particular this holds for every quiver with a loop, since a
loop at `i` makes the Tits form of the simple dimension vector at `i` nonpositive. -/
theorem not_module_finite_preprojectiveAlgebra_of_not_posDef_titsForm
    (h : ¬ (titsForm Q).PosDef) : ¬ Module.Finite k (preprojectiveAlgebra k Q) := by
  classical
  -- The matrix `2I - (A + Aᵀ)` of the underlying multigraph; its form is twice the Tits form.
  set c : Q → Q → ℝ := fun i j ↦ ((Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) : ℕ) : ℝ)
  set M : Matrix Q Q ℝ := Matrix.of fun i j ↦ (if i = j then 2 else 0) - c i j
  have hM : M.IsSymm := Matrix.IsSymm.ext fun i j ↦ by
    simp only [M, c, Matrix.of_apply, eq_comm (a := j), add_comm (Fintype.card (j ⟶ i))]
  have hM0 (i j : Q) (hij : i ≠ j) : M i j ≤ 0 := by
    simp only [M, c, Matrix.of_apply, hij, ↓reduceIte, zero_sub, neg_nonpos]
    positivity
  simp only [QuadraticMap.PosDef, not_forall, not_lt] at h
  obtain ⟨d, hd, hq⟩ := h
  set x : Q → ℝ := fun i ↦ (d i : ℝ)
  have hx : x ≠ 0 := fun h0 ↦ hd (funext fun i ↦ by simpa [x] using congrFun h0 i)
  have hxM : x ⬝ᵥ M *ᵥ x = 2 * (titsForm Q d : ℝ) := by
    have hterm (i j : Q) : x i * (M i j * x j) = (if i = j then 2 * (x i * x j) else 0) -
        (Fintype.card (i ⟶ j) : ℝ) * (x i * x j) - (Fintype.card (j ⟶ i) : ℝ) * (x j * x i) := by
      simp only [M, c, Matrix.of_apply]
      push_cast
      split_ifs <;> ring
    have hsymm : ∑ i, ∑ j, (Fintype.card (j ⟶ i) : ℝ) * (x j * x i) =
        ∑ i, ∑ j, (Fintype.card (i ⟶ j) : ℝ) * (x i * x j) :=
      Finset.sum_comm
    rw [titsForm_def, eulerForm_eq_sum_card]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, hterm, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, hsymm]
    push_cast
    simp only [x, ← Finset.mul_sum]
    ring
  obtain ⟨δ, hδ0, hδ, hMδ⟩ :=
    Matrix.exists_nonneg_mulVec_nonpos_of_dotProduct_mulVec_nonpos hM hM0 hx (by
      have hq' : (titsForm Q d : ℝ) ≤ 0 := by exact_mod_cast hq
      linarith)
  refine not_module_finite_preprojectiveAlgebra_of_two_mul_le_sum k hδ0 hδ fun i ↦ ?_
  have hi := hMδ i
  simp only [M, c, Matrix.mulVec, dotProduct, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.zero_apply] at hi
  linarith

end Quiver

section Graph

open DoubledQuiver

attribute [local instance] Fintype.ofFinite

variable {V : Type u} {G : SimpleGraph V}

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
      OrientedQuiver.card_hom_add_card_hom G o i j]
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

section NonDynkin

open DoubledQuiver

attribute [local instance] Fintype.ofFinite

variable {V : Type u} {G : SimpleGraph V}

variable (k : Type w) [Field k] [Finite V]

/-- **The preprojective algebra of an oriented graph with non-positive-definite form is
infinite-dimensional.** If the generalized Cartan matrix `2I - A` of a finite simple graph `G` is
not positive definite over `ℝ`, then the preprojective algebra of every orientation of `G` is not a
finite-dimensional `k`-vector space. -/
theorem not_module_finite_preprojectiveAlgebra_orientedQuiver_of_not_posDef [DecidableEq V]
    [DecidableRel G.Adj] (o : Orientation G) (h : ¬ (G.graphCartanMatrix ℝ).PosDef) :
    ¬ Module.Finite k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨δ, hδ0, hδ, hMδ⟩ := Matrix.exists_nonneg_mulVec_nonpos_of_not_posDef
    (G.isSymm_graphCartanMatrix) (fun i j hij ↦ by
      simp only [SimpleGraph.graphCartanMatrix_apply, hij, ↓reduceIte]
      split_ifs <;> norm_num) h
  refine not_module_finite_preprojectiveAlgebra_orientedQuiver_of_two_mul_le_sum k o hδ0 hδ
    fun i ↦ ?_
  have hi := hMδ i
  rw [Pi.zero_apply, SimpleGraph.graphCartanMatrix_mulVec_apply] at hi
  linarith

/-- **The preprojective algebra of a connected non-Dynkin graph is infinite-dimensional.** If a
connected finite simple graph `G` is not isomorphic to the diagram of any valid Dynkin type, then
the preprojective algebra of every orientation of `G` is not a finite-dimensional `k`-vector
space. -/
theorem not_module_finite_preprojectiveAlgebra_orientedQuiver_of_not_exists_dynkinType_iso
    (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (o : Orientation G) :
    ¬ Module.Finite k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  classical
  exact not_module_finite_preprojectiveAlgebra_orientedQuiver_of_not_posDef k o fun h ↦
    hD (SimpleGraph.exists_dynkinType_iso_of_isFiniteType_graphCartanMatrix hG
      (SimpleGraph.isFiniteType_graphCartanMatrix_of_posDef h))

end NonDynkin

end TauCeti
