/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.Combinatorics.SimpleGraph.Finite
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Isomorphism
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

/-!
# Signless preprojective algebras of induced subgraphs

If `H` is the subgraph of a finite simple graph `G` induced on a set of vertices, killing the
vertices outside `H` and every arrow incident to them defines a surjective algebra homomorphism

```text
Π⁺(G) ⟶ Π⁺(H).
```

Here `Π⁺` denotes the signless preprojective algebra.  At a retained vertex, the signless
relation of `G` maps to the relation of `H`; at a deleted vertex it maps to zero.  Consequently
finite-dimensionality descends from a graph to each of its induced subgraphs.  In particular,
this reduction lets a finite-dimensionality calculation for the exceptional diagram `E₈` supply
the corresponding results for `E₇` and `E₆` after deleting end vertices.

Moreover, restriction preserves the path-length grading and is surjective in every degree.  Along
any induced graph embedding `H ↪g G`, every nonzero homogeneous cyclic class of `Π⁺(H)` therefore
lifts to a nonzero homogeneous cyclic class of the same path degree in `Π⁺(G)`.

## Main definitions

* `TauCeti.signlessPreprojectiveInducedSubgraphHom`: the quotient map from the signless
  preprojective algebra of a graph to that of an induced subgraph.
* `TauCeti.signlessPreprojectiveEmbeddingHom`: the quotient map associated to an induced graph
  embedding `H ↪g G`.

## Main results

* `TauCeti.signlessPreprojectiveEmbeddingHom_vertexIdempotent_apply`,
  `TauCeti.signlessPreprojectiveEmbeddingHom_ofArrow_apply`,
  `TauCeti.signlessPreprojectiveEmbeddingHom_refl`, and
  `TauCeti.signlessPreprojectiveEmbeddingHom_comp`: generator formulas and contravariant
  functoriality of the embedding quotient.
* `TauCeti.signlessPreprojectiveInducedSubgraphHom_surjective` and
  `TauCeti.signlessPreprojectiveEmbeddingHom_surjective`: the induced maps are surjective.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_signlessPreprojectiveInducedSubgraphHom_eq` and
  `TauCeti.exists_mem_signlessPreprojectiveGrade_signlessPreprojectiveEmbeddingHom_eq`: surjectivity
  in each path-length degree.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_embedding`: a
  nonzero homogeneous cyclic class of an induced subgraph lifts to the ambient graph.
* `TauCeti.moduleFinite_signlessPreprojectiveAlgebra_induce`: finite generation over the
  coefficient ring descends to an induced subgraph.

## References

See W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
problem*, Section 1, for the local presentation of preprojective algebras used here.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

universe u w

section PathAlgebra

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type w) [CommRing k] {V : Type u} [Finite V]
  (G : SimpleGraph V) (S : Set V)

private abbrev InducedAlgebra :=
  signlessPreprojectiveAlgebra k (DoubledQuiver (G.induce S))

omit [Finite V] in
private theorem inducedAdj {i j : V} (hi : i ∈ S) (hj : j ∈ S) (h : G.Adj i j) :
    (G.induce S).Adj ⟨i, hi⟩ ⟨j, hj⟩ :=
  SimpleGraph.induce_adj.mpr h

/-- The image of a vertex idempotent under restriction to an induced subgraph. -/
private noncomputable def inducedSubgraphVertex
    (v : DoubledQuiver G) : InducedAlgebra k G S :=
  by
    classical
    exact if hv : (vertexEquiv G).symm v ∈ S then
      signlessPreprojectiveMk k _
        (vertexIdempotent k (vertex (G.induce S) ⟨(vertexEquiv G).symm v, hv⟩))
    else 0

/-- The image of an arrow under restriction to an induced subgraph. -/
private noncomputable def inducedSubgraphArrow {a b : DoubledQuiver G}
    (e : a ⟶ b) : InducedAlgebra k G S :=
  by
    classical
    exact if ha : (vertexEquiv G).symm a ∈ S then
      if hb : (vertexEquiv G).symm b ∈ S then
        signlessPreprojectiveMk k _
          (ofArrow (arrow (G.induce S) (inducedAdj G S ha hb e.down)))
      else 0
    else 0

/-- The image of a path under restriction to an induced subgraph. -/
private noncomputable def inducedSubgraphPath :
    {a b : DoubledQuiver G} → Path a b → InducedAlgebra k G S
  | a, _, .nil => inducedSubgraphVertex k G S a
  | _, _, .cons p e => inducedSubgraphArrow k G S e * inducedSubgraphPath p

private theorem inducedSubgraphVertex_mul_inducedSubgraphArrow
    {a b : DoubledQuiver G} (e : a ⟶ b) :
    inducedSubgraphVertex k G S b * inducedSubgraphArrow k G S e =
      inducedSubgraphArrow k G S e := by
  classical
  simp only [inducedSubgraphVertex, inducedSubgraphArrow]
  split_ifs with ha hb hb'
  · rw [← map_mul, vertexIdempotent_mul_ofArrow]
  all_goals simp

private theorem inducedSubgraphArrow_mul_inducedSubgraphVertex
    {a b : DoubledQuiver G} (e : a ⟶ b) :
    inducedSubgraphArrow k G S e * inducedSubgraphVertex k G S a =
      inducedSubgraphArrow k G S e := by
  classical
  simp only [inducedSubgraphVertex, inducedSubgraphArrow]
  split_ifs
  · rw [← map_mul, ofArrow_mul_vertexIdempotent]
  all_goals simp

/-- The image of a path lies in the corner of its target vertex. -/
private theorem inducedSubgraphVertex_mul_inducedSubgraphPath
    {a b : DoubledQuiver G} (p : Path a b) :
    inducedSubgraphVertex k G S b * inducedSubgraphPath k G S p =
      inducedSubgraphPath k G S p := by
  cases p with
  | nil =>
      classical
      simp only [inducedSubgraphPath, inducedSubgraphVertex]
      split_ifs
      · rw [← map_mul, vertexIdempotent_mul_self]
      · simp
  | cons p e =>
      rw [inducedSubgraphPath, ← mul_assoc,
        inducedSubgraphVertex_mul_inducedSubgraphArrow]

/-- The image of a path lies in the corner of its source vertex. -/
private theorem inducedSubgraphPath_mul_inducedSubgraphVertex
    {a b : DoubledQuiver G} (p : Path a b) :
    inducedSubgraphPath k G S p * inducedSubgraphVertex k G S a =
      inducedSubgraphPath k G S p := by
  induction p with
  | nil =>
      classical
      simp only [inducedSubgraphPath, inducedSubgraphVertex]
      split_ifs
      · rw [← map_mul, vertexIdempotent_mul_self]
      · simp
  | cons p e ih => rw [inducedSubgraphPath, mul_assoc, ih]

/-- Concatenation of paths becomes multiplication, in later-factor-first order. -/
private theorem inducedSubgraphPath_comp {a b c : DoubledQuiver G}
    (p : Path a b) (q : Path c a) :
    inducedSubgraphPath k G S p * inducedSubgraphPath k G S q =
      inducedSubgraphPath k G S (q.comp p) := by
  induction p with
  | nil => rw [Path.comp_nil, inducedSubgraphPath,
      inducedSubgraphVertex_mul_inducedSubgraphPath]
  | cons p e ih =>
      rw [Path.comp_cons, inducedSubgraphPath, inducedSubgraphPath, mul_assoc, ih]

private theorem inducedSubgraphPath_zero {x y : Quiver.TotalPath (DoubledQuiver G)}
    (h : y.2.1 ≠ x.1) :
    inducedSubgraphPath k G S x.2.2 * inducedSubgraphPath k G S y.2.2 = 0 := by
  rw [← inducedSubgraphPath_mul_inducedSubgraphVertex k G S x.2.2,
    ← inducedSubgraphVertex_mul_inducedSubgraphPath k G S y.2.2, mul_assoc,
    ← mul_assoc (inducedSubgraphVertex k G S x.1)]
  classical
  simp only [inducedSubgraphVertex]
  split_ifs with hx hy
  · rw [← map_mul, vertexIdempotent_mul_vertexIdempotent_of_ne, map_zero, zero_mul, mul_zero]
    intro hxy
    have hsub := vertex_injective (G.induce S) hxy
    exact h ((vertexEquiv G).symm.injective (congrArg Subtype.val hsub).symm)
  all_goals simp

private theorem inducedSubgraphPath_one :
    letI := Fintype.ofFinite (DoubledQuiver G)
    ∑ v : DoubledQuiver G, inducedSubgraphPath k G S (Path.nil : Path v v) = 1 := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite (DoubledQuiver G)
  simp only [inducedSubgraphPath]
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun v : V => v ∈ S)
    (fun v => inducedSubgraphVertex k G S (vertex G v))
  have hcompl : ∑ v : {v : V // ¬v ∈ S},
      inducedSubgraphVertex k G S (vertex G v) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp [inducedSubgraphVertex, v.property]
  rw [hcompl, add_zero] at hsum
  calc
    ∑ x : DoubledQuiver G, inducedSubgraphVertex k G S x =
        ∑ v : V, inducedSubgraphVertex k G S (vertex G v) :=
      by simpa only [vertexEquiv_apply] using
        ((vertexEquiv G).sum_comp (inducedSubgraphVertex k G S)).symm
    _ = ∑ v : S, inducedSubgraphVertex k G S (vertex G v) := hsum.symm
    _ = ∑ v : S, signlessPreprojectiveMk k _
          (vertexIdempotent k (vertex (G.induce S) v)) := by
      apply Finset.sum_congr rfl
      intro v _
      simp [inducedSubgraphVertex, v.property]
    _ = signlessPreprojectiveMk k _
          (∑ x : DoubledQuiver (G.induce S), vertexIdempotent k x) := by
      rw [← map_sum]
      congr 1
      simpa only [vertexEquiv_apply] using
        (vertexEquiv (G.induce S)).sum_comp (fun x => vertexIdempotent k x)
    _ = 1 := by rw [← one_def, map_one]

/-- The path-algebra map which kills vertices outside an induced subgraph and retains every path
entirely contained in it. -/
private noncomputable def inducedSubgraphPathAlgebraHom :
    pathAlgebra k (DoubledQuiver G) →ₐ[k] InducedAlgebra k G S :=
  liftAlgHom k (fun x => inducedSubgraphPath k G S x.2.2)
    (inducedSubgraphPath_comp k G S) (inducedSubgraphPath_zero k G S)
    (inducedSubgraphPath_one k G S)

open scoped Classical in
/-- Restriction sends an arrow with both endpoints retained to the corresponding arrow of the
induced graph. -/
private theorem inducedSubgraphPathAlgebraHom_ofArrow {i j : V} (h : G.Adj i j) :
    inducedSubgraphPathAlgebraHom k G S (ofArrow (arrow G h)) =
      if hi : i ∈ S then
        if hj : j ∈ S then
          signlessPreprojectiveMk k _
            (ofArrow (arrow (G.induce S) (inducedAdj G S hi hj h)))
        else 0
      else 0 := by
  classical
  rw [ofArrow_eq_ofPath, inducedSubgraphPathAlgebraHom, liftAlgHom_ofPath]
  rw [Hom.toPath, inducedSubgraphPath, inducedSubgraphPath,
    inducedSubgraphArrow_mul_inducedSubgraphVertex]
  simp only [inducedSubgraphArrow, vertexEquiv_symm_vertex]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · simp only [dite_eq_left hi, dite_eq_left hj]
      have hi' : (⟨(vertexEquiv G).symm (vertex G i), by simpa using hi⟩ : S) =
          ⟨i, hi⟩ := Subtype.ext (vertexEquiv_symm_vertex G i)
      have hj' : (⟨(vertexEquiv G).symm (vertex G j), by simpa using hj⟩ : S) =
          ⟨j, hj⟩ := Subtype.ext (vertexEquiv_symm_vertex G j)
      have hvi := congrArg (vertex (G.induce S)) hi'
      have hvj := congrArg (vertex (G.induce S)) hj'
      congr 3
      apply proof_irrel_heq
    · simp [hj]
  · simp [hi]

open scoped Classical in
/-- Restriction sends a retained backtrack to the corresponding backtrack and kills a backtrack
incident to a deleted vertex. -/
private theorem inducedSubgraphPathAlgebraHom_backtrackElem {i j : V} (h : G.Adj i j) :
    inducedSubgraphPathAlgebraHom k G S (backtrackElem G k h) =
      if hi : i ∈ S then
        if hj : j ∈ S then
          signlessPreprojectiveMk k _
            (backtrackElem (G.induce S) k
              (inducedAdj G S hi hj h))
        else 0
      else 0 := by
  classical
  rw [← ofArrow_symm_mul_ofArrow G k h, map_mul,
    inducedSubgraphPathAlgebraHom_ofArrow, inducedSubgraphPathAlgebraHom_ofArrow]
  split_ifs with hi hj
  · rw [← map_mul, ofArrow_symm_mul_ofArrow]
  all_goals simp

/-- The restricted backtrack elements at a vertex of `S` sum to zero. -/
private theorem sum_inducedSubgraphPathAlgebraHom_backtrackElem_eq_zero {v : V} (hv : v ∈ S)
    [Fintype (G.neighborSet v)] :
    ∑ w : G.neighborSet v,
      inducedSubgraphPathAlgebraHom k G S (backtrackElem G k w.2) = 0 := by
  classical
  let f : G.neighborSet v → InducedAlgebra k G S := fun w =>
    inducedSubgraphPathAlgebraHom k G S (backtrackElem G k w.2)
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun w : G.neighborSet v => (w : V) ∈ S) f
  have hcompl : ∑ w : {w : G.neighborSet v // (w : V) ∉ S}, f w = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    simp only [f]
    rw [inducedSubgraphPathAlgebraHom_backtrackElem
      (k := k) (G := G) (S := S) w.1.2]
    simp [w.property]
  rw [hcompl, add_zero] at hsum
  rw [← hsum]
  calc
    ∑ w : {w : G.neighborSet v // (w : V) ∈ S}, f w =
        ∑ w : {w : G.neighborSet v // (w : V) ∈ S},
          signlessPreprojectiveMk k _
            (backtrackElem (G.induce S) k
              (inducedAdj G S hv w.2 w.1.2)) := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [f]
      rw [inducedSubgraphPathAlgebraHom_backtrackElem
        (k := k) (G := G) (S := S) w.1.2]
      simp [hv, w.property]
    _ = ∑ w : (G.induce S).neighborSet ⟨v, hv⟩,
          signlessPreprojectiveMk k _ (backtrackElem (G.induce S) k w.2) := by
      let e : {w : G.neighborSet v // (w : V) ∈ S} ≃ (G.induce S).neighborSet ⟨v, hv⟩ :=
        (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ G.neighborSet v) (· ∈ S)).trans
          ((Equiv.subtypeEquivRight fun _ ↦ and_comm).trans
            (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ S) (G.Adj v ·)).symm)
      apply Fintype.sum_equiv e
      intro w
      rfl
    _ = 0 := by
      rw [← map_sum, ← signlessPreprojectiveRelator_vertex]
      rw [signlessPreprojectiveRelator_congr k (vertex (G.induce S) ⟨v, hv⟩)
        (DoubledQuiver.instFintypeStarVertex (G.induce S) ⟨v, hv⟩)
        (DoubledQuiver.instFintypeStar (G := G.induce S)
          (vertex (G.induce S) ⟨v, hv⟩))]
      exact signlessPreprojectiveMk_signlessPreprojectiveRelator k
        (vertex (G.induce S) ⟨v, hv⟩)

/-- The path-algebra restriction kills every signless relation. -/
private theorem inducedSubgraphPathAlgebraHom_signlessPreprojectiveRelator
    (v : DoubledQuiver G) :
    inducedSubgraphPathAlgebraHom k G S (signlessPreprojectiveRelator k v) = 0 := by
  classical
  obtain ⟨v, rfl⟩ := exists_eq_vertex G v
  rw [signlessPreprojectiveRelator_congr k (vertex G v) _ inferInstance,
    signlessPreprojectiveRelator_vertex, map_sum]
  by_cases hv : v ∈ S
  · exact sum_inducedSubgraphPathAlgebraHom_backtrackElem_eq_zero k G S hv
  · apply Finset.sum_eq_zero
    intro w _
    rw [inducedSubgraphPathAlgebraHom_backtrackElem
      (k := k) (G := G) (S := S) w.2]
    simp [hv]

private theorem inducedSubgraphPathAlgebraHom_surjective_ofPath
    {a b : DoubledQuiver (G.induce S)} (p : Path a b) :
    ∃ x ∈ grade k (DoubledQuiver G) p.length, inducedSubgraphPathAlgebraHom k G S x =
      signlessPreprojectiveMk k _ (ofPath ⟨a, b, p⟩) := by
  induction p with
  | nil =>
      obtain ⟨v, rfl⟩ := exists_eq_vertex (G.induce S) a
      refine ⟨vertexIdempotent k (vertex G v.1), vertexIdempotent_mem_grade_zero _, ?_⟩
      rw [vertexIdempotent_eq_ofPath, inducedSubgraphPathAlgebraHom, liftAlgHom_ofPath]
      simp only [inducedSubgraphPath, inducedSubgraphVertex, vertexEquiv_symm_vertex]
      split_ifs with hv
      · rw [vertexIdempotent_eq_ofPath]
      · rw [vertexEquiv_symm_vertex] at hv
        exact (hv v.2).elim
  | @cons b c p e ih =>
      obtain ⟨i, rfl⟩ := exists_eq_vertex (G.induce S) b
      obtain ⟨j, rfl⟩ := exists_eq_vertex (G.induce S) c
      obtain ⟨x, hxgrade, hx⟩ := ih
      let h : G.Adj i.1 j.1 := by
        have he := e.down
        rw [vertexEquiv_symm_vertex, vertexEquiv_symm_vertex] at he
        exact SimpleGraph.induce_adj.mp he
      refine ⟨ofArrow (arrow G h) * x, ?_, ?_⟩
      · simpa [Path.length_cons, add_comm] using
          SetLike.mul_mem_graded (ofArrow_mem_grade_one (arrow G h)) hxgrade
      · rw [map_mul, inducedSubgraphPathAlgebraHom_ofArrow, dite_eq_left i.2,
          dite_eq_left j.2, hx]
        have he : arrow (G.induce S) (inducedAdj G S i.2 j.2 h) = e :=
          Subsingleton.elim _ _
        rw [he, ← map_mul, ofArrow_mul_ofPath]

/-- Every element of the induced graph's signless algebra is in the image of the path-algebra
restriction. -/
private theorem inducedSubgraphPathAlgebraHom_surjective :
    Function.Surjective (inducedSubgraphPathAlgebraHom k G S) := by
  intro y
  obtain ⟨z, rfl⟩ := signlessPreprojectiveMk_surjective k _ y
  induction z using PathAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
      obtain ⟨x, hx⟩ := hx
      obtain ⟨y, hy⟩ := hy
      exact ⟨x + y, by simp [hx, hy]⟩
  | single x c =>
      obtain ⟨a, b, p⟩ := x
      obtain ⟨x, -, hx⟩ := inducedSubgraphPathAlgebraHom_surjective_ofPath k G S p
      exact ⟨c • x, by simp only [map_smul, hx, single_eq_smul_ofPath]⟩

/-- The surjective algebra homomorphism from the signless preprojective algebra of a finite graph
to that of an induced subgraph, obtained by killing the omitted vertices and all incident
arrows. -/
noncomputable def signlessPreprojectiveInducedSubgraphHom :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) →ₐ[k]
      signlessPreprojectiveAlgebra k (DoubledQuiver (G.induce S)) :=
  signlessPreprojectiveLift (inducedSubgraphPathAlgebraHom k G S)
    (inducedSubgraphPathAlgebraHom_signlessPreprojectiveRelator k G S)

open scoped Classical in
/-- The induced-subgraph homomorphism retains a vertex idempotent exactly when its vertex belongs
to the inducing set. -/
@[simp]
theorem signlessPreprojectiveInducedSubgraphHom_vertexIdempotent (i : V) :
    signlessPreprojectiveInducedSubgraphHom k G S
        (signlessPreprojectiveMk k _ (vertexIdempotent k (vertex G i))) =
      if hi : i ∈ S then
        signlessPreprojectiveMk k _
          (vertexIdempotent k (vertex (G.induce S) ⟨i, hi⟩))
      else 0 := by
  classical
  rw [signlessPreprojectiveInducedSubgraphHom,
    signlessPreprojectiveLift_signlessPreprojectiveMk, vertexIdempotent_eq_ofPath,
    inducedSubgraphPathAlgebraHom, liftAlgHom_ofPath]
  simp only [inducedSubgraphPath, inducedSubgraphVertex, vertexEquiv_symm_vertex]

open scoped Classical in
/-- The induced-subgraph homomorphism retains an arrow exactly when both endpoints belong to the
inducing set. -/
theorem signlessPreprojectiveInducedSubgraphHom_ofArrow {i j : V} (h : G.Adj i j) :
    signlessPreprojectiveInducedSubgraphHom k G S
        (signlessPreprojectiveMk k _ (ofArrow (arrow G h))) =
      if hi : i ∈ S then
        if hj : j ∈ S then
          signlessPreprojectiveMk k _
            (ofArrow (arrow (G.induce S) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
              (SimpleGraph.induce_adj.mpr h)))
        else 0
      else 0 := by
  rw [signlessPreprojectiveInducedSubgraphHom,
    signlessPreprojectiveLift_signlessPreprojectiveMk,
    inducedSubgraphPathAlgebraHom_ofArrow]

private theorem inducedSubgraphPath_mem_grade {a b : DoubledQuiver G} (p : Path a b) :
    inducedSubgraphPath k G S p ∈
      signlessPreprojectiveGrade k (DoubledQuiver (G.induce S)) p.length := by
  classical
  induction p with
  | nil =>
      simp only [inducedSubgraphPath, inducedSubgraphVertex, Path.length_nil]
      split_ifs
      · exact signlessPreprojectiveMk_mem_grade k _ (vertexIdempotent_mem_grade_zero _)
      · exact Submodule.zero_mem _
  | cons p e ih =>
      simp only [inducedSubgraphPath, Path.length_cons]
      have he : inducedSubgraphArrow k G S e ∈
          signlessPreprojectiveGrade k (DoubledQuiver (G.induce S)) 1 := by
        simp only [inducedSubgraphArrow]
        split_ifs
        · exact signlessPreprojectiveMk_mem_grade k _ (ofArrow_mem_grade_one _)
        all_goals exact Submodule.zero_mem _
      simpa [add_comm] using mul_mem_signlessPreprojectiveGrade k _ he ih

/-- Restriction to an induced subgraph preserves every path-length graded piece. -/
theorem signlessPreprojectiveInducedSubgraphHom_mem_grade {d : ℕ}
    {x : signlessPreprojectiveAlgebra k (DoubledQuiver G)}
    (hx : x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d) :
    signlessPreprojectiveInducedSubgraphHom k G S x ∈
      signlessPreprojectiveGrade k (DoubledQuiver (G.induce S)) d := by
  obtain ⟨z, hz, rfl⟩ := (mem_signlessPreprojectiveGrade_iff k _).mp hx
  clear hx
  rw [grade_eq_span_range] at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨⟨⟨a, b, p⟩, rfl⟩, rfl⟩ := hw
      rw [signlessPreprojectiveInducedSubgraphHom,
        signlessPreprojectiveLift_signlessPreprojectiveMk,
        inducedSubgraphPathAlgebraHom, liftAlgHom_ofPath]
      exact inducedSubgraphPath_mem_grade k G S p
  | zero => simp
  | add u v _ _ hu hv => simpa [map_add] using Submodule.add_mem _ hu hv
  | smul c u _ hu => simpa [map_smul] using Submodule.smul_mem _ c hu

/-- Every homogeneous class on an induced subgraph lifts to a homogeneous class of the same path
degree on the ambient graph. -/
theorem exists_mem_signlessPreprojectiveGrade_signlessPreprojectiveInducedSubgraphHom_eq
    {d : ℕ} {y : signlessPreprojectiveAlgebra k (DoubledQuiver (G.induce S))}
    (hy : y ∈ signlessPreprojectiveGrade k (DoubledQuiver (G.induce S)) d) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      signlessPreprojectiveInducedSubgraphHom k G S x = y := by
  obtain ⟨z, hz, rfl⟩ := (mem_signlessPreprojectiveGrade_iff k _).mp hy
  clear hy
  rw [grade_eq_span_range] at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨⟨⟨a, b, p⟩, rfl⟩, rfl⟩ := hw
      obtain ⟨x, hx, hmap⟩ := inducedSubgraphPathAlgebraHom_surjective_ofPath k G S p
      refine ⟨signlessPreprojectiveMk k _ x, signlessPreprojectiveMk_mem_grade k _ hx, ?_⟩
      rw [signlessPreprojectiveInducedSubgraphHom,
        signlessPreprojectiveLift_signlessPreprojectiveMk, hmap]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
      obtain ⟨x₁, hx₁, h₁⟩ := hu
      obtain ⟨x₂, hx₂, h₂⟩ := hv
      exact ⟨x₁ + x₂, Submodule.add_mem _ hx₁ hx₂, by simp [h₁, h₂]⟩
  | smul c u _ hu =>
      obtain ⟨x, hx, h⟩ := hu
      exact ⟨c • x, Submodule.smul_mem _ c hx, by simp [h]⟩

/-- The homomorphism from a signless preprojective algebra onto the algebra of an induced
subgraph is surjective. -/
theorem signlessPreprojectiveInducedSubgraphHom_surjective :
    Function.Surjective (signlessPreprojectiveInducedSubgraphHom k G S) := by
  intro y
  obtain ⟨x, hx⟩ := inducedSubgraphPathAlgebraHom_surjective k G S y
  refine ⟨signlessPreprojectiveMk k _ x, ?_⟩
  rw [signlessPreprojectiveInducedSubgraphHom,
    signlessPreprojectiveLift_signlessPreprojectiveMk, hx]

/-- If the signless preprojective algebra of a finite graph is finite as a module, then so is the
signless preprojective algebra of every induced subgraph. -/
theorem moduleFinite_signlessPreprojectiveAlgebra_induce
    [Module.Finite k (signlessPreprojectiveAlgebra k (DoubledQuiver G))] :
    Module.Finite k (signlessPreprojectiveAlgebra k (DoubledQuiver (G.induce S))) :=
  Module.Finite.of_surjective
    (signlessPreprojectiveInducedSubgraphHom k G S).toLinearMap
    (signlessPreprojectiveInducedSubgraphHom_surjective k G S)

private abbrev SignlessAlgebraOfFinite :=
  signlessPreprojectiveAlgebra k (DoubledQuiver G)

private noncomputable abbrev signlessMkOfFinite :=
  signlessPreprojectiveMk k (DoubledQuiver G)

private noncomputable abbrev signlessGradeOfFinite :=
  signlessPreprojectiveGrade k (DoubledQuiver G)

end PathAlgebra

section Embedding

variable (k : Type w) [CommRing k] {V : Type u} {W : Type*} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W}
  [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]

private noncomputable def neighborSetOfFiniteEquiv :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) ≃ₐ[k] SignlessAlgebraOfFinite k G :=
  @signlessPreprojectiveAlgebraEquiv V V _ _ G G k _ inferInstance
    (SimpleGraph.neighborSetFintypeOfFinite G) SimpleGraph.Iso.refl

@[simp]
private theorem neighborSetOfFiniteEquiv_signlessPreprojectiveMk
    (x : pathAlgebra k (DoubledQuiver G)) :
    neighborSetOfFiniteEquiv (G := G) k (signlessPreprojectiveMk k _ x) =
      signlessMkOfFinite k G x := by
  simp [neighborSetOfFiniteEquiv, signlessMkOfFinite]

private theorem neighborSetOfFiniteEquiv_mem_grade_iff {d : ℕ}
    {x : signlessPreprojectiveAlgebra k (DoubledQuiver G)} :
    neighborSetOfFiniteEquiv (G := G) k x ∈ signlessGradeOfFinite k G d ↔
      x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d :=
  @signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff V V _ _ G G k _
    inferInstance (SimpleGraph.neighborSetFintypeOfFinite G) SimpleGraph.Iso.refl d x

/-- The surjective algebra homomorphism `Π⁺(G) →ₐ[k] Π⁺(H)` associated to an induced graph
embedding `f : H ↪g G`, obtained by restricting to `Set.range f` and identifying the induced
subgraph with `H`. -/
noncomputable def signlessPreprojectiveEmbeddingHom (f : H ↪g G) :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) →ₐ[k]
      signlessPreprojectiveAlgebra k (DoubledQuiver H) :=
  letI := SimpleGraph.neighborSetFintypeOfFinite (G.induce (Set.range f))
  (signlessPreprojectiveAlgebraEquiv k f.isoInduceRange.symm).toAlgHom.comp
    ((signlessPreprojectiveInducedSubgraphHom k G (Set.range f)).comp
      (neighborSetOfFiniteEquiv k).toAlgHom)

/-- The embedding quotient sends the vertex idempotent of `f j` to the vertex idempotent of `j`. -/
@[simp]
theorem signlessPreprojectiveEmbeddingHom_vertexIdempotent_apply (f : H ↪g G) (j : W) :
    signlessPreprojectiveEmbeddingHom k f
        (signlessPreprojectiveMk k _ (vertexIdempotent k (vertex G (f j)))) =
      signlessPreprojectiveMk k _ (vertexIdempotent k (vertex H j)) := by
  classical
  let := SimpleGraph.neighborSetFintypeOfFinite (G.induce (Set.range f))
  have hj : f j ∈ Set.range f := ⟨j, rfl⟩
  apply (signlessPreprojectiveAlgebraEquiv k f.isoInduceRange).injective
  simp only [signlessPreprojectiveEmbeddingHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    neighborSetOfFiniteEquiv_signlessPreprojectiveMk, ← signlessPreprojectiveAlgebraEquiv_symm,
    AlgEquiv.apply_symm_apply, signlessPreprojectiveInducedSubgraphHom_vertexIdempotent,
    dite_eq_left hj, signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk,
    pathAlgebraEquiv_vertexIdempotent]
  rfl

/-- The embedding quotient annihilates every vertex idempotent outside the image of `f`. -/
@[simp]
theorem signlessPreprojectiveEmbeddingHom_vertexIdempotent_eq_zero_of_notMem_range
    (f : H ↪g G) {i : V} (hi : i ∉ Set.range f) :
    signlessPreprojectiveEmbeddingHom k f
        (signlessPreprojectiveMk k _ (vertexIdempotent k (vertex G i))) = 0 := by
  classical
  let := SimpleGraph.neighborSetFintypeOfFinite (G.induce (Set.range f))
  simp [signlessPreprojectiveEmbeddingHom,
    signlessPreprojectiveInducedSubgraphHom_vertexIdempotent, hi]

/-- The embedding quotient sends an arrow between image vertices `f i` and `f j` to the
corresponding arrow of `H`. -/
theorem signlessPreprojectiveEmbeddingHom_ofArrow_apply (f : H ↪g G) {i j : W}
    (h : H.Adj i j) :
    signlessPreprojectiveEmbeddingHom k f
        (signlessPreprojectiveMk k _ (ofArrow (arrow G (f.map_adj_iff.mpr h)))) =
      signlessPreprojectiveMk k _ (ofArrow (arrow H h)) := by
  classical
  let := SimpleGraph.neighborSetFintypeOfFinite (G.induce (Set.range f))
  have hi : f i ∈ Set.range f := ⟨i, rfl⟩
  have hj : f j ∈ Set.range f := ⟨j, rfl⟩
  apply (signlessPreprojectiveAlgebraEquiv k f.isoInduceRange).injective
  simp only [signlessPreprojectiveEmbeddingHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    neighborSetOfFiniteEquiv_signlessPreprojectiveMk, ← signlessPreprojectiveAlgebraEquiv_symm,
    AlgEquiv.apply_symm_apply, signlessPreprojectiveInducedSubgraphHom_ofArrow,
    dite_eq_left hi, dite_eq_left hj, signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk,
    pathAlgebraEquiv_ofArrow]
  rfl

/-- The embedding quotient annihilates any arrow whose source lies outside the image of `f`. -/
theorem signlessPreprojectiveEmbeddingHom_ofArrow_eq_zero_of_notMem_range_left
    (f : H ↪g G) {i j : V} (h : G.Adj i j) (hi : i ∉ Set.range f) :
    signlessPreprojectiveEmbeddingHom k f
        (signlessPreprojectiveMk k _ (ofArrow (arrow G h))) = 0 := by
  classical
  let := SimpleGraph.neighborSetFintypeOfFinite (G.induce (Set.range f))
  simp only [signlessPreprojectiveEmbeddingHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    neighborSetOfFiniteEquiv_signlessPreprojectiveMk,
    signlessPreprojectiveInducedSubgraphHom_ofArrow, hi, ↓reduceDIte, map_zero]

/-- The embedding quotient annihilates any arrow whose target lies outside the image of `f`. -/
theorem signlessPreprojectiveEmbeddingHom_ofArrow_eq_zero_of_notMem_range_right
    (f : H ↪g G) {i j : V} (h : G.Adj i j) (hj : j ∉ Set.range f) :
    signlessPreprojectiveEmbeddingHom k f
        (signlessPreprojectiveMk k _ (ofArrow (arrow G h))) = 0 := by
  classical
  let := SimpleGraph.neighborSetFintypeOfFinite (G.induce (Set.range f))
  simp only [signlessPreprojectiveEmbeddingHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    neighborSetOfFiniteEquiv_signlessPreprojectiveMk,
    signlessPreprojectiveInducedSubgraphHom_ofArrow, hj, ↓reduceDIte, dite_eq_ite, ite_self,
    map_zero]

omit [∀ j, Fintype (H.neighborSet j)] in
private theorem signlessPreprojectiveAlgebra_algHom_ext
    {A : Type*} [Semiring A] [Algebra k A]
    {φ ψ : signlessPreprojectiveAlgebra k (DoubledQuiver G) →ₐ[k] A}
    (hv : ∀ i : V, φ (signlessPreprojectiveMk k _ (vertexIdempotent k (vertex G i))) =
      ψ (signlessPreprojectiveMk k _ (vertexIdempotent k (vertex G i))))
    (ha : ∀ {i j : V} (h : G.Adj i j),
      φ (signlessPreprojectiveMk k _ (ofArrow (arrow G h))) =
        ψ (signlessPreprojectiveMk k _ (ofArrow (arrow G h)))) :
    φ = ψ := by
  have hcomp : φ.comp (signlessPreprojectiveMk k _) = ψ.comp (signlessPreprojectiveMk k _) := by
    apply AlgHom.ext_of_adjoin_eq_top adjoin_vertexIdempotents_union_arrows
    rintro _ (⟨v, rfl⟩ | ⟨⟨a, b, e⟩, rfl⟩)
    · obtain ⟨i, rfl⟩ := exists_eq_vertex G v
      exact hv i
    · obtain ⟨i, rfl⟩ := exists_eq_vertex G a
      obtain ⟨j, rfl⟩ := exists_eq_vertex G b
      have h : G.Adj i j := by
        have he := e.down
        rwa [vertexEquiv_symm_vertex, vertexEquiv_symm_vertex] at he
      have he' : arrow G h = e := Subsingleton.elim _ _
      rw [← he']
      exact ha h
  ext z
  obtain ⟨x, rfl⟩ := signlessPreprojectiveMk_surjective k _ z
  exact AlgHom.congr_fun hcomp x

omit [∀ j, Fintype (H.neighborSet j)] in
/-- The identity graph embedding induces the identity homomorphism of signless preprojective
algebras. -/
@[simp]
theorem signlessPreprojectiveEmbeddingHom_refl :
    signlessPreprojectiveEmbeddingHom k (SimpleGraph.Embedding.refl (G := G)) =
      AlgHom.id k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  apply signlessPreprojectiveAlgebra_algHom_ext k
  · intro i
    exact signlessPreprojectiveEmbeddingHom_vertexIdempotent_apply k .refl i
  · intro i j h
    exact signlessPreprojectiveEmbeddingHom_ofArrow_apply k .refl h

/-- Composing induced graph embeddings composes the associated signless preprojective quotient
homomorphisms contravariantly. -/
theorem signlessPreprojectiveEmbeddingHom_comp {U : Type*} [Finite U] {K : SimpleGraph U}
    [∀ l, Fintype (K.neighborSet l)] (f : H ↪g G) (g : K ↪g H) :
    signlessPreprojectiveEmbeddingHom k (f.comp g) =
      (signlessPreprojectiveEmbeddingHom k g).comp
        (signlessPreprojectiveEmbeddingHom k f) := by
  apply signlessPreprojectiveAlgebra_algHom_ext k
  · intro i
    by_cases hif : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hif
      by_cases hjg : j ∈ Set.range g
      · obtain ⟨l, rfl⟩ := hjg
        exact (signlessPreprojectiveEmbeddingHom_vertexIdempotent_apply k (f.comp g) l).trans
          (by simp)
      · have hfg : f j ∉ Set.range (f.comp g) := fun ⟨l, hl⟩ => hjg ⟨l, f.injective hl⟩
        rw [signlessPreprojectiveEmbeddingHom_vertexIdempotent_eq_zero_of_notMem_range k
          (f.comp g) hfg]
        simp [hjg]
    · have hfg : i ∉ Set.range (f.comp g) := fun ⟨l, hl⟩ => hif ⟨g l, hl⟩
      rw [signlessPreprojectiveEmbeddingHom_vertexIdempotent_eq_zero_of_notMem_range k
        (f.comp g) hfg]
      simp [hif]
  · intro i j h
    rw [AlgHom.comp_apply]
    by_cases hif : i ∈ Set.range f
    · obtain ⟨i', rfl⟩ := hif
      by_cases hjf : j ∈ Set.range f
      · obtain ⟨j', rfl⟩ := hjf
        have h' : H.Adj i' j' := f.map_adj_iff.mp h
        rw [signlessPreprojectiveEmbeddingHom_ofArrow_apply k f h']
        by_cases hig : i' ∈ Set.range g
        · obtain ⟨i'', rfl⟩ := hig
          by_cases hjg : j' ∈ Set.range g
          · obtain ⟨j'', rfl⟩ := hjg
            have h'' : K.Adj i'' j'' := g.map_adj_iff.mp h'
            exact (signlessPreprojectiveEmbeddingHom_ofArrow_apply k (f.comp g) h'').trans
              (signlessPreprojectiveEmbeddingHom_ofArrow_apply k g h'').symm
          · have hfg : f j' ∉ Set.range (f.comp g) := fun ⟨l, hl⟩ => hjg ⟨l, f.injective hl⟩
            rw [signlessPreprojectiveEmbeddingHom_ofArrow_eq_zero_of_notMem_range_right k
                (f.comp g) h hfg,
              signlessPreprojectiveEmbeddingHom_ofArrow_eq_zero_of_notMem_range_right k g h' hjg]
        · have hfg : f i' ∉ Set.range (f.comp g) := fun ⟨l, hl⟩ => hig ⟨l, f.injective hl⟩
          rw [signlessPreprojectiveEmbeddingHom_ofArrow_eq_zero_of_notMem_range_left k
              (f.comp g) h hfg,
            signlessPreprojectiveEmbeddingHom_ofArrow_eq_zero_of_notMem_range_left k g h' hig]
      · have hfg : j ∉ Set.range (f.comp g) := fun ⟨l, hl⟩ => hjf ⟨g l, hl⟩
        rw [signlessPreprojectiveEmbeddingHom_ofArrow_eq_zero_of_notMem_range_right k
            (f.comp g) h hfg,
          signlessPreprojectiveEmbeddingHom_ofArrow_eq_zero_of_notMem_range_right k f h hjf,
          map_zero]
    · have hfg : i ∉ Set.range (f.comp g) := fun ⟨l, hl⟩ => hif ⟨g l, hl⟩
      rw [signlessPreprojectiveEmbeddingHom_ofArrow_eq_zero_of_notMem_range_left k
          (f.comp g) h hfg,
        signlessPreprojectiveEmbeddingHom_ofArrow_eq_zero_of_notMem_range_left k f h hif,
        map_zero]

/-- The quotient homomorphism associated to an induced graph embedding is surjective. -/
theorem signlessPreprojectiveEmbeddingHom_surjective (f : H ↪g G) :
    Function.Surjective (signlessPreprojectiveEmbeddingHom k f) := by
  let := SimpleGraph.neighborSetFintypeOfFinite (G.induce (Set.range f))
  exact (signlessPreprojectiveAlgebraEquiv k f.isoInduceRange.symm).surjective.comp
    ((signlessPreprojectiveInducedSubgraphHom_surjective k G (Set.range f)).comp
      (neighborSetOfFiniteEquiv k).surjective)

/-- The quotient homomorphism associated to an induced graph embedding preserves every path-length
graded piece. -/
theorem signlessPreprojectiveEmbeddingHom_mem_grade (f : H ↪g G) {d : ℕ}
    {x : signlessPreprojectiveAlgebra k (DoubledQuiver G)}
    (hx : x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d) :
    signlessPreprojectiveEmbeddingHom k f x ∈
      signlessPreprojectiveGrade k (DoubledQuiver H) d := by
  let := SimpleGraph.neighborSetFintypeOfFinite (G.induce (Set.range f))
  rw [signlessPreprojectiveEmbeddingHom, AlgHom.comp_apply, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
    signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff]
  exact signlessPreprojectiveInducedSubgraphHom_mem_grade k G (Set.range f)
    ((neighborSetOfFiniteEquiv_mem_grade_iff k).mpr hx)

/-- Every homogeneous class of degree `d` on an induced subgraph `f : H ↪g G` lifts along
`signlessPreprojectiveEmbeddingHom` to a homogeneous class of degree `d` on `G`. -/
theorem exists_mem_signlessPreprojectiveGrade_signlessPreprojectiveEmbeddingHom_eq
    (f : H ↪g G) {d : ℕ} {y : signlessPreprojectiveAlgebra k (DoubledQuiver H)}
    (hy : y ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      signlessPreprojectiveEmbeddingHom k f x = y := by
  let := SimpleGraph.neighborSetFintypeOfFinite (G.induce (Set.range f))
  have hy' : signlessPreprojectiveAlgebraEquiv k f.isoInduceRange y ∈
      signlessPreprojectiveGrade k (DoubledQuiver (G.induce (Set.range f))) d :=
    (signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff k _).mpr hy
  obtain ⟨x, hx, hmap⟩ :=
    exists_mem_signlessPreprojectiveGrade_signlessPreprojectiveInducedSubgraphHom_eq
      k G (Set.range f) hy'
  refine ⟨(neighborSetOfFiniteEquiv k).symm x, ?_, ?_⟩
  · rwa [← neighborSetOfFiniteEquiv_mem_grade_iff k, AlgEquiv.apply_symm_apply]
  · simp [signlessPreprojectiveEmbeddingHom, hmap, ← signlessPreprojectiveAlgebraEquiv_symm]

/-- **Any nonzero homogeneous cyclic class of an induced subgraph lifts to the ambient graph** in
the same path degree, retaining the caller's neighborhood enumerations. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_embedding
    (f : H ↪g G) {d : ℕ}
    (hH : ∃ y ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d,
      y ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨y, hy, hy0⟩ := hH
  obtain ⟨x, hx, rfl⟩ :=
    exists_mem_signlessPreprojectiveGrade_signlessPreprojectiveEmbeddingHom_eq k f hy
  exact ⟨x, hx, fun hx0 => hy0 (map_mem_commutatorSubmodule _ hx0)⟩

end Embedding

end TauCeti
