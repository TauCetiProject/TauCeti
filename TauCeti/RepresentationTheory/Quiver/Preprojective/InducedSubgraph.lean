/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

## Main definitions

* `TauCeti.signlessPreprojectiveInducedSubgraphHom`: the quotient map from the signless
  preprojective algebra of a graph to that of an induced subgraph.

## Main results

* `TauCeti.signlessPreprojectiveInducedSubgraphHom_surjective`: the induced map is surjective.
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

/-- Neighbor sets in a graph on a finite vertex type are finite. -/
noncomputable local instance inducedSubgraphNeighborSetFintype
    {V : Type u} [Finite V] (G : SimpleGraph V) (v : V) : Fintype (G.neighborSet v) :=
  Fintype.ofFinite _

section PathAlgebra

variable (k : Type w) [CommRing k] {V : Type u} [Finite V]
  (G : SimpleGraph V) (S : Set V)

private abbrev InducedAlgebra :=
  signlessPreprojectiveAlgebra k (DoubledQuiver (G.induce S))

omit [Finite V] in
private theorem inducedAdj {i j : V} (hi : i ∈ S) (hj : j ∈ S) (h : G.Adj i j) :
    (G.induce S).Adj ⟨i, hi⟩ ⟨j, hj⟩ :=
  h

private theorem proof_heq {p q : Prop} (hp : p) (hq : q) : HEq hp hq := by
  have hpq : p = q := propext ⟨fun _ ↦ hq, fun _ ↦ hp⟩
  cases hpq
  exact heq_of_eq (Subsingleton.elim _ _)

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
      apply proof_heq
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

/-- Neighbours retained by an induced subgraph are its neighbours in the original graph which
belong to the inducing set. -/
private def inducedNeighborEquiv (v : V) (hv : v ∈ S) :
    {w : G.neighborSet v // (w : V) ∈ S} ≃ (G.induce S).neighborSet ⟨v, hv⟩ where
  toFun w := ⟨⟨w.1, w.2⟩, w.1.2⟩
  invFun w := ⟨⟨w.1.1, w.2⟩, w.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The path-algebra restriction kills every signless relation. -/
private theorem inducedSubgraphPathAlgebraHom_signlessPreprojectiveRelator
    (v : DoubledQuiver G) :
    inducedSubgraphPathAlgebraHom k G S (signlessPreprojectiveRelator k v) = 0 := by
  classical
  obtain ⟨v, rfl⟩ := exists_eq_vertex G v
  rw [signlessPreprojectiveRelator_congr k (vertex G v) _ inferInstance,
    signlessPreprojectiveRelator_vertex, map_sum]
  by_cases hv : v ∈ S
  · let f : G.neighborSet v → InducedAlgebra k G S := fun w =>
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
        apply Fintype.sum_equiv (inducedNeighborEquiv G S v hv)
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
  · apply Finset.sum_eq_zero
    intro w _
    rw [inducedSubgraphPathAlgebraHom_backtrackElem
      (k := k) (G := G) (S := S) w.2]
    simp [hv]

private theorem inducedSubgraphPathAlgebraHom_surjective_ofPath
    {a b : DoubledQuiver (G.induce S)} (p : Path a b) :
    ∃ x, inducedSubgraphPathAlgebraHom k G S x =
      signlessPreprojectiveMk k _ (ofPath ⟨a, b, p⟩) := by
  induction p with
  | nil =>
      obtain ⟨v, rfl⟩ := exists_eq_vertex (G.induce S) a
      refine ⟨vertexIdempotent k (vertex G v.1), ?_⟩
      rw [vertexIdempotent_eq_ofPath, inducedSubgraphPathAlgebraHom, liftAlgHom_ofPath]
      simp only [inducedSubgraphPath, inducedSubgraphVertex, vertexEquiv_symm_vertex]
      split_ifs with hv
      · rw [vertexIdempotent_eq_ofPath]
      · rw [vertexEquiv_symm_vertex] at hv
        exact (hv v.2).elim
  | @cons b c p e ih =>
      obtain ⟨i, rfl⟩ := exists_eq_vertex (G.induce S) b
      obtain ⟨j, rfl⟩ := exists_eq_vertex (G.induce S) c
      obtain ⟨x, hx⟩ := ih
      let h : G.Adj i.1 j.1 := by
        have he := e.down
        rw [vertexEquiv_symm_vertex, vertexEquiv_symm_vertex] at he
        exact SimpleGraph.induce_adj.mp he
      refine ⟨ofArrow (arrow G h) * x, ?_⟩
      rw [map_mul, inducedSubgraphPathAlgebraHom_ofArrow, dite_eq_left i.2,
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
      obtain ⟨x, hx⟩ := inducedSubgraphPathAlgebraHom_surjective_ofPath k G S p
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
            (ofArrow (arrow (G.induce S) (show (G.induce S).Adj ⟨i, hi⟩ ⟨j, hj⟩ from h)))
        else 0
      else 0 := by
  rw [signlessPreprojectiveInducedSubgraphHom,
    signlessPreprojectiveLift_signlessPreprojectiveMk,
    inducedSubgraphPathAlgebraHom_ofArrow]

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

end PathAlgebra

end TauCeti
