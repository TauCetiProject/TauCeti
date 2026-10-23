/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.OfArrows
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

/-!
# Matrix representations of signless preprojective algebras

Let `G` be a finite simple graph and `m` a finite type. Put a copy of `kᵐ` at every vertex and
choose, for every pair of adjacent vertices `i ∼ j`, a matrix `β i j` for the arrow `i → j` of the
doubled quiver. The backtrack `v → w → v` then acts at `v` by `β w v * β v w`, so the family is a
representation of the signless preprojective algebra `Π⁺(G)` exactly when the **signless matrix
relations**

```text
∑_{w ∼ v} β w v * β v w = 0
```

hold at every vertex `v`. The representation is an algebra homomorphism
`Π⁺(G) → Matrix (V × m) (V × m) k` sending the vertex idempotent at `v` to the block projection
`E_vv ⊗ 1` and the arrow `i → j` to the block `E_ji ⊗ β i j`.

Through such a representation, the matrix trace is a linear functional on `Π⁺(G)` which vanishes
on commutators. An element whose image has nonzero trace therefore has nonzero class in the cyclic
quotient `Π⁺(G) / [Π⁺(G), Π⁺(G)]`, the zeroth Hochschild homology of `Π⁺(G)`.

A representation of a subgraph extends by zero along a copy, by
`SimpleGraph.Copy.sum_extendByZero_mul_extendByZero`.

## Main definitions

* `TauCeti.signlessMatrixRepresentation`: the representation of `Π⁺(G)` determined by a family of
  matrices satisfying the signless relations.

## Main results

* `TauCeti.signlessMatrixRepresentation_vertexIdempotent`,
  `TauCeti.signlessMatrixRepresentation_ofPath_toPath` and
  `TauCeti.signlessMatrixRepresentation_ofArrow`: the values on vertex idempotents and arrows.
* `TauCeti.signlessMatrixRepresentation_backtrackElem`: a backtrack `v → w → v` acts by the block
  `E_vv ⊗ (β w v * β v w)`.
* `TauCeti.trace_signlessMatrixRepresentation_backtrackElem_mul_backtrackElem`: the trace of a
  product of two backtracks at a common vertex.

## References

* S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3, for the
  signless relation.
* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the cyclic quotient as zeroth Hochschild
  homology.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver Matrix
open scoped Kronecker

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} {m : Type*}

/-! ### The representation -/

section Representation

variable [Fintype V] [DecidableEq V] [Fintype m] [DecidableEq m]

/-- The block projection at a vertex of the doubled quiver. -/
private noncomputable def matrixVertex (v : DoubledQuiver G) : Matrix (V × m) (V × m) k :=
  single ((vertexEquiv G).symm v) ((vertexEquiv G).symm v) 1 ⊗ₖ 1

/-- The block of an arrow `i → j` of the doubled quiver: `β i j`, from the block of `i` to the
block of `j`. -/
private noncomputable def matrixArrow (β : V → V → Matrix m m k) {i j : DoubledQuiver G}
    (_ : i ⟶ j) : Matrix (V × m) (V × m) k :=
  single ((vertexEquiv G).symm j) ((vertexEquiv G).symm i) 1 ⊗ₖ
    β ((vertexEquiv G).symm i) ((vertexEquiv G).symm j)

/-- The block projections are complete orthogonal idempotents. -/
private theorem completeOrthogonalIdempotents_matrixVertex :
    CompleteOrthogonalIdempotents (matrixVertex (G := G) (k := k) (m := m)) := by
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  refine ⟨fun v w hvw => ?_, ?_⟩
  · simp [matrixVertex, ← mul_kronecker_mul, (vertexEquiv G).symm.injective.ne hvw]
  · ext ⟨a, i⟩ ⟨b, j⟩
    rw [← (vertexEquiv G).sum_comp]
    simp only [matrixVertex, Equiv.symm_apply_apply, Matrix.sum_apply, kroneckerMap_apply,
      single_apply, one_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp only [Prod.mk.injEq, hab, false_and, ite_false]
      exact Finset.sum_eq_zero fun c _ => by by_cases hc : c = a <;> simp_all

/-- The block of an arrow lies in the corner of its target block. -/
private theorem matrixVertex_mul_matrixArrow (β : V → V → Matrix m m k) {i j : DoubledQuiver G}
    (e : i ⟶ j) : matrixVertex j * matrixArrow β e = matrixArrow β e := by
  simp only [matrixVertex, matrixArrow, ← mul_kronecker_mul, single_mul_single_same, mul_one,
    one_mul]

/-- The block of an arrow lies in the corner of its source block. -/
private theorem matrixArrow_mul_matrixVertex (β : V → V → Matrix m m k) {i j : DoubledQuiver G}
    (e : i ⟶ j) : matrixArrow β e * matrixVertex i = matrixArrow β e := by
  simp only [matrixVertex, matrixArrow, ← mul_kronecker_mul, single_mul_single_same, mul_one]

variable (k) in
/-- The algebra homomorphism from the doubled path algebra prescribed by the matrix family. -/
private noncomputable def matrixPathAlgHom (β : V → V → Matrix m m k) :
    pathAlgebra k (DoubledQuiver G) →ₐ[k] Matrix (V × m) (V × m) k :=
  liftAlgHomOfArrows k matrixVertex completeOrthogonalIdempotents_matrixVertex
    (matrixArrow β) (matrixVertex_mul_matrixArrow β) (matrixArrow_mul_matrixVertex β)

private theorem matrixPathAlgHom_ofArrow (β : V → V → Matrix m m k) {i j : V} (h : G.Adj i j) :
    matrixPathAlgHom k β (ofArrow (arrow G h)) = single j i 1 ⊗ₖ β i j := by
  rw [matrixPathAlgHom, ofArrow_eq_ofPath, liftAlgHomOfArrows_ofPath_toPath, matrixArrow,
    vertexEquiv_symm_vertex, vertexEquiv_symm_vertex]

private theorem matrixPathAlgHom_backtrackElem (β : V → V → Matrix m m k) {v w : V}
    (h : G.Adj v w) :
    matrixPathAlgHom k β (backtrackElem G k h) = single v v 1 ⊗ₖ (β w v * β v w) := by
  rw [← ofArrow_symm_mul_ofArrow, map_mul, matrixPathAlgHom_ofArrow, matrixPathAlgHom_ofArrow,
    ← mul_kronecker_mul, single_mul_single_same, mul_one]

variable [DecidableRel G.Adj]

/-- The matrix family kills every signless relator exactly when it satisfies the signless matrix
relations; this is the direction needed to descend to the quotient. -/
private theorem matrixPathAlgHom_signlessPreprojectiveRelator (β : V → V → Matrix m m k)
    (hβ : ∀ v, ∑ w ∈ G.neighborFinset v, β w v * β v w = 0) (x : DoubledQuiver G) :
    matrixPathAlgHom k β (signlessPreprojectiveRelator k x) = 0 := by
  obtain ⟨v, rfl⟩ := exists_eq_vertex G x
  rw [signlessPreprojectiveRelator_congr k (vertex G v) _ inferInstance,
    signlessPreprojectiveRelator_vertex, map_sum]
  simp_rw [matrixPathAlgHom_backtrackElem]
  -- Pull the common block `E_vv` out of the sum and recognize the relation at `v`.
  have hsum : ∑ w : G.neighborSet v, single v v (1 : k) ⊗ₖ (β w v * β v w) =
      single v v 1 ⊗ₖ ∑ w ∈ G.neighborFinset v, β w v * β v w := by
    rw [← Finset.sum_coe_sort (G.neighborFinset v)]
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => by simp) _ _ fun _ => rfl
  rw [hsum, hβ, kronecker_zero]

variable (k) in
/-- **The matrix representation of a signless preprojective algebra**: a family `β` of matrices,
`β i j` for the arrow `i → j` of the doubled quiver, satisfying the signless relations
`∑_{w ∼ v} β w v * β v w = 0` defines an algebra homomorphism from `Π⁺(G)` to block matrices. The
vertex idempotent at `v` goes to the block projection `E_vv ⊗ 1`, and the arrow `i → j` to the
block `E_ji ⊗ β i j`. The values of `β` at non-adjacent vertices are not used. -/
noncomputable def signlessMatrixRepresentation (β : V → V → Matrix m m k)
    (hβ : ∀ v, ∑ w ∈ G.neighborFinset v, β w v * β v w = 0) :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) →ₐ[k] Matrix (V × m) (V × m) k :=
  signlessPreprojectiveLift (matrixPathAlgHom k β)
    (matrixPathAlgHom_signlessPreprojectiveRelator β hβ)

variable (β : V → V → Matrix m m k) (hβ : ∀ v, ∑ w ∈ G.neighborFinset v, β w v * β v w = 0)

/-- The matrix representation sends the vertex idempotent at `v` to the block projection. -/
@[simp]
theorem signlessMatrixRepresentation_vertexIdempotent (v : V) :
    signlessMatrixRepresentation k β hβ
        (signlessPreprojectiveMk k _ (vertexIdempotent k (vertex G v))) =
      single v v 1 ⊗ₖ 1 := by
  rw [signlessMatrixRepresentation, signlessPreprojectiveLift_signlessPreprojectiveMk,
    matrixPathAlgHom, liftAlgHomOfArrows_vertexIdempotent, matrixVertex, vertexEquiv_symm_vertex]

/-- The matrix representation sends the length-one path of the arrow `i → j` to the block
`E_ji ⊗ β i j`. This is the simp-normal form of `signlessMatrixRepresentation_ofArrow`. -/
@[simp]
theorem signlessMatrixRepresentation_ofPath_toPath {i j : V} (h : G.Adj i j) :
    signlessMatrixRepresentation k β hβ
        (signlessPreprojectiveMk k _ (ofPath ⟨vertex G i, vertex G j, (arrow G h).toPath⟩)) =
      single j i 1 ⊗ₖ β i j := by
  rw [signlessMatrixRepresentation, signlessPreprojectiveLift_signlessPreprojectiveMk,
    ← ofArrow_eq_ofPath, matrixPathAlgHom_ofArrow]

/-- The matrix representation sends the arrow `i → j` to the block `E_ji ⊗ β i j`. This is not a
simp lemma: `ofArrow` is not in simp-normal form, and
`signlessMatrixRepresentation_ofPath_toPath` covers its normal form. -/
theorem signlessMatrixRepresentation_ofArrow {i j : V} (h : G.Adj i j) :
    signlessMatrixRepresentation k β hβ (signlessPreprojectiveMk k _ (ofArrow (arrow G h))) =
      single j i 1 ⊗ₖ β i j := by
  rw [ofArrow_eq_ofPath, signlessMatrixRepresentation_ofPath_toPath]

/-- The matrix representation sends the backtrack `v → w → v` to the block
`E_vv ⊗ (β w v * β v w)`. -/
@[simp]
theorem signlessMatrixRepresentation_backtrackElem {v w : V} (h : G.Adj v w) :
    signlessMatrixRepresentation k β hβ (signlessPreprojectiveMk k _ (backtrackElem G k h)) =
      single v v 1 ⊗ₖ (β w v * β v w) := by
  rw [signlessMatrixRepresentation, signlessPreprojectiveLift_signlessPreprojectiveMk,
    matrixPathAlgHom_backtrackElem]

/-- The trace of the image of a product of two backtracks `v → w₁ → v` and `v → w₂ → v` at a
common vertex `v` is the trace of the product of their blocks at `v`. -/
theorem trace_signlessMatrixRepresentation_backtrackElem_mul_backtrackElem {v w₁ w₂ : V}
    (h₁ : G.Adj v w₁) (h₂ : G.Adj v w₂) :
    trace (signlessMatrixRepresentation k β hβ
        (signlessPreprojectiveMk k _ (backtrackElem G k h₁ * backtrackElem G k h₂))) =
      trace (β w₁ v * β v w₁ * (β w₂ v * β v w₂)) := by
  rw [map_mul, map_mul, signlessMatrixRepresentation_backtrackElem,
    signlessMatrixRepresentation_backtrackElem, ← mul_kronecker_mul, single_mul_single_same,
    trace_kronecker, trace_single_eq_same, mul_one, one_mul]

end Representation

end TauCeti
