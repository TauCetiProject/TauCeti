/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Algebra.TemperleyLieb.PathModel
public import TauCeti.Combinatorics.SimpleGraph.EndpointWalk
public import TauCeti.Data.Matrix.Block
/-! # Endpoint-graded path algebras of locally finite graphs

Restricting `TauCeti.Algebra.TemperleyLieb.PathModel` to genuine `n`-step walks from `v₀` and
decomposing by their endpoint in `G.walkEndpoints v₀ n` extends the path model to arbitrary locally
finite graphs: `PathAlgebra K G v₀ n`, one-step extension homomorphisms `pathAlgebraExtend` /
`pathAlgebraStarExtend` (injective when no reachable vertex is a dead end), Temperley–Lieb
(`⋆`-)representations `pathAlgebraRep` / `pathAlgebraStarRep` and `pathAlgebraRep_surjective`,
the weighted last-step closure map `pathAlgebraExpect` (a unital `pathAlgebraExtend`-bimodule
retraction when `r` is nowhere zero, `δ ≠ 0`, and `r ^ 2` is a `δ`-eigenvector; positivity and
C⋆-conditional expectations are developed in `Quotient.Positivity` and `Quotient.Tower`), and the
Markov trace `pathAlgebraTrace` / `isMarkovTrace_pathAlgebraTrace`.

## References

* F. M. Goodman, P. de la Harpe, V. F. R. Jones, *Coxeter Graphs and Towers of Algebras*, MSRI
  Publications 14, Springer (1989) (path algebras of graphs, Bratteli extension homomorphisms, and
  Temperley–Lieb path representations).
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25 (Temperley–Lieb algebras
  and Markov traces). -/
public section
open Function Matrix SimpleGraph
namespace TauCeti.TemperleyLieb
section PathAlgebra
variable (K : Type*) {V : Type*} (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V)
/-- The **endpoint-graded path algebra** of a locally finite graph `G` from `v₀` at level `n`: the
finite product over `v ∈ G.walkEndpoints v₀ n` of full matrix algebras on `EndpointWalk`. -/
abbrev PathAlgebra (n : ℕ) :=
  ∀ v : G.walkEndpoints v₀ n, Matrix (G.EndpointWalk v₀ n v.val) (G.EndpointWalk v₀ n v.val) K
namespace PathAlgebra
variable {K G v₀}
section Semiring
variable [Semiring K] {n : ℕ}
/-- A matrix entry supported on a single endpoint block `t` at `(p, q)`. -/
def blockSingle (t : G.walkEndpoints v₀ n) (p q : G.EndpointWalk v₀ n t.val) (c : K) :
    PathAlgebra K G v₀ n := Pi.single t (Matrix.single p q c)
@[simp] theorem blockSingle_apply_same (t : G.walkEndpoints v₀ n) (p q : G.EndpointWalk v₀ n t.val)
    (c : K) : blockSingle t p q c t = Matrix.single p q c := Pi.single_eq_same t _
theorem blockSingle_apply_of_ne {t s : G.walkEndpoints v₀ n} (hts : s ≠ t)
    (p q : G.EndpointWalk v₀ n t.val) (c : K) : blockSingle t p q c s = 0 :=
  Pi.single_eq_of_ne hts _
/-- Every element of `PathAlgebra K G v₀ n` expands in the `blockSingle` matrix-unit basis. -/
theorem eq_sum_blockSingle (X : PathAlgebra K G v₀ n) :
    X = ∑ t : G.walkEndpoints v₀ n, ∑ p : G.EndpointWalk v₀ n t.val,
      ∑ q : G.EndpointWalk v₀ n t.val, X t p q • blockSingle t p q (1 : K) := by
  conv_lhs => rw [← LinearMap.sum_single_apply _ X]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  conv_lhs => rw [Matrix.matrix_eq_sum_single (X t)]
  simp only [blockSingle, ← LinearMap.single_apply (R := K)
    (φ := fun t : G.walkEndpoints v₀ n ↦
      Matrix (G.EndpointWalk v₀ n t.val) (G.EndpointWalk v₀ n t.val) K),
    ← map_sum, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
/-- The identity of `PathAlgebra K G v₀ n` is the sum of diagonal `blockSingle` matrix units. -/
theorem one_eq_sum_blockSingle : (1 : PathAlgebra K G v₀ n) =
    ∑ s : G.walkEndpoints v₀ n, ∑ w : G.EndpointWalk v₀ n s.val, blockSingle s w w 1 := by
  conv_lhs => rw [← LinearMap.sum_single_apply _ (1 : PathAlgebra K G v₀ n)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Pi.one_apply, ← Matrix.sum_single_one]
  simp only [blockSingle, ← LinearMap.single_apply (R := ℕ)
    (φ := fun t : G.walkEndpoints v₀ n ↦
      Matrix (G.EndpointWalk v₀ n t.val) (G.EndpointWalk v₀ n t.val) K), map_sum]
end Semiring
section CommSemiring
variable [CommSemiring K] {n : ℕ}
/-- Extract the `u`-block of `PathAlgebra K G v₀ n` (`0` when `u ∉ G.walkEndpoints v₀ n`). -/
def blockAt (u : V) :
    PathAlgebra K G v₀ n →ₐ[K] Matrix (G.EndpointWalk v₀ n u) (G.EndpointWalk v₀ n u) K where
  toFun X := if hu : u ∈ G.walkEndpoints v₀ n then X ⟨u, hu⟩ else 0
  map_one' := by
    split_ifs with hu; · rfl
    have := G.isEmpty_endpointWalk_of_notMem v₀ hu; exact Subsingleton.elim _ _
  map_mul' _ _ := by split_ifs <;> simp
  map_zero' := by split_ifs <;> rfl
  map_add' _ _ := by split_ifs <;> simp
  commutes' _ := by
    split_ifs with hu; · simp [Algebra.algebraMap_eq_smul_one]
    have := G.isEmpty_endpointWalk_of_notMem v₀ hu; exact Subsingleton.elim _ _
@[simp] theorem blockAt_of_mem {u : V} (hu : u ∈ G.walkEndpoints v₀ n) (X : PathAlgebra K G v₀ n) :
    blockAt u X = X ⟨u, hu⟩ := dite_eq_left hu
theorem blockAt_of_notMem {u : V} (hu : u ∉ G.walkEndpoints v₀ n) (X : PathAlgebra K G v₀ n) :
    blockAt u X = 0 := dite_eq_right hu
@[simp] theorem blockAt_conjTranspose [StarRing K] (u : V) (X : PathAlgebra K G v₀ n) :
    (blockAt u X)ᴴ = blockAt u (star X) := by
  by_cases hu : u ∈ G.walkEndpoints v₀ n <;>
    simp [blockAt_of_mem, blockAt_of_notMem, hu, Matrix.star_eq_conjTranspose]
end CommSemiring
end PathAlgebra
section Finrank
variable [Field K]
/-- Dimension of `PathAlgebra K G v₀ n` as a sum of squared `n`-step walk counts. -/
theorem finrank_pathAlgebra (n : ℕ) : Module.finrank K (PathAlgebra K G v₀ n) =
    ∑ v ∈ G.walkEndpoints v₀ n, Fintype.card (G.EndpointWalk v₀ n v) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_matrix, Module.finrank_self, mul_one, ← sq]
  exact (G.walkEndpoints v₀ n).sum_attach fun v ↦ Fintype.card (G.EndpointWalk v₀ n v) ^ 2
/-- On a finite vertex type, `finrank_pathAlgebra` sums squared `n`-step walk counts over all
vertices. -/
theorem finrank_pathAlgebra_of_fintype [Fintype V] (n : ℕ) :
    Module.finrank K (PathAlgebra K G v₀ n) =
      ∑ v : V, Fintype.card (G.EndpointWalk v₀ n v) ^ 2 := by
  rw [finrank_pathAlgebra]; exact Finset.sum_subset (Finset.subset_univ _) fun v _ hv ↦ by
    have := G.isEmpty_endpointWalk_of_notMem v₀ hv
    simp [Fintype.card_eq_zero]
end Finrank
end PathAlgebra
section Extend
variable {K : Type*} [CommSemiring K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [LocallyFinite G] (v₀ : V) {n : ℕ}
/-- One-step extension homomorphism `PathAlgebra K G v₀ n →ₐ[K] PathAlgebra K G v₀ (n + 1)` acting
block-diagonally along `SimpleGraph.EndpointWalk.succEquiv`. It need not be injective in general: a
block at a reachable vertex with no neighbours maps to `0`, so injectivity requires excluding
reachable dead ends. -/
def pathAlgebraExtend : PathAlgebra K G v₀ n →ₐ[K] PathAlgebra K G v₀ (n + 1) :=
  AlgHom.pi fun v ↦
    (Matrix.reindexAlgEquiv K K (EndpointWalk.succEquiv G v₀ n v.val).symm).toAlgHom.comp
      ((Matrix.blockDiagonal'AlgHom _ K K).comp
        (AlgHom.pi fun u : G.neighborSet v.val ↦ PathAlgebra.blockAt u.val))
theorem pathAlgebraExtend_apply (X : PathAlgebra K G v₀ n) (v : G.walkEndpoints v₀ (n + 1)) :
    pathAlgebraExtend G v₀ X v =
      (Matrix.blockDiagonal' fun u : G.neighborSet v.val ↦ PathAlgebra.blockAt u.val X).submatrix
        (EndpointWalk.succEquiv G v₀ n v.val) (EndpointWalk.succEquiv G v₀ n v.val) := by
  simp only [pathAlgebraExtend, AlgHom.pi_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Equiv.symm_symm,
    Matrix.blockDiagonal'AlgHom_apply]
  rfl
/-- Matrix entries of `pathAlgebraExtend G v₀ X` on extended walks `p.snoc h₁` and `q.snoc h₂`. -/
theorem pathAlgebraExtend_apply_snoc (X : PathAlgebra K G v₀ n) {u₁ u₂ v : V}
    (p : G.EndpointWalk v₀ n u₁) (q : G.EndpointWalk v₀ n u₂) (h₁ : G.Adj u₁ v) (h₂ : G.Adj u₂ v)
    (hv : v ∈ G.walkEndpoints v₀ (n + 1)) :
    pathAlgebraExtend G v₀ X ⟨v, hv⟩ (p.snoc h₁) (q.snoc h₂) =
      if h : u₁ = u₂ then X ⟨u₁, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩⟩ p (q.cast h.symm)
      else 0 := by
  rw [pathAlgebraExtend_apply, Matrix.submatrix_apply, EndpointWalk.succEquiv_snoc,
    EndpointWalk.succEquiv_snoc]; split_ifs with h
  · subst h; simp [Matrix.blockDiagonal'_apply_eq, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩]
  · rw [Matrix.blockDiagonal'_apply, dite_eq_right fun heq ↦ h (congrArg Subtype.val heq)]
@[simp] theorem pathAlgebraExtend_apply_snoc_same (X : PathAlgebra K G v₀ n) {u v : V}
    (p q : G.EndpointWalk v₀ n u) (h : G.Adj u v) (hv : v ∈ G.walkEndpoints v₀ (n + 1)) :
    pathAlgebraExtend G v₀ X ⟨v, hv⟩ (p.snoc h) (q.snoc h) =
      X ⟨u, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩⟩ p q := by
  rw [pathAlgebraExtend_apply_snoc, dite_eq_left rfl, EndpointWalk.cast_rfl]
/-- `pathAlgebraExtend` is injective whenever every `n`-step reachable vertex has a neighbour. -/
theorem pathAlgebraExtend_injective
    (hneigh : ∀ u ∈ G.walkEndpoints v₀ n, ∃ v, G.Adj u v) :
    Function.Injective (pathAlgebraExtend G v₀ (K := K) (n := n)) := by
  intro X Y hXY; ext u p q
  obtain ⟨v, huv⟩ := hneigh u.val u.property
  have hv : v ∈ G.walkEndpoints v₀ (n + 1) := (G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc huv⟩
  have h := congrFun (congrFun (congrFun hXY ⟨v, hv⟩) (p.snoc huv)) (q.snoc huv)
  simpa [pathAlgebraExtend_apply_snoc_same] using h
/-- Entries of `pathAlgebraExtend` applied to a single matrix unit `blockSingle u p₁ p₂ c`. -/
theorem pathAlgebraExtend_blockSingle_apply (u : G.walkEndpoints v₀ n)
    (p₁ p₂ : G.EndpointWalk v₀ n u.val)
    (c : K) (s : G.walkEndpoints v₀ (n + 1)) (w y : G.EndpointWalk v₀ (n + 1) s.val) :
    pathAlgebraExtend G v₀ (PathAlgebra.blockSingle u p₁ p₂ c) s w y =
      if (w.init : Fin (n + 1) → V) = p₁ ∧ (y.init : Fin (n + 1) → V) = p₂ then c else 0 := by
  rcases u with ⟨u₀, hu₀⟩; conv_lhs => rw [← w.snoc_init, ← y.snoc_init]
  rw [pathAlgebraExtend_apply_snoc]
  by_cases hwy : w (Fin.last n).castSucc = y (Fin.last n).castSucc
  · rw [dite_eq_left hwy]; by_cases hwu : u₀ = w (Fin.last n).castSucc
    · subst hwu; rw [PathAlgebra.blockSingle_apply_same, Matrix.single_apply]
      simp only [← DFunLike.coe_injective.eq_iff, EndpointWalk.coe_cast, eq_comm]
    · rw [PathAlgebra.blockSingle_apply_of_ne (fun h ↦ hwu (congrArg Subtype.val h).symm),
        Matrix.zero_apply,
        ite_eq_right fun h ↦ hwu (EndpointWalk.penultimate_eq_of_coe_init_eq h.1).symm]
  · rw [dite_eq_right hwy, ite_eq_right fun h ↦
      hwy ((EndpointWalk.penultimate_eq_of_coe_init_eq h.1).trans
        (EndpointWalk.penultimate_eq_of_coe_init_eq h.2).symm)]
/-- The extension homomorphism `pathAlgebraExtend` preserves the blockwise conjugate-transpose
adjoint. -/
@[simp] theorem pathAlgebraExtend_star [StarRing K] (X : PathAlgebra K G v₀ n) :
    pathAlgebraExtend G v₀ (star X) = star (pathAlgebraExtend G v₀ X) := funext fun _ ↦ by
  simp [pathAlgebraExtend_apply, Matrix.star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose]
/-- One-step `⋆`-algebra extension homomorphism (injective without reachable dead ends). -/
def pathAlgebraStarExtend [StarRing K] : PathAlgebra K G v₀ n →⋆ₐ[K] PathAlgebra K G v₀ (n + 1) :=
  { pathAlgebraExtend G v₀ with map_star' := pathAlgebraExtend_star G v₀ }
/-- Forgetting the star structure on `pathAlgebraStarExtend` recovers `pathAlgebraExtend`. -/
@[simp] theorem pathAlgebraStarExtend_toAlgHom [StarRing K] :
    (pathAlgebraStarExtend G v₀ (K := K) (n := n)).toAlgHom = pathAlgebraExtend G v₀ := (rfl)
/-- Evaluating `pathAlgebraStarExtend` agrees with `pathAlgebraExtend`. -/
@[simp] theorem pathAlgebraStarExtend_apply [StarRing K] (X : PathAlgebra K G v₀ n) :
    pathAlgebraStarExtend G v₀ X = pathAlgebraExtend G v₀ X := (rfl)
end Extend
section WalkTraceBasic
variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [LocallyFinite G] (v₀ : V) (r : V → K)
/-- The **endpoint-weighted matrix trace** on `PathAlgebra K G v₀ n`, summing `(r v / r v₀) ^ 2`
times the matrix trace on each endpoint block `v`. -/
def pathAlgebraTrace {n : ℕ} : PathAlgebra K G v₀ n →ₗ[K] K where
  toFun X := ∑ v : G.walkEndpoints v₀ n, (r v.val / r v₀) ^ 2 * (X v).trace
  map_add' _ _ := by simp [Matrix.trace_add, mul_add, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Matrix.trace_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
variable {G v₀ r}
theorem pathAlgebraTrace_apply {n : ℕ} (X : PathAlgebra K G v₀ n) :
    pathAlgebraTrace G v₀ r X =
      ∑ v : G.walkEndpoints v₀ n, (r v.val / r v₀) ^ 2 * (X v).trace := (rfl)
theorem pathAlgebraTrace_eq_sum_walkEndpoints {n : ℕ} (X : PathAlgebra K G v₀ n) :
    pathAlgebraTrace G v₀ r X =
    ∑ v ∈ G.walkEndpoints v₀ n, (r v / r v₀) ^ 2 * (PathAlgebra.blockAt v X).trace := by
  rw [pathAlgebraTrace_apply, ← (G.walkEndpoints v₀ n).sum_attach]; simp [Finset.univ_eq_attach]
/-- `pathAlgebraTrace` is tracial on `PathAlgebra K G v₀ n`. -/
theorem pathAlgebraTrace_mul_comm {n : ℕ} (X Y : PathAlgebra K G v₀ n) :
    pathAlgebraTrace G v₀ r (X * Y) = pathAlgebraTrace G v₀ r (Y * X) :=
  Finset.sum_congr rfl fun _ _ ↦ by rw [Pi.mul_apply, Pi.mul_apply, Matrix.trace_mul_comm]
/-- When `r ^ 2` is a `δ`-eigenvector of `G`'s adjacency matrix, `pathAlgebraExtend` scales
`pathAlgebraTrace` by `δ`. -/
theorem pathAlgebraTrace_pathAlgebraExtend {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) {n : ℕ}
    (X : PathAlgebra K G v₀ n) :
    pathAlgebraTrace G v₀ r (pathAlgebraExtend G v₀ X) = δ * pathAlgebraTrace G v₀ r X := by
  rw [pathAlgebraTrace_eq_sum_walkEndpoints, pathAlgebraTrace_eq_sum_walkEndpoints, Finset.mul_sum]
  have htr {v : V} (hv : v ∈ G.walkEndpoints v₀ (n + 1)) :
      (PathAlgebra.blockAt v (pathAlgebraExtend G v₀ X)).trace =
        ∑ u ∈ G.neighborFinset v, (PathAlgebra.blockAt u X).trace := by
    rw [PathAlgebra.blockAt_of_mem hv, Matrix.trace, G.sum_endpointWalk_succ v₀ n v,
      ← (G.neighborFinset v).sum_attach fun u ↦ (PathAlgebra.blockAt u X).trace]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    by_cases hu : u.val ∈ G.walkEndpoints v₀ n; · simp [hu, Matrix.trace]
    have := G.isEmpty_endpointWalk_of_notMem v₀ hu
    simp [PathAlgebra.blockAt_of_notMem hu]
  rw [Finset.sum_congr rfl fun _ hv ↦ by rw [htr hv, Finset.mul_sum],
    G.sum_walkEndpoints_succ v₀ n (fun v u ↦ (r v / r v₀) ^ 2 * (PathAlgebra.blockAt u X).trace)
      fun _ _ hu ↦ by rw [PathAlgebra.blockAt_of_notMem hu, Matrix.trace_zero, mul_zero]]
  exact Finset.sum_congr rfl fun u _ ↦ by
    rw [← Finset.sum_mul]; simp_rw [div_pow, div_eq_mul_inv, ← Finset.sum_mul, hδ u]; ring
/-- `pathAlgebraTrace 1 = δ ^ n` when `r v₀ ≠ 0` and `r ^ 2` is a `δ`-eigenvector. -/
theorem pathAlgebraTrace_one (hr₀ : r v₀ ≠ 0) {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (n : ℕ) :
    pathAlgebraTrace G v₀ r (1 : PathAlgebra K G v₀ n) = δ ^ n := by
  induction n with
  | zero => simp [pathAlgebraTrace_eq_sum_walkEndpoints, div_self hr₀]
  | succ n ih =>
    rw [← map_one (pathAlgebraExtend G v₀ (K := K) (n := n)),
      pathAlgebraTrace_pathAlgebraExtend hδ, ih, pow_succ']
end WalkTraceBasic
section WalkExpect
variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [G.LocallyFinite] (v₀ : V) (r : V → K) (δ : K)
/-- Weighted last-step closure `PathAlgebra K G v₀ (n + 1) →ₗ[K] PathAlgebra K G v₀ n` closing
the final step of walks from `u` across `v ∈ G.neighborFinset u` with weight
`δ⁻¹ * (r v / r u) ^ 2`. It is always a `pathAlgebraExtend`-bimodule map, and is a unital
`pathAlgebraExtend`-bimodule retraction (`pathAlgebraExpect_one`,
`pathAlgebraExpect_pathAlgebraExtend`) when `r` is nowhere zero, `δ ≠ 0`, and `r ^ 2` is a
`δ`-eigenvector of `G`'s adjacency matrix. Over `ℂ` with self-adjoint weights `r` and real
`δ > 0`, `pathAlgebraExpect (star Y * Y)` is a finite sum of squares
(`TauCeti.Algebra.TemperleyLieb.Quotient.Positivity`), yielding the C⋆-conditional expectation
`IsMarkovTrace.cstarConditionalExpectation` on the positive Jones quotient tower
(`TauCeti.Algebra.TemperleyLieb.Quotient.Tower`). -/
def pathAlgebraExpect {n : ℕ} : PathAlgebra K G v₀ (n + 1) →ₗ[K] PathAlgebra K G v₀ n where
  toFun Y u := Matrix.of fun p q ↦
    δ⁻¹ * ∑ v ∈ (G.neighborFinset u.val).attach, (r v.val / r u.val) ^ 2 *
      PathAlgebra.blockAt v.val Y (p.snoc ((G.mem_neighborFinset u.val v.val).1 v.property))
        (q.snoc ((G.mem_neighborFinset u.val v.val).1 v.property))
  map_add' _ _ := by ext u p q; simp [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' _ _ := by
    ext u p q; simp only [RingHom.id_apply, Pi.smul_apply, Matrix.smul_apply, Matrix.of_apply,
      map_smul, smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
theorem pathAlgebraExpect_apply {n : ℕ} (Y : PathAlgebra K G v₀ (n + 1)) (u : G.walkEndpoints v₀ n)
    (p q : G.EndpointWalk v₀ n u.val) : pathAlgebraExpect G v₀ r δ Y u p q =
      δ⁻¹ * ∑ v ∈ (G.neighborFinset u.val).attach, (r v.val / r u.val) ^ 2 *
        PathAlgebra.blockAt v.val Y (p.snoc ((G.mem_neighborFinset u.val v.val).1 v.property))
          (q.snoc ((G.mem_neighborFinset u.val v.val).1 v.property)) := (rfl)
variable {G v₀ r δ}
/-- `pathAlgebraExpect` is unital when `r` is nowhere zero, `δ ≠ 0`, and `r ^ 2` is a
`δ`-eigenvector. -/
@[simp] theorem pathAlgebraExpect_one (hr : ∀ v, r v ≠ 0) (hδ₀ : δ ≠ 0)
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (n : ℕ) :
    pathAlgebraExpect G v₀ r δ (1 : PathAlgebra K G v₀ (n + 1)) = 1 := by
  ext u p q; rw [pathAlgebraExpect_apply, Pi.one_apply, Matrix.one_apply]
  have hsnoc {v : V} (h : G.Adj u.val v) : p.snoc h = q.snoc h ↔ p = q :=
    ⟨fun hpq ↦ EndpointWalk.ext fun i ↦ by simpa using congrArg (· i.castSucc) hpq, (· ▸ rfl)⟩
  simp_rw [map_one (PathAlgebra.blockAt _), Matrix.one_apply, hsnoc]; split_ifs
  · rw [Finset.sum_attach (G.neighborFinset u.val) fun v ↦ (r v / r u.val) ^ 2 * 1]
    simp_rw [mul_one, div_pow, div_eq_mul_inv, ← Finset.sum_mul, hδ u.val]
    have := hr u.val; field_simp
  · simp
/-- Left bimodule property of `pathAlgebraExpect` over `pathAlgebraExtend`. -/
@[simp] theorem pathAlgebraExpect_pathAlgebraExtend_mul {n : ℕ} (X : PathAlgebra K G v₀ n)
    (Y : PathAlgebra K G v₀ (n + 1)) :
    pathAlgebraExpect G v₀ r δ (pathAlgebraExtend G v₀ X * Y) =
      X * pathAlgebraExpect G v₀ r δ Y := by
  ext u p q; rw [pathAlgebraExpect_apply, Pi.mul_apply, Matrix.mul_apply]
  have hterm {v : V} (hv : G.Adj u.val v) :
      PathAlgebra.blockAt v (pathAlgebraExtend G v₀ X * Y) (p.snoc hv) (q.snoc hv) =
        ∑ p' : G.EndpointWalk v₀ n u.val,
          X u p p' * PathAlgebra.blockAt v Y (p'.snoc hv) (q.snoc hv) := by
    rw [map_mul, PathAlgebra.blockAt_of_mem ((G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc hv⟩),
      Matrix.mul_apply, G.sum_endpointWalk_succ v₀ n v,
      Finset.sum_eq_single_of_mem ⟨u.val, (G.mem_neighborFinset v u.val).2 hv.symm⟩
        (Finset.mem_attach _ _) fun _ _ hu' ↦ Finset.sum_eq_zero fun _ _ ↦ by
          rw [pathAlgebraExtend_apply_snoc,
            dite_eq_right fun h ↦ hu' (Subtype.ext h.symm), zero_mul],
      Finset.sum_congr rfl fun _ _ ↦ by rw [pathAlgebraExtend_apply_snoc_same]]
  simp_rw [hterm, Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ ↦ ?_
  simp_rw [pathAlgebraExpect_apply, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
/-- Right bimodule property of `pathAlgebraExpect` over `pathAlgebraExtend`. -/
@[simp] theorem pathAlgebraExpect_mul_pathAlgebraExtend {n : ℕ} (Y : PathAlgebra K G v₀ (n + 1))
    (X : PathAlgebra K G v₀ n) :
    pathAlgebraExpect G v₀ r δ (Y * pathAlgebraExtend G v₀ X) =
      pathAlgebraExpect G v₀ r δ Y * X := by
  let trp {m : ℕ} (Z : PathAlgebra K G v₀ m) : PathAlgebra K G v₀ m := fun u ↦ (Z u).transpose
  have hAt {m} (Z : PathAlgebra K G v₀ m) (u : V) :
      (PathAlgebra.blockAt u Z).transpose = PathAlgebra.blockAt u (trp Z) := by
    by_cases hu : u ∈ G.walkEndpoints v₀ m <;> simp [trp, PathAlgebra.blockAt_of_notMem, hu]
  have hE : pathAlgebraExtend G v₀ (trp X) = trp (pathAlgebraExtend G v₀ X) := funext fun _ ↦ by
    simp [trp, pathAlgebraExtend_apply, Matrix.blockDiagonal'_transpose, hAt]
  have hW {Z : PathAlgebra K G v₀ (n + 1)} :
      pathAlgebraExpect G v₀ r δ (trp Z) = trp (pathAlgebraExpect G v₀ r δ Z) := by
    ext; simp [trp, pathAlgebraExpect_apply, ← hAt]
  have h := congrArg trp (pathAlgebraExpect_pathAlgebraExtend_mul (r := r) (δ := δ) (trp X) (trp Y))
  rw [hE, (funext fun _ ↦ (Matrix.transpose_mul _ _).symm :
    trp (pathAlgebraExtend G v₀ X) * trp Y = trp (Y * pathAlgebraExtend G v₀ X)), hW, hW] at h
  exact funext fun u ↦ by simpa [trp] using congrFun h u
/-- `pathAlgebraExpect` is a left inverse to `pathAlgebraExtend` under the eigenvector
normalization. -/
@[simp] theorem pathAlgebraExpect_pathAlgebraExtend (hr : ∀ v, r v ≠ 0) (hδ₀ : δ ≠ 0)
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) {n : ℕ}
    (X : PathAlgebra K G v₀ n) : pathAlgebraExpect G v₀ r δ (pathAlgebraExtend G v₀ X) = X := by
  rw [← mul_one (pathAlgebraExtend G v₀ X), pathAlgebraExpect_pathAlgebraExtend_mul,
    pathAlgebraExpect_one hr hδ₀ hδ, mul_one]
/-- Trace compatibility of `pathAlgebraExpect`:
`pathAlgebraTrace (pathAlgebraExpect Y) = δ⁻¹ * pathAlgebraTrace Y`. -/
@[simp] theorem pathAlgebraTrace_pathAlgebraExpect (hr : ∀ v, r v ≠ 0) {n : ℕ}
    (Y : PathAlgebra K G v₀ (n + 1)) :
    pathAlgebraTrace G v₀ r (pathAlgebraExpect G v₀ r δ Y) = δ⁻¹ * pathAlgebraTrace G v₀ r Y := by
  classical
  let step (v u : V) : K := if h : G.Adj u v then
    ∑ p : G.EndpointWalk v₀ n u, PathAlgebra.blockAt v Y (p.snoc h) (p.snoc h) else 0
  have htrY (v : V) : (PathAlgebra.blockAt v Y).trace = ∑ u ∈ G.neighborFinset v, step v u := by
    rw [Matrix.trace, G.sum_endpointWalk_succ v₀ n v, ← (G.neighborFinset v).sum_attach (step v)]
    exact Finset.sum_congr rfl fun u _ ↦ by
      simp only [Matrix.diag_apply, step,
        dite_eq_left ((G.mem_neighborFinset v u.val).1 u.property).symm]
  have htrE {u : V} (hu : u ∈ G.walkEndpoints v₀ n) :
      (PathAlgebra.blockAt u (pathAlgebraExpect G v₀ r δ Y)).trace =
        δ⁻¹ * ∑ v ∈ G.neighborFinset u, (r v / r u) ^ 2 * step v u := by
    simp only [PathAlgebra.blockAt_of_mem hu, Matrix.trace, Matrix.diag_apply,
      pathAlgebraExpect_apply]
    rw [← Finset.mul_sum, Finset.sum_comm, ← (G.neighborFinset u).sum_attach fun v ↦ _]
    exact congrArg (δ⁻¹ * ·) (Finset.sum_congr rfl fun v _ ↦ by
      simp only [step, dite_eq_left ((G.mem_neighborFinset u v.val).1 v.property), Finset.mul_sum])
  rw [pathAlgebraTrace_eq_sum_walkEndpoints, pathAlgebraTrace_eq_sum_walkEndpoints, Finset.mul_sum,
    Finset.sum_congr rfl fun _ hu ↦ by rw [htrE hu, mul_left_comm, Finset.mul_sum, Finset.mul_sum],
    Finset.sum_congr (s₁ := G.walkEndpoints v₀ (n + 1)) rfl fun v _ ↦ by
      rw [htrY v, Finset.mul_sum, Finset.mul_sum],
    G.sum_walkEndpoints_succ v₀ n (fun v u ↦ δ⁻¹ * ((r v / r v₀) ^ 2 * step v u)) fun _ _ hu ↦ by
      have := G.isEmpty_endpointWalk_of_notMem v₀ hu; simp [step]]
  exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
    have := hr u; have := hr v₀; field_simp
end WalkExpect
section WalkRep
variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [DecidableRel G.Adj] [LocallyFinite G] (v₀ : V) (r : V → K)
section Generator
variable {n : ℕ}
/-- The generator element in `PathAlgebra K G v₀ n` acting at interior position `b` between `a` and
`c`, with entry `r (s b) * r (t b) / r (s a) ^ 2` when `s a = s c` and `t` updates `s` at `b`. -/
def pathAlgebraGenerator (a b c : Fin (n + 1)) : PathAlgebra K G v₀ n :=
  fun _ ↦ walkGenerator G r DFunLike.coe (fun _ ↦ True) a b c
theorem pathAlgebraGenerator_apply (a b c : Fin (n + 1)) (v : G.walkEndpoints v₀ n)
    (s t : G.EndpointWalk v₀ n v.val) : pathAlgebraGenerator G v₀ r a b c v s t =
      if s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
          G.Adj (s a) (t b) then r (s b) * r (t b) / r (s a) ^ 2 else 0 := by
  simp [pathAlgebraGenerator, walkGenerator_apply]
variable {G v₀ r}
/-- Left multiplication by `pathAlgebraGenerator a b c` sums over neighbours `x` of `s a`
when `s a = s c` and vanishes otherwise. -/
theorem pathAlgebraGenerator_mul_apply {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (v : G.walkEndpoints v₀ n)
    (X : Matrix (G.EndpointWalk v₀ n v.val) (G.EndpointWalk v₀ n v.val) K)
    (s u : G.EndpointWalk v₀ n v.val) : (pathAlgebraGenerator G v₀ r a b c v * X) s u =
      if hac : s a = s c then
        ∑ x ∈ (G.neighborFinset (s a)).attach, r (s b) * r x.val / r (s a) ^ 2 *
          X (s.update hab hbc hac ((G.mem_neighborFinset _ _).1 x.property)) u
      else 0 := by
  rw [pathAlgebraGenerator, walkGenerator_mul_apply DFunLike.coe DFunLike.coe_injective
    (fun _ ↦ True) (fun s _ hac x hx ↦ s.update hab hbc hac hx)
    (fun _ _ _ _ ↦ EndpointWalk.coe_update _ hab hbc _ _)]
  by_cases hac : s a = s c
  · rw [dite_eq_left ⟨trivial, hac⟩, dite_eq_left hac]
  · rw [dite_eq_right fun h ↦ hac h.2, dite_eq_right hac]
theorem pathAlgebraGenerator_update_apply {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) {v : G.walkEndpoints v₀ n} (s : G.EndpointWalk v₀ n v.val)
    (hac : s a = s c) {x : V} (hx : G.Adj (s a) x) (u : G.EndpointWalk v₀ n v.val) :
    pathAlgebraGenerator G v₀ r a b c v (s.update hab hbc hac hx) u =
      if (u : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (u b) ∧ G.Adj (s a) (u b) then
        r x * r (u b) / r (s a) ^ 2 else 0 :=
  walkGenerator_update_apply DFunLike.coe (fun _ ↦ True) hab hbc trivial hac
    (EndpointWalk.coe_update s hab hbc hac hx) u
/-- When the vertex weights `r` are self-adjoint, each block of `pathAlgebraGenerator` is
Hermitian. -/
theorem conjTranspose_pathAlgebraGenerator [StarRing K] (hrs : ∀ v, IsSelfAdjoint (r v))
    {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (v : G.walkEndpoints v₀ n) :
    (pathAlgebraGenerator G v₀ r a b c v)ᴴ = pathAlgebraGenerator G v₀ r a b c v :=
  conjTranspose_walkGenerator hrs DFunLike.coe (fun _ ↦ True) hab hbc (fun {s} _ ↦ s.isWalkFrom)
    (fun _ _ _ _ ↦ trivial)
/-- Temperley–Lieb idempotent relation `e_i ^ 2 = δ • e_i` for `pathAlgebraGenerator`. -/
theorem pathAlgebraGenerator_mul_self (hr : ∀ v, r v ≠ 0) {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
    {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) :
    pathAlgebraGenerator G v₀ r a b c * pathAlgebraGenerator G v₀ r a b c =
      δ • pathAlgebraGenerator G v₀ r a b c :=
  funext fun _ ↦ walkGenerator_mul_self hr DFunLike.coe DFunLike.coe_injective (fun _ ↦ True)
    hab hbc (fun _ ↦ hδ _) (fun s _ hac _ hx ↦ s.update hab hbc hac hx)
    (fun _ _ _ _ ↦ EndpointWalk.coe_update _ hab hbc _ _) (fun _ _ _ _ ↦ trivial)
/-- Temperley–Lieb zigzag relation `e_i * e_{i±1} * e_i = e_i` for adjacent
`pathAlgebraGenerator`s. -/
private theorem pathAlgebraGenerator_zigzag (hr : ∀ v, r v ≠ 0) {a₁ b₁ c₁ a₂ b₂ c₂ q : Fin (n + 1)}
    (hab₁ : a₁.val + 1 = b₁.val) (hbc₁ : b₁.val + 1 = c₁.val)
    (hab₂ : a₂.val + 1 = b₂.val) (hbc₂ : b₂.val + 1 = c₂.val)
    (hc : (a₂ = b₁ ∧ b₂ = c₁ ∧ c₂ = q) ∨ (c₂ = b₁ ∧ b₂ = a₁ ∧ a₂ = q)) :
    pathAlgebraGenerator G v₀ r a₁ b₁ c₁ * pathAlgebraGenerator G v₀ r a₂ b₂ c₂ *
      pathAlgebraGenerator G v₀ r a₁ b₁ c₁ = pathAlgebraGenerator G v₀ r a₁ b₁ c₁ :=
  funext fun _ ↦ walkGenerator_zigzag hr DFunLike.coe DFunLike.coe_injective (fun _ ↦ True)
    (fun {s} _ ↦ s.isWalkFrom) hab₁ hbc₁ hab₂ hbc₂ hc
    (fun hab hbc s _ hac _ hx ↦ s.update hab hbc hac hx)
    (fun {_ _ _} hab hbc {_} _ hac {_} hx ↦ EndpointWalk.coe_update _ hab hbc hac hx)
    (fun {_ _ _} _ _ {_} _ _ {_} _ ↦ trivial)
/-- Matrix entries of a product of two `pathAlgebraGenerator`s whose updated positions are
disjoint. -/
theorem pathAlgebraGenerator_mul_pathAlgebraGenerator_apply {a b c a' b' c' : Fin (n + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (h₁ : b ≠ a') (h₂ : b ≠ b')
    (h₃ : b ≠ c') (v : G.walkEndpoints v₀ n) (s u : G.EndpointWalk v₀ n v.val) :
    (pathAlgebraGenerator G v₀ r a b c * pathAlgebraGenerator G v₀ r a' b' c') v s u =
      if s a = s c ∧ s a' = s c' ∧
          (u : Fin (n + 1) → V) = update (update (s : Fin (n + 1) → V) b (u b)) b' (u b') ∧
          G.Adj (s a) (u b) ∧ G.Adj (s a') (u b') then
        r (s b) * r (u b) / r (s a) ^ 2 * (r (s b') * r (u b') / r (s a') ^ 2) else 0 := by
  simpa [pathAlgebraGenerator] using
    walkGenerator_mul_walkGenerator_apply DFunLike.coe DFunLike.coe_injective (fun _ ↦ True)
      h₁ h₂ h₃ (fun s _ hac _ hx ↦ s.update hab hbc hac hx)
      (fun _ _ _ _ ↦ EndpointWalk.coe_update _ hab hbc _ _) (fun _ _ _ _ ↦ trivial) s u
/-- Far-commutation relation `e_i * e_j = e_j * e_i` for disjoint `pathAlgebraGenerator`s. -/
theorem pathAlgebraGenerator_mul_pathAlgebraGenerator_comm {a b c a' b' c' : Fin (n + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (hab' : a'.val + 1 = b'.val)
    (hbc' : b'.val + 1 = c'.val) (h₁ : b ≠ a') (h₂ : b ≠ b') (h₃ : b ≠ c') (h₄ : b' ≠ a)
    (h₅ : b' ≠ c) : pathAlgebraGenerator G v₀ r a b c * pathAlgebraGenerator G v₀ r a' b' c' =
      pathAlgebraGenerator G v₀ r a' b' c' * pathAlgebraGenerator G v₀ r a b c :=
  funext fun _ ↦ walkGenerator_mul_walkGenerator_comm DFunLike.coe DFunLike.coe_injective
    (fun _ ↦ True) h₁ h₂ h₃ h₄ h₅
    (fun s _ hac _ hx ↦ s.update hab hbc hac hx)
    (fun _ _ _ _ ↦ EndpointWalk.coe_update _ hab hbc _ _) (fun _ _ _ _ ↦ trivial)
    (fun s _ hac _ hx ↦ s.update hab' hbc' hac hx)
    (fun _ _ _ _ ↦ EndpointWalk.coe_update _ hab' hbc' _ _) (fun _ _ _ _ ↦ trivial)
/-- `pathAlgebraExtend` shifts `pathAlgebraGenerator` indices by `Fin.castSucc`. -/
theorem pathAlgebraExtend_pathAlgebraGenerator {a b c : Fin (n + 2)} (hbc : b.val + 1 = c.val) :
    pathAlgebraExtend G v₀ (pathAlgebraGenerator G v₀ r a b c) =
      pathAlgebraGenerator G v₀ r a.castSucc b.castSucc c.castSucc := by
  have hb_last : b ≠ Fin.last (n + 1) := Fin.ne_of_val_ne (by simp; omega)
  ext v s t; conv_lhs => rw [← s.snoc_init, ← t.snoc_init]
  rw [pathAlgebraExtend_apply_snoc, pathAlgebraGenerator_apply]
  by_cases hu : s (Fin.last (n + 1)).castSucc = t (Fin.last (n + 1)).castSucc
  · rw [dite_eq_left hu, pathAlgebraGenerator_apply, t.init.coe_cast hu.symm]
    conv_rhs => rw [← s.snoc_init, ← t.snoc_init]
    simp only [EndpointWalk.coe_snoc, Fin.snoc_castSucc, ← Fin.snoc_update, Fin.snoc_inj,
      and_true, EndpointWalk.init_apply]
  · rw [dite_eq_right hu, ite_eq_right]; rintro ⟨_, hEq, _⟩
    have := congrFun hEq (Fin.last (n + 1)).castSucc
    rw [update_of_ne (Fin.castSucc_inj.not.2 hb_last.symm)] at this; exact hu this.symm
end Generator
section Representation
variable {G v₀ r} (hr : ∀ v, r v ≠ 0) {δ : K}
  (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) {n : ℕ}
variable (G v₀) in
/-- Endpoint-graded path representation `TemperleyLieb K δ n →ₐ[K] PathAlgebra K G v₀ n`. -/
def pathAlgebraRep : TemperleyLieb K δ n →ₐ[K] PathAlgebra K G v₀ n :=
  lift (fun i ↦ pathAlgebraGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩)
    (fun _ ↦ pathAlgebraGenerator_mul_self hr hδ rfl rfl)
    (fun {i j} h ↦ by
      rcases i, j, h with ⟨⟨i, _⟩, ⟨j, _⟩, rfl | rfl⟩
      · exact pathAlgebraGenerator_zigzag hr rfl rfl rfl rfl (Or.inl ⟨rfl, rfl, rfl⟩)
      · exact pathAlgebraGenerator_zigzag hr rfl rfl rfl rfl (Or.inr ⟨rfl, rfl, rfl⟩))
    (fun {_ _} h ↦ by
      refine pathAlgebraGenerator_mul_pathAlgebraGenerator_comm rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ <;>
        (simp [Fin.ext_iff]; omega))
@[simp] theorem pathAlgebraRep_e (i : Fin (n - 1)) : pathAlgebraRep G v₀ hr hδ (e δ i) =
    pathAlgebraGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ :=
  lift_e _ _ _ _ i
/-- `pathAlgebraRep` intertwines `strandIncl` with `pathAlgebraExtend`. -/
@[simp] theorem pathAlgebraRep_strandIncl {m : ℕ} (x : TemperleyLieb K δ (m + 1)) :
    pathAlgebraRep G v₀ hr hδ (strandIncl x) =
      pathAlgebraExtend G v₀ (pathAlgebraRep G v₀ hr hδ x) :=
  DFunLike.congr_fun (hom_ext (F := (pathAlgebraRep G v₀ hr hδ).comp strandIncl)
    (G := (pathAlgebraExtend G v₀).comp (pathAlgebraRep G v₀ hr hδ)) fun i ↦ by
      simp only [AlgHom.comp_apply, strandIncl_e, pathAlgebraRep_e]
      exact (pathAlgebraExtend_pathAlgebraGenerator (a := ⟨i, by omega⟩) (b := ⟨i + 1, by omega⟩)
        (c := ⟨i + 2, by omega⟩) rfl).symm) x
/-- `pathAlgebraRep` intertwines `strandInclAll n` with `pathAlgebraExtend` at every
level `n ≥ 0`. -/
@[simp] theorem pathAlgebraRep_strandInclAll (n : ℕ) (x : TemperleyLieb K δ n) :
    pathAlgebraRep G v₀ hr hδ (strandInclAll n x) =
      pathAlgebraExtend G v₀ (pathAlgebraRep G v₀ hr hδ x) := by
  cases n with
  | zero => rw [eq_algebraMap_aug_of_le_one (Nat.zero_le 1) x]; simp
  | succ _ => rw [strandInclAll_succ, pathAlgebraRep_strandIncl]
section Star
variable [StarRing K] (hrs : ∀ v, IsSelfAdjoint (r v)) [Fact (IsSelfAdjoint δ)]
include hrs in
/-- For self-adjoint weights `r`, `pathAlgebraRep` preserves the `⋆`-involution. -/
@[simp] theorem pathAlgebraRep_star (x : TemperleyLieb K δ n) :
    pathAlgebraRep G v₀ hr hδ (star x) = star (pathAlgebraRep G v₀ hr hδ x) :=
  (map_star_iff.mpr fun i ↦ by
    have := i.isLt; obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    funext v; rw [Pi.star_apply, Matrix.star_eq_conjTranspose, pathAlgebraRep_e,
      conjTranspose_pathAlgebraGenerator hrs rfl rfl v]) x
variable (G v₀) in
/-- The **endpoint-graded path `⋆`-representation** of `TemperleyLieb K δ n`. -/
def pathAlgebraStarRep : TemperleyLieb K δ n →⋆ₐ[K] PathAlgebra K G v₀ n :=
  { pathAlgebraRep G v₀ hr hδ with map_star' := pathAlgebraRep_star hr hδ hrs }
@[simp] theorem pathAlgebraStarRep_toAlgHom :
    (pathAlgebraStarRep G v₀ hr hδ hrs (n := n)).toAlgHom = pathAlgebraRep G v₀ hr hδ := (rfl)
/-- Evaluating `pathAlgebraStarRep` agrees with `pathAlgebraRep`. -/
@[simp] theorem pathAlgebraStarRep_apply (x : TemperleyLieb K δ n) :
    pathAlgebraStarRep G v₀ hr hδ hrs x = pathAlgebraRep G v₀ hr hδ x := (rfl)
end Star
end Representation
section Surjective
variable {G v₀ r} (hr : ∀ v, r v ≠ 0) {δ : K}
  (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
/-- Left multiplication by `pathAlgebraExtend (blockSingle u p₁ p₂ 1)` isolates `p₂.snoc`. -/
private theorem pathAlgebraExtend_blockSingle_mul_apply {m : ℕ} (u : G.walkEndpoints v₀ m)
    (p₁ p₂ : G.EndpointWalk v₀ m u.val) (Y : PathAlgebra K G v₀ (m + 1))
    (s : G.walkEndpoints v₀ (m + 1)) (w z : G.EndpointWalk v₀ (m + 1) s.val) :
    (pathAlgebraExtend G v₀ (PathAlgebra.blockSingle u p₁ p₂ (1 : K)) * Y) s w z =
      if h : (w.init : Fin (m + 1) → V) = p₁ ∧ G.Adj u.val s.val then
        Y s (p₂.snoc h.2) z
      else 0 := by
  rw [Pi.mul_apply, Matrix.mul_apply]; simp_rw [pathAlgebraExtend_blockSingle_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (p₂.snoc h.2) (fun _ _ hy ↦ by
        rw [ite_eq_right fun hy' ↦ hy (EndpointWalk.eq_of_coe_init_eq <| by
          simpa [EndpointWalk.coe_init] using hy'.2), zero_mul])
      (fun hm ↦ (hm (Finset.mem_univ _)).elim), ite_eq_left ⟨h.1, by ext; simp⟩, one_mul]
  · exact Finset.sum_eq_zero fun y _ ↦ by
      rw [ite_eq_right fun ⟨hw, hy⟩ ↦
        h ⟨hw, EndpointWalk.penultimate_eq_of_coe_init_eq hy ▸ y.adj_init_last⟩, zero_mul]
/-- Right multiplication by `pathAlgebraExtend (blockSingle u p₁ p₂ 1)` isolates `p₁.snoc`. -/
private theorem mul_pathAlgebraExtend_blockSingle_apply {m : ℕ} (X : PathAlgebra K G v₀ (m + 1))
    (u : G.walkEndpoints v₀ m) (p₁ p₂ : G.EndpointWalk v₀ m u.val)
    (s : G.walkEndpoints v₀ (m + 1)) (w z : G.EndpointWalk v₀ (m + 1) s.val) :
    (X * pathAlgebraExtend G v₀ (PathAlgebra.blockSingle u p₁ p₂ (1 : K))) s w z =
      if h : (z.init : Fin (m + 1) → V) = p₂ ∧ G.Adj u.val s.val then
        X s w (p₁.snoc h.2)
      else 0 := by
  rw [Pi.mul_apply, Matrix.mul_apply]; simp_rw [pathAlgebraExtend_blockSingle_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (p₁.snoc h.2) (fun _ _ hy ↦ by
        rw [ite_eq_right fun hy' ↦ hy (EndpointWalk.eq_of_coe_init_eq <| by
          simpa [EndpointWalk.coe_init] using hy'.1), mul_zero])
      (fun hm ↦ (hm (Finset.mem_univ _)).elim), ite_eq_left ⟨by ext; simp, h.1⟩, mul_one]
  · exact Finset.sum_eq_zero fun y _ ↦ by
      rw [ite_eq_right fun ⟨hy, hz⟩ ↦
        h ⟨hz, EndpointWalk.penultimate_eq_of_coe_init_eq hy ▸ y.adj_init_last⟩, mul_zero]
/-- Sandwiching the last `pathAlgebraGenerator` between extended matrix units gives a nonzero
multiple of
`blockSingle t p q 1` whenever `t` is reachable in `m` steps. -/
private theorem
    pathAlgebraExtend_blockSingle_mul_pathAlgebraGenerator_mul_pathAlgebraExtend_blockSingle
    {m : ℕ} (t : G.walkEndpoints v₀ (m + 2)) (p₀ : G.EndpointWalk v₀ m t.val)
    (p q : G.EndpointWalk v₀ (m + 2) t.val) :
    let u := p (Fin.last (m + 1)).castSucc; let u' := q (Fin.last (m + 1)).castSucc
    pathAlgebraExtend G v₀ (PathAlgebra.blockSingle ⟨u, (G.mem_walkEndpoints_iff v₀).2 ⟨p.init⟩⟩
          p.init (p₀.snoc p.adj_init_last.symm) 1) *
        pathAlgebraGenerator G v₀ r (Fin.last m).castSucc.castSucc (Fin.last (m + 1)).castSucc
          (Fin.last (m + 2)) *
        pathAlgebraExtend G v₀
          (PathAlgebra.blockSingle ⟨u', (G.mem_walkEndpoints_iff v₀).2 ⟨q.init⟩⟩
          (p₀.snoc q.adj_init_last.symm) q.init 1) =
      (r u * r u' / r t.val ^ 2) • PathAlgebra.blockSingle t p q 1 := by
  intro u u'; ext s w z
  -- Collapse both outer matrix products to the unique intermediate walks through `u` and `u'`.
  rw [mul_pathAlgebraExtend_blockSingle_apply]; simp_rw [pathAlgebraExtend_blockSingle_mul_apply]
  simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]; by_cases hst : s = t
  · subst hst; rw [PathAlgebra.blockSingle_apply_same, Matrix.single_apply]
    by_cases hwz : (w.init : Fin (m + 2) → V) = p.init ∧ (z.init : Fin (m + 2) → V) = q.init
    · obtain rfl := EndpointWalk.eq_of_coe_init_eq hwz.1
      obtain rfl := EndpointWalk.eq_of_coe_init_eq hwz.2
      rw [dite_eq_left ⟨rfl, z.adj_init_last⟩, dite_eq_left ⟨rfl, w.adj_init_last⟩,
        ite_eq_left ⟨rfl, rfl⟩, mul_one, pathAlgebraGenerator_apply, ite_eq_left
          ⟨by simp, by simp [← Fin.snoc_update, Fin.update_snoc_last],
            by simpa using z.adj_init_last.symm⟩]; simp [u, u']
    · rw [ite_eq_right fun ⟨rfl, rfl⟩ ↦ hwz ⟨rfl, rfl⟩, mul_zero]
      split_ifs with hz hw <;> first | rfl | exact (hwz ⟨hw.1, hz.1⟩).elim
  · rw [PathAlgebra.blockSingle_apply_of_ne hst, Matrix.zero_apply, mul_zero]
    -- On any block `s ≠ t`, the generator entry vanishes since vertex `m` is `t.val ≠ s.val`.
    split_ifs with hz hw
    · rw [pathAlgebraGenerator_apply, ite_eq_right fun ⟨heq, _, _⟩ ↦
        hst (Subtype.ext (by simpa [p₀.apply_last] using heq.symm))]
    all_goals rfl
private theorem blockSingle_mem_pathAlgebraRep_range_of_mem_walkEndpoints
    {m : ℕ} (ih : Function.Surjective (pathAlgebraRep G v₀ hr hδ (n := m + 1)))
    (t : G.walkEndpoints v₀ (m + 2)) (ht : t.val ∈ G.walkEndpoints v₀ m)
    (p q : G.EndpointWalk v₀ (m + 2) t.val) :
    PathAlgebra.blockSingle t p q (1 : K) ∈ (pathAlgebraRep G v₀ hr hδ (n := m + 2)).range := by
  obtain ⟨p₀⟩ := (G.mem_walkEndpoints_iff v₀).1 ht
  let u := p (Fin.last (m + 1)).castSucc; let u' := q (Fin.last (m + 1)).castSucc
  obtain ⟨a, ha⟩ := ih (PathAlgebra.blockSingle ⟨u, (G.mem_walkEndpoints_iff v₀).2 ⟨p.init⟩⟩
    p.init (p₀.snoc p.adj_init_last.symm) 1)
  obtain ⟨b, hb⟩ := ih (PathAlgebra.blockSingle ⟨u', (G.mem_walkEndpoints_iff v₀).2 ⟨q.init⟩⟩
    (p₀.snoc q.adj_init_last.symm) q.init 1)
  let R := (pathAlgebraRep G v₀ hr hδ (n := m + 2)).range
  have hprod : (r u * r u' / r t.val ^ 2) • PathAlgebra.blockSingle t p q 1 ∈ R := by
    rw [←
      pathAlgebraExtend_blockSingle_mul_pathAlgebraGenerator_mul_pathAlgebraExtend_blockSingle
        t p₀ p q]
    exact (pathAlgebraRep G v₀ hr hδ).mem_range.2
      ⟨strandIncl a * e δ (Fin.last m) * strandIncl b, by
        simp only [map_mul, pathAlgebraRep_strandIncl, ha, hb, pathAlgebraRep_e]
        exact congrArg (fun g ↦ _ * g * _) <|
          congr (congr (congrArg (pathAlgebraGenerator G v₀ r) (Fin.ext (by simp)))
            (Fin.ext (by simp))) (Fin.ext (by simp))⟩
  have hc : r u * r u' / r t.val ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (hr u) (hr u')) (pow_ne_zero 2 (hr t.val))
  convert R.smul_mem hprod (r u * r u' / r t.val ^ 2)⁻¹ using 1
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
/-- Under an injective unit-step height from `v₀` with nonzero weights, `pathAlgebraRep` is
surjective. -/
theorem pathAlgebraRep_surjective {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) :
    ∀ n : ℕ, Function.Surjective (pathAlgebraRep G v₀ hr hδ (n := n))
  | 0 => fun X ↦ ⟨algebraMap K _ (X ⟨v₀, by simp⟩ default default), by
    ext ⟨v, hv⟩ p q; obtain rfl : v = v₀ := by simpa using hv
    rw [Subsingleton.elim p default, Subsingleton.elim q default]
    simp [Algebra.algebraMap_eq_smul_one]⟩
  | 1 => fun X ↦ by
    rcases (G.walkEndpoints v₀ 1).eq_empty_or_nonempty with hne | ⟨v₁, hv₁⟩
    · exact ⟨0, by ext ⟨v, hv⟩; simp [hne] at hv⟩
    · obtain ⟨p₁⟩ := (G.mem_walkEndpoints_iff v₀).1 hv₁
      refine ⟨algebraMap K _ (X ⟨v₁, hv₁⟩ p₁ p₁), ?_⟩; ext ⟨v, hv⟩ p q
      obtain rfl : v = v₁ :=
        Finset.card_le_one.1 (G.card_walkEndpoints_one_le_one v₀ hf hf₀ hadj) v hv v₁ hv₁
      rw [Subsingleton.elim p p₁, Subsingleton.elim q p₁]; simp [Algebra.algebraMap_eq_smul_one]
  | m + 2 => fun X ↦ (pathAlgebraRep G v₀ hr hδ).mem_range.1 <| by
    have ih := pathAlgebraRep_surjective hf hf₀ hadj (m + 1)
    let R := (pathAlgebraRep G v₀ hr hδ (n := m + 2)).range
    have hmax {s : G.walkEndpoints v₀ (m + 2)} (hs : s.val ∉ G.walkEndpoints v₀ m) :
        f s.val = m + 2 := by
      obtain ⟨w⟩ := (G.mem_walkEndpoints_iff v₀).1 s.property
      exact (w.forall_apply_eq_val_or_nonempty hf hf₀ hadj).elim
        (fun h ↦ by simpa [w.apply_last] using h (Fin.last (m + 2)))
        fun h ↦ (hs ((G.mem_walkEndpoints_iff v₀).2 h)).elim
    rw [X.eq_sum_blockSingle]
    refine R.sum_mem fun t _ ↦ R.sum_mem fun p _ ↦ R.sum_mem fun q _ ↦ R.smul_mem ?_ _
    by_cases ht : t.val ∈ G.walkEndpoints v₀ m
    · exact blockSingle_mem_pathAlgebraRep_range_of_mem_walkEndpoints hr hδ ih t ht p q
    · have := EndpointWalk.subsingleton_of_last_eq hf hf₀ hadj (hmax ht)
      obtain rfl : p = q := Subsingleton.elim _ _
      have h1 : (1 : PathAlgebra K G v₀ (m + 2)) = PathAlgebra.blockSingle t p p 1 +
          ∑ s ∈ Finset.univ.erase t, ∑ w, PathAlgebra.blockSingle s w w 1 := by
        rw [PathAlgebra.one_eq_sum_blockSingle, ← Finset.add_sum_erase _ _ (Finset.mem_univ t),
          Fintype.sum_subsingleton _ p]
      rw [eq_sub_of_add_eq h1.symm]
      exact R.sub_mem R.one_mem <| R.sum_mem fun s hs ↦ R.sum_mem fun w _ ↦
        blockSingle_mem_pathAlgebraRep_range_of_mem_walkEndpoints hr hδ ih s (by_contra fun hns ↦
          Finset.ne_of_mem_erase hs <| Subtype.ext <| hf ((hmax hns).trans (hmax ht).symm)) w w
end Surjective
section WalkTraceMarkov
variable {G v₀ r}
private theorem pathAlgebraGenerator_mul_pathAlgebraExtend_snoc_diag (hr : ∀ v, r v ≠ 0) {n : ℕ}
    (X : PathAlgebra K G v₀ (n + 1)) {a' : Fin (n + 2)} (ha' : a'.val = n)
    {u v : V} (hv : v ∈ G.walkEndpoints v₀ (n + 2)) (huv : G.Adj u v)
    (p : G.EndpointWalk v₀ (n + 1) u) :
    (r v / r v₀) ^ 2 *
        (pathAlgebraGenerator G v₀ r a'.castSucc (Fin.last (n + 1)).castSucc
            (Fin.last (n + 2)) ⟨v, hv⟩ *
          pathAlgebraExtend G v₀ X ⟨v, hv⟩) (p.snoc huv) (p.snoc huv) =
      if p a' = v then (r u / r v₀) ^ 2 * PathAlgebra.blockAt u X p p else 0 := by
  let w : G.EndpointWalk v₀ (n + 2) v := p.snoc huv
  rw [pathAlgebraGenerator_mul_apply (by simp [ha']) (by simp)]
  have hwa : w a'.castSucc = p a' := by simp [w]
  have hwb : w (Fin.last (n + 1)).castSucc = u := by simp [w]
  by_cases hpv : p a' = v
  · have hac : w a'.castSucc = w (Fin.last (n + 2)) := by rw [hwa, w.apply_last, hpv]
    have humem : u ∈ G.neighborFinset (w a'.castSucc) :=
      (G.mem_neighborFinset _ _).2 (by rw [hwa, hpv]; exact huv.symm)
    rw [dite_eq_left hac, ite_eq_left hpv,
      Finset.sum_eq_single_of_mem ⟨u, humem⟩ (Finset.mem_attach _ _) fun x _ hxu ↦ by
        set w' := w.update (b := (Fin.last (n + 1)).castSucc) (by simp [ha']) (by simp) hac _
        rw [← w'.snoc_init, pathAlgebraExtend_apply_snoc, dite_eq_right
          (by simpa [w'] using fun h ↦ hxu (Subtype.ext h)), mul_zero],
      w.update_eq_self (b := (Fin.last (n + 1)).castSucc) (by simp [ha']) (by simp) hac
        ((G.mem_neighborFinset _ _).1 humem) hwb.symm, pathAlgebraExtend_apply_snoc_same,
      PathAlgebra.blockAt_of_mem ((G.mem_walkEndpoints_iff v₀).2 ⟨p⟩), hwb]
    dsimp only; rw [hwa, hpv]; have := hr v; have := hr v₀; field_simp
  · rw [dite_eq_right (by rw [hwa, w.apply_last]; exact hpv), ite_eq_right hpv, mul_zero]
/-- Markov property: multiplying `pathAlgebraExtend X` by the last generator preserves
`pathAlgebraTrace`. -/
theorem pathAlgebraTrace_pathAlgebraExtend_mul_pathAlgebraGenerator (hr : ∀ v, r v ≠ 0) {n : ℕ}
    (X : PathAlgebra K G v₀ (n + 1)) {a b c : Fin (n + 3)}
    (ha : a.val = n) (hb : b.val = n + 1) (hc : c.val = n + 2) :
    pathAlgebraTrace G v₀ r (pathAlgebraExtend G v₀ X * pathAlgebraGenerator G v₀ r a b c) =
      pathAlgebraTrace G v₀ r X := by
  obtain ⟨a', rfl, ha'⟩ : ∃ a' : Fin (n + 2), a = a'.castSucc ∧ a'.val = n :=
    ⟨⟨n, by omega⟩, Fin.ext ha, rfl⟩
  obtain ⟨rfl, rfl⟩ : b = (Fin.last (n + 1)).castSucc ∧ c = Fin.last (n + 2) :=
    ⟨Fin.ext hb, Fin.ext hc⟩
  let g (v u : V) : K := ∑ p : G.EndpointWalk v₀ (n + 1) u,
    if p a' = v then (r u / r v₀) ^ 2 * PathAlgebra.blockAt u X p p else 0
  rw [pathAlgebraTrace_mul_comm, pathAlgebraTrace_eq_sum_walkEndpoints,
    pathAlgebraTrace_eq_sum_walkEndpoints,
    Finset.sum_congr rfl fun v hv ↦ by
      rw [PathAlgebra.blockAt_of_mem hv, Pi.mul_apply, Matrix.trace,
        G.sum_endpointWalk_succ v₀ (n + 1) v, Finset.mul_sum]
      simp_rw [Finset.mul_sum, Matrix.diag_apply,
        pathAlgebraGenerator_mul_pathAlgebraExtend_snoc_diag hr X ha' hv]
      exact (G.neighborFinset v).sum_attach (g v),
    G.sum_walkEndpoints_succ v₀ (n + 1) g fun _ u hu ↦ by
      have := G.isEmpty_endpointWalk_of_notMem v₀ hu; exact Fintype.sum_empty _]
  exact Finset.sum_congr rfl fun u _ ↦ by
    rw [Finset.sum_comm, Matrix.trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.sum_eq_single_of_mem (p a') ((G.mem_neighborFinset _ _).2 <| by
        simpa [p.apply_last] using (p.adj (b := Fin.last (n + 1)) (by simp [ha'])).symm)
        fun _ _ h ↦ ite_eq_right h.symm, ite_eq_left rfl, Matrix.diag_apply]
variable (hr : ∀ v, r v ≠ 0) {δ : K} (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
variable (G v₀) in
/-- Pulling back `pathAlgebraTrace` along `pathAlgebraRep` defines a Markov trace on the
Temperley–Lieb
tower. -/
theorem isMarkovTrace_pathAlgebraTrace :
    IsMarkovTrace K δ
      (fun n ↦ (pathAlgebraTrace G v₀ r).comp (pathAlgebraRep G v₀ hr hδ (n := n)).toLinearMap) :=
  ⟨fun _ ↦ by simp [pathAlgebraTrace_one (hr v₀) hδ],
    fun _ _ _ ↦ by simp [pathAlgebraTrace_mul_comm],
    fun _ _ ↦ by simp [pathAlgebraTrace_pathAlgebraExtend hδ], fun _ _ ↦ by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, pathAlgebraRep_strandIncl,
        pathAlgebraRep_e]
      exact pathAlgebraTrace_pathAlgebraExtend_mul_pathAlgebraGenerator hr _ rfl rfl rfl⟩
variable (G v₀) in
/-- By uniqueness of the Markov trace, any Markov trace `tr` equals
`pathAlgebraTrace ∘ pathAlgebraRep`. -/
theorem IsMarkovTrace.apply_eq_pathAlgebraTrace_pathAlgebraRep
    {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
    (htr : IsMarkovTrace K δ tr) (n : ℕ) (x : TemperleyLieb K δ n) :
    tr n x = pathAlgebraTrace G v₀ r (pathAlgebraRep G v₀ hr hδ x) :=
  LinearMap.congr_fun (congrFun (htr.unique (isMarkovTrace_pathAlgebraTrace G v₀ hr hδ)) n) x
end WalkTraceMarkov
end WalkRep
end TauCeti.TemperleyLieb
