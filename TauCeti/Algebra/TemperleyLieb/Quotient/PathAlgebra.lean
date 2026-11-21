/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Algebra.TemperleyLieb.PathModel
public import TauCeti.Combinatorics.SimpleGraph.EndpointWalk
public import TauCeti.Data.Matrix.Block
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Reindex
/-! # Endpoint-graded path algebras of locally finite graphs

Restricting `TauCeti.Algebra.TemperleyLieb.PathModel` to genuine `n`-step walks from `v₀` and
decomposing by their endpoint in `G.walkEndpoints v₀ n` extends the path model to arbitrary locally
finite graphs: `PathAlgebra K G v₀ n`, one-step extension homomorphisms `walkExtend` /
`walkStarExtend` (injective when no reachable vertex is a dead end), Temperley–Lieb
(`⋆`-)representations `walkRep` / `walkStarRep` and `walkRep_surjective`, the conditional
expectation `walkExpect`, and the Markov trace `walkTrace` / `isMarkovTrace_walkTrace`.

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
  ext s w z; simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single s (fun _ _ hts ↦ by simp [blockSingle_apply_of_ne hts.symm])
    (fun hs ↦ (hs (Finset.mem_univ s)).elim)]
  simp [Matrix.single_apply, mul_ite, ite_and]
/-- The identity of `PathAlgebra K G v₀ n` is the sum of diagonal `blockSingle` matrix units. -/
theorem one_eq_sum_blockSingle : (1 : PathAlgebra K G v₀ n) =
    ∑ s : G.walkEndpoints v₀ n, ∑ w : G.EndpointWalk v₀ n s.val, blockSingle s w w 1 := by
  ext s p q; simp only [Pi.one_apply, Matrix.one_apply, Finset.sum_apply, Matrix.sum_apply]
  rw [Finset.sum_eq_single s (fun _ _ hts ↦ by simp [blockSingle_apply_of_ne hts.symm])
    (fun h ↦ (h (Finset.mem_univ _)).elim)]
  simp [Matrix.single_apply, ite_and]
end Semiring
section CommSemiring
variable [CommSemiring K] {n : ℕ}
/-- Extract the `u`-block of `PathAlgebra K G v₀ n` (`0` when `u ∉ G.walkEndpoints v₀ n`). -/
def blockAt (u : V) :
    PathAlgebra K G v₀ n →ₐ[K] Matrix (G.EndpointWalk v₀ n u) (G.EndpointWalk v₀ n u) K where
  toFun X := if hu : u ∈ G.walkEndpoints v₀ n then X ⟨u, hu⟩ else 0
  map_one' := by
    split_ifs with hu; · rfl
    have := not_nonempty_iff.1 ((G.mem_walkEndpoints_iff v₀).not.1 hu); exact Subsingleton.elim _ _
  map_mul' _ _ := by split_ifs <;> simp
  map_zero' := by split_ifs <;> rfl
  map_add' _ _ := by split_ifs <;> simp
  commutes' _ := by
    split_ifs with hu; · simp [Algebra.algebraMap_eq_smul_one]
    have := not_nonempty_iff.1 ((G.mem_walkEndpoints_iff v₀).not.1 hu); exact Subsingleton.elim _ _
@[simp] theorem blockAt_of_mem {u : V} (hu : u ∈ G.walkEndpoints v₀ n) (X : PathAlgebra K G v₀ n) :
    blockAt u X = X ⟨u, hu⟩ := dite_eq_left hu
theorem blockAt_of_notMem {u : V} (hu : u ∉ G.walkEndpoints v₀ n) (X : PathAlgebra K G v₀ n) :
    blockAt u X = 0 := dite_eq_right hu
@[simp] theorem blockAt_conjTranspose [StarRing K] (u : V) (X : PathAlgebra K G v₀ n) :
    (blockAt u X)ᴴ = blockAt u (star X) := by
  by_cases hu : u ∈ G.walkEndpoints v₀ n <;>
    simp [blockAt_of_mem, blockAt_of_notMem, hu, Matrix.star_eq_conjTranspose]
end CommSemiring
section Finrank
variable (K G v₀) [Field K]
/-- Dimension of `PathAlgebra K G v₀ n` as a sum of squared `n`-step walk counts. -/
theorem finrank (n : ℕ) : Module.finrank K (PathAlgebra K G v₀ n) =
    ∑ v ∈ G.walkEndpoints v₀ n, Fintype.card (G.EndpointWalk v₀ n v) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_matrix, Module.finrank_self, mul_one, ← sq]
  exact (G.walkEndpoints v₀ n).sum_attach fun v ↦ Fintype.card (G.EndpointWalk v₀ n v) ^ 2
/-- On a finite vertex type, `finrank` sums squared `n`-step walk counts over all vertices. -/
theorem finrank_fintype [Fintype V] (n : ℕ) : Module.finrank K (PathAlgebra K G v₀ n) =
    ∑ v : V, Fintype.card (G.EndpointWalk v₀ n v) ^ 2 := by
  rw [finrank]; exact Finset.sum_subset (Finset.subset_univ _) fun v _ hv ↦ by
    have : IsEmpty (G.EndpointWalk v₀ n v) := ⟨fun p ↦ hv ((G.mem_walkEndpoints_iff v₀).2 ⟨p⟩)⟩
    simp [Fintype.card_eq_zero]
end Finrank
end PathAlgebra
end PathAlgebra
section Extend
variable {K : Type*} [CommSemiring K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [LocallyFinite G] (v₀ : V) {n : ℕ}
/-- One-step extension homomorphism `PathAlgebra K G v₀ n →ₐ[K] PathAlgebra K G v₀ (n + 1)` acting
block-diagonally along `SimpleGraph.EndpointWalk.succEquiv`. It need not be injective in general: a
block at a reachable vertex with no neighbours maps to `0`, so injectivity requires excluding
reachable dead ends. -/
def walkExtend : PathAlgebra K G v₀ n →ₐ[K] PathAlgebra K G v₀ (n + 1) :=
  AlgHom.pi fun v ↦
    (Matrix.reindexAlgEquiv K K (EndpointWalk.succEquiv G v₀ n v.val).symm).toAlgHom.comp
      ((Matrix.blockDiagonal'AlgHom _ K K).comp
        (AlgHom.pi fun u : G.neighborSet v.val ↦ PathAlgebra.blockAt u.val))
theorem walkExtend_apply (X : PathAlgebra K G v₀ n) (v : G.walkEndpoints v₀ (n + 1)) :
    walkExtend G v₀ X v =
      (Matrix.blockDiagonal' fun u : G.neighborSet v.val ↦ PathAlgebra.blockAt u.val X).submatrix
        (EndpointWalk.succEquiv G v₀ n v.val) (EndpointWalk.succEquiv G v₀ n v.val) := by
  simp [walkExtend]; rfl
/-- Matrix entries of `walkExtend G v₀ X` on extended walks `p.snoc h₁` and `q.snoc h₂`. -/
theorem walkExtend_apply_snoc (X : PathAlgebra K G v₀ n) {u₁ u₂ v : V}
    (p : G.EndpointWalk v₀ n u₁) (q : G.EndpointWalk v₀ n u₂) (h₁ : G.Adj u₁ v) (h₂ : G.Adj u₂ v)
    (hv : v ∈ G.walkEndpoints v₀ (n + 1)) :
    walkExtend G v₀ X ⟨v, hv⟩ (p.snoc h₁) (q.snoc h₂) =
      if h : u₁ = u₂ then X ⟨u₁, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩⟩ p (q.cast h.symm)
      else 0 := by
  rw [walkExtend_apply, Matrix.submatrix_apply, EndpointWalk.succEquiv_snoc,
    EndpointWalk.succEquiv_snoc]; split_ifs with h
  · subst h; simp [Matrix.blockDiagonal'_apply_eq, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩]
  · rw [Matrix.blockDiagonal'_apply, dite_eq_right fun heq ↦ h (congrArg Subtype.val heq)]
@[simp] theorem walkExtend_apply_snoc_same (X : PathAlgebra K G v₀ n) {u v : V}
    (p q : G.EndpointWalk v₀ n u) (h : G.Adj u v) (hv : v ∈ G.walkEndpoints v₀ (n + 1)) :
    walkExtend G v₀ X ⟨v, hv⟩ (p.snoc h) (q.snoc h) =
      X ⟨u, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩⟩ p q := by
  rw [walkExtend_apply_snoc, dite_eq_left rfl, EndpointWalk.cast_rfl]
omit [DecidableEq V] [LocallyFinite G] in
variable {G v₀} in
private theorem penultimate_eq_of_coe_init_eq {u v : V} {x : G.EndpointWalk v₀ (n + 1) v}
    {p : G.EndpointWalk v₀ n u} (hx : (x.init : Fin (n + 1) → V) = p) :
    x (Fin.last n).castSucc = u := by
  simpa [EndpointWalk.coe_init, p.apply_last_eq] using congrFun hx (Fin.last n)
/-- Entries of `walkExtend` applied to a single matrix unit `blockSingle u p₁ p₂ c`. -/
theorem walkExtend_blockSingle_apply (u : G.walkEndpoints v₀ n) (p₁ p₂ : G.EndpointWalk v₀ n u.val)
    (c : K) (s : G.walkEndpoints v₀ (n + 1)) (w y : G.EndpointWalk v₀ (n + 1) s.val) :
    walkExtend G v₀ (PathAlgebra.blockSingle u p₁ p₂ c) s w y =
      if (w.init : Fin (n + 1) → V) = p₁ ∧ (y.init : Fin (n + 1) → V) = p₂ then c else 0 := by
  rcases u with ⟨u₀, hu₀⟩; conv_lhs => rw [← w.snoc_init, ← y.snoc_init]
  rw [walkExtend_apply_snoc]; by_cases hwy : w (Fin.last n).castSucc = y (Fin.last n).castSucc
  · rw [dite_eq_left hwy]; by_cases hwu : u₀ = w (Fin.last n).castSucc
    · subst hwu; rw [PathAlgebra.blockSingle_apply_same, Matrix.single_apply]
      simp only [← DFunLike.coe_injective.eq_iff, EndpointWalk.coe_cast, eq_comm]
    · rw [PathAlgebra.blockSingle_apply_of_ne (fun h ↦ hwu (congrArg Subtype.val h).symm),
        Matrix.zero_apply, ite_eq_right fun h ↦ hwu (penultimate_eq_of_coe_init_eq h.1).symm]
  · rw [dite_eq_right hwy, ite_eq_right fun h ↦
      hwy ((penultimate_eq_of_coe_init_eq h.1).trans (penultimate_eq_of_coe_init_eq h.2).symm)]
/-- The extension homomorphism `walkExtend` preserves the blockwise conjugate-transpose adjoint. -/
@[simp] theorem walkExtend_star [StarRing K] (X : PathAlgebra K G v₀ n) :
    walkExtend G v₀ (star X) = star (walkExtend G v₀ X) := funext fun _ ↦ by
  simp [walkExtend_apply, Matrix.star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose]
/-- One-step `⋆`-algebra extension homomorphism (injective without reachable dead ends). -/
def walkStarExtend [StarRing K] : PathAlgebra K G v₀ n →⋆ₐ[K] PathAlgebra K G v₀ (n + 1) :=
  { walkExtend G v₀ with map_star' := walkExtend_star G v₀ }
end Extend
section WalkTraceBasic
variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [LocallyFinite G] (v₀ : V) (r : V → K)
/-- The **endpoint-weighted matrix trace** on `PathAlgebra K G v₀ n`, summing `(r v / r v₀) ^ 2`
times the matrix trace on each endpoint block `v`. -/
def walkTrace {n : ℕ} : PathAlgebra K G v₀ n →ₗ[K] K where
  toFun X := ∑ v : G.walkEndpoints v₀ n, (r v.val / r v₀) ^ 2 * (X v).trace
  map_add' _ _ := by simp [Matrix.trace_add, mul_add, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Matrix.trace_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
variable {G v₀ r}
theorem walkTrace_apply {n : ℕ} (X : PathAlgebra K G v₀ n) :
    walkTrace G v₀ r X = ∑ v : G.walkEndpoints v₀ n, (r v.val / r v₀) ^ 2 * (X v).trace := (rfl)
theorem walkTrace_eq_sum_walkEndpoints {n : ℕ} (X : PathAlgebra K G v₀ n) : walkTrace G v₀ r X =
    ∑ v ∈ G.walkEndpoints v₀ n, (r v / r v₀) ^ 2 * (PathAlgebra.blockAt v X).trace := by
  rw [walkTrace_apply, ← (G.walkEndpoints v₀ n).sum_attach]; simp [Finset.univ_eq_attach]
/-- `walkTrace` is tracial on `PathAlgebra K G v₀ n`. -/
theorem walkTrace_mul_comm {n : ℕ} (X Y : PathAlgebra K G v₀ n) :
    walkTrace G v₀ r (X * Y) = walkTrace G v₀ r (Y * X) :=
  Finset.sum_congr rfl fun _ _ ↦ by rw [Pi.mul_apply, Pi.mul_apply, Matrix.trace_mul_comm]
/-- When `r ^ 2` is a `δ`-eigenvector of `G`'s adjacency matrix, `walkExtend` scales `walkTrace`
by `δ`. -/
theorem walkTrace_walkExtend {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) {n : ℕ}
    (X : PathAlgebra K G v₀ n) : walkTrace G v₀ r (walkExtend G v₀ X) = δ * walkTrace G v₀ r X := by
  rw [walkTrace_eq_sum_walkEndpoints, walkTrace_eq_sum_walkEndpoints, Finset.mul_sum]
  have htr {v : V} (hv : v ∈ G.walkEndpoints v₀ (n + 1)) :
      (PathAlgebra.blockAt v (walkExtend G v₀ X)).trace =
        ∑ u ∈ G.neighborFinset v, (PathAlgebra.blockAt u X).trace := by
    rw [PathAlgebra.blockAt_of_mem hv, Matrix.trace, G.sum_endpointWalk_succ v₀ n v,
      ← (G.neighborFinset v).sum_attach fun u ↦ (PathAlgebra.blockAt u X).trace]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    by_cases hu : u.val ∈ G.walkEndpoints v₀ n; · simp [hu, Matrix.trace]
    have := not_nonempty_iff.1 ((G.mem_walkEndpoints_iff v₀).not.1 hu)
    simp [PathAlgebra.blockAt_of_notMem hu]
  rw [Finset.sum_congr rfl fun _ hv ↦ by rw [htr hv, Finset.mul_sum],
    G.sum_walkEndpoints_succ v₀ n (fun v u ↦ (r v / r v₀) ^ 2 * (PathAlgebra.blockAt u X).trace)
      fun _ _ hu ↦ by rw [PathAlgebra.blockAt_of_notMem hu, Matrix.trace_zero, mul_zero]]
  exact Finset.sum_congr rfl fun u _ ↦ by
    rw [← Finset.sum_mul]; simp_rw [div_pow, div_eq_mul_inv, ← Finset.sum_mul, hδ u]; ring
/-- `walkTrace 1 = δ ^ n` when `r v₀ ≠ 0` and `r ^ 2` is a `δ`-eigenvector. -/
theorem walkTrace_one (hr₀ : r v₀ ≠ 0) {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (n : ℕ) :
    walkTrace G v₀ r (1 : PathAlgebra K G v₀ n) = δ ^ n := by
  induction n with
  | zero => simp [walkTrace_eq_sum_walkEndpoints, div_self hr₀]
  | succ n ih =>
    rw [← map_one (walkExtend G v₀ (K := K) (n := n)), walkTrace_walkExtend hδ, ih, pow_succ']
end WalkTraceBasic
section WalkExpect
variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [G.LocallyFinite] (v₀ : V) (r : V → K) (δ : K)
/-- Conditional expectation `PathAlgebra K G v₀ (n + 1) →ₗ[K] PathAlgebra K G v₀ n` closing the
final step of walks from `u` across `v ∈ G.neighborFinset u` with weight `δ⁻¹ * (r v / r u) ^ 2`. -/
def walkExpect {n : ℕ} : PathAlgebra K G v₀ (n + 1) →ₗ[K] PathAlgebra K G v₀ n where
  toFun Y u := Matrix.of fun p q ↦
    δ⁻¹ * ∑ v ∈ (G.neighborFinset u.val).attach, (r v.val / r u.val) ^ 2 *
      PathAlgebra.blockAt v.val Y (p.snoc ((G.mem_neighborFinset u.val v.val).1 v.property))
        (q.snoc ((G.mem_neighborFinset u.val v.val).1 v.property))
  map_add' _ _ := by ext u p q; simp [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' _ _ := by
    ext u p q; simp only [RingHom.id_apply, Pi.smul_apply, Matrix.smul_apply, Matrix.of_apply,
      map_smul, smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
theorem walkExpect_apply {n : ℕ} (Y : PathAlgebra K G v₀ (n + 1)) (u : G.walkEndpoints v₀ n)
    (p q : G.EndpointWalk v₀ n u.val) : walkExpect G v₀ r δ Y u p q =
      δ⁻¹ * ∑ v ∈ (G.neighborFinset u.val).attach, (r v.val / r u.val) ^ 2 *
        PathAlgebra.blockAt v.val Y (p.snoc ((G.mem_neighborFinset u.val v.val).1 v.property))
          (q.snoc ((G.mem_neighborFinset u.val v.val).1 v.property)) := (rfl)
variable {G v₀ r δ}
/-- `walkExpect` is unital when `r` is nowhere zero, `δ ≠ 0`, and `r ^ 2` is a `δ`-eigenvector. -/
@[simp] theorem walkExpect_one (hr : ∀ v, r v ≠ 0) (hδ₀ : δ ≠ 0)
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (n : ℕ) :
    walkExpect G v₀ r δ (1 : PathAlgebra K G v₀ (n + 1)) = 1 := by
  ext u p q; rw [walkExpect_apply, Pi.one_apply, Matrix.one_apply]
  have hsnoc {v : V} (h : G.Adj u.val v) : p.snoc h = q.snoc h ↔ p = q :=
    ⟨fun hpq ↦ EndpointWalk.ext fun i ↦ by simpa using congrArg (· i.castSucc) hpq, (· ▸ rfl)⟩
  simp_rw [map_one (PathAlgebra.blockAt _), Matrix.one_apply, hsnoc]; split_ifs
  · rw [Finset.sum_attach (G.neighborFinset u.val) fun v ↦ (r v / r u.val) ^ 2 * 1]
    simp_rw [mul_one, div_pow, div_eq_mul_inv, ← Finset.sum_mul, hδ u.val]
    have := hr u.val; field_simp
  · simp
/-- Left bimodule property of `walkExpect` over `walkExtend`. -/
@[simp] theorem walkExpect_walkExtend_mul {n : ℕ} (X : PathAlgebra K G v₀ n)
    (Y : PathAlgebra K G v₀ (n + 1)) :
    walkExpect G v₀ r δ (walkExtend G v₀ X * Y) = X * walkExpect G v₀ r δ Y := by
  ext u p q; rw [walkExpect_apply, Pi.mul_apply, Matrix.mul_apply]
  have hterm {v : V} (hv : G.Adj u.val v) :
      PathAlgebra.blockAt v (walkExtend G v₀ X * Y) (p.snoc hv) (q.snoc hv) =
        ∑ p' : G.EndpointWalk v₀ n u.val,
          X u p p' * PathAlgebra.blockAt v Y (p'.snoc hv) (q.snoc hv) := by
    rw [map_mul, PathAlgebra.blockAt_of_mem ((G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc hv⟩),
      Matrix.mul_apply, G.sum_endpointWalk_succ v₀ n v,
      Finset.sum_eq_single_of_mem ⟨u.val, (G.mem_neighborFinset v u.val).2 hv.symm⟩
        (Finset.mem_attach _ _) fun _ _ hu' ↦ Finset.sum_eq_zero fun _ _ ↦ by
          rw [walkExtend_apply_snoc, dite_eq_right fun h ↦ hu' (Subtype.ext h.symm), zero_mul],
      Finset.sum_congr rfl fun _ _ ↦ by rw [walkExtend_apply_snoc_same]]
  simp_rw [hterm, Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ ↦ ?_
  simp_rw [walkExpect_apply, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
/-- Right bimodule property of `walkExpect` over `walkExtend`. -/
@[simp] theorem walkExpect_mul_walkExtend {n : ℕ} (Y : PathAlgebra K G v₀ (n + 1))
    (X : PathAlgebra K G v₀ n) :
    walkExpect G v₀ r δ (Y * walkExtend G v₀ X) = walkExpect G v₀ r δ Y * X := by
  let trp {m : ℕ} (Z : PathAlgebra K G v₀ m) : PathAlgebra K G v₀ m := fun u ↦ (Z u).transpose
  have hAt {m} (Z : PathAlgebra K G v₀ m) (u : V) :
      (PathAlgebra.blockAt u Z).transpose = PathAlgebra.blockAt u (trp Z) := by
    by_cases hu : u ∈ G.walkEndpoints v₀ m <;> simp [trp, PathAlgebra.blockAt_of_notMem, hu]
  have hE : walkExtend G v₀ (trp X) = trp (walkExtend G v₀ X) := funext fun _ ↦ by
    simp [trp, walkExtend_apply, Matrix.blockDiagonal'_transpose, hAt]
  have hW {Z : PathAlgebra K G v₀ (n + 1)} :
      walkExpect G v₀ r δ (trp Z) = trp (walkExpect G v₀ r δ Z) := by
    ext; simp [trp, walkExpect_apply, ← hAt]
  have h := congrArg trp (walkExpect_walkExtend_mul (r := r) (δ := δ) (trp X) (trp Y))
  rw [hE, (funext fun _ ↦ (Matrix.transpose_mul _ _).symm :
    trp (walkExtend G v₀ X) * trp Y = trp (Y * walkExtend G v₀ X)), hW, hW] at h
  exact funext fun u ↦ by simpa [trp] using congrFun h u
/-- `walkExpect` is a left inverse to `walkExtend` under the eigenvector normalization. -/
@[simp] theorem walkExpect_walkExtend (hr : ∀ v, r v ≠ 0) (hδ₀ : δ ≠ 0)
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) {n : ℕ}
    (X : PathAlgebra K G v₀ n) : walkExpect G v₀ r δ (walkExtend G v₀ X) = X := by
  rw [← mul_one (walkExtend G v₀ X), walkExpect_walkExtend_mul, walkExpect_one hr hδ₀ hδ, mul_one]
/-- Trace compatibility of `walkExpect`: `walkTrace (walkExpect Y) = δ⁻¹ * walkTrace Y`. -/
@[simp] theorem walkTrace_walkExpect (hr : ∀ v, r v ≠ 0) {n : ℕ}
    (Y : PathAlgebra K G v₀ (n + 1)) :
    walkTrace G v₀ r (walkExpect G v₀ r δ Y) = δ⁻¹ * walkTrace G v₀ r Y := by
  classical
  let step (v u : V) : K := if h : G.Adj u v then
    ∑ p : G.EndpointWalk v₀ n u, PathAlgebra.blockAt v Y (p.snoc h) (p.snoc h) else 0
  have htrY (v : V) : (PathAlgebra.blockAt v Y).trace = ∑ u ∈ G.neighborFinset v, step v u := by
    rw [Matrix.trace, G.sum_endpointWalk_succ v₀ n v, ← (G.neighborFinset v).sum_attach (step v)]
    exact Finset.sum_congr rfl fun u _ ↦ by
      simp only [Matrix.diag_apply, step,
        dite_eq_left ((G.mem_neighborFinset v u.val).1 u.property).symm]
  have htrE {u : V} (hu : u ∈ G.walkEndpoints v₀ n) :
      (PathAlgebra.blockAt u (walkExpect G v₀ r δ Y)).trace =
        δ⁻¹ * ∑ v ∈ G.neighborFinset u, (r v / r u) ^ 2 * step v u := by
    simp only [PathAlgebra.blockAt_of_mem hu, Matrix.trace, Matrix.diag_apply, walkExpect_apply]
    rw [← Finset.mul_sum, Finset.sum_comm, ← (G.neighborFinset u).sum_attach fun v ↦ _]
    exact congrArg (δ⁻¹ * ·) (Finset.sum_congr rfl fun v _ ↦ by
      simp only [step, dite_eq_left ((G.mem_neighborFinset u v.val).1 v.property), Finset.mul_sum])
  rw [walkTrace_eq_sum_walkEndpoints, walkTrace_eq_sum_walkEndpoints, Finset.mul_sum,
    Finset.sum_congr rfl fun _ hu ↦ by rw [htrE hu, mul_left_comm, Finset.mul_sum, Finset.mul_sum],
    Finset.sum_congr (s₁ := G.walkEndpoints v₀ (n + 1)) rfl fun v _ ↦ by
      rw [htrY v, Finset.mul_sum, Finset.mul_sum],
    G.sum_walkEndpoints_succ v₀ n (fun v u ↦ δ⁻¹ * ((r v / r v₀) ^ 2 * step v u)) fun _ _ hu ↦ by
      have := not_nonempty_iff.1 ((G.mem_walkEndpoints_iff v₀).not.1 hu); simp [step]]
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
def walkGenerator (a b c : Fin (n + 1)) : PathAlgebra K G v₀ n :=
  fun v ↦ Matrix.of fun s t : G.EndpointWalk v₀ n v.val ↦
    if s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
        G.Adj (s a) (t b) then r (s b) * r (t b) / r (s a) ^ 2 else 0
theorem walkGenerator_apply (a b c : Fin (n + 1)) (v : G.walkEndpoints v₀ n)
    (s t : G.EndpointWalk v₀ n v.val) : walkGenerator G v₀ r a b c v s t =
      if s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
          G.Adj (s a) (t b) then r (s b) * r (t b) / r (s a) ^ 2 else 0 := (rfl)
variable {G v₀ r}
/-- Left multiplication by `walkGenerator a b c` sums over neighbours `x` of `s a` when `s a = s c`
and vanishes otherwise. -/
theorem walkGenerator_mul_apply {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (v : G.walkEndpoints v₀ n)
    (X : Matrix (G.EndpointWalk v₀ n v.val) (G.EndpointWalk v₀ n v.val) K)
    (s u : G.EndpointWalk v₀ n v.val) : (walkGenerator G v₀ r a b c v * X) s u =
      if hac : s a = s c then
        ∑ x ∈ (G.neighborFinset (s a)).attach, r (s b) * r x.val / r (s a) ^ 2 *
          X (s.update hab hbc hac ((G.mem_neighborFinset _ _).1 x.property)) u
      else 0 := by
  rw [Matrix.mul_apply]; split_ifs with hac
  · let f (x : {x // x ∈ G.neighborFinset (s a)}) :=
      s.update hab hbc hac ((G.mem_neighborFinset _ _).1 x.property)
    rw [← Finset.sum_subset (Finset.subset_univ ((G.neighborFinset (s a)).attach.image f)),
      Finset.sum_image fun _ _ _ _ h ↦ Subtype.ext <| by
        simpa [f] using congrArg (fun w : G.EndpointWalk v₀ n v.val ↦ w b) h]
    · exact Finset.sum_congr rfl fun x _ ↦ by
        have hx : G.Adj (s c) x.val := hac ▸ (G.mem_neighborFinset _ _).1 x.property
        simp [walkGenerator_apply, f, hac, hx]
    · intro t _ ht
      rw [walkGenerator_apply, ite_eq_right fun ⟨_, hst, hadj⟩ ↦ ht <| Finset.mem_image.2
        ⟨⟨t b, (G.mem_neighborFinset _ _).2 hadj⟩, Finset.mem_attach _ _,
          EndpointWalk.ext fun i ↦ by simpa [f] using (congrFun hst i).symm⟩, zero_mul]
  · exact Finset.sum_eq_zero fun _ _ ↦ by simp [walkGenerator_apply, hac]
theorem walkGenerator_update_apply {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) {v : G.walkEndpoints v₀ n} (s : G.EndpointWalk v₀ n v.val)
    (hac : s a = s c) {x : V} (hx : G.Adj (s a) x) (u : G.EndpointWalk v₀ n v.val) :
    walkGenerator G v₀ r a b c v (s.update hab hbc hac hx) u =
      if (u : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (u b) ∧ G.Adj (s a) (u b) then
        r x * r (u b) / r (s a) ^ 2 else 0 := by
  rw [walkGenerator_apply]; simp [update_of_ne (Fin.ne_of_val_ne (by omega) : a ≠ b),
    update_of_ne (Fin.ne_of_val_ne (by omega) : c ≠ b), hac]
/-- When the vertex weights `r` are self-adjoint, each block of `walkGenerator` is Hermitian. -/
theorem conjTranspose_walkGenerator [StarRing K] (hrs : ∀ v, IsSelfAdjoint (r v))
    {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (v : G.walkEndpoints v₀ n) :
    (walkGenerator G v₀ r a b c v)ᴴ = walkGenerator G v₀ r a b c v := by
  have ha : a ≠ b := Fin.ne_of_val_ne (by omega); have hc : c ≠ b := Fin.ne_of_val_ne (by omega)
  have hsymm {s t : G.EndpointWalk v₀ n v.val}
      (h : s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
        G.Adj (s a) (t b)) :
      t a = t c ∧ (s : Fin (n + 1) → V) = update (t : Fin (n + 1) → V) b (s b) ∧
        G.Adj (t a) (s b) := by
    have hta : t a = s a := by rw [congrFun h.2.1 a, update_of_ne ha]
    exact ⟨by rw [hta, congrFun h.2.1 c, update_of_ne hc, h.1],
      by rw [h.2.1, update_idem, update_eq_self], hta ▸ s.adj hab⟩
  ext s t; rw [Matrix.conjTranspose_apply, walkGenerator_apply, walkGenerator_apply]
  split_ifs with h₁ h₂ h₃
  · rw [congrFun h₂.2.1 a, update_of_ne ha]
    simp only [star_div₀, star_mul, star_pow, (hrs _).star_eq, mul_comm (r (s b))]
  all_goals first | exact star_zero K | exact (h₂ (hsymm h₁)).elim | exact (h₁ (hsymm h₃)).elim
/-- Temperley–Lieb idempotent relation `e_i ^ 2 = δ • e_i` for `walkGenerator`. -/
theorem walkGenerator_mul_self (hr : ∀ v, r v ≠ 0) {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
    {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) :
    walkGenerator G v₀ r a b c * walkGenerator G v₀ r a b c = δ • walkGenerator G v₀ r a b c := by
  ext v s u; rw [Pi.mul_apply, walkGenerator_mul_apply hab hbc, Pi.smul_apply, Matrix.smul_apply,
    walkGenerator_apply, smul_eq_mul]
  by_cases hac : s a = s c
  · rw [dite_eq_left hac]
    by_cases hu : (u : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (u b) ∧ G.Adj (s a) (u b)
    · rw [ite_eq_left ⟨hac, hu⟩]
      simp_rw [walkGenerator_update_apply hab hbc s hac, ite_eq_left hu]
      rw [(G.neighborFinset (s a)).sum_attach fun x ↦
          r (s b) * r x / r (s a) ^ 2 * (r x * r (u b) / r (s a) ^ 2),
        Finset.sum_congr rfl fun x _ ↦ (by ring :
          r (s b) * r x / r (s a) ^ 2 * (r x * r (u b) / r (s a) ^ 2) =
            r (s b) * r (u b) / r (s a) ^ 4 * r x ^ 2), ← Finset.mul_sum, hδ]
      have := hr (s a); field_simp
    · rw [ite_eq_right fun h ↦ hu h.2, mul_zero]
      simp [walkGenerator_update_apply hab hbc s hac, hu]
  · rw [dite_eq_right hac, ite_eq_right fun h ↦ hac h.1, mul_zero]
/-- Temperley–Lieb zigzag relation `e_i * e_{i±1} * e_i = e_i` for adjacent `walkGenerator`s. -/
private theorem walkGenerator_zigzag (hr : ∀ v, r v ≠ 0) {a₁ b₁ c₁ a₂ b₂ c₂ q : Fin (n + 1)}
    (hab₁ : a₁.val + 1 = b₁.val) (hbc₁ : b₁.val + 1 = c₁.val)
    (hab₂ : a₂.val + 1 = b₂.val) (hbc₂ : b₂.val + 1 = c₂.val)
    (hc : (a₂ = b₁ ∧ b₂ = c₁ ∧ c₂ = q) ∨ (c₂ = b₁ ∧ b₂ = a₁ ∧ a₂ = q)) :
    walkGenerator G v₀ r a₁ b₁ c₁ * walkGenerator G v₀ r a₂ b₂ c₂ *
      walkGenerator G v₀ r a₁ b₁ c₁ = walkGenerator G v₀ r a₁ b₁ c₁ := by
  have hb₁q : b₁ ≠ q := hc.elim (fun ⟨_, rfl, rfl⟩ ↦ Fin.ne_of_val_ne (by omega))
    fun ⟨_, rfl, rfl⟩ ↦ Fin.ne_of_val_ne (by omega)
  have ⟨hab₁', hcb₁, hac₁'⟩ : a₁ ≠ b₁ ∧ c₁ ≠ b₁ ∧ a₁ ≠ c₁ := by
    refine ⟨?_, ?_, ?_⟩ <;> exact Fin.ne_of_val_ne (by omega)
  ext v s u
  rw [mul_assoc, Pi.mul_apply, Pi.mul_apply, walkGenerator_mul_apply hab₁ hbc₁, walkGenerator_apply]
  by_cases hac : s a₁ = s c₁
  · -- First reduction: in the sum over `x ∈ neighborFinset (s a₁)` updating `b₁`, the middle
    -- generator requires `s₁ a₂ = s₁ c₂`, isolating the unique summand `x = s q`.
    rw [dite_eq_left hac]
    have hqadj : G.Adj (s a₁) (s q) := hc.elim (fun ⟨_, rfl, rfl⟩ ↦ hac ▸ s.adj hbc₂)
      fun ⟨_, rfl, rfl⟩ ↦ (s.adj hab₂).symm
    rw [Finset.sum_eq_single_of_mem ⟨s q, (G.mem_neighborFinset _ _).2 hqadj⟩
      (Finset.mem_attach _ _) fun x _ hxq ↦ by
        rw [walkGenerator_mul_apply hab₂ hbc₂, dite_eq_right fun hEq ↦ hxq <| Subtype.ext <| by
          rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · simpa [update_of_ne hb₁q.symm] using hEq
          · simpa [update_of_ne hb₁q.symm] using hEq.symm, mul_zero]]
    let s₁ := s.update hab₁ hbc₁ hac hqadj
    have ⟨hs₁a₂, hs₁c₂, hs₁b₂⟩ : s₁ a₂ = s q ∧ s₁ c₂ = s q ∧ s₁ b₂ = s a₁ := by
      rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        simp [s₁, update_of_ne hb₁q.symm, update_of_ne hab₁', update_of_ne hcb₁, hac]
    have hs₁ : s₁ a₂ = s₁ c₂ := hs₁a₂.trans hs₁c₂.symm
    -- Second reduction: in the sum over `y ∈ neighborFinset (s₁ a₂)` updating `b₂`, the rightmost
    -- generator requires matching vertices at `a₁` and `c₁`, isolating `y = s a₁ = s₁ b₂`.
    have hamem : s a₁ ∈ G.neighborFinset (s₁ a₂) :=
      (G.mem_neighborFinset _ _).2 (hs₁a₂ ▸ hqadj.symm)
    rw [walkGenerator_mul_apply hab₂ hbc₂, dite_eq_left hs₁,
      Finset.sum_eq_single_of_mem ⟨s a₁, hamem⟩ (Finset.mem_attach _ _) fun y _ hya ↦ by
        rw [walkGenerator_apply, ite_eq_right fun ⟨hEq, _, _⟩ ↦ hya <| Subtype.ext <| by
          rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · simpa [s₁, update_of_ne hac₁', update_of_ne hab₁'] using hEq.symm
          · simpa [s₁, update_of_ne hac₁'.symm, update_of_ne hcb₁, ← hac] using hEq, mul_zero],
      s₁.update_eq_self hab₂ hbc₂ hs₁ ((G.mem_neighborFinset _ _).1 hamem) hs₁b₂.symm,
      walkGenerator_update_apply hab₁ hbc₁ s hac hqadj]
    simp only [hac, true_and]; split_ifs
    · rw [hs₁b₂, hs₁a₂, hac]; have := hr (s c₁); have := hr (s q); field_simp
    · simp
  · rw [dite_eq_right hac, ite_eq_right fun h ↦ hac h.1]
/-- Matrix entries of a product of two `walkGenerator`s whose updated positions are disjoint. -/
theorem walkGenerator_mul_walkGenerator_apply {a b c a' b' c' : Fin (n + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (h₁ : b ≠ a') (h₂ : b ≠ b')
    (h₃ : b ≠ c') (v : G.walkEndpoints v₀ n) (s u : G.EndpointWalk v₀ n v.val) :
    (walkGenerator G v₀ r a b c * walkGenerator G v₀ r a' b' c') v s u =
      if s a = s c ∧ s a' = s c' ∧
          (u : Fin (n + 1) → V) = update (update (s : Fin (n + 1) → V) b (u b)) b' (u b') ∧
          G.Adj (s a) (u b) ∧ G.Adj (s a') (u b') then
        r (s b) * r (u b) / r (s a) ^ 2 * (r (s b') * r (u b') / r (s a') ^ 2) else 0 := by
  rw [Pi.mul_apply, walkGenerator_mul_apply hab hbc]; by_cases hac : s a = s c
  · rw [dite_eq_left hac]; by_cases hub : G.Adj (s a) (u b)
    · rw [Finset.sum_eq_single_of_mem ⟨u b, (G.mem_neighborFinset _ _).2 hub⟩
        (Finset.mem_attach _ _) fun x _ hxu ↦ by
          rw [walkGenerator_apply, ite_eq_right fun ⟨_, hEq, _⟩ ↦ hxu <| Subtype.ext <| by
            simpa [update_of_ne h₂] using (congrFun hEq b).symm, mul_zero],
        walkGenerator_apply]
      simp only [EndpointWalk.coe_update, update_of_ne h₁.symm, update_of_ne h₂.symm,
        update_of_ne h₃.symm, hac, hac ▸ hub, true_and]; split_ifs <;> simp
    · rw [ite_eq_right fun h ↦ hub h.2.2.2.1]; refine Finset.sum_eq_zero fun x _ ↦ ?_
      rw [walkGenerator_apply, ite_eq_right fun ⟨_, hEq, _⟩ ↦ hub <|
        (by simpa [update_of_ne h₂] using congrFun hEq b : u b = x.val) ▸
          (G.mem_neighborFinset _ _).1 x.property, mul_zero]
  · rw [dite_eq_right hac, ite_eq_right fun h ↦ hac h.1]
/-- Far-commutation relation `e_i * e_j = e_j * e_i` for disjoint `walkGenerator`s. -/
theorem walkGenerator_mul_walkGenerator_comm {a b c a' b' c' : Fin (n + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (hab' : a'.val + 1 = b'.val)
    (hbc' : b'.val + 1 = c'.val) (h₁ : b ≠ a') (h₂ : b ≠ b') (h₃ : b ≠ c') (h₄ : b' ≠ a)
    (h₅ : b' ≠ c) : walkGenerator G v₀ r a b c * walkGenerator G v₀ r a' b' c' =
      walkGenerator G v₀ r a' b' c' * walkGenerator G v₀ r a b c := by
  ext v s u; rw [walkGenerator_mul_walkGenerator_apply hab hbc h₁ h₂ h₃,
    walkGenerator_mul_walkGenerator_apply hab' hbc' h₄ h₂.symm h₅, update_comm h₂]
  split_ifs <;> first | ring1 | (exfalso; tauto)
/-- `walkExtend` shifts `walkGenerator` indices by `Fin.castSucc`. -/
theorem walkExtend_walkGenerator {a b c : Fin (n + 2)} (hbc : b.val + 1 = c.val) :
    walkExtend G v₀ (walkGenerator G v₀ r a b c) =
      walkGenerator G v₀ r a.castSucc b.castSucc c.castSucc := by
  have hb_last : b ≠ Fin.last (n + 1) := Fin.ne_of_val_ne (by simp; omega)
  ext v s t; conv_lhs => rw [← s.snoc_init, ← t.snoc_init]
  rw [walkExtend_apply_snoc, walkGenerator_apply]
  by_cases hu : s (Fin.last (n + 1)).castSucc = t (Fin.last (n + 1)).castSucc
  · rw [dite_eq_left hu, walkGenerator_apply, t.init.coe_cast hu.symm]
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
def walkRep : TemperleyLieb K δ n →ₐ[K] PathAlgebra K G v₀ n :=
  lift (fun i ↦ walkGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩)
    (fun _ ↦ walkGenerator_mul_self hr hδ rfl rfl)
    (fun {i j} h ↦ by
      rcases i, j, h with ⟨⟨i, _⟩, ⟨j, _⟩, rfl | rfl⟩
      · exact walkGenerator_zigzag hr rfl rfl rfl rfl (Or.inl ⟨rfl, rfl, rfl⟩)
      · exact walkGenerator_zigzag hr rfl rfl rfl rfl (Or.inr ⟨rfl, rfl, rfl⟩))
    (fun {_ _} h ↦ by
      refine walkGenerator_mul_walkGenerator_comm rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ <;>
        (simp [Fin.ext_iff]; omega))
@[simp] theorem walkRep_e (i : Fin (n - 1)) : walkRep G v₀ hr hδ (e δ i) =
    walkGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ := lift_e _ _ _ _ i
/-- `walkRep` intertwines `strandIncl` with `walkExtend`. -/
@[simp] theorem walkRep_strandIncl {m : ℕ} (x : TemperleyLieb K δ (m + 1)) :
    walkRep G v₀ hr hδ (strandIncl x) = walkExtend G v₀ (walkRep G v₀ hr hδ x) :=
  DFunLike.congr_fun (hom_ext (F := (walkRep G v₀ hr hδ).comp strandIncl)
    (G := (walkExtend G v₀).comp (walkRep G v₀ hr hδ)) fun i ↦ by
      simp only [AlgHom.comp_apply, strandIncl_e, walkRep_e]
      exact (walkExtend_walkGenerator (a := ⟨i, by omega⟩) (b := ⟨i + 1, by omega⟩)
        (c := ⟨i + 2, by omega⟩) rfl).symm) x
/-- `walkRep` intertwines `strandInclAll n` with `walkExtend` at every level `n ≥ 0`. -/
@[simp] theorem walkRep_strandInclAll (n : ℕ) (x : TemperleyLieb K δ n) :
    walkRep G v₀ hr hδ (strandInclAll n x) = walkExtend G v₀ (walkRep G v₀ hr hδ x) := by
  cases n with
  | zero => rw [eq_algebraMap_aug_zero x]; simp
  | succ _ => rw [strandInclAll_succ, walkRep_strandIncl]
section Star
variable [StarRing K] (hrs : ∀ v, IsSelfAdjoint (r v)) [Fact (IsSelfAdjoint δ)]
include hrs in
/-- For self-adjoint weights `r`, `walkRep` preserves the `⋆`-involution. -/
@[simp] theorem walkRep_star (x : TemperleyLieb K δ n) :
    walkRep G v₀ hr hδ (star x) = star (walkRep G v₀ hr hδ x) :=
  (map_star_iff.mpr fun i ↦ by
    have := i.isLt; obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    funext v; rw [Pi.star_apply, Matrix.star_eq_conjTranspose, walkRep_e,
      conjTranspose_walkGenerator hrs rfl rfl v]) x
variable (G v₀) in
/-- The **endpoint-graded path `⋆`-representation** of `TemperleyLieb K δ n`. -/
def walkStarRep : TemperleyLieb K δ n →⋆ₐ[K] PathAlgebra K G v₀ n :=
  { walkRep G v₀ hr hδ with map_star' := walkRep_star hr hδ hrs }
@[simp] theorem walkStarRep_toAlgHom :
    (walkStarRep G v₀ hr hδ hrs (n := n)).toAlgHom = walkRep G v₀ hr hδ := (rfl)
end Star
end Representation
section Surjective
variable {G v₀ r} (hr : ∀ v, r v ≠ 0) {δ : K}
  (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
/-- Left multiplication by `walkExtend (blockSingle u p₁ p₂ 1)` isolates `p₂.snoc`. -/
private theorem walkExtend_blockSingle_mul_apply {m : ℕ} (u : G.walkEndpoints v₀ m)
    (p₁ p₂ : G.EndpointWalk v₀ m u.val) (Y : PathAlgebra K G v₀ (m + 1))
    (s : G.walkEndpoints v₀ (m + 1)) (w z : G.EndpointWalk v₀ (m + 1) s.val) :
    (walkExtend G v₀ (PathAlgebra.blockSingle u p₁ p₂ (1 : K)) * Y) s w z =
      if h : (w.init : Fin (m + 1) → V) = p₁ ∧ G.Adj u.val s.val then
        Y s (p₂.snoc h.2) z
      else 0 := by
  rw [Pi.mul_apply, Matrix.mul_apply]; simp_rw [walkExtend_blockSingle_apply]; split_ifs with h
  · rw [Finset.sum_eq_single (p₂.snoc h.2) (fun _ _ hy ↦ by
        rw [ite_eq_right fun hy' ↦ hy (EndpointWalk.eq_of_coe_init_eq <| by
          simpa [EndpointWalk.coe_init] using hy'.2), zero_mul])
      (fun hm ↦ (hm (Finset.mem_univ _)).elim), ite_eq_left ⟨h.1, by ext; simp⟩, one_mul]
  · exact Finset.sum_eq_zero fun y _ ↦ by
      rw [ite_eq_right fun ⟨hw, hy⟩ ↦ h ⟨hw, penultimate_eq_of_coe_init_eq hy ▸ y.adj_init_last⟩,
        zero_mul]
/-- Right multiplication by `walkExtend (blockSingle u p₁ p₂ 1)` isolates `p₁.snoc`. -/
private theorem mul_walkExtend_blockSingle_apply {m : ℕ} (X : PathAlgebra K G v₀ (m + 1))
    (u : G.walkEndpoints v₀ m) (p₁ p₂ : G.EndpointWalk v₀ m u.val)
    (s : G.walkEndpoints v₀ (m + 1)) (w z : G.EndpointWalk v₀ (m + 1) s.val) :
    (X * walkExtend G v₀ (PathAlgebra.blockSingle u p₁ p₂ (1 : K))) s w z =
      if h : (z.init : Fin (m + 1) → V) = p₂ ∧ G.Adj u.val s.val then
        X s w (p₁.snoc h.2)
      else 0 := by
  rw [Pi.mul_apply, Matrix.mul_apply]; simp_rw [walkExtend_blockSingle_apply]; split_ifs with h
  · rw [Finset.sum_eq_single (p₁.snoc h.2) (fun _ _ hy ↦ by
        rw [ite_eq_right fun hy' ↦ hy (EndpointWalk.eq_of_coe_init_eq <| by
          simpa [EndpointWalk.coe_init] using hy'.1), mul_zero])
      (fun hm ↦ (hm (Finset.mem_univ _)).elim), ite_eq_left ⟨by ext; simp, h.1⟩, mul_one]
  · exact Finset.sum_eq_zero fun y _ ↦ by
      rw [ite_eq_right fun ⟨hy, hz⟩ ↦ h ⟨hz, penultimate_eq_of_coe_init_eq hy ▸ y.adj_init_last⟩,
        mul_zero]
/-- Sandwiching the last `walkGenerator` between extended matrix units gives a nonzero multiple of
`blockSingle t p q 1` whenever `t` is reachable in `m` steps. -/
private theorem walkExtend_blockSingle_mul_walkGenerator_mul_walkExtend_blockSingle
    {m : ℕ} (t : G.walkEndpoints v₀ (m + 2)) (p₀ : G.EndpointWalk v₀ m t.val)
    (p q : G.EndpointWalk v₀ (m + 2) t.val) :
    let u := p (Fin.last (m + 1)).castSucc; let u' := q (Fin.last (m + 1)).castSucc
    walkExtend G v₀ (PathAlgebra.blockSingle ⟨u, (G.mem_walkEndpoints_iff v₀).2 ⟨p.init⟩⟩
          p.init (p₀.snoc p.adj_init_last.symm) 1) *
        walkGenerator G v₀ r (Fin.last m).castSucc.castSucc (Fin.last (m + 1)).castSucc
          (Fin.last (m + 2)) *
        walkExtend G v₀ (PathAlgebra.blockSingle ⟨u', (G.mem_walkEndpoints_iff v₀).2 ⟨q.init⟩⟩
          (p₀.snoc q.adj_init_last.symm) q.init 1) =
      (r u * r u' / r t.val ^ 2) • PathAlgebra.blockSingle t p q 1 := by
  intro u u'; ext s w z
  -- Collapse both outer matrix products to the unique intermediate walks through `u` and `u'`.
  rw [mul_walkExtend_blockSingle_apply]; simp_rw [walkExtend_blockSingle_mul_apply]
  simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]; by_cases hst : s = t
  · subst hst; rw [PathAlgebra.blockSingle_apply_same, Matrix.single_apply]
    by_cases hwz : (w.init : Fin (m + 2) → V) = p.init ∧ (z.init : Fin (m + 2) → V) = q.init
    · obtain rfl := EndpointWalk.eq_of_coe_init_eq hwz.1
      obtain rfl := EndpointWalk.eq_of_coe_init_eq hwz.2
      rw [dite_eq_left ⟨rfl, z.adj_init_last⟩, dite_eq_left ⟨rfl, w.adj_init_last⟩,
        ite_eq_left ⟨rfl, rfl⟩, mul_one, walkGenerator_apply, ite_eq_left
          ⟨by simp, by simp [← Fin.snoc_update, Fin.update_snoc_last],
            by simpa using z.adj_init_last.symm⟩]; simp [u, u']
    · rw [ite_eq_right fun ⟨rfl, rfl⟩ ↦ hwz ⟨rfl, rfl⟩, mul_zero]
      split_ifs with hz hw <;> first | rfl | exact (hwz ⟨hw.1, hz.1⟩).elim
  · rw [PathAlgebra.blockSingle_apply_of_ne hst, Matrix.zero_apply, mul_zero]
    -- On any block `s ≠ t`, the generator entry vanishes since vertex `m` is `t.val ≠ s.val`.
    split_ifs with hz hw
    · rw [walkGenerator_apply, ite_eq_right fun ⟨heq, _, _⟩ ↦
        hst (Subtype.ext (by simpa [p₀.apply_last_eq] using heq.symm))]
    all_goals rfl
private theorem blockSingle_mem_walkRep_range_of_mem_walkEndpoints
    {m : ℕ} (ih : Function.Surjective (walkRep G v₀ hr hδ (n := m + 1)))
    (t : G.walkEndpoints v₀ (m + 2)) (ht : t.val ∈ G.walkEndpoints v₀ m)
    (p q : G.EndpointWalk v₀ (m + 2) t.val) :
    PathAlgebra.blockSingle t p q (1 : K) ∈ (walkRep G v₀ hr hδ (n := m + 2)).range := by
  obtain ⟨p₀⟩ := (G.mem_walkEndpoints_iff v₀).1 ht
  let u := p (Fin.last (m + 1)).castSucc; let u' := q (Fin.last (m + 1)).castSucc
  obtain ⟨a, ha⟩ := ih (PathAlgebra.blockSingle ⟨u, (G.mem_walkEndpoints_iff v₀).2 ⟨p.init⟩⟩
    p.init (p₀.snoc p.adj_init_last.symm) 1)
  obtain ⟨b, hb⟩ := ih (PathAlgebra.blockSingle ⟨u', (G.mem_walkEndpoints_iff v₀).2 ⟨q.init⟩⟩
    (p₀.snoc q.adj_init_last.symm) q.init 1)
  let R := (walkRep G v₀ hr hδ (n := m + 2)).range
  have hprod : (r u * r u' / r t.val ^ 2) • PathAlgebra.blockSingle t p q 1 ∈ R := by
    rw [← walkExtend_blockSingle_mul_walkGenerator_mul_walkExtend_blockSingle t p₀ p q]
    exact (walkRep G v₀ hr hδ).mem_range.2 ⟨strandIncl a * e δ (Fin.last m) * strandIncl b, by
      simp only [map_mul, walkRep_strandIncl, ha, hb, walkRep_e]; rfl⟩
  have hc : r u * r u' / r t.val ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (hr u) (hr u')) (pow_ne_zero 2 (hr t.val))
  convert R.smul_mem hprod (r u * r u' / r t.val ^ 2)⁻¹ using 1
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
/-- Under an injective unit-step height from `v₀` with nonzero weights, `walkRep` is surjective. -/
theorem walkRep_surjective {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) :
    ∀ n : ℕ, Function.Surjective (walkRep G v₀ hr hδ (n := n))
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
  | m + 2 => fun X ↦ (walkRep G v₀ hr hδ).mem_range.1 <| by
    have ih := walkRep_surjective hf hf₀ hadj (m + 1)
    let R := (walkRep G v₀ hr hδ (n := m + 2)).range
    have hmax {s : G.walkEndpoints v₀ (m + 2)} (hs : s.val ∉ G.walkEndpoints v₀ m) :
        f s.val = m + 2 := by
      obtain ⟨w⟩ := (G.mem_walkEndpoints_iff v₀).1 s.property
      exact (w.forall_eq_or_exists_endpointWalk hf hf₀ hadj).elim
        (fun h ↦ by simpa [w.apply_last_eq] using h (Fin.last (m + 2)))
        fun h ↦ (hs ((G.mem_walkEndpoints_iff v₀).2 h)).elim
    rw [X.eq_sum_blockSingle]
    refine R.sum_mem fun t _ ↦ R.sum_mem fun p _ ↦ R.sum_mem fun q _ ↦ R.smul_mem ?_ _
    by_cases ht : t.val ∈ G.walkEndpoints v₀ m
    · exact blockSingle_mem_walkRep_range_of_mem_walkEndpoints hr hδ ih t ht p q
    · have := EndpointWalk.subsingleton_of_last_eq hf hf₀ hadj (hmax ht)
      obtain rfl : p = q := Subsingleton.elim _ _
      have h1 : (1 : PathAlgebra K G v₀ (m + 2)) = PathAlgebra.blockSingle t p p 1 +
          ∑ s ∈ Finset.univ.erase t, ∑ w, PathAlgebra.blockSingle s w w 1 := by
        rw [PathAlgebra.one_eq_sum_blockSingle, ← Finset.add_sum_erase _ _ (Finset.mem_univ t),
          Fintype.sum_subsingleton _ p]
      rw [eq_sub_of_add_eq h1.symm]
      exact R.sub_mem R.one_mem <| R.sum_mem fun s hs ↦ R.sum_mem fun w _ ↦
        blockSingle_mem_walkRep_range_of_mem_walkEndpoints hr hδ ih s (by_contra fun hns ↦
          Finset.ne_of_mem_erase hs <| Subtype.ext <| hf ((hmax hns).trans (hmax ht).symm)) w w
end Surjective
section WalkTraceMarkov
variable {G v₀ r}
private theorem walkGenerator_mul_walkExtend_snoc_diag (hr : ∀ v, r v ≠ 0) {n : ℕ}
    (X : PathAlgebra K G v₀ (n + 1)) {a' : Fin (n + 2)} (ha' : a'.val = n)
    {u v : V} (hv : v ∈ G.walkEndpoints v₀ (n + 2)) (huv : G.Adj u v)
    (p : G.EndpointWalk v₀ (n + 1) u) :
    (r v / r v₀) ^ 2 *
        (walkGenerator G v₀ r a'.castSucc (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) ⟨v, hv⟩ *
          walkExtend G v₀ X ⟨v, hv⟩) (p.snoc huv) (p.snoc huv) =
      if p a' = v then (r u / r v₀) ^ 2 * PathAlgebra.blockAt u X p p else 0 := by
  let w : G.EndpointWalk v₀ (n + 2) v := p.snoc huv
  rw [walkGenerator_mul_apply (by simp [ha']) (by simp)]
  have hwa : w a'.castSucc = p a' := by simp [w]
  have hwb : w (Fin.last (n + 1)).castSucc = u := by simp [w]
  by_cases hpv : p a' = v
  · have hac : w a'.castSucc = w (Fin.last (n + 2)) := by rw [hwa, w.apply_last_eq, hpv]
    have humem : u ∈ G.neighborFinset (w a'.castSucc) :=
      (G.mem_neighborFinset _ _).2 (by rw [hwa, hpv]; exact huv.symm)
    rw [dite_eq_left hac, ite_eq_left hpv,
      Finset.sum_eq_single_of_mem ⟨u, humem⟩ (Finset.mem_attach _ _) fun x _ hxu ↦ by
        set w' := w.update (b := (Fin.last (n + 1)).castSucc) (by simp [ha']) (by simp) hac _
        rw [← w'.snoc_init, walkExtend_apply_snoc, dite_eq_right
          (by simpa [w'] using fun h ↦ hxu (Subtype.ext h)), mul_zero],
      w.update_eq_self (b := (Fin.last (n + 1)).castSucc) (by simp [ha']) (by simp) hac
        ((G.mem_neighborFinset _ _).1 humem) hwb.symm, walkExtend_apply_snoc_same,
      PathAlgebra.blockAt_of_mem ((G.mem_walkEndpoints_iff v₀).2 ⟨p⟩), hwb]
    dsimp only; rw [hwa, hpv]; have := hr v; have := hr v₀; field_simp
  · rw [dite_eq_right (by rw [hwa, w.apply_last_eq]; exact hpv), ite_eq_right hpv, mul_zero]
/-- Markov property: multiplying `walkExtend X` by the last generator preserves `walkTrace`. -/
theorem walkTrace_walkExtend_mul_walkGenerator (hr : ∀ v, r v ≠ 0) {n : ℕ}
    (X : PathAlgebra K G v₀ (n + 1)) {a b c : Fin (n + 3)}
    (ha : a.val = n) (hb : b.val = n + 1) (hc : c.val = n + 2) :
    walkTrace G v₀ r (walkExtend G v₀ X * walkGenerator G v₀ r a b c) = walkTrace G v₀ r X := by
  obtain ⟨a', rfl, ha'⟩ : ∃ a' : Fin (n + 2), a = a'.castSucc ∧ a'.val = n :=
    ⟨⟨n, by omega⟩, Fin.ext ha, rfl⟩
  obtain ⟨rfl, rfl⟩ : b = (Fin.last (n + 1)).castSucc ∧ c = Fin.last (n + 2) :=
    ⟨Fin.ext hb, Fin.ext hc⟩
  let g (v u : V) : K := ∑ p : G.EndpointWalk v₀ (n + 1) u,
    if p a' = v then (r u / r v₀) ^ 2 * PathAlgebra.blockAt u X p p else 0
  rw [walkTrace_mul_comm, walkTrace_eq_sum_walkEndpoints, walkTrace_eq_sum_walkEndpoints,
    Finset.sum_congr rfl fun v hv ↦ by
      rw [PathAlgebra.blockAt_of_mem hv, Pi.mul_apply, Matrix.trace,
        G.sum_endpointWalk_succ v₀ (n + 1) v, Finset.mul_sum]
      simp_rw [Finset.mul_sum, Matrix.diag_apply,
        walkGenerator_mul_walkExtend_snoc_diag hr X ha' hv]
      exact (G.neighborFinset v).sum_attach (g v),
    G.sum_walkEndpoints_succ v₀ (n + 1) g fun _ u hu ↦ by
      have := not_nonempty_iff.1 ((G.mem_walkEndpoints_iff v₀).not.1 hu); exact Fintype.sum_empty _]
  exact Finset.sum_congr rfl fun u _ ↦ by
    rw [Finset.sum_comm, Matrix.trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.sum_eq_single_of_mem (p a') ((G.mem_neighborFinset _ _).2 <| by
        simpa [p.apply_last_eq] using (p.adj (b := Fin.last (n + 1)) (by simp [ha'])).symm)
        fun _ _ h ↦ ite_eq_right h.symm, ite_eq_left rfl, Matrix.diag_apply]
variable (hr : ∀ v, r v ≠ 0) {δ : K} (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
variable (G v₀) in
/-- Pulling back `walkTrace` along `walkRep` defines a Markov trace on the Temperley–Lieb tower. -/
theorem isMarkovTrace_walkTrace :
    IsMarkovTrace K δ (fun n ↦ (walkTrace G v₀ r).comp (walkRep G v₀ hr hδ (n := n)).toLinearMap) :=
  ⟨fun _ ↦ by simp [walkTrace_one (hr v₀) hδ], fun _ _ _ ↦ by simp [walkTrace_mul_comm],
    fun _ _ ↦ by simp [walkTrace_walkExtend hδ], fun _ _ ↦ by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, walkRep_strandIncl,
        walkRep_e]; exact walkTrace_walkExtend_mul_walkGenerator hr _ rfl rfl rfl⟩
variable (G v₀) in
/-- By uniqueness of the Markov trace, any Markov trace `tr` equals `walkTrace ∘ walkRep`. -/
theorem IsMarkovTrace.eq_walkTrace_comp_walkRep {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
    (htr : IsMarkovTrace K δ tr) (n : ℕ) (x : TemperleyLieb K δ n) :
    tr n x = walkTrace G v₀ r (walkRep G v₀ hr hδ x) :=
  LinearMap.congr_fun (congrFun (htr.unique (isMarkovTrace_walkTrace G v₀ hr hδ)) n) x
end WalkTraceMarkov
end WalkRep
section FiniteGraph
variable {K : Type*} [Field K] {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (v₀ : V) {r : V → K} (hr : ∀ v, r v ≠ 0) {δ : K}
  (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
/-- On a finite graph, `walkRep` agrees entrywise with `pathRep` on genuine walks. -/
theorem walkRep_eq_pathRep_apply {n : ℕ} (x : TemperleyLieb K δ n)
    (v : G.walkEndpoints v₀ n) (p q : G.EndpointWalk v₀ n v.val) :
    walkRep G v₀ hr hδ x v p q = pathRep G v₀ hr (.of_forall hδ n) x p q := by
  induction x using TemperleyLieb.induction generalizing p q with
  | e _ =>
    have hp : G.IsWalkFrom v₀ ⇑p := p.isWalkFrom
    simp only [walkRep_e, pathRep_e, walkGenerator_apply, pathGenerator_apply, hp, true_and]
  | algebraMap _ =>
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply, DFunLike.coe_injective.eq_iff]
  | add _ _ hx hy => simp [hx, hy]
  | mul x _ hx hy =>
    simp only [map_mul, Pi.mul_apply, Matrix.mul_apply]
    let emb : G.EndpointWalk v₀ n v.val → (Fin (n + 1) → V) := (↑)
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb)),
      Finset.sum_image fun _ _ _ _ h ↦ DFunLike.coe_injective h]
    · exact Finset.sum_congr rfl fun _ _ ↦ by rw [hx, hy]
    · intro u _ hu
      rw [pathRep_apply_eq_zero hr (.of_forall hδ n) x (s := ⇑p) fun ⟨hp, hlast⟩ ↦ hu <|
        Finset.mem_image.2 ⟨⟨u, hp.1 p.isWalkFrom, hlast.symm.trans p.apply_last_eq⟩,
          Finset.mem_univ _, rfl⟩, zero_mul]
/-- On a finite graph, `walkTrace ∘ walkRep` coincides with `pathTrace`. -/
theorem walkTrace_walkRep_eq_pathTrace {n : ℕ} (x : TemperleyLieb K δ n) :
    walkTrace G v₀ r (walkRep G v₀ hr hδ x) = pathTrace G v₀ hr (.of_forall hδ n) x :=
  ((isMarkovTrace_pathTrace G v₀ hr hδ).eq_walkTrace_comp_walkRep G v₀ hr hδ n x).symm
end FiniteGraph
end TauCeti.TemperleyLieb
