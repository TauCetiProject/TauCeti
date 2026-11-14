/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.PathModel
public import TauCeti.Combinatorics.SimpleGraph.EndpointWalk
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Endpoint-graded path algebras of locally finite graphs

In `TauCeti.Algebra.TemperleyLieb.PathModel`, the Temperley–Lieb algebra acts on matrices indexed
by all vertex sequences `Fin (n + 1) → V` of a finite graph `G`. Because non-walk sequences are
retained and `V` must be finite, that ambient matrix algebra neither extends to infinite locally
finite graphs (such as the half-line `SimpleGraph.hasse ℕ`) nor cuts out the Markov trace radical
as its representation kernel.

Restricting to genuine `n`-step walks from `v₀` and decomposing by their endpoint in
`G.walkEndpoints v₀ n` resolves both points:

* `TauCeti.TemperleyLieb.PathAlgebra K G v₀ n` is the finite product of full matrix algebras
  `∏ v : G.walkEndpoints v₀ n, Matrix (G.EndpointWalk v₀ n v) (G.EndpointWalk v₀ n v) K`, defined
  for any locally finite graph `G`.
* `TauCeti.TemperleyLieb.walkExtend` (and `walkStarExtend`) embeds level `n` block-diagonally into
  level `n + 1` along `SimpleGraph.EndpointWalk.succEquiv`.
* `TauCeti.TemperleyLieb.walkRep` (and `walkStarRep`) restricts the path representation to
  `PathAlgebra K G v₀ n`, intertwining `strandIncl` with `walkExtend`.
* `TauCeti.TemperleyLieb.walkRep_surjective` shows that when `G` admits an injective unit-step
  `ℕ`-valued height function starting at `0` at `v₀`, `walkRep` surjects onto `PathAlgebra K G v₀ n`
  at every level `n`.
* `TauCeti.TemperleyLieb.walkTrace` is the endpoint-weighted matrix trace on `PathAlgebra K G v₀ n`,
  whose pullback along `walkRep` is an unnormalized Markov trace
  (`TauCeti.TemperleyLieb.isMarkovTrace_walkTrace`).

## Main definitions

* `TauCeti.TemperleyLieb.PathAlgebra`: endpoint-graded multimatrix path algebra on `n`-step walks
  from `v₀` in a locally finite graph `G`.
* `TauCeti.TemperleyLieb.walkExtend`, `TauCeti.TemperleyLieb.walkStarExtend`: one-step tower
  inclusion of path algebras.
* `TauCeti.TemperleyLieb.walkGenerator`: Temperley–Lieb generator in `PathAlgebra`.
* `TauCeti.TemperleyLieb.walkRep`, `TauCeti.TemperleyLieb.walkStarRep`: Temperley–Lieb
  representation (and `⋆`-representation) into `PathAlgebra`.
* `TauCeti.TemperleyLieb.walkTrace`: endpoint-weighted matrix trace on `PathAlgebra`.

## Main results

* `TauCeti.TemperleyLieb.PathAlgebra.finrank`: dimension formula `∑ v, #(EndpointWalk v₀ n v) ^ 2`.
* `TauCeti.TemperleyLieb.walkRep_strandIncl`: `walkRep` intertwines `strandIncl` with `walkExtend`.
* `TauCeti.TemperleyLieb.walkRep_surjective`: surjectivity of `walkRep` on graphs with an injective
  unit-step height function from `v₀`.
* `TauCeti.TemperleyLieb.isMarkovTrace_walkTrace`: `walkTrace ∘ walkRep` is a Markov trace.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989, Chapter 2.
* H. Wenzl, *Hecke algebras of type `A_n` and subfactors*, Invent. Math. 92 (1988), 349–383.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, §§4.4–4.5.
-/

public section

open Function Matrix SimpleGraph

namespace TauCeti.TemperleyLieb

section PathAlgebra

variable (K : Type*) {V : Type*} (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V)

/-- The **endpoint-graded path algebra** of a locally finite graph `G` from base vertex `v₀` at
level `n`: the finite product over reachable endpoints `v ∈ G.walkEndpoints v₀ n` of the full matrix
algebras indexed by `n`-step walks `G.EndpointWalk v₀ n v`. -/
abbrev PathAlgebra (n : ℕ) :=
  ∀ v : G.walkEndpoints v₀ n, Matrix (G.EndpointWalk v₀ n v.1) (G.EndpointWalk v₀ n v.1) K

namespace PathAlgebra

variable {K G v₀}

section Semiring

variable [Semiring K] {n : ℕ}

/-- A matrix entry supported on a single endpoint block `t` at `(p, q)`. -/
def blockSingle (t : G.walkEndpoints v₀ n) (p q : G.EndpointWalk v₀ n t.1) (c : K) :
    PathAlgebra K G v₀ n :=
  Pi.single t (Matrix.single p q c)

@[simp]
theorem blockSingle_apply_same (t : G.walkEndpoints v₀ n) (p q : G.EndpointWalk v₀ n t.1) (c : K) :
    blockSingle t p q c t = Matrix.single p q c :=
  Pi.single_eq_same t _

theorem blockSingle_apply_of_ne {t s : G.walkEndpoints v₀ n} (hts : s ≠ t)
    (p q : G.EndpointWalk v₀ n t.1) (c : K) :
    blockSingle t p q c s = 0 :=
  Pi.single_eq_of_ne hts _

@[simp]
theorem smul_blockSingle (c d : K) (t : G.walkEndpoints v₀ n) (p q : G.EndpointWalk v₀ n t.1) :
    c • blockSingle t p q d = blockSingle t p q (c * d) := by
  ext s w z
  by_cases hst : s = t
  · subst hst
    simp [blockSingle, Matrix.single_apply, mul_ite, mul_zero]
  · simp [blockSingle, Pi.single_eq_of_ne hst]

/-- Every element of `PathAlgebra K G v₀ n` is the sum of its `blockSingle` matrix units. -/
theorem eq_sum_blockSingle (X : PathAlgebra K G v₀ n) :
    X = ∑ t : G.walkEndpoints v₀ n,
      ∑ p : G.EndpointWalk v₀ n t.1, ∑ q : G.EndpointWalk v₀ n t.1,
        X t p q • blockSingle t p q (1 : K) := by
  ext s w z
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single s (fun t _ hts ↦ Finset.sum_eq_zero fun p _ ↦
    Finset.sum_eq_zero fun q _ ↦ by simp [blockSingle_apply_of_ne hts.symm])
    (fun hs ↦ (hs (Finset.mem_univ s)).elim)]
  simp only [blockSingle_apply_same, Matrix.single_apply, mul_ite, mul_one, mul_zero, ite_and]
  simp

/-- Extract the `u`-block of `X : PathAlgebra K G v₀ n` for an arbitrary vertex `u : V`, returning
`0` (on the empty walk type) when `u ∉ G.walkEndpoints v₀ n`. -/
def blockAt (X : PathAlgebra K G v₀ n) (u : V) :
    Matrix (G.EndpointWalk v₀ n u) (G.EndpointWalk v₀ n u) K :=
  if hu : u ∈ G.walkEndpoints v₀ n then X ⟨u, hu⟩ else 0

@[simp]
theorem blockAt_of_mem (X : PathAlgebra K G v₀ n) {u : V} (hu : u ∈ G.walkEndpoints v₀ n) :
    blockAt X u = X ⟨u, hu⟩ :=
  dite_eq_left hu

theorem blockAt_of_notMem (X : PathAlgebra K G v₀ n) {u : V} (hu : u ∉ G.walkEndpoints v₀ n) :
    blockAt X u = 0 :=
  dite_eq_right hu

@[simp]
theorem blockAt_zero (u : V) : blockAt (0 : PathAlgebra K G v₀ n) u = 0 := by
  simp [blockAt]

@[simp]
theorem blockAt_one (u : V) : blockAt (1 : PathAlgebra K G v₀ n) u = 1 := by
  by_cases hu : u ∈ G.walkEndpoints v₀ n
  · simp [hu]
  · have : IsEmpty (G.EndpointWalk v₀ n u) :=
      not_nonempty_iff.1 ((G.mem_walkEndpoints_iff v₀).not.1 hu)
    exact Subsingleton.elim _ _

@[simp]
theorem blockAt_add (X Y : PathAlgebra K G v₀ n) (u : V) :
    blockAt (X + Y) u = blockAt X u + blockAt Y u := by
  by_cases hu : u ∈ G.walkEndpoints v₀ n <;> simp [blockAt, hu]

@[simp]
theorem blockAt_mul (X Y : PathAlgebra K G v₀ n) (u : V) :
    blockAt (X * Y) u = blockAt X u * blockAt Y u := by
  by_cases hu : u ∈ G.walkEndpoints v₀ n <;> simp [blockAt, hu]

@[simp]
theorem blockAt_smul {R : Type*} [Semiring R] [Module R K] (c : R)
    (X : PathAlgebra K G v₀ n) (u : V) :
    blockAt (c • X) u = c • blockAt X u := by
  by_cases hu : u ∈ G.walkEndpoints v₀ n <;> simp [blockAt, hu]

@[simp]
theorem blockAt_conjTranspose [StarRing K] (X : PathAlgebra K G v₀ n) (u : V) :
    (blockAt X u)ᴴ = blockAt (star X) u := by
  by_cases hu : u ∈ G.walkEndpoints v₀ n
  · simp [blockAt, hu, Matrix.star_eq_conjTranspose]
  · simp [blockAt, hu]

end Semiring

section CommSemiring

variable [CommSemiring K] {n : ℕ}

/-- `PathAlgebra.blockAt` bundled as a `K`-algebra homomorphism. -/
def blockAtAlgHom (u : V) :
    PathAlgebra K G v₀ n →ₐ[K] Matrix (G.EndpointWalk v₀ n u) (G.EndpointWalk v₀ n u) K where
  toFun X := blockAt X u
  map_one' := blockAt_one u
  map_mul' X Y := blockAt_mul X Y u
  map_zero' := blockAt_zero u
  map_add' X Y := blockAt_add X Y u
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

@[simp]
theorem blockAtAlgHom_apply (u : V) (X : PathAlgebra K G v₀ n) :
    blockAtAlgHom u X = blockAt X u :=
  (rfl)

end CommSemiring

section Dimension

variable (K G v₀) [Field K]

/-- The vector-space dimension of `PathAlgebra K G v₀ n` is the sum of squares of the numbers of
`n`-step walks from `v₀` to each reachable endpoint. -/
theorem finrank (n : ℕ) :
    Module.finrank K (PathAlgebra K G v₀ n) =
      ∑ v ∈ G.walkEndpoints v₀ n, Fintype.card (G.EndpointWalk v₀ n v) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_matrix, Module.finrank_self, mul_one, ← sq]
  exact Finset.sum_attach (G.walkEndpoints v₀ n)
    (fun v ↦ Fintype.card (G.EndpointWalk v₀ n v) ^ 2)

end Dimension

end PathAlgebra

end PathAlgebra

section Extend

variable {K : Type*} [CommSemiring K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [LocallyFinite G] (v₀ : V) {n : ℕ}

private def blockDiagonal'AlgHom {o : Type*} [DecidableEq o] [Fintype o] {m' : o → Type*}
    [∀ i, DecidableEq (m' i)] [∀ i, Fintype (m' i)] :
    (∀ i, Matrix (m' i) (m' i) K) →ₐ[K] Matrix (Σ i, m' i) (Σ i, m' i) K :=
  { Matrix.blockDiagonal'RingHom m' K with
    commutes' c := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      exact (Matrix.blockDiagonal'_smul c 1).trans (congrArg (c • ·) Matrix.blockDiagonal'_one) }

/-- One-step tower inclusion `PathAlgebra K G v₀ n →ₐ[K] PathAlgebra K G v₀ (n + 1)`: on the walks
ending at `v`, an operator at level `n` acts block-diagonally according to the penultimate vertex
in `G.neighborSet v` under `SimpleGraph.EndpointWalk.succEquiv`. -/
def walkExtend : PathAlgebra K G v₀ n →ₐ[K] PathAlgebra K G v₀ (n + 1) :=
  AlgHom.pi fun v ↦
    (Matrix.reindexAlgEquiv K K (EndpointWalk.succEquiv G v₀ n v.1).symm).toAlgHom.comp
      (blockDiagonal'AlgHom.comp
        (AlgHom.pi fun u : G.neighborSet v.1 ↦ PathAlgebra.blockAtAlgHom u.1))

theorem walkExtend_apply (X : PathAlgebra K G v₀ n) (v : G.walkEndpoints v₀ (n + 1)) :
    walkExtend G v₀ X v =
      (Matrix.blockDiagonal' fun u : G.neighborSet v.1 ↦ PathAlgebra.blockAt X u.1).submatrix
        (EndpointWalk.succEquiv G v₀ n v.1) (EndpointWalk.succEquiv G v₀ n v.1) :=
  (rfl)

theorem walkExtend_apply_snoc (X : PathAlgebra K G v₀ n) {u₁ u₂ v : V}
    (p : G.EndpointWalk v₀ n u₁) (q : G.EndpointWalk v₀ n u₂)
    (h₁ : G.Adj u₁ v) (h₂ : G.Adj u₂ v)
    (hv : v ∈ G.walkEndpoints v₀ (n + 1)) :
    walkExtend G v₀ X ⟨v, hv⟩ (p.snoc h₁) (q.snoc h₂) =
      if h : u₁ = u₂ then
        X ⟨u₁, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩⟩ p (q.cast h.symm)
      else 0 := by
  rw [walkExtend_apply, Matrix.submatrix_apply, EndpointWalk.succEquiv_snoc,
    EndpointWalk.succEquiv_snoc]
  by_cases h : u₁ = u₂
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩]
  · rw [dite_eq_right h, Matrix.blockDiagonal'_apply,
      dite_eq_right (fun heq ↦ h (congrArg Subtype.val heq))]

@[simp]
theorem walkExtend_apply_snoc_same (X : PathAlgebra K G v₀ n) {u v : V}
    (p q : G.EndpointWalk v₀ n u) (h : G.Adj u v) (hv : v ∈ G.walkEndpoints v₀ (n + 1)) :
    walkExtend G v₀ X ⟨v, hv⟩ (p.snoc h) (q.snoc h) =
      X ⟨u, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩⟩ p q := by
  rw [walkExtend_apply_snoc, dite_eq_left rfl, EndpointWalk.cast_rfl]

/-- Evaluating `walkExtend` on a `blockSingle` matrix unit checks only whether the initial walks of
the row and column match the given `n`-step walks. -/
theorem walkExtend_blockSingle_apply (u : G.walkEndpoints v₀ n)
    (p₁ p₂ : G.EndpointWalk v₀ n u.1) (c : K)
    (s : G.walkEndpoints v₀ (n + 1)) (w y : G.EndpointWalk v₀ (n + 1) s.1) :
    walkExtend G v₀ (PathAlgebra.blockSingle u p₁ p₂ c) s w y =
      if (w.init : Fin (n + 1) → V) = p₁ ∧ (y.init : Fin (n + 1) → V) = p₂ then c else 0 := by
  rcases u with ⟨u₀, hu₀⟩
  have hlast_eq {x : G.EndpointWalk v₀ (n + 1) s.1} {p : G.EndpointWalk v₀ n u₀}
      (hx : (x.init : Fin (n + 1) → V) = p) : x (Fin.last n).castSucc = u₀ := by
    have := congrFun hx (Fin.last n)
    simpa [EndpointWalk.coe_init, p.apply_last_eq] using this
  conv_lhs => rw [← w.snoc_init, ← y.snoc_init]
  rw [walkExtend_apply_snoc]
  by_cases hwy : w (Fin.last n).castSucc = y (Fin.last n).castSucc
  · rw [dite_eq_left hwy]
    by_cases hwu : u₀ = w (Fin.last n).castSucc
    · subst hwu
      rw [PathAlgebra.blockSingle_apply_same, Matrix.single_apply]
      congr 1
      refine propext (and_congr ?_ ?_)
      · exact ⟨fun h ↦ congrArg DFunLike.coe h.symm, fun h ↦ DFunLike.coe_injective h.symm⟩
      · exact ⟨fun h ↦ by rw [← y.init.coe_cast hwy.symm, ← h],
          fun h ↦ DFunLike.coe_injective (by rw [y.init.coe_cast hwy.symm, ← h])⟩
    · rw [PathAlgebra.blockSingle_apply_of_ne (fun h ↦ hwu (congrArg Subtype.val h).symm),
        Matrix.zero_apply, ite_eq_right (fun h ↦ hwu (hlast_eq h.1).symm)]
  · rw [dite_eq_right hwy,
      ite_eq_right (fun h ↦ hwy ((hlast_eq h.1).trans (hlast_eq h.2).symm))]

theorem walkExtend_injective (hconn : ∀ u ∈ G.walkEndpoints v₀ n, (G.neighborFinset u).Nonempty) :
    Function.Injective (walkExtend G v₀ (K := K) (n := n)) := by
  intro X Y hXY
  ext ⟨u, hu⟩ p q
  obtain ⟨v, huv⟩ := hconn u hu
  have hadj : G.Adj u v := (G.mem_neighborFinset u v).1 huv
  have hv : v ∈ G.walkEndpoints v₀ (n + 1) := (G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc hadj⟩
  have h := congrFun (congrFun (congrFun hXY ⟨v, hv⟩) (p.snoc hadj)) (q.snoc hadj)
  simpa [walkExtend_apply_snoc_same] using h

@[simp]
theorem walkExtend_star [StarRing K] (X : PathAlgebra K G v₀ n) :
    walkExtend G v₀ (star X) = star (walkExtend G v₀ X) := by
  funext v
  have h : (fun u : G.neighborSet v.1 ↦ PathAlgebra.blockAt (star X) u.1) =
      fun u : G.neighborSet v.1 ↦ (PathAlgebra.blockAt X u.1)ᴴ :=
    funext fun u ↦ (PathAlgebra.blockAt_conjTranspose X u.1).symm
  rw [walkExtend_apply, Pi.star_apply, Matrix.star_eq_conjTranspose, walkExtend_apply,
    Matrix.conjTranspose_submatrix, Matrix.blockDiagonal'_conjTranspose, h]

/-- One-step `⋆`-algebra inclusion of path algebras. -/
def walkStarExtend [StarRing K] : PathAlgebra K G v₀ n →⋆ₐ[K] PathAlgebra K G v₀ (n + 1) :=
  { walkExtend G v₀ with map_star' := walkExtend_star G v₀ }

@[simp]
theorem walkStarExtend_toAlgHom [StarRing K] :
    (walkStarExtend G v₀ (K := K) (n := n)).toAlgHom = walkExtend G v₀ :=
  (rfl)

end Extend

section WalkTraceBasic

variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [LocallyFinite G] (v₀ : V) (r : V → K)

/-- The **endpoint-weighted matrix trace** on `PathAlgebra K G v₀ n`, summing `(r v / r v₀) ^ 2`
times the ordinary matrix trace on each endpoint block `v`. -/
def walkTrace {n : ℕ} : PathAlgebra K G v₀ n →ₗ[K] K where
  toFun X := ∑ v : G.walkEndpoints v₀ n, (r v.1 / r v₀) ^ 2 * (X v).trace
  map_add' X Y := by simp [Matrix.trace_add, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by simp [Matrix.trace_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]

variable {G v₀ r}

theorem walkTrace_apply {n : ℕ} (X : PathAlgebra K G v₀ n) :
    walkTrace G v₀ r X = ∑ v : G.walkEndpoints v₀ n, (r v.1 / r v₀) ^ 2 * (X v).trace :=
  (rfl)

/-- `walkTrace` is tracial on all of `PathAlgebra K G v₀ n`. -/
theorem walkTrace_mul_comm {n : ℕ} (X Y : PathAlgebra K G v₀ n) :
    walkTrace G v₀ r (X * Y) = walkTrace G v₀ r (Y * X) := by
  rw [walkTrace_apply, walkTrace_apply]
  exact Finset.sum_congr rfl fun v _ ↦ by rw [Pi.mul_apply, Pi.mul_apply, Matrix.trace_mul_comm]

/-- Extending an element of `PathAlgebra` by one step multiplies `walkTrace` by `δ`. -/
theorem walkTrace_walkExtend {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) {n : ℕ}
    (X : PathAlgebra K G v₀ n) :
    walkTrace G v₀ r (walkExtend G v₀ X) = δ * walkTrace G v₀ r X := by
  rw [walkTrace_apply, walkTrace_apply, Finset.mul_sum]
  have htr (v : G.walkEndpoints v₀ (n + 1)) :
      (walkExtend G v₀ X v).trace =
        ∑ u ∈ G.neighborFinset v.1 ∩ G.walkEndpoints v₀ n,
          (PathAlgebra.blockAt X u).trace := by
    have hsub : (walkExtend G v₀ X v).trace =
        (Matrix.blockDiagonal' fun u : G.neighborSet v.1 ↦ PathAlgebra.blockAt X u.1).trace := by
      rw [walkExtend_apply, Matrix.trace, Matrix.trace]
      exact (EndpointWalk.succEquiv G v₀ n v.1).sum_comp
        (fun i ↦ (Matrix.blockDiagonal' fun u : G.neighborSet v.1 ↦
          PathAlgebra.blockAt X u.1).diag i)
    rw [hsub, Matrix.trace_blockDiagonal']
    have hbij : ∑ u : G.neighborSet v.1, (PathAlgebra.blockAt X u.1).trace =
        ∑ u ∈ G.neighborFinset v.1, (PathAlgebra.blockAt X u).trace :=
      Finset.sum_bij (fun u _ ↦ u.1) (fun u _ ↦ (G.mem_neighborFinset v.1 u.1).2 u.2)
        (fun _ _ _ _ h ↦ Subtype.ext h)
        (fun u hu ↦ ⟨⟨u, (G.mem_neighborFinset v.1 u).1 hu⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ ↦ rfl)
    rw [hbij]
    exact (Finset.sum_subset Finset.inter_subset_left fun u _ hnu ↦ by
      have hu : u ∉ G.walkEndpoints v₀ n := fun h ↦ hnu (Finset.mem_inter.2 ⟨‹_›, h⟩)
      rw [PathAlgebra.blockAt_of_notMem X hu, Matrix.trace_zero]).symm
  simp_rw [htr, Finset.mul_sum]
  rw [Finset.univ_eq_attach, Finset.sum_attach (G.walkEndpoints v₀ (n + 1))
    (fun v ↦ ∑ u ∈ G.neighborFinset v ∩ G.walkEndpoints v₀ n,
      (r v / r v₀) ^ 2 * (PathAlgebra.blockAt X u).trace),
    Finset.sum_sigma' (G.walkEndpoints v₀ (n + 1))
      (fun v ↦ G.neighborFinset v ∩ G.walkEndpoints v₀ n)
      (fun v u ↦ (r v / r v₀) ^ 2 * (PathAlgebra.blockAt X u).trace)]
  have hswap :
      ∑ p ∈ (G.walkEndpoints v₀ (n + 1)).sigma (fun v ↦ G.neighborFinset v ∩ G.walkEndpoints v₀ n),
          (r p.1 / r v₀) ^ 2 * (PathAlgebra.blockAt X p.2).trace =
        ∑ q ∈ (G.walkEndpoints v₀ n).sigma (fun u ↦ G.neighborFinset u),
          (r q.2 / r v₀) ^ 2 * (PathAlgebra.blockAt X q.1).trace :=
    Finset.sum_bij (fun p _ ↦ ⟨p.2, p.1⟩)
      (fun p hp ↦ by
        rcases Finset.mem_sigma.1 hp with ⟨_, hp₂⟩
        rcases Finset.mem_inter.1 hp₂ with ⟨hadj, hu⟩
        exact Finset.mem_sigma.2 ⟨hu,
          (G.mem_neighborFinset _ _).2 ((G.mem_neighborFinset _ _).1 hadj).symm⟩)
      (fun p₁ _ p₂ _ h ↦ by cases p₁; cases p₂; cases h; rfl)
      (fun q hq ↦ by
        rcases Finset.mem_sigma.1 hq with ⟨hu, hadj⟩
        have hv : q.2 ∈ G.walkEndpoints v₀ (n + 1) := by
          rw [walkEndpoints_succ]
          exact Finset.mem_biUnion.2 ⟨q.1, hu, hadj⟩
        refine ⟨⟨q.2, q.1⟩, Finset.mem_sigma.2 ⟨hv, Finset.mem_inter.2 ⟨?_, hu⟩⟩, rfl⟩
        exact (G.mem_neighborFinset _ _).2 ((G.mem_neighborFinset _ _).1 hadj).symm)
      (fun _ _ ↦ rfl)
  rw [hswap, ← Finset.sum_sigma' (G.walkEndpoints v₀ n) (fun u ↦ G.neighborFinset u)
      (fun u v ↦ (r v / r v₀) ^ 2 * (PathAlgebra.blockAt X u).trace),
    Finset.univ_eq_attach]
  conv_rhs =>
    rw [← Finset.sum_congr rfl (fun u _ ↦ by rw [← PathAlgebra.blockAt_of_mem X u.2]),
      Finset.sum_attach (G.walkEndpoints v₀ n)
        (fun u ↦ δ * ((r u / r v₀) ^ 2 * (PathAlgebra.blockAt X u).trace))]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ v ∈ G.neighborFinset u, (r v / r v₀) ^ 2 = δ * (r u / r v₀) ^ 2 := by
    simp_rw [div_pow, div_eq_mul_inv]
    rw [← Finset.sum_mul, hδ u, mul_assoc]
  rw [hsum, mul_assoc]

@[simp]
theorem walkTrace_one (hr : ∀ v, r v ≠ 0) {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (n : ℕ) :
    walkTrace G v₀ r (1 : PathAlgebra K G v₀ n) = δ ^ n := by
  induction n with
  | zero =>
    rw [walkTrace_apply, pow_zero]
    let t₀ : G.walkEndpoints v₀ 0 := ⟨v₀, by simp⟩
    rw [Finset.sum_eq_single t₀
      (fun t _ ht ↦ False.elim (ht (Subtype.ext (by simpa [t₀] using t.2))))
      (fun h ↦ (h (Finset.mem_univ _)).elim)]
    simp [t₀, div_self (hr v₀)]
  | succ n ih =>
    rw [← map_one (walkExtend G v₀ (K := K) (n := n)), walkTrace_walkExtend hδ, ih,
      pow_succ, mul_comm]

end WalkTraceBasic

section WalkRep

variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [DecidableRel G.Adj] [LocallyFinite G] (v₀ : V) (r : V → K)

section Generator

variable {n : ℕ}

/-- The generator element in `PathAlgebra K G v₀ n` acting at interior position `b` between `a` and
`c`: on walks `s, t` with `s a = s c` that agree outside `b` and satisfy `G.Adj (s a) (t b)`, its
entry is `r (s b) * r (t b) / r (s a) ^ 2`, and `0` otherwise. -/
def walkGenerator (a b c : Fin (n + 1)) : PathAlgebra K G v₀ n :=
  fun v ↦ Matrix.of fun s t : G.EndpointWalk v₀ n v.1 ↦
    if s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
        G.Adj (s a) (t b) then
      r (s b) * r (t b) / r (s a) ^ 2
    else 0

theorem walkGenerator_apply (a b c : Fin (n + 1)) (v : G.walkEndpoints v₀ n)
    (s t : G.EndpointWalk v₀ n v.1) :
    walkGenerator G v₀ r a b c v s t =
      if s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
          G.Adj (s a) (t b) then
        r (s b) * r (t b) / r (s a) ^ 2
      else 0 :=
  (rfl)

variable {G v₀ r}

/-- Left multiplication by `walkGenerator` sums over the neighbours of `s a` via
`EndpointWalk.update`. -/
theorem walkGenerator_mul_apply {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (v : G.walkEndpoints v₀ n)
    (X : Matrix (G.EndpointWalk v₀ n v.1) (G.EndpointWalk v₀ n v.1) K)
    (s u : G.EndpointWalk v₀ n v.1) :
    (walkGenerator G v₀ r a b c v * X) s u =
      if hac : s a = s c then
        ∑ x ∈ (G.neighborFinset (s a)).attach,
          r (s b) * r x.1 / r (s a) ^ 2 *
            X (s.update hab hbc hac ((G.mem_neighborFinset _ _).1 x.2)) u
      else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with hac
  · let f : {x // x ∈ G.neighborFinset (s a)} → G.EndpointWalk v₀ n v.1 :=
      fun x ↦ s.update hab hbc hac ((G.mem_neighborFinset _ _).1 x.2)
    have hf : Function.Injective f := fun x₁ x₂ h ↦ Subtype.ext <| by
      have hb := congrArg (fun w : G.EndpointWalk v₀ n v.1 ↦ w b) h
      simpa [f, EndpointWalk.coe_update] using hb
    rw [← Finset.sum_subset (Finset.subset_univ ((G.neighborFinset (s a)).attach.image f)),
      Finset.sum_image (fun _ _ _ _ h ↦ hf h)]
    · refine Finset.sum_congr rfl fun x _ ↦ ?_
      have hcond : s a = s c ∧
          (f x : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (f x b) ∧
          G.Adj (s a) (f x b) := by
        refine ⟨hac, ?_, ?_⟩
        · simp [f, EndpointWalk.coe_update]
        · simpa [f, EndpointWalk.coe_update] using (G.mem_neighborFinset _ _).1 x.2
      rw [walkGenerator_apply, ite_eq_left hcond]
      simp [f, EndpointWalk.coe_update]
    · intro t _ ht
      have hnot : ¬(s a = s c ∧
          (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
          G.Adj (s a) (t b)) := by
        rintro ⟨_, hst, hadj⟩
        refine ht (Finset.mem_image.2 ⟨⟨t b, (G.mem_neighborFinset _ _).2 hadj⟩,
          Finset.mem_attach _ _, ?_⟩)
        ext i
        simpa [f, EndpointWalk.coe_update] using (congrFun hst i).symm
      rw [walkGenerator_apply, ite_eq_right hnot, zero_mul]
  · refine Finset.sum_eq_zero fun t _ ↦ ?_
    rw [walkGenerator_apply, ite_eq_right_iff.2 fun h ↦ (hac h.1).elim, zero_mul]

theorem walkGenerator_update_apply {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) {v : G.walkEndpoints v₀ n}
    (s : G.EndpointWalk v₀ n v.1) (hac : s a = s c) {x : V} (hx : G.Adj (s a) x)
    (u : G.EndpointWalk v₀ n v.1) :
    walkGenerator G v₀ r a b c v (s.update hab hbc hac hx) u =
      if (u : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (u b) ∧
          G.Adj (s a) (u b) then
        r x * r (u b) / r (s a) ^ 2
      else 0 := by
  have ha : a ≠ b := Fin.ne_of_val_ne (by omega)
  have hc : c ≠ b := Fin.ne_of_val_ne (by omega)
  rw [walkGenerator_apply]
  simp [EndpointWalk.coe_update, update_of_ne ha, update_of_ne hc, hac]

theorem conjTranspose_walkGenerator [StarRing K] (hrs : ∀ v, IsSelfAdjoint (r v))
    {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (v : G.walkEndpoints v₀ n) :
    (walkGenerator G v₀ r a b c v)ᴴ = walkGenerator G v₀ r a b c v := by
  have ha : a ≠ b := Fin.ne_of_val_ne (by omega)
  have hc : c ≠ b := Fin.ne_of_val_ne (by omega)
  ext s t
  rw [Matrix.conjTranspose_apply, walkGenerator_apply, walkGenerator_apply]
  have hiff : (t a = t c ∧ (s : Fin (n + 1) → V) = update (t : Fin (n + 1) → V) b (s b) ∧
      G.Adj (t a) (s b)) ↔
      (s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
        G.Adj (s a) (t b)) := by
    constructor <;> rintro ⟨h₁, h₂, _⟩
    · have hsa : s a = t a := by rw [congrFun h₂ a, update_of_ne ha]
      have hsc : s c = t c := by rw [congrFun h₂ c, update_of_ne hc]
      refine ⟨by rw [hsa, hsc, h₁], ?_, hsa ▸ t.adj hab⟩
      ext i
      rw [h₂, update_idem, update_eq_self]
    · have hta : t a = s a := by rw [congrFun h₂ a, update_of_ne ha]
      have htc : t c = s c := by rw [congrFun h₂ c, update_of_ne hc]
      refine ⟨by rw [hta, htc, h₁], ?_, hta ▸ s.adj hab⟩
      ext i
      rw [h₂, update_idem, update_eq_self]
  by_cases h : s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
      G.Adj (s a) (t b)
  · have ht := hiff.mpr h
    have hta : t a = s a := by rw [congrFun h.2.1 a, update_of_ne ha]
    rw [ite_eq_left ht, ite_eq_left h, hta]
    simp only [star_div₀, star_mul, star_pow, (hrs _).star_eq, mul_comm (r (s b))]
  · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h, star_zero]

variable (hr : ∀ v, r v ≠ 0) {δ : K}

include hr in
theorem walkGenerator_mul_self (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
    {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) :
    walkGenerator G v₀ r a b c * walkGenerator G v₀ r a b c =
      δ • walkGenerator G v₀ r a b c := by
  ext v s u
  rw [Pi.mul_apply, walkGenerator_mul_apply hab hbc, Pi.smul_apply, Matrix.smul_apply,
    walkGenerator_apply, smul_eq_mul]
  by_cases hac : s a = s c
  · rw [dite_eq_left hac]
    by_cases hu : (u : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (u b) ∧ G.Adj (s a) (u b)
    · rw [ite_eq_left ⟨hac, hu.1, hu.2⟩]
      have hterm : ∀ x : {x // x ∈ G.neighborFinset (s a)},
          r (s b) * r x.1 / r (s a) ^ 2 *
            walkGenerator G v₀ r a b c v
              (s.update hab hbc hac ((G.mem_neighborFinset _ _).1 x.2)) u =
          r (s b) * r x.1 / r (s a) ^ 2 * (r x.1 * r (u b) / r (s a) ^ 2) := fun x ↦ by
        rw [walkGenerator_update_apply hab hbc s hac ((G.mem_neighborFinset _ _).1 x.2),
          ite_eq_left hu]
      simp_rw [hterm]
      rw [Finset.sum_attach (G.neighborFinset (s a))
        (fun x ↦ r (s b) * r x / r (s a) ^ 2 * (r x * r (u b) / r (s a) ^ 2))]
      have hsa := hr (s a)
      calc ∑ x ∈ G.neighborFinset (s a),
            r (s b) * r x / r (s a) ^ 2 * (r x * r (u b) / r (s a) ^ 2)
          = r (s b) * r (u b) / r (s a) ^ 4 * ∑ x ∈ G.neighborFinset (s a), r x ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ ↦ ?_
            field_simp
        _ = _ := by
            rw [hδ]
            field_simp
    · rw [ite_eq_right fun h ↦ hu h.2, mul_zero]
      refine Finset.sum_eq_zero fun x _ ↦ ?_
      rw [walkGenerator_update_apply hab hbc s hac ((G.mem_neighborFinset _ _).1 x.2),
        ite_eq_right hu, mul_zero]
  · rw [dite_eq_right hac, ite_eq_right fun h ↦ hac h.1, mul_zero]

include hr in
theorem walkGenerator_zigzag_left {a b c d : Fin (n + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (hcd : c.val + 1 = d.val) :
    walkGenerator G v₀ r a b c * walkGenerator G v₀ r b c d * walkGenerator G v₀ r a b c =
      walkGenerator G v₀ r a b c := by
  have hab' : a ≠ b := Fin.ne_of_val_ne (by omega)
  have hac' : a ≠ c := Fin.ne_of_val_ne (by omega)
  have hbd : b ≠ d := Fin.ne_of_val_ne (by omega)
  have hcb : c ≠ b := Fin.ne_of_val_ne (by omega)
  ext v s u
  rw [mul_assoc, Pi.mul_apply, Pi.mul_apply, walkGenerator_mul_apply hab hbc, walkGenerator_apply]
  by_cases hac : s a = s c
  · rw [dite_eq_left hac]
    have hdmem : s d ∈ G.neighborFinset (s a) := by
      rw [SimpleGraph.mem_neighborFinset, hac]; exact s.adj hcd
    rw [Finset.sum_eq_single_of_mem ⟨s d, hdmem⟩ (Finset.mem_attach _ _) fun x _ hxd ↦ by
      rw [walkGenerator_mul_apply hbc hcd, dite_eq_right ?_, mul_zero]
      intro hEq
      apply hxd
      ext
      simpa [EndpointWalk.coe_update, update_of_ne hbd.symm] using hEq]
    let s₁ := s.update hab hbc hac ((G.mem_neighborFinset _ _).1 hdmem)
    have hs₁bd : s₁ b = s₁ d := by
      simp [s₁, EndpointWalk.coe_update, update_of_ne hbd.symm]
    have hamem : s a ∈ G.neighborFinset (s₁ b) := by
      rw [SimpleGraph.mem_neighborFinset]
      simpa [s₁, EndpointWalk.coe_update, hac] using (s.adj hcd).symm
    rw [walkGenerator_mul_apply hbc hcd, dite_eq_left hs₁bd,
      Finset.sum_eq_single_of_mem ⟨s a, hamem⟩ (Finset.mem_attach _ _) fun y _ hya ↦ by
        rw [walkGenerator_apply, ite_eq_right ?_, mul_zero]
        rintro ⟨hEq, _, _⟩
        apply hya
        ext
        simpa [s₁, EndpointWalk.coe_update, update_of_ne hac', update_of_ne hab'] using hEq.symm]
    have hs₂ : s₁.update hbc hcd hs₁bd ((G.mem_neighborFinset _ _).1 hamem) = s₁ := by
      ext i
      simp only [EndpointWalk.coe_update, s₁]
      rw [hac, update_comm hcb.symm, update_eq_self]
    rw [hs₂, walkGenerator_update_apply hab hbc s hac ((G.mem_neighborFinset _ _).1 hdmem)]
    simp only [hac, true_and]
    split_ifs
    · have hs₁b : s₁ b = s d := by simp [s₁, EndpointWalk.coe_update]
      have hs₁c : s₁ c = s a := by simp [s₁, EndpointWalk.coe_update, update_of_ne hcb, hac]
      rw [hs₁b, hs₁c, ← hac]
      have := hr (s a)
      have := hr (s d)
      field_simp
    · simp
  · rw [dite_eq_right hac, ite_eq_right fun h ↦ hac h.1]

include hr in
theorem walkGenerator_zigzag_right {a b c d : Fin (n + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (hcd : c.val + 1 = d.val) :
    walkGenerator G v₀ r b c d * walkGenerator G v₀ r a b c * walkGenerator G v₀ r b c d =
      walkGenerator G v₀ r b c d := by
  have hac' : a ≠ c := Fin.ne_of_val_ne (by omega)
  have hbc' : b ≠ c := Fin.ne_of_val_ne (by omega)
  have hdc : d ≠ c := Fin.ne_of_val_ne (by omega)
  have hdb : d ≠ b := Fin.ne_of_val_ne (by omega)
  ext v s u
  rw [mul_assoc, Pi.mul_apply, Pi.mul_apply, walkGenerator_mul_apply hbc hcd, walkGenerator_apply]
  by_cases hbd : s b = s d
  · rw [dite_eq_left hbd]
    have hamem : s a ∈ G.neighborFinset (s b) := by
      rw [SimpleGraph.mem_neighborFinset]; exact (s.adj hab).symm
    rw [Finset.sum_eq_single_of_mem ⟨s a, hamem⟩ (Finset.mem_attach _ _) fun x _ hxa ↦ by
      rw [walkGenerator_mul_apply hab hbc, dite_eq_right ?_, mul_zero]
      intro hEq
      apply hxa
      ext
      simpa [EndpointWalk.coe_update, update_of_ne hac'] using hEq.symm]
    let s₁ := s.update hbc hcd hbd ((G.mem_neighborFinset _ _).1 hamem)
    have hs₁ac : s₁ a = s₁ c := by
      simp [s₁, EndpointWalk.coe_update, update_of_ne hac']
    have hdmem : s d ∈ G.neighborFinset (s₁ a) := by
      rw [SimpleGraph.mem_neighborFinset]
      simpa [s₁, EndpointWalk.coe_update, update_of_ne hac', ← hbd] using s.adj hab
    rw [walkGenerator_mul_apply hab hbc, dite_eq_left hs₁ac,
      Finset.sum_eq_single_of_mem ⟨s d, hdmem⟩ (Finset.mem_attach _ _) fun y _ hyd ↦ by
        rw [walkGenerator_apply, ite_eq_right ?_, mul_zero]
        rintro ⟨hEq, _, _⟩
        apply hyd
        ext
        simpa [s₁, EndpointWalk.coe_update, update_of_ne hdb, update_of_ne hdc] using hEq]
    have hs₂ : s₁.update hab hbc hs₁ac ((G.mem_neighborFinset _ _).1 hdmem) = s₁ := by
      ext i
      simp only [EndpointWalk.coe_update, s₁]
      exact congrFun (update_eq_self_iff.2 (by rw [update_of_ne hbc', hbd])) i
    rw [hs₂, walkGenerator_update_apply hbc hcd s hbd ((G.mem_neighborFinset _ _).1 hamem)]
    simp only [hbd, true_and]
    split_ifs
    · simp only [EndpointWalk.coe_update, update_of_ne hbc', update_of_ne hac']
      rw [← hbd]
      have := hr (s a)
      have := hr (s b)
      field_simp
    · simp
  · rw [dite_eq_right hbd, ite_eq_right fun h ↦ hbd h.1]

theorem walkGenerator_mul_walkGenerator_apply {a b c a' b' c' : Fin (n + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (h₁ : b ≠ a') (h₂ : b ≠ b')
    (h₃ : b ≠ c') (v : G.walkEndpoints v₀ n) (s u : G.EndpointWalk v₀ n v.1) :
    (walkGenerator G v₀ r a b c * walkGenerator G v₀ r a' b' c') v s u =
      if s a = s c ∧ s a' = s c' ∧
          (u : Fin (n + 1) → V) = update (update (s : Fin (n + 1) → V) b (u b)) b' (u b') ∧
          G.Adj (s a) (u b) ∧ G.Adj (s a') (u b') then
        r (s b) * r (u b) / r (s a) ^ 2 * (r (s b') * r (u b') / r (s a') ^ 2)
      else 0 := by
  rw [Pi.mul_apply, walkGenerator_mul_apply hab hbc]
  by_cases hac : s a = s c
  swap
  · rw [dite_eq_right hac, ite_eq_right fun h ↦ hac h.1]
  rw [dite_eq_left hac]
  by_cases hub : G.Adj (s a) (u b)
  · have hubmem : u b ∈ G.neighborFinset (s a) := (G.mem_neighborFinset _ _).2 hub
    have hub' : G.Adj (s c) (u b) := hac ▸ hub
    rw [Finset.sum_eq_single_of_mem ⟨u b, hubmem⟩ (Finset.mem_attach _ _) fun x _ hxu ↦ by
      rw [walkGenerator_apply, ite_eq_right ?_, mul_zero]
      rintro ⟨_, hEq, _⟩
      apply hxu
      ext
      have := congrFun hEq b
      simpa [EndpointWalk.coe_update, update_of_ne h₂] using this.symm]
    rw [walkGenerator_apply]
    simp only [EndpointWalk.coe_update, update_of_ne h₁.symm, update_of_ne h₂.symm,
      update_of_ne h₃.symm, hac, hub', true_and]
    split_ifs <;> simp
  · rw [ite_eq_right fun h ↦ hub h.2.2.2.1]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    rw [walkGenerator_apply, ite_eq_right ?_, mul_zero]
    rintro ⟨_, hEq, _⟩
    have hxb : u b = x.1 := by
      have := congrFun hEq b
      simpa [EndpointWalk.coe_update, update_of_ne h₂] using this
    exact hub (hxb ▸ (G.mem_neighborFinset _ _).1 x.2)

theorem walkGenerator_mul_walkGenerator_comm {a b c a' b' c' : Fin (n + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (hab' : a'.val + 1 = b'.val)
    (hbc' : b'.val + 1 = c'.val) (h₁ : b ≠ a') (h₂ : b ≠ b') (h₃ : b ≠ c') (h₄ : b' ≠ a)
    (h₅ : b' ≠ c) :
    walkGenerator G v₀ r a b c * walkGenerator G v₀ r a' b' c' =
      walkGenerator G v₀ r a' b' c' * walkGenerator G v₀ r a b c := by
  ext v s u
  rw [walkGenerator_mul_walkGenerator_apply hab hbc h₁ h₂ h₃,
    walkGenerator_mul_walkGenerator_apply hab' hbc' h₄ h₂.symm h₅, update_comm h₂]
  split_ifs <;> first | ring1 | (exfalso; tauto)

/-- Extending a generator from level `n + 1` to level `n + 2` via `walkExtend` acts at the cast
positions. -/
theorem walkExtend_walkGenerator {a b c : Fin (n + 2)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) :
    walkExtend G v₀ (walkGenerator G v₀ r a b c) =
      walkGenerator G v₀ r a.castSucc b.castSucc c.castSucc := by
  have hb_last : b ≠ Fin.last (n + 1) := Fin.ne_of_val_ne (by simp; omega)
  have hb_last' : b.castSucc ≠ Fin.last (n + 2) :=
    Fin.ne_of_val_ne (Nat.ne_of_lt b.isLt)
  ext v s t
  have hs : s.init.snoc s.adj_init_last = s := s.snoc_init
  have ht : t.init.snoc t.adj_init_last = t := t.snoc_init
  conv_lhs => rw [← hs, ← ht]
  rw [walkExtend_apply_snoc, walkGenerator_apply]
  by_cases hu : s (Fin.last (n + 1)).castSucc = t (Fin.last (n + 1)).castSucc
  · rw [dite_eq_left hu, walkGenerator_apply, t.init.coe_cast hu.symm]
    have hiff : (s.init a = s.init c ∧
        (t.init : Fin (n + 2) → V) = update (s.init : Fin (n + 2) → V) b (t.init b) ∧
        G.Adj (s.init a) (t.init b)) ↔
        (s a.castSucc = s c.castSucc ∧
          (t : Fin (n + 3) → V) = update (s : Fin (n + 3) → V) b.castSucc (t b.castSucc) ∧
          G.Adj (s a.castSucc) (t b.castSucc)) := by
      simp only [EndpointWalk.init_apply]
      refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
      constructor
      · intro h
        ext i
        induction i using Fin.lastCases with
        | last => rw [update_of_ne hb_last'.symm, t.apply_last_eq, s.apply_last_eq]
        | cast j =>
          have hj := congrFun h j
          simp only [EndpointWalk.coe_init, Fin.init] at hj
          by_cases hjb : j = b
          · subst hjb; simp
          · simpa [Fin.init, update_of_ne hjb, update_of_ne (Fin.castSucc_inj.not.2 hjb)] using hj
      · intro h
        ext j
        have hj := congrFun h j.castSucc
        by_cases hjb : j = b
        · subst hjb; simp [EndpointWalk.coe_init]
        · simpa [EndpointWalk.coe_init, Fin.init, update_of_ne hjb,
            update_of_ne (Fin.castSucc_inj.not.2 hjb)] using hj
    by_cases h : s.init a = s.init c ∧
        (t.init : Fin (n + 2) → V) = update (s.init : Fin (n + 2) → V) b (t.init b) ∧
        G.Adj (s.init a) (t.init b)
    · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
      simp only [EndpointWalk.init_apply]
    · rw [ite_eq_right h, ite_eq_right (mt hiff.mpr h)]
  · rw [dite_eq_right hu, ite_eq_right]
    rintro ⟨_, hEq, _⟩
    have := congrFun hEq (Fin.last (n + 1)).castSucc
    rw [update_of_ne (Fin.castSucc_inj.not.2 hb_last.symm)] at this
    exact hu this.symm

end Generator

section Representation

variable {G v₀ r}
variable (hr : ∀ v, r v ≠ 0) {δ : K} (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
  {n : ℕ}

variable (G v₀) in
/-- The **endpoint-graded path representation** of `TemperleyLieb K δ n` in
`PathAlgebra K G v₀ n`, valid for any locally finite graph `G`. -/
def walkRep : TemperleyLieb K δ n →ₐ[K] PathAlgebra K G v₀ n :=
  lift (fun i ↦ walkGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩)
    (fun _ ↦ walkGenerator_mul_self hr hδ rfl rfl)
    (fun {i j} h ↦ by
      obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj⟩ := j
      simp only at h
      rcases h with rfl | rfl
      · exact walkGenerator_zigzag_left hr rfl rfl rfl
      · exact walkGenerator_zigzag_right hr rfl rfl rfl)
    (fun {i j} h ↦ walkGenerator_mul_walkGenerator_comm rfl rfl rfl rfl
      (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega))

@[simp]
theorem walkRep_e (i : Fin (n - 1)) :
    walkRep G v₀ hr hδ (e δ i) =
      walkGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ :=
  lift_e _ _ _ _ i

/-- `walkRep` intertwines `strandIncl` with `walkExtend`. -/
@[simp]
theorem walkRep_strandIncl {m : ℕ} (x : TemperleyLieb K δ (m + 1)) :
    walkRep G v₀ hr hδ (strandIncl x) = walkExtend G v₀ (walkRep G v₀ hr hδ x) := by
  refine DFunLike.congr_fun
    (hom_ext (F := (walkRep G v₀ hr hδ).comp strandIncl)
      (G := (walkExtend G v₀).comp (walkRep G v₀ hr hδ)) fun i ↦ ?_) x
  simp only [AlgHom.comp_apply, strandIncl_e, walkRep_e]
  exact (walkExtend_walkGenerator (a := ⟨i, by omega⟩) (b := ⟨i + 1, by omega⟩)
    (c := ⟨i + 2, by omega⟩) rfl rfl).symm

section Star

variable [StarRing K] (hrs : ∀ v, IsSelfAdjoint (r v)) [Fact (IsSelfAdjoint δ)]

include hrs in
@[simp]
theorem walkRep_star (x : TemperleyLieb K δ n) :
    walkRep G v₀ hr hδ (star x) = star (walkRep G v₀ hr hδ x) := by
  refine (map_star_iff.mpr fun i ↦ ?_) x
  have := i.isLt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [IsSelfAdjoint]
  funext v
  rw [Pi.star_apply, Matrix.star_eq_conjTranspose, walkRep_e,
    conjTranspose_walkGenerator hrs rfl rfl v]

variable (G v₀) in
/-- The **endpoint-graded path `⋆`-representation** of `TemperleyLieb K δ n` for self-adjoint
weights `r`. -/
def walkStarRep : TemperleyLieb K δ n →⋆ₐ[K] PathAlgebra K G v₀ n :=
  { walkRep G v₀ hr hδ with map_star' := walkRep_star hr hδ hrs }

@[simp]
theorem walkStarRep_toAlgHom :
    (walkStarRep G v₀ hr hδ hrs (n := n)).toAlgHom = walkRep G v₀ hr hδ :=
  (rfl)

@[simp]
theorem walkStarRep_e (i : Fin (n - 1)) :
    walkStarRep G v₀ hr hδ hrs (e δ i) =
      walkGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ :=
  walkRep_e hr hδ i

@[simp]
theorem walkStarRep_strandIncl {m : ℕ} (x : TemperleyLieb K δ (m + 1)) :
    walkStarRep G v₀ hr hδ hrs (strandIncl x) =
      walkStarExtend G v₀ (walkStarRep G v₀ hr hδ hrs x) :=
  walkRep_strandIncl hr hδ x

end Star

end Representation

section Surjective

variable {G v₀ r}
variable (hr : ∀ v, r v ≠ 0) {δ : K} (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)

/-- Sandwiching a last-position generator between two extended `blockSingle` units passing through
an `m`-step walk `p₀ : G.EndpointWalk v₀ m t` isolates the single matrix unit `(p, q)` on block `t`,
killing all other endpoint blocks. -/
private theorem walkExtend_blockSingle_mul_walkGenerator_mul_walkExtend_blockSingle
    {m : ℕ} (t : G.walkEndpoints v₀ (m + 2)) (p₀ : G.EndpointWalk v₀ m t.1)
    (p q : G.EndpointWalk v₀ (m + 2) t.1) :
    let u := p (Fin.last (m + 1)).castSucc
    let u' := q (Fin.last (m + 1)).castSucc
    let hu : u ∈ G.walkEndpoints v₀ (m + 1) := (G.mem_walkEndpoints_iff v₀).2 ⟨p.init⟩
    let hu' : u' ∈ G.walkEndpoints v₀ (m + 1) := (G.mem_walkEndpoints_iff v₀).2 ⟨q.init⟩
    walkExtend G v₀ (PathAlgebra.blockSingle ⟨u, hu⟩ p.init (p₀.snoc p.adj_init_last.symm) 1) *
        walkGenerator G v₀ r ⟨m, by omega⟩ ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩ *
        walkExtend G v₀
          (PathAlgebra.blockSingle ⟨u', hu'⟩ (p₀.snoc q.adj_init_last.symm) q.init 1) =
      (r u * r u' / r t.1 ^ 2) • PathAlgebra.blockSingle t p q 1 := by
  intro u u' hu hu'
  set a : Fin (m + 3) := ⟨m, by omega⟩
  set b : Fin (m + 3) := ⟨m + 1, by omega⟩
  set c : Fin (m + 3) := ⟨m + 2, by omega⟩
  have hb : b = (Fin.last (m + 1)).castSucc := rfl
  have hc : c = Fin.last (m + 2) := rfl
  ext s w z
  simp only [Pi.mul_apply, Matrix.mul_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    walkExtend_blockSingle_apply]
  have heq_of_init {x₁ x₂ : G.EndpointWalk v₀ (m + 2) s.1}
      (h : (x₁.init : Fin (m + 2) → V) = x₂.init) : x₁ = x₂ := by
    ext i
    induction i using Fin.lastCases with
    | last => rw [x₁.apply_last_eq, x₂.apply_last_eq]
    | cast j => simpa only [EndpointWalk.init_apply] using congrFun h j
  by_cases hst : s = t
  · subst hst
    rw [PathAlgebra.blockSingle_apply_same, Matrix.single_apply]
    let y₀ : G.EndpointWalk v₀ (m + 2) s.1 := (p₀.snoc p.adj_init_last.symm).snoc p.adj_init_last
    let y₀' : G.EndpointWalk v₀ (m + 2) s.1 := (p₀.snoc q.adj_init_last.symm).snoc q.adj_init_last
    have hy₀_init : (y₀.init : Fin (m + 2) → V) = p₀.snoc p.adj_init_last.symm := by
      ext i; simp [y₀]
    have hy₀'_init : (y₀'.init : Fin (m + 2) → V) = p₀.snoc q.adj_init_last.symm := by
      ext i; simp [y₀']
    rw [Finset.sum_eq_single y₀' (fun y' _ hy' ↦ by
        rw [ite_eq_right (fun h ↦ hy' (heq_of_init (h.1.trans hy₀'_init.symm))), mul_zero])
      (fun h ↦ (h (Finset.mem_univ _)).elim)]
    rw [Finset.sum_eq_single y₀ (fun y _ hy ↦ by
        rw [ite_eq_right (fun h ↦ hy (heq_of_init (h.2.trans hy₀_init.symm))), zero_mul])
      (fun h ↦ (h (Finset.mem_univ _)).elim)]
    by_cases hwz : p = w ∧ q = z
    · rcases hwz with ⟨rfl, rfl⟩
      rw [ite_eq_left ⟨rfl, hy₀_init⟩, ite_eq_left ⟨hy₀'_init, rfl⟩, ite_eq_left ⟨rfl, rfl⟩,
        one_mul, mul_one, mul_one, walkGenerator_apply]
      have ha_eq : a = (Fin.last m).castSucc.castSucc := rfl
      have hy₀a : y₀ a = s.1 := by rw [ha_eq]; simp [y₀]
      have hy₀c : y₀ c = s.1 := by rw [hc]; exact y₀.apply_last_eq
      have hy₀b : y₀ b = u := by simp [y₀, hb, u]
      have hy₀'b : y₀' b = u' := by simp [y₀', hb, u']
      have hupd : (y₀' : Fin (m + 3) → V) = update (y₀ : Fin (m + 3) → V) b (y₀' b) := by
        ext i
        induction i using Fin.lastCases with
        | last =>
          rw [update_of_ne (Fin.ne_of_val_ne (by simp [b])),
            y₀'.apply_last_eq, y₀.apply_last_eq]
        | cast j =>
          induction j using Fin.lastCases with
          | last =>
            have hbl : (Fin.last (m + 1)).castSucc = b := rfl
            rw [hbl, update_self]
          | cast k =>
            rw [update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt (by simpa [b] using k.isLt)))]
            simp [y₀, y₀']
      have hgen : y₀ a = y₀ c ∧
          (y₀' : Fin (m + 3) → V) = update (y₀ : Fin (m + 3) → V) b (y₀' b) ∧
          G.Adj (y₀ a) (y₀' b) :=
        ⟨hy₀a.trans hy₀c.symm, hupd, by rw [hy₀a, hy₀'b]; exact q.adj_init_last.symm⟩
      rw [ite_eq_left hgen, hy₀b, hy₀'b, hy₀a]
    · rw [ite_eq_right hwz, mul_zero]
      by_cases hwp : w = p
      · have hzq : z ≠ q := fun h ↦ hwz ⟨hwp.symm, h.symm⟩
        have hR0 : (if (y₀'.init : Fin (m + 2) → V) = p₀.snoc q.adj_init_last.symm ∧
            (z.init : Fin (m + 2) → V) = q.init then (1 : K) else 0) = 0 :=
          ite_eq_right (fun h ↦ hzq (heq_of_init h.2))
        rw [hR0, mul_zero]
      · have hL0 : (if (w.init : Fin (m + 2) → V) = p.init ∧
            (y₀.init : Fin (m + 2) → V) = p₀.snoc p.adj_init_last.symm then (1 : K) else 0) = 0 :=
          ite_eq_right (fun h ↦ hwp (heq_of_init h.1))
        rw [hL0, zero_mul, zero_mul]
  · rw [PathAlgebra.blockSingle_apply_of_ne hst, Matrix.zero_apply, mul_zero]
    refine Finset.sum_eq_zero fun y' _ ↦ ?_
    suffices ∑ y : G.EndpointWalk v₀ (m + 2) s.1,
        (if (w.init : Fin (m + 2) → V) = p.init ∧
          (y.init : Fin (m + 2) → V) = p₀.snoc p.adj_init_last.symm then (1 : K) else 0) *
        walkGenerator G v₀ r a b c s y y' = 0 by rw [this, zero_mul]
    refine Finset.sum_eq_zero fun y _ ↦ ?_
    split_ifs with hL_cond
    · rw [one_mul, walkGenerator_apply, ite_eq_right]
      rintro ⟨hyac, _, _⟩
      apply hst
      ext
      have ha_eq : a = (Fin.last m).castSucc.castSucc := rfl
      have hya : y a = t.1 := by
        have h := congrFun hL_cond.2 (Fin.last m).castSucc
        simpa [ha_eq, EndpointWalk.coe_init, Fin.init] using h
      have hyc : y c = s.1 := by rw [hc]; exact y.apply_last_eq
      exact hyc.symm.trans (hyac.symm.trans hya)
    · rw [zero_mul]

include hr hδ in
/-- **Surjectivity of the endpoint-graded path representation.** When `G` admits an injective
`ℕ`-valued height function starting at `0` at `v₀` that changes by `1` along edges (as on finite
path graphs `SimpleGraph.pathGraph L` and on the half-line `SimpleGraph.hasse ℕ`),
`walkRep G v₀ hr hδ` surjects onto `PathAlgebra K G v₀ n` at every level `n`. -/
theorem walkRep_surjective {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) :
    ∀ n : ℕ, Function.Surjective (walkRep G v₀ hr hδ (n := n))
  | 0 => fun X ↦ by
    let t₀ : G.walkEndpoints v₀ 0 := ⟨v₀, by simp⟩
    let p₀ : G.EndpointWalk v₀ 0 v₀ := EndpointWalk.zero G v₀
    refine ⟨algebraMap K _ (X t₀ p₀ p₀), ?_⟩
    ext ⟨v, hv⟩ p q
    have hv₀ : v = v₀ := by simpa using hv
    subst hv₀
    have hp : p = p₀ := Subsingleton.elim _ _
    have hq : q = p₀ := Subsingleton.elim _ _
    subst hp; subst hq
    simp [Algebra.algebraMap_eq_smul_one, t₀]
  | 1 => fun X ↦ by
    have hcard := G.card_walkEndpoints_one_le_one v₀ hf hf₀ hadj
    by_cases hne : (G.walkEndpoints v₀ 1).Nonempty
    · obtain ⟨v₁, hv₁⟩ := hne
      obtain ⟨p₁⟩ := (G.mem_walkEndpoints_iff v₀).1 hv₁
      refine ⟨algebraMap K _ (X ⟨v₁, hv₁⟩ p₁ p₁), ?_⟩
      ext ⟨v, hv⟩ p q
      have hvv : v = v₁ := Finset.card_le_one.1 hcard v hv v₁ hv₁
      subst hvv
      have hp : p = p₁ := Subsingleton.elim _ _
      have hq : q = p₁ := Subsingleton.elim _ _
      subst hp; subst hq
      simp [Algebra.algebraMap_eq_smul_one]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨0, ?_⟩
      ext ⟨v, hv⟩
      exact False.elim (by simp [hne] at hv)
  | m + 2 => by
    have ih := walkRep_surjective hf hf₀ hadj (m + 1)
    let R := (walkRep G v₀ hr hδ (n := m + 2)).range
    have hstepback (t : G.walkEndpoints v₀ (m + 2)) (ht : t.1 ∈ G.walkEndpoints v₀ m)
        (p q : G.EndpointWalk v₀ (m + 2) t.1) :
        PathAlgebra.blockSingle t p q (1 : K) ∈ R := by
      obtain ⟨p₀⟩ := (G.mem_walkEndpoints_iff v₀).1 ht
      let u := p (Fin.last (m + 1)).castSucc
      let u' := q (Fin.last (m + 1)).castSucc
      have hu : u ∈ G.walkEndpoints v₀ (m + 1) := (G.mem_walkEndpoints_iff v₀).2 ⟨p.init⟩
      have hu' : u' ∈ G.walkEndpoints v₀ (m + 1) := (G.mem_walkEndpoints_iff v₀).2 ⟨q.init⟩
      obtain ⟨a, ha⟩ := ih
        (PathAlgebra.blockSingle ⟨u, hu⟩ p.init (p₀.snoc p.adj_init_last.symm) 1)
      obtain ⟨b, hb⟩ := ih
        (PathAlgebra.blockSingle ⟨u', hu'⟩ (p₀.snoc q.adj_init_last.symm) q.init 1)
      have hprod : walkExtend G v₀
            (PathAlgebra.blockSingle ⟨u, hu⟩ p.init (p₀.snoc p.adj_init_last.symm) 1) *
          walkGenerator G v₀ r ⟨m, by omega⟩ ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩ *
          walkExtend G v₀
            (PathAlgebra.blockSingle ⟨u', hu'⟩ (p₀.snoc q.adj_init_last.symm) q.init 1) ∈ R := by
        rw [AlgHom.mem_range]
        refine ⟨strandIncl a * e δ (Fin.last m) * strandIncl b, ?_⟩
        simp only [map_mul, walkRep_strandIncl, ha, hb, walkRep_e]
        rfl
      rw [walkExtend_blockSingle_mul_walkGenerator_mul_walkExtend_blockSingle t p₀ p q] at hprod
      have hc : r u * r u' / r t.1 ^ 2 ≠ 0 :=
        div_ne_zero (mul_ne_zero (hr u) (hr u')) (pow_ne_zero 2 (hr t.1))
      have hsmul := R.smul_mem hprod (r u * r u' / r t.1 ^ 2)⁻¹
      dsimp only [u, u'] at hc hsmul
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hsmul
    have hunit (t : G.walkEndpoints v₀ (m + 2)) (p q : G.EndpointWalk v₀ (m + 2) t.1) :
        PathAlgebra.blockSingle t p q (1 : K) ∈ R := by
      by_cases ht : t.1 ∈ G.walkEndpoints v₀ m
      · exact hstepback t ht p q
      · have hft : f t.1 = m + 2 := by
          rcases p.forall_eq_or_exists_endpointWalk hf hf₀ hadj with hfwd | hne
          · simpa [p.apply_last_eq] using hfwd (Fin.last (m + 2))
          · exact False.elim (ht ((G.mem_walkEndpoints_iff v₀).2 hne))
        have : Subsingleton (G.EndpointWalk v₀ (m + 2) t.1) :=
          EndpointWalk.subsingleton_of_last_eq hf hf₀ hadj hft
        have hpq : p = q := Subsingleton.elim _ _
        subst hpq
        have hid (s : G.walkEndpoints v₀ (m + 2)) (hst : s ≠ t) :
            Pi.single s (1 : Matrix (G.EndpointWalk v₀ (m + 2) s.1) _ K) ∈ R := by
          have hs : s.1 ∈ G.walkEndpoints v₀ m := by
            by_contra hns
            obtain ⟨ws⟩ := (G.mem_walkEndpoints_iff v₀).1 s.2
            rcases ws.forall_eq_or_exists_endpointWalk hf hf₀ hadj with hfwd | hne
            · have hfs : f s.1 = m + 2 := by
                simpa [ws.apply_last_eq] using hfwd (Fin.last (m + 2))
              exact hst (Subtype.ext (hf (hfs.trans hft.symm)))
            · exact hns ((G.mem_walkEndpoints_iff v₀).2 hne)
          have hsum : Pi.single s (1 : Matrix (G.EndpointWalk v₀ (m + 2) s.1) _ K) =
              ∑ w : G.EndpointWalk v₀ (m + 2) s.1, PathAlgebra.blockSingle s w w (1 : K) := by
            ext s' w₁ w₂
            by_cases hss' : s' = s
            · subst hss'
              simp only [Pi.single_eq_same, Finset.sum_apply, Matrix.sum_apply,
                PathAlgebra.blockSingle_apply_same, Matrix.single_apply, Matrix.one_apply]
              rw [Finset.sum_eq_single w₁
                (fun w _ hww ↦ ite_eq_right (fun h ↦ hww h.1))
                (fun h ↦ (h (Finset.mem_univ _)).elim)]
              by_cases hw : w₁ = w₂ <;> simp [hw]
            · simp [PathAlgebra.blockSingle, Pi.single_eq_of_ne hss']
          rw [hsum]
          exact R.sum_mem fun w _ ↦ hstepback s hs w w
        have hsingle_eq : PathAlgebra.blockSingle t p p (1 : K) =
            (1 : PathAlgebra K G v₀ (m + 2)) -
              ∑ s ∈ Finset.univ.erase t,
                Pi.single s
                  (1 : Matrix (G.EndpointWalk v₀ (m + 2) s.1)
                    (G.EndpointWalk v₀ (m + 2) s.1) K) := by
          funext s
          by_cases hst : s = t
          · subst hst
            have h0 : (∑ s' ∈ Finset.univ.erase s,
                Pi.single s'
                  (1 : Matrix (G.EndpointWalk v₀ (m + 2) s'.1)
                    (G.EndpointWalk v₀ (m + 2) s'.1) K)) s = 0 := by
              rw [Finset.sum_apply]
              exact Finset.sum_eq_zero fun s' hs' ↦
                Pi.single_eq_of_ne (Finset.ne_of_mem_erase hs').symm _
            simp only [Pi.sub_apply, Pi.one_apply, h0, sub_zero, PathAlgebra.blockSingle_apply_same]
            ext w₁ w₂
            rw [Subsingleton.elim w₁ p, Subsingleton.elim w₂ p]
            simp
          · have h1 : (∑ s' ∈ Finset.univ.erase t,
                Pi.single s'
                  (1 : Matrix (G.EndpointWalk v₀ (m + 2) s'.1)
                    (G.EndpointWalk v₀ (m + 2) s'.1) K)) s = 1 := by
              rw [Finset.sum_apply, Finset.sum_eq_single s
                (fun s' _ hs's ↦ Pi.single_eq_of_ne hs's.symm _)
                (fun hs ↦ (hs (Finset.mem_erase.2 ⟨hst, Finset.mem_univ s⟩)).elim),
                Pi.single_eq_same]
            simp only [Pi.sub_apply, Pi.one_apply, h1, sub_self,
              PathAlgebra.blockSingle_apply_of_ne hst]
        rw [hsingle_eq]
        exact R.sub_mem R.one_mem
          (R.sum_mem fun s hs ↦ hid s (Finset.ne_of_mem_erase hs))
    intro X
    rw [X.eq_sum_blockSingle]
    exact R.sum_mem fun t _ ↦ R.sum_mem fun p _ ↦ R.sum_mem fun q _ ↦
      R.smul_mem (hunit t p q) (X t p q)

end Surjective

section WalkTraceMarkov

variable {G v₀ r}

/-- Capping the last two strands against `walkExtend X` preserves `walkTrace`. -/
theorem walkTrace_walkExtend_mul_walkGenerator (hr : ∀ v, r v ≠ 0) {n : ℕ}
    (X : PathAlgebra K G v₀ (n + 1)) {a b c : Fin (n + 3)}
    (ha : a.val = n) (hb : b.val = n + 1) (hc : c.val = n + 2) :
    walkTrace G v₀ r (walkExtend G v₀ X * walkGenerator G v₀ r a b c) =
      walkTrace G v₀ r X := by
  obtain ⟨a', rfl, ha'⟩ : ∃ a' : Fin (n + 2), a = a'.castSucc ∧ a'.val = n :=
    ⟨⟨n, by omega⟩, Fin.ext ha, rfl⟩
  obtain rfl : b = (Fin.last (n + 1)).castSucc := Fin.ext hb
  obtain rfl : c = Fin.last (n + 2) := Fin.ext hc
  have ha'l : a'.val + 1 = (Fin.last (n + 1)).val := by simp [ha']
  rw [walkTrace_mul_comm, walkTrace_apply]
  have hblock (v : G.walkEndpoints v₀ (n + 2)) :
      (r v.1 / r v₀) ^ 2 *
          ((walkGenerator G v₀ r a'.castSucc (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) *
              walkExtend G v₀ X) v).trace =
        ∑ u ∈ G.neighborFinset v.1 ∩ G.walkEndpoints v₀ (n + 1),
          ∑ p : G.EndpointWalk v₀ (n + 1) u,
            if p a' = v.1 then (r u / r v₀) ^ 2 * PathAlgebra.blockAt X u p p else 0 := by
    rw [Pi.mul_apply, Matrix.trace,
      ← (EndpointWalk.succEquiv G v₀ (n + 1) v.1).symm.sum_comp,
      ← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.mul_sum]
    have hentry (u : G.neighborSet v.1) (p : G.EndpointWalk v₀ (n + 1) u.1) :
        (r v.1 / r v₀) ^ 2 *
            (walkGenerator G v₀ r a'.castSucc (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) v *
              walkExtend G v₀ X v)
              ((EndpointWalk.succEquiv G v₀ (n + 1) v.1).symm ⟨u, p⟩)
              ((EndpointWalk.succEquiv G v₀ (n + 1) v.1).symm ⟨u, p⟩) =
          if p a' = v.1 then (r u.1 / r v₀) ^ 2 * PathAlgebra.blockAt X u.1 p p else 0 := by
      let huv : G.Adj u.1 v.1 := ((G.mem_neighborSet v.1 u.1).1 u.2).symm
      let w : G.EndpointWalk v₀ (n + 2) v.1 := p.snoc huv
      have hw : (EndpointWalk.succEquiv G v₀ (n + 1) v.1).symm ⟨u, p⟩ = w :=
        EndpointWalk.succEquiv_symm_apply ⟨u, p⟩
      rw [hw, walkGenerator_mul_apply (by simp [ha']) (by simp)]
      have hwa : w a'.castSucc = p a' := by simp [w]
      have hwb : w (Fin.last (n + 1)).castSucc = u.1 := by simp [w, p.apply_last_eq]
      have hwc : w (Fin.last (n + 2)) = v.1 := by simp [w]
      by_cases hpv : p a' = v.1
      · have hac : w a'.castSucc = w (Fin.last (n + 2)) := by rw [hwa, hwc, hpv]
        rw [dite_eq_left hac, ite_eq_left hpv]
        have humem : u.1 ∈ G.neighborFinset (w a'.castSucc) := by
          rw [SimpleGraph.mem_neighborFinset, hwa, hpv]; exact huv.symm
        rw [Finset.sum_eq_single_of_mem ⟨u.1, humem⟩ (Finset.mem_attach _ _) fun x _ hxu ↦ by
          set w' := w.update (b := (Fin.last (n + 1)).castSucc) (by simp [ha']) (by simp) hac
            ((G.mem_neighborFinset _ _).1 x.2)
          conv_lhs => rw [← w'.snoc_init]
          have hw'b : w' (Fin.last (n + 1)).castSucc = x.1 := by
            simp [w', EndpointWalk.coe_update]
          rw [walkExtend_apply_snoc,
            dite_eq_right (by rw [hw'b]; exact fun h ↦ hxu (Subtype.ext h)), mul_zero]]
        have hw_self : w.update (b := (Fin.last (n + 1)).castSucc) (by simp [ha']) (by simp) hac
            ((G.mem_neighborFinset _ _).1 humem) = w := by
          ext i
          simp only [EndpointWalk.coe_update]
          exact congrFun (update_eq_self_iff.2 hwb.symm) i
        have hrwa : r (w a'.castSucc) = r v.1 := by rw [hwa, hpv]
        rw [hw_self, walkExtend_apply_snoc_same,
          PathAlgebra.blockAt_of_mem X ((G.mem_walkEndpoints_iff v₀).2 ⟨p⟩), hwb, hrwa]
        dsimp only
        have := hr v.1
        have := hr v₀
        field_simp
      · have hnac : w a'.castSucc ≠ w (Fin.last (n + 2)) := by rw [hwa, hwc]; exact hpv
        rw [dite_eq_right hnac, ite_eq_right hpv, mul_zero]
    have hdiag :
        ∑ u : G.neighborSet v.1,
            (r v.1 / r v₀) ^ 2 *
              ∑ p : G.EndpointWalk v₀ (n + 1) u.1,
                (walkGenerator G v₀ r a'.castSucc (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) v *
                  walkExtend G v₀ X v).diag
                  ((EndpointWalk.succEquiv G v₀ (n + 1) v.1).symm ⟨u, p⟩) =
          ∑ u : G.neighborSet v.1,
            ∑ p : G.EndpointWalk v₀ (n + 1) u.1,
              (if p a' = v.1 then (r u.1 / r v₀) ^ 2 * PathAlgebra.blockAt X u.1 p p else 0) := by
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Matrix.diag_apply]
      exact hentry u p
    rw [hdiag]
    have hbij :
        ∑ u : G.neighborSet v.1,
            ∑ p : G.EndpointWalk v₀ (n + 1) u.1,
              (if p a' = v.1 then (r u.1 / r v₀) ^ 2 * PathAlgebra.blockAt X u.1 p p else 0) =
          ∑ u ∈ G.neighborFinset v.1,
            ∑ p : G.EndpointWalk v₀ (n + 1) u,
              (if p a' = v.1 then (r u / r v₀) ^ 2 * PathAlgebra.blockAt X u p p else 0) :=
      Finset.sum_bij (fun u _ ↦ u.1) (fun u _ ↦ (G.mem_neighborFinset v.1 u.1).2 u.2)
        (fun _ _ _ _ h ↦ Subtype.ext h)
        (fun u hu ↦ ⟨⟨u, (G.mem_neighborFinset v.1 u).1 hu⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ ↦ rfl)
    rw [hbij]
    exact (Finset.sum_subset Finset.inter_subset_left fun u _ hnu ↦ by
      have hu : u ∉ G.walkEndpoints v₀ (n + 1) := fun h ↦ hnu (Finset.mem_inter.2 ⟨‹_›, h⟩)
      have : IsEmpty (G.EndpointWalk v₀ (n + 1) u) :=
        not_nonempty_iff.1 ((G.mem_walkEndpoints_iff v₀).not.1 hu)
      exact Fintype.sum_empty _).symm
  simp_rw [hblock]
  let g (v : V) (u : V) : K :=
    ∑ p : G.EndpointWalk v₀ (n + 1) u,
      if p a' = v then (r u / r v₀) ^ 2 * PathAlgebra.blockAt X u p p else 0
  -- Fold the inner sum into `g v.1 u` so `Finset.sum_sigma'` reindexes cleanly.
  change (∑ v : G.walkEndpoints v₀ (n + 2),
      ∑ u ∈ G.neighborFinset v.1 ∩ G.walkEndpoints v₀ (n + 1), g v.1 u) = _
  rw [Finset.univ_eq_attach, Finset.sum_attach (G.walkEndpoints v₀ (n + 2))
    (fun v ↦ ∑ u ∈ G.neighborFinset v ∩ G.walkEndpoints v₀ (n + 1), g v u),
    Finset.sum_sigma' (G.walkEndpoints v₀ (n + 2))
      (fun v ↦ G.neighborFinset v ∩ G.walkEndpoints v₀ (n + 1)) g]
  have hswap :
      ∑ vp ∈ (G.walkEndpoints v₀ (n + 2)).sigma
          (fun v ↦ G.neighborFinset v ∩ G.walkEndpoints v₀ (n + 1)), g vp.1 vp.2 =
        ∑ uq ∈ (G.walkEndpoints v₀ (n + 1)).sigma (fun u ↦ G.neighborFinset u), g uq.2 uq.1 :=
    Finset.sum_bij (fun vp _ ↦ ⟨vp.2, vp.1⟩)
      (fun vp hvp ↦ by
        rcases Finset.mem_sigma.1 hvp with ⟨_, hp₂⟩
        rcases Finset.mem_inter.1 hp₂ with ⟨hadj, hu⟩
        exact Finset.mem_sigma.2 ⟨hu,
          (G.mem_neighborFinset _ _).2 ((G.mem_neighborFinset _ _).1 hadj).symm⟩)
      (fun p₁ _ p₂ _ h ↦ by cases p₁; cases p₂; cases h; rfl)
      (fun uq huq ↦ by
        rcases Finset.mem_sigma.1 huq with ⟨hu, hadj⟩
        have hv : uq.2 ∈ G.walkEndpoints v₀ (n + 2) := by
          rw [walkEndpoints_succ]
          exact Finset.mem_biUnion.2 ⟨uq.1, hu, hadj⟩
        refine ⟨⟨uq.2, uq.1⟩, Finset.mem_sigma.2 ⟨hv, Finset.mem_inter.2 ⟨?_, hu⟩⟩, rfl⟩
        exact (G.mem_neighborFinset _ _).2 ((G.mem_neighborFinset _ _).1 hadj).symm)
      (fun _ _ ↦ rfl)
  rw [hswap, ← Finset.sum_sigma' (G.walkEndpoints v₀ (n + 1)) (fun u ↦ G.neighborFinset u)
      (fun u v ↦ g v u),
    walkTrace_apply, Finset.univ_eq_attach]
  conv_rhs =>
    rw [← Finset.sum_congr rfl (fun u _ ↦ by rw [← PathAlgebra.blockAt_of_mem X u.2]),
      Finset.sum_attach (G.walkEndpoints v₀ (n + 1))
        (fun u ↦ (r u / r v₀) ^ 2 * (PathAlgebra.blockAt X u).trace)]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  dsimp only [g]
  rw [Finset.sum_comm, Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hadj : p a' ∈ G.neighborFinset u := by
    rw [SimpleGraph.mem_neighborFinset]
    have h := (p.adj ha'l).symm
    rwa [p.apply_last_eq] at h
  rw [Finset.sum_eq_single_of_mem (p a') hadj (fun v _ hvp ↦ ite_eq_right hvp.symm),
    ite_eq_left rfl, Matrix.diag_apply]

variable (hr : ∀ v, r v ≠ 0) {δ : K} (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)

theorem walkTrace_walkRep_strandIncl {n : ℕ} (x : TemperleyLieb K δ (n + 1)) :
    walkTrace G v₀ r (walkRep G v₀ hr hδ (strandIncl x)) =
      δ * walkTrace G v₀ r (walkRep G v₀ hr hδ x) := by
  rw [walkRep_strandIncl, walkTrace_walkExtend hδ]

theorem walkTrace_walkRep_strandIncl_mul_e_last {n : ℕ} (x : TemperleyLieb K δ (n + 1)) :
    walkTrace G v₀ r (walkRep G v₀ hr hδ (strandIncl x * e δ (Fin.last n))) =
      walkTrace G v₀ r (walkRep G v₀ hr hδ x) := by
  rw [map_mul, walkRep_strandIncl, walkRep_e]
  exact walkTrace_walkExtend_mul_walkGenerator hr _ rfl rfl rfl

variable (G v₀) in
/-- `walkTrace ∘ walkRep` is an unnormalized Markov trace on the Temperley–Lieb tower. -/
theorem isMarkovTrace_walkTrace :
    IsMarkovTrace K δ (fun n ↦ (walkTrace G v₀ r).comp (walkRep G v₀ hr hδ (n := n)).toLinearMap) :=
  ⟨fun n ↦ by simp [walkTrace_one hr hδ],
    fun _ x y ↦ by simp [walkTrace_mul_comm],
    fun _ x ↦ walkTrace_walkRep_strandIncl hr hδ x,
    fun _ x ↦ walkTrace_walkRep_strandIncl_mul_e_last hr hδ x⟩

variable (G v₀) in
/-- By uniqueness of Markov traces, every Markov trace at loop value `δ` equals
`walkTrace ∘ walkRep`. -/
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

/-- On a finite graph, `walkRep` agrees entrywise on all walks with `PathModel.pathRep`. -/
theorem walkRep_eq_pathRep_apply {n : ℕ} (x : TemperleyLieb K δ n)
    (v : G.walkEndpoints v₀ n) (p q : G.EndpointWalk v₀ n v.1) :
    walkRep G v₀ hr hδ x v p q = pathRep G v₀ hr hδ x p q := by
  induction x using TemperleyLieb.induction generalizing p q with
  | e i =>
    have hp : G.IsWalkFrom v₀ ⇑p := p.isWalkFrom
    simp only [walkRep_e, pathRep_e, walkGenerator_apply, pathGenerator_apply, hp, true_and]
  | algebraMap k =>
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply, DFunLike.coe_injective.eq_iff]
  | add x y hx hy => simp [hx, hy]
  | mul x y hx hy =>
    simp only [map_mul, Pi.mul_apply, Matrix.mul_apply]
    let emb : G.EndpointWalk v₀ n v.1 → (Fin (n + 1) → V) := (↑)
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb)),
      Finset.sum_image (fun _ _ _ _ h ↦ DFunLike.coe_injective h)]
    · exact Finset.sum_congr rfl fun w _ ↦ by rw [hx, hy]
    · intro u _ hu
      have hnot : ¬((G.IsWalkFrom v₀ p ↔ G.IsWalkFrom v₀ u) ∧
          p (Fin.last n) = u (Fin.last n)) := by
        rintro ⟨hp, hlast⟩
        have huw : G.IsWalkFrom v₀ u := hp.1 p.isWalkFrom
        have hul : u (Fin.last n) = v.1 := hlast.symm.trans p.apply_last_eq
        exact hu (Finset.mem_image.2 ⟨⟨u, huw, hul⟩, Finset.mem_univ _, rfl⟩)
      rw [pathRep_apply_eq_zero hr hδ x hnot, zero_mul]

/-- On a finite graph, `walkTrace (walkRep x)` coincides with `PathModel.pathTrace x`. -/
theorem walkTrace_walkRep_eq_pathTrace {n : ℕ} (x : TemperleyLieb K δ n) :
    walkTrace G v₀ r (walkRep G v₀ hr hδ x) = pathTrace G v₀ hr hδ x :=
  ((isMarkovTrace_pathTrace G v₀ hr hδ).eq_walkTrace_comp_walkRep G v₀ hr hδ n x).symm

end FiniteGraph

end TauCeti.TemperleyLieb
