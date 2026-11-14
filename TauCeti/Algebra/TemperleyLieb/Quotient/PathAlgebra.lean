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
/-! # Endpoint-graded path algebras of locally finite graphs

Restricting `TauCeti.Algebra.TemperleyLieb.PathModel` to genuine `n`-step walks from `v₀` and
decomposing by their endpoint in `G.walkEndpoints v₀ n` extends the path model to arbitrary locally
finite graphs: `PathAlgebra K G v₀ n`, tower inclusions `walkExtend` / `walkStarExtend`,
Temperley–Lieb (`⋆`-)representations `walkRep` / `walkStarRep` and `walkRep_surjective`, and the
Markov trace `walkTrace` / `isMarkovTrace_walkTrace`. -/
public section
open Function Matrix SimpleGraph
namespace TauCeti.TemperleyLieb
section PathAlgebra
variable (K : Type*) {V : Type*} (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V)
/-- The **endpoint-graded path algebra** of a locally finite graph `G` from `v₀` at level `n`: the
finite product over `v ∈ G.walkEndpoints v₀ n` of full matrix algebras on `EndpointWalk`. -/
abbrev PathAlgebra (n : ℕ) :=
  ∀ v : G.walkEndpoints v₀ n, Matrix (G.EndpointWalk v₀ n v.1) (G.EndpointWalk v₀ n v.1) K
namespace PathAlgebra
variable {K G v₀}
section Semiring
variable [Semiring K] {n : ℕ}
/-- A matrix entry supported on a single endpoint block `t` at `(p, q)`. -/
def blockSingle (t : G.walkEndpoints v₀ n) (p q : G.EndpointWalk v₀ n t.1) (c : K) :
    PathAlgebra K G v₀ n := Pi.single t (Matrix.single p q c)
@[simp] theorem blockSingle_apply_same (t : G.walkEndpoints v₀ n)
    (p q : G.EndpointWalk v₀ n t.1) (c : K) :
    blockSingle t p q c t = Matrix.single p q c := Pi.single_eq_same t _
theorem blockSingle_apply_of_ne {t s : G.walkEndpoints v₀ n} (hts : s ≠ t)
    (p q : G.EndpointWalk v₀ n t.1) (c : K) : blockSingle t p q c s = 0 := Pi.single_eq_of_ne hts _
theorem eq_sum_blockSingle (X : PathAlgebra K G v₀ n) :
    X = ∑ t : G.walkEndpoints v₀ n, ∑ p : G.EndpointWalk v₀ n t.1,
      ∑ q : G.EndpointWalk v₀ n t.1, X t p q • blockSingle t p q (1 : K) := by
  ext s w z
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single s (fun t _ hts ↦ Finset.sum_eq_zero fun _ _ ↦
    Finset.sum_eq_zero fun _ _ ↦ by simp [blockSingle_apply_of_ne hts.symm])
    (fun hs ↦ (hs (Finset.mem_univ s)).elim)]
  simp [Matrix.single_apply, mul_ite, ite_and]
theorem one_eq_sum_blockSingle : (1 : PathAlgebra K G v₀ n) =
    ∑ s : G.walkEndpoints v₀ n, ∑ w : G.EndpointWalk v₀ n s.1, blockSingle s w w 1 := by
  conv_lhs => rw [eq_sum_blockSingle 1]
  refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun w₁ _ ↦ ?_
  rw [Finset.sum_eq_single w₁ (fun _ _ hne ↦ by simp [hne.symm])
    (fun h ↦ (h (Finset.mem_univ _)).elim)]; simp
end Semiring
section CommSemiring
variable [CommSemiring K] {n : ℕ}
/-- Extract the `u`-block of `PathAlgebra K G v₀ n` as a `K`-algebra homomorphism, returning `0`
when `u ∉ G.walkEndpoints v₀ n`. -/
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
@[simp] theorem blockAt_of_mem {u : V} (hu : u ∈ G.walkEndpoints v₀ n)
    (X : PathAlgebra K G v₀ n) : blockAt u X = X ⟨u, hu⟩ := dite_eq_left hu
theorem blockAt_of_notMem {u : V} (hu : u ∉ G.walkEndpoints v₀ n) (X : PathAlgebra K G v₀ n) :
    blockAt u X = 0 := dite_eq_right hu
@[simp] theorem blockAt_conjTranspose [StarRing K] (u : V) (X : PathAlgebra K G v₀ n) :
    (blockAt u X)ᴴ = blockAt u (star X) := by
  by_cases hu : u ∈ G.walkEndpoints v₀ n <;>
    simp [blockAt_of_mem, blockAt_of_notMem, hu, Matrix.star_eq_conjTranspose]
end CommSemiring
variable (K G v₀) in
theorem finrank [Field K] (n : ℕ) : Module.finrank K (PathAlgebra K G v₀ n) =
    ∑ v ∈ G.walkEndpoints v₀ n, Fintype.card (G.EndpointWalk v₀ n v) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_matrix, Module.finrank_self, mul_one, ← sq]
  exact (G.walkEndpoints v₀ n).sum_attach fun v ↦ Fintype.card (G.EndpointWalk v₀ n v) ^ 2
end PathAlgebra
end PathAlgebra
section Extend
variable {K : Type*} [CommSemiring K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [LocallyFinite G] (v₀ : V) {n : ℕ}
private def blockDiagonal'AlgHom {o : Type*} [DecidableEq o] [Fintype o] {m' : o → Type*}
    [∀ i, DecidableEq (m' i)] [∀ i, Fintype (m' i)] :
    (∀ i, Matrix (m' i) (m' i) K) →ₐ[K] Matrix (Σ i, m' i) (Σ i, m' i) K :=
  { Matrix.blockDiagonal'RingHom m' K with
    commutes' _ := by simp [Algebra.algebraMap_eq_smul_one] }
/-- One-step tower inclusion `PathAlgebra K G v₀ n →ₐ[K] PathAlgebra K G v₀ (n + 1)` acting
block-diagonally along `SimpleGraph.EndpointWalk.succEquiv`. -/
def walkExtend : PathAlgebra K G v₀ n →ₐ[K] PathAlgebra K G v₀ (n + 1) :=
  AlgHom.pi fun v ↦
    (Matrix.reindexAlgEquiv K K (EndpointWalk.succEquiv G v₀ n v.1).symm).toAlgHom.comp
      (blockDiagonal'AlgHom.comp (AlgHom.pi fun u : G.neighborSet v.1 ↦ PathAlgebra.blockAt u.1))
theorem walkExtend_apply (X : PathAlgebra K G v₀ n) (v : G.walkEndpoints v₀ (n + 1)) :
    walkExtend G v₀ X v =
      (Matrix.blockDiagonal' fun u : G.neighborSet v.1 ↦ PathAlgebra.blockAt u.1 X).submatrix
        (EndpointWalk.succEquiv G v₀ n v.1) (EndpointWalk.succEquiv G v₀ n v.1) := (rfl)
theorem walkExtend_apply_snoc (X : PathAlgebra K G v₀ n) {u₁ u₂ v : V}
    (p : G.EndpointWalk v₀ n u₁) (q : G.EndpointWalk v₀ n u₂)
    (h₁ : G.Adj u₁ v) (h₂ : G.Adj u₂ v) (hv : v ∈ G.walkEndpoints v₀ (n + 1)) :
    walkExtend G v₀ X ⟨v, hv⟩ (p.snoc h₁) (q.snoc h₂) =
      if h : u₁ = u₂ then X ⟨u₁, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩⟩ p (q.cast h.symm)
      else 0 := by
  rw [walkExtend_apply, Matrix.submatrix_apply, EndpointWalk.succEquiv_snoc,
    EndpointWalk.succEquiv_snoc]; by_cases h : u₁ = u₂
  · subst h; simp [Matrix.blockDiagonal'_apply_eq, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩]
  · rw [dite_eq_right h, Matrix.blockDiagonal'_apply,
      dite_eq_right fun heq ↦ h (congrArg Subtype.val heq)]
@[simp] theorem walkExtend_apply_snoc_same (X : PathAlgebra K G v₀ n) {u v : V}
    (p q : G.EndpointWalk v₀ n u) (h : G.Adj u v) (hv : v ∈ G.walkEndpoints v₀ (n + 1)) :
    walkExtend G v₀ X ⟨v, hv⟩ (p.snoc h) (q.snoc h) =
      X ⟨u, (G.mem_walkEndpoints_iff v₀).2 ⟨p⟩⟩ p q := by
  rw [walkExtend_apply_snoc, dite_eq_left rfl, EndpointWalk.cast_rfl]
theorem walkExtend_blockSingle_apply (u : G.walkEndpoints v₀ n)
    (p₁ p₂ : G.EndpointWalk v₀ n u.1) (c : K)
    (s : G.walkEndpoints v₀ (n + 1)) (w y : G.EndpointWalk v₀ (n + 1) s.1) :
    walkExtend G v₀ (PathAlgebra.blockSingle u p₁ p₂ c) s w y =
      if (w.init : Fin (n + 1) → V) = p₁ ∧ (y.init : Fin (n + 1) → V) = p₂ then c else 0 := by
  rcases u with ⟨u₀, hu₀⟩
  have hlast {x : G.EndpointWalk v₀ (n + 1) s.1} {p : G.EndpointWalk v₀ n u₀}
      (hx : (x.init : Fin (n + 1) → V) = p) : x (Fin.last n).castSucc = u₀ := by
    simpa [EndpointWalk.coe_init, p.apply_last_eq] using congrFun hx (Fin.last n)
  conv_lhs => rw [← w.snoc_init, ← y.snoc_init]
  rw [walkExtend_apply_snoc]; by_cases hwy : w (Fin.last n).castSucc = y (Fin.last n).castSucc
  · rw [dite_eq_left hwy]; by_cases hwu : u₀ = w (Fin.last n).castSucc
    · subst hwu; rw [PathAlgebra.blockSingle_apply_same, Matrix.single_apply]
      congr 1; refine propext (and_congr (eq_comm.trans DFunLike.coe_injective.eq_iff.symm) ?_)
      exact ⟨fun h ↦ by rw [← y.init.coe_cast hwy.symm, ← h],
        fun h ↦ DFunLike.coe_injective (by rw [y.init.coe_cast hwy.symm, ← h])⟩
    · rw [PathAlgebra.blockSingle_apply_of_ne (fun h ↦ hwu (congrArg Subtype.val h).symm),
        Matrix.zero_apply, ite_eq_right fun h ↦ hwu (hlast h.1).symm]
  · rw [dite_eq_right hwy, ite_eq_right fun h ↦ hwy ((hlast h.1).trans (hlast h.2).symm)]
@[simp] theorem walkExtend_star [StarRing K] (X : PathAlgebra K G v₀ n) :
    walkExtend G v₀ (star X) = star (walkExtend G v₀ X) := by
  funext v; rw [walkExtend_apply, Pi.star_apply, Matrix.star_eq_conjTranspose, walkExtend_apply,
    Matrix.conjTranspose_submatrix, Matrix.blockDiagonal'_conjTranspose]
  simp_rw [PathAlgebra.blockAt_conjTranspose]
/-- One-step `⋆`-algebra inclusion of path algebras. -/
def walkStarExtend [StarRing K] : PathAlgebra K G v₀ n →⋆ₐ[K] PathAlgebra K G v₀ (n + 1) :=
  { walkExtend G v₀ with map_star' := walkExtend_star G v₀ }
end Extend
section WalkTraceBasic
variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [LocallyFinite G] (v₀ : V) (r : V → K)
/-- The **endpoint-weighted matrix trace** on `PathAlgebra K G v₀ n`, summing `(r v / r v₀) ^ 2`
times the matrix trace on each endpoint block `v`. -/
def walkTrace {n : ℕ} : PathAlgebra K G v₀ n →ₗ[K] K where
  toFun X := ∑ v : G.walkEndpoints v₀ n, (r v.1 / r v₀) ^ 2 * (X v).trace
  map_add' _ _ := by simp [Matrix.trace_add, mul_add, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Matrix.trace_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
variable {G v₀ r}
theorem walkTrace_apply {n : ℕ} (X : PathAlgebra K G v₀ n) :
    walkTrace G v₀ r X = ∑ v : G.walkEndpoints v₀ n, (r v.1 / r v₀) ^ 2 * (X v).trace := (rfl)
theorem walkTrace_eq_sum_walkEndpoints {n : ℕ} (X : PathAlgebra K G v₀ n) :
    walkTrace G v₀ r X =
      ∑ v ∈ G.walkEndpoints v₀ n, (r v / r v₀) ^ 2 * (PathAlgebra.blockAt v X).trace := by
  rw [walkTrace_apply, Finset.univ_eq_attach, ← (G.walkEndpoints v₀ n).sum_attach
    (fun v ↦ (r v / r v₀) ^ 2 * (PathAlgebra.blockAt v X).trace)]
  exact Finset.sum_congr rfl fun v _ ↦ by rw [PathAlgebra.blockAt_of_mem v.2]
theorem walkTrace_mul_comm {n : ℕ} (X Y : PathAlgebra K G v₀ n) :
    walkTrace G v₀ r (X * Y) = walkTrace G v₀ r (Y * X) :=
  Finset.sum_congr rfl fun _ _ ↦ by rw [Pi.mul_apply, Pi.mul_apply, Matrix.trace_mul_comm]
theorem walkTrace_walkExtend {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) {n : ℕ}
    (X : PathAlgebra K G v₀ n) :
    walkTrace G v₀ r (walkExtend G v₀ X) = δ * walkTrace G v₀ r X := by
  rw [walkTrace_eq_sum_walkEndpoints, walkTrace_eq_sum_walkEndpoints, Finset.mul_sum]
  have htr {v : V} (hv : v ∈ G.walkEndpoints v₀ (n + 1)) :
      (PathAlgebra.blockAt v (walkExtend G v₀ X)).trace =
        ∑ u ∈ G.neighborFinset v, (PathAlgebra.blockAt u X).trace := by
    rw [PathAlgebra.blockAt_of_mem hv, Matrix.trace, G.sum_endpointWalk_succ v₀ n v]
    simp only [Matrix.diag_apply, walkExtend_apply_snoc_same]
    rw [← (G.neighborFinset v).sum_attach fun u ↦ (PathAlgebra.blockAt u X).trace]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    by_cases hu : u.1 ∈ G.walkEndpoints v₀ n
    · rw [PathAlgebra.blockAt_of_mem hu, Matrix.trace]; rfl
    · have := not_nonempty_iff.1 ((G.mem_walkEndpoints_iff v₀).not.1 hu)
      rw [PathAlgebra.blockAt_of_notMem hu, Matrix.trace_zero, Fintype.sum_empty]
  rw [Finset.sum_congr rfl fun v hv ↦ by rw [htr hv, Finset.mul_sum],
    G.sum_walkEndpoints_succ v₀ n (fun v u ↦ (r v / r v₀) ^ 2 * (PathAlgebra.blockAt u X).trace)
      fun v u hu ↦ by rw [PathAlgebra.blockAt_of_notMem hu, Matrix.trace_zero, mul_zero]]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← Finset.sum_mul, show ∑ v ∈ G.neighborFinset u, (r v / r v₀) ^ 2 = δ * (r u / r v₀) ^ 2 by
    simp_rw [div_pow, div_eq_mul_inv]; rw [← Finset.sum_mul, hδ u, mul_assoc], mul_assoc]
@[simp] theorem walkTrace_one (hr : ∀ v, r v ≠ 0) {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (n : ℕ) :
    walkTrace G v₀ r (1 : PathAlgebra K G v₀ n) = δ ^ n := by
  induction n with
  | zero =>
    rw [walkTrace_eq_sum_walkEndpoints, Finset.sum_congr rfl fun _ _ ↦ by rw [map_one]]
    simp [div_self (hr v₀)]
  | succ n ih =>
    rw [← map_one (walkExtend G v₀ (K := K) (n := n)), walkTrace_walkExtend hδ, ih, pow_succ,
      mul_comm]
end WalkTraceBasic
section WalkRep
variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [DecidableRel G.Adj] [LocallyFinite G] (v₀ : V) (r : V → K)
section Generator
variable {n : ℕ}
/-- The generator element in `PathAlgebra K G v₀ n` acting at interior position `b` between `a` and
`c`, with entry `r (s b) * r (t b) / r (s a) ^ 2` when `s a = s c` and `t` updates `s` at `b`. -/
def walkGenerator (a b c : Fin (n + 1)) : PathAlgebra K G v₀ n :=
  fun v ↦ Matrix.of fun s t : G.EndpointWalk v₀ n v.1 ↦
    if s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
        G.Adj (s a) (t b) then r (s b) * r (t b) / r (s a) ^ 2 else 0
theorem walkGenerator_apply (a b c : Fin (n + 1)) (v : G.walkEndpoints v₀ n)
    (s t : G.EndpointWalk v₀ n v.1) : walkGenerator G v₀ r a b c v s t =
      if s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
          G.Adj (s a) (t b) then r (s b) * r (t b) / r (s a) ^ 2 else 0 := (rfl)
variable {G v₀ r}
theorem walkGenerator_mul_apply {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (v : G.walkEndpoints v₀ n)
    (X : Matrix (G.EndpointWalk v₀ n v.1) (G.EndpointWalk v₀ n v.1) K)
    (s u : G.EndpointWalk v₀ n v.1) :
    (walkGenerator G v₀ r a b c v * X) s u =
      if hac : s a = s c then
        ∑ x ∈ (G.neighborFinset (s a)).attach, r (s b) * r x.1 / r (s a) ^ 2 *
          X (s.update hab hbc hac ((G.mem_neighborFinset _ _).1 x.2)) u
      else 0 := by
  rw [Matrix.mul_apply]; split_ifs with hac
  · let f : {x // x ∈ G.neighborFinset (s a)} → G.EndpointWalk v₀ n v.1 :=
      fun x ↦ s.update hab hbc hac ((G.mem_neighborFinset _ _).1 x.2)
    have hf : Function.Injective f := fun _ _ h ↦ Subtype.ext <| by
      simpa [f, EndpointWalk.coe_update] using congrArg (fun w : G.EndpointWalk v₀ n v.1 ↦ w b) h
    rw [← Finset.sum_subset (Finset.subset_univ ((G.neighborFinset (s a)).attach.image f)),
      Finset.sum_image fun _ _ _ _ h ↦ hf h]
    · refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [walkGenerator_apply, ite_eq_left ⟨hac, by simp [f, EndpointWalk.coe_update],
        by simpa [f, EndpointWalk.coe_update] using (G.mem_neighborFinset _ _).1 x.2⟩]
      simp [f, EndpointWalk.coe_update]
    · intro t _ ht
      rw [walkGenerator_apply, ite_eq_right fun ⟨_, hst, hadj⟩ ↦ ht <| Finset.mem_image.2
        ⟨⟨t b, (G.mem_neighborFinset _ _).2 hadj⟩, Finset.mem_attach _ _,
          EndpointWalk.ext fun i ↦ by simpa [f] using (congrFun hst i).symm⟩, zero_mul]
  · exact Finset.sum_eq_zero fun t _ ↦ by
      rw [walkGenerator_apply, ite_eq_right_iff.2 fun h ↦ (hac h.1).elim, zero_mul]
theorem walkGenerator_update_apply {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) {v : G.walkEndpoints v₀ n}
    (s : G.EndpointWalk v₀ n v.1) (hac : s a = s c) {x : V} (hx : G.Adj (s a) x)
    (u : G.EndpointWalk v₀ n v.1) :
    walkGenerator G v₀ r a b c v (s.update hab hbc hac hx) u =
      if (u : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (u b) ∧ G.Adj (s a) (u b) then
        r x * r (u b) / r (s a) ^ 2 else 0 := by
  rw [walkGenerator_apply]
  simp [EndpointWalk.coe_update, update_of_ne (Fin.ne_of_val_ne (by omega) : a ≠ b),
    update_of_ne (Fin.ne_of_val_ne (by omega) : c ≠ b), hac]
theorem conjTranspose_walkGenerator [StarRing K] (hrs : ∀ v, IsSelfAdjoint (r v))
    {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (v : G.walkEndpoints v₀ n) :
    (walkGenerator G v₀ r a b c v)ᴴ = walkGenerator G v₀ r a b c v := by
  have ha : a ≠ b := Fin.ne_of_val_ne (by omega); have hc : c ≠ b := Fin.ne_of_val_ne (by omega)
  have hsymm {s t : G.EndpointWalk v₀ n v.1}
      (h : s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
        G.Adj (s a) (t b)) :
      t a = t c ∧ (s : Fin (n + 1) → V) = update (t : Fin (n + 1) → V) b (s b) ∧
        G.Adj (t a) (s b) := by
    have hta : t a = s a := by rw [congrFun h.2.1 a, update_of_ne ha]
    have htc : t c = s c := by rw [congrFun h.2.1 c, update_of_ne hc]
    exact ⟨by rw [hta, htc, h.1], by rw [h.2.1, update_idem, update_eq_self], hta ▸ s.adj hab⟩
  ext s t; rw [Matrix.conjTranspose_apply, walkGenerator_apply, walkGenerator_apply]
  by_cases h : s a = s c ∧ (t : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (t b) ∧
      G.Adj (s a) (t b)
  · rw [ite_eq_left (hsymm h), ite_eq_left h,
      show t a = s a by rw [congrFun h.2.1 a, update_of_ne ha]]
    simp only [star_div₀, star_mul, star_pow, (hrs _).star_eq, mul_comm (r (s b))]
  · rw [ite_eq_right (mt hsymm h), ite_eq_right h, star_zero]
variable (hr : ∀ v, r v ≠ 0) {δ : K}
include hr in
theorem walkGenerator_mul_self (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
    {a b c : Fin (n + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) :
    walkGenerator G v₀ r a b c * walkGenerator G v₀ r a b c = δ • walkGenerator G v₀ r a b c := by
  ext v s u; rw [Pi.mul_apply, walkGenerator_mul_apply hab hbc, Pi.smul_apply, Matrix.smul_apply,
    walkGenerator_apply, smul_eq_mul]
  by_cases hac : s a = s c
  · rw [dite_eq_left hac]
    by_cases hu : (u : Fin (n + 1) → V) = update (s : Fin (n + 1) → V) b (u b) ∧ G.Adj (s a) (u b)
    · rw [ite_eq_left ⟨hac, hu.1, hu.2⟩, Finset.sum_congr rfl fun x _ ↦ by
        rw [walkGenerator_update_apply hab hbc s hac ((G.mem_neighborFinset _ _).1 x.2),
          ite_eq_left hu],
        (G.neighborFinset (s a)).sum_attach fun x ↦
          r (s b) * r x / r (s a) ^ 2 * (r x * r (u b) / r (s a) ^ 2)]
      have := hr (s a)
      rw [show ∑ x ∈ G.neighborFinset (s a),
          r (s b) * r x / r (s a) ^ 2 * (r x * r (u b) / r (s a) ^ 2) =
        r (s b) * r (u b) / r (s a) ^ 4 * ∑ x ∈ G.neighborFinset (s a), r x ^ 2 by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by field_simp, hδ]
      field_simp
    · rw [ite_eq_right fun h ↦ hu h.2, mul_zero]
      exact Finset.sum_eq_zero fun x _ ↦ by
        rw [walkGenerator_update_apply hab hbc s hac ((G.mem_neighborFinset _ _).1 x.2),
          ite_eq_right hu, mul_zero]
  · rw [dite_eq_right hac, ite_eq_right fun h ↦ hac h.1, mul_zero]
include hr in
private theorem walkGenerator_zigzag {a₁ b₁ c₁ a₂ b₂ c₂ q : Fin (n + 1)}
    (hab₁ : a₁.val + 1 = b₁.val) (hbc₁ : b₁.val + 1 = c₁.val)
    (hab₂ : a₂.val + 1 = b₂.val) (hbc₂ : b₂.val + 1 = c₂.val)
    (hc : (a₂ = b₁ ∧ b₂ = c₁ ∧ c₂ = q) ∨ (c₂ = b₁ ∧ b₂ = a₁ ∧ a₂ = q)) :
    walkGenerator G v₀ r a₁ b₁ c₁ * walkGenerator G v₀ r a₂ b₂ c₂ *
      walkGenerator G v₀ r a₁ b₁ c₁ = walkGenerator G v₀ r a₁ b₁ c₁ := by
  have hb₁q : b₁ ≠ q := by
    rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> exact Fin.ne_of_val_ne (by omega)
  have hab₁' : a₁ ≠ b₁ := Fin.ne_of_val_ne (by omega)
  have hcb₁ : c₁ ≠ b₁ := Fin.ne_of_val_ne (by omega)
  have hac₁' : a₁ ≠ c₁ := Fin.ne_of_val_ne (by omega)
  ext v s u
  rw [mul_assoc, Pi.mul_apply, Pi.mul_apply, walkGenerator_mul_apply hab₁ hbc₁, walkGenerator_apply]
  by_cases hac : s a₁ = s c₁
  · rw [dite_eq_left hac]
    have hqadj : G.Adj (s a₁) (s q) := by
      rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact hac ▸ s.adj hbc₂
      · exact (s.adj hab₂).symm
    have hqmem : s q ∈ G.neighborFinset (s a₁) := (G.mem_neighborFinset _ _).2 hqadj
    rw [Finset.sum_eq_single_of_mem ⟨s q, hqmem⟩ (Finset.mem_attach _ _) fun x _ hxq ↦ by
      rw [walkGenerator_mul_apply hab₂ hbc₂, dite_eq_right fun hEq ↦ hxq <| Subtype.ext <| by
        rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · simpa [EndpointWalk.coe_update, update_of_ne hb₁q.symm] using hEq
        · simpa [EndpointWalk.coe_update, update_of_ne hb₁q.symm] using hEq.symm, mul_zero]]
    let s₁ := s.update hab₁ hbc₁ hac hqadj
    have ⟨hs₁a₂, hs₁c₂⟩ : s₁ a₂ = s q ∧ s₁ c₂ = s q := by
      rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        simp [s₁, EndpointWalk.coe_update, update_of_ne hb₁q.symm]
    have hs₁ : s₁ a₂ = s₁ c₂ := hs₁a₂.trans hs₁c₂.symm
    have hamem : s a₁ ∈ G.neighborFinset (s₁ a₂) :=
      (G.mem_neighborFinset _ _).2 (hs₁a₂ ▸ hqadj.symm)
    have hs₁b₂ : s₁ b₂ = s a₁ := by
      rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        simp [s₁, EndpointWalk.coe_update, update_of_ne hab₁', update_of_ne hcb₁, hac]
    rw [walkGenerator_mul_apply hab₂ hbc₂, dite_eq_left hs₁,
      Finset.sum_eq_single_of_mem ⟨s a₁, hamem⟩ (Finset.mem_attach _ _) fun y _ hya ↦ by
        rw [walkGenerator_apply, ite_eq_right fun ⟨hEq, _, _⟩ ↦ hya <| Subtype.ext <| by
          rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · simpa [s₁, update_of_ne hac₁', update_of_ne hab₁'] using hEq.symm
          · simpa [s₁, update_of_ne hac₁'.symm, update_of_ne hcb₁, ← hac] using hEq, mul_zero],
      show s₁.update hab₂ hbc₂ hs₁ ((G.mem_neighborFinset _ _).1 hamem) = s₁ from
        DFunLike.coe_injective (by rw [EndpointWalk.coe_update, update_eq_self_iff.2 hs₁b₂.symm]),
      walkGenerator_update_apply hab₁ hbc₁ s hac hqadj]
    simp only [hac, true_and]; split_ifs
    · rw [hs₁b₂, hs₁a₂, hac]; have := hr (s c₁); have := hr (s q); field_simp
    · simp
  · rw [dite_eq_right hac, ite_eq_right fun h ↦ hac h.1]
theorem walkGenerator_mul_walkGenerator_apply {a b c a' b' c' : Fin (n + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (h₁ : b ≠ a') (h₂ : b ≠ b')
    (h₃ : b ≠ c') (v : G.walkEndpoints v₀ n) (s u : G.EndpointWalk v₀ n v.1) :
    (walkGenerator G v₀ r a b c * walkGenerator G v₀ r a' b' c') v s u =
      if s a = s c ∧ s a' = s c' ∧
          (u : Fin (n + 1) → V) = update (update (s : Fin (n + 1) → V) b (u b)) b' (u b') ∧
          G.Adj (s a) (u b) ∧ G.Adj (s a') (u b') then
        r (s b) * r (u b) / r (s a) ^ 2 * (r (s b') * r (u b') / r (s a') ^ 2)
      else 0 := by
  rw [Pi.mul_apply, walkGenerator_mul_apply hab hbc]; by_cases hac : s a = s c
  swap; · rw [dite_eq_right hac, ite_eq_right fun h ↦ hac h.1]
  rw [dite_eq_left hac]; by_cases hub : G.Adj (s a) (u b)
  · have hubmem : u b ∈ G.neighborFinset (s a) := (G.mem_neighborFinset _ _).2 hub
    have hub' : G.Adj (s c) (u b) := hac ▸ hub
    rw [Finset.sum_eq_single_of_mem ⟨u b, hubmem⟩ (Finset.mem_attach _ _) fun x _ hxu ↦ by
      rw [walkGenerator_apply, ite_eq_right fun ⟨_, hEq, _⟩ ↦ hxu <| Subtype.ext <| by
        simpa [EndpointWalk.coe_update, update_of_ne h₂] using (congrFun hEq b).symm, mul_zero],
      walkGenerator_apply]
    simp only [EndpointWalk.coe_update, update_of_ne h₁.symm, update_of_ne h₂.symm,
      update_of_ne h₃.symm, hac, hub', true_and]
    split_ifs <;> simp
  · rw [ite_eq_right fun h ↦ hub h.2.2.2.1]; refine Finset.sum_eq_zero fun x _ ↦ ?_
    rw [walkGenerator_apply, ite_eq_right ?_, mul_zero]; rintro ⟨_, hEq, _⟩
    have hxb : u b = x.1 := by simpa [update_of_ne h₂] using congrFun hEq b
    exact hub (hxb ▸ (G.mem_neighborFinset _ _).1 x.2)
theorem walkGenerator_mul_walkGenerator_comm {a b c a' b' c' : Fin (n + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (hab' : a'.val + 1 = b'.val)
    (hbc' : b'.val + 1 = c'.val) (h₁ : b ≠ a') (h₂ : b ≠ b') (h₃ : b ≠ c') (h₄ : b' ≠ a)
    (h₅ : b' ≠ c) : walkGenerator G v₀ r a b c * walkGenerator G v₀ r a' b' c' =
      walkGenerator G v₀ r a' b' c' * walkGenerator G v₀ r a b c := by
  ext v s u
  rw [walkGenerator_mul_walkGenerator_apply hab hbc h₁ h₂ h₃,
    walkGenerator_mul_walkGenerator_apply hab' hbc' h₄ h₂.symm h₅, update_comm h₂]
  split_ifs <;> first | ring1 | (exfalso; tauto)
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
/-- The **endpoint-graded path representation** of `TemperleyLieb K δ n` in
`PathAlgebra K G v₀ n`. -/
def walkRep : TemperleyLieb K δ n →ₐ[K] PathAlgebra K G v₀ n :=
  lift (fun i ↦ walkGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩)
    (fun _ ↦ walkGenerator_mul_self hr hδ rfl rfl)
    (fun {i j} h ↦ by
      obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j; simp only at h; rcases h with rfl | rfl
      · exact walkGenerator_zigzag hr rfl rfl rfl rfl (Or.inl ⟨rfl, rfl, rfl⟩)
      · exact walkGenerator_zigzag hr rfl rfl rfl rfl (Or.inr ⟨rfl, rfl, rfl⟩))
    (fun {_ _} h ↦ walkGenerator_mul_walkGenerator_comm rfl rfl rfl rfl
      (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega))
@[simp] theorem walkRep_e (i : Fin (n - 1)) : walkRep G v₀ hr hδ (e δ i) =
    walkGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ := lift_e _ _ _ _ i
@[simp] theorem walkRep_strandIncl {m : ℕ} (x : TemperleyLieb K δ (m + 1)) :
    walkRep G v₀ hr hδ (strandIncl x) = walkExtend G v₀ (walkRep G v₀ hr hδ x) := by
  refine DFunLike.congr_fun (hom_ext (F := (walkRep G v₀ hr hδ).comp strandIncl)
    (G := (walkExtend G v₀).comp (walkRep G v₀ hr hδ)) fun i ↦ ?_) x
  simp only [AlgHom.comp_apply, strandIncl_e, walkRep_e]
  exact (walkExtend_walkGenerator (a := ⟨i, by omega⟩) (b := ⟨i + 1, by omega⟩)
    (c := ⟨i + 2, by omega⟩) rfl).symm
section Star
variable [StarRing K] (hrs : ∀ v, IsSelfAdjoint (r v)) [Fact (IsSelfAdjoint δ)]
include hrs in
@[simp] theorem walkRep_star (x : TemperleyLieb K δ n) :
    walkRep G v₀ hr hδ (star x) = star (walkRep G v₀ hr hδ x) := by
  refine (map_star_iff.mpr fun i ↦ ?_) x
  have := i.isLt; obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  funext v; rw [Pi.star_apply, Matrix.star_eq_conjTranspose, walkRep_e,
    conjTranspose_walkGenerator hrs rfl rfl v]
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
private theorem walkExtend_blockSingle_mul_walkGenerator_mul_walkExtend_blockSingle
    {m : ℕ} (t : G.walkEndpoints v₀ (m + 2)) (p₀ : G.EndpointWalk v₀ m t.1)
    (p q : G.EndpointWalk v₀ (m + 2) t.1) :
    let u := p (Fin.last (m + 1)).castSucc; let u' := q (Fin.last (m + 1)).castSucc
    walkExtend G v₀ (PathAlgebra.blockSingle ⟨u, (G.mem_walkEndpoints_iff v₀).2 ⟨p.init⟩⟩
          p.init (p₀.snoc p.adj_init_last.symm) 1) *
        walkGenerator G v₀ r (Fin.last m).castSucc.castSucc (Fin.last (m + 1)).castSucc
          (Fin.last (m + 2)) *
        walkExtend G v₀ (PathAlgebra.blockSingle ⟨u', (G.mem_walkEndpoints_iff v₀).2 ⟨q.init⟩⟩
          (p₀.snoc q.adj_init_last.symm) q.init 1) =
      (r u * r u' / r t.1 ^ 2) • PathAlgebra.blockSingle t p q 1 := by
  intro u u'; ext s w z
  simp only [Pi.mul_apply, Matrix.mul_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    walkExtend_blockSingle_apply]
  have heq_of_init {x₁ x₂ : G.EndpointWalk v₀ (m + 2) s.1}
      (h : (x₁.init : Fin (m + 2) → V) = x₂.init) : x₁ = x₂ :=
    EndpointWalk.ext fun i ↦ Fin.lastCases (x₁.apply_last_eq.trans x₂.apply_last_eq.symm)
      (fun j ↦ by simpa only [EndpointWalk.init_apply] using congrFun h j) i
  by_cases hwz : (w.init : Fin (m + 2) → V) = p.init ∧ (z.init : Fin (m + 2) → V) = q.init
  · by_cases hst : s = t
    · subst hst; obtain rfl := heq_of_init hwz.1; obtain rfl := heq_of_init hwz.2
      let y₀ : G.EndpointWalk v₀ (m + 2) s.1 := (p₀.snoc w.adj_init_last.symm).snoc w.adj_init_last
      let y₀' : G.EndpointWalk v₀ (m + 2) s.1 := (p₀.snoc z.adj_init_last.symm).snoc z.adj_init_last
      have hy₀ : (y₀.init : Fin (m + 2) → V) = p₀.snoc w.adj_init_last.symm := by ext; simp [y₀]
      have hy₀' : (y₀'.init : Fin (m + 2) → V) = p₀.snoc z.adj_init_last.symm := by ext; simp [y₀']
      rw [Finset.sum_eq_single y₀' (fun _ _ hy' ↦ by
          rw [ite_eq_right fun h ↦ hy' (heq_of_init (h.1.trans hy₀'.symm)), mul_zero])
          (fun h ↦ (h (Finset.mem_univ _)).elim),
        Finset.sum_eq_single y₀ (fun _ _ hy ↦ by
          rw [ite_eq_right fun h ↦ hy (heq_of_init (h.2.trans hy₀.symm)), zero_mul])
          (fun h ↦ (h (Finset.mem_univ _)).elim),
        PathAlgebra.blockSingle_apply_same, Matrix.single_apply, ite_eq_left ⟨rfl, hy₀⟩,
        ite_eq_left ⟨hy₀', rfl⟩, ite_eq_left ⟨rfl, rfl⟩, one_mul, mul_one, mul_one,
        walkGenerator_apply]
      have hupd : (y₀' : Fin (m + 3) → V) = update (y₀ : Fin (m + 3) → V)
          (Fin.last (m + 1)).castSucc (y₀' (Fin.last (m + 1)).castSucc) := by
        simp only [y₀, y₀', EndpointWalk.coe_snoc, ← Fin.snoc_update,
          Fin.snoc_castSucc, Fin.snoc_last, Fin.update_snoc_last]
      rw [ite_eq_left ⟨by simp [y₀], hupd, by simpa [y₀, y₀'] using z.adj_init_last.symm⟩]
      simp [y₀, y₀', u, u']
    · rw [PathAlgebra.blockSingle_apply_of_ne hst, Matrix.zero_apply, mul_zero]
      refine Finset.sum_eq_zero fun _ _ ↦ ?_
      rw [Finset.sum_eq_zero fun y _ ↦ ?_, zero_mul]; split_ifs with hL
      · rw [one_mul, walkGenerator_apply, ite_eq_right]; rintro ⟨hyac, _, _⟩
        have hya : y (Fin.last m).castSucc.castSucc = t.1 := by
          simpa [EndpointWalk.coe_init, Fin.init] using congrFun hL.2 (Fin.last m).castSucc
        exact hst (Subtype.ext (y.apply_last_eq.symm.trans (hyac.symm.trans hya)))
      · rw [zero_mul]
  · have hrhs : PathAlgebra.blockSingle t p q (1 : K) s w z = 0 := by
      by_cases hst : s = t
      · subst hst; rw [PathAlgebra.blockSingle_apply_same, Matrix.single_apply,
          ite_eq_right fun ⟨rfl, rfl⟩ ↦ hwz ⟨rfl, rfl⟩]
      · simp [PathAlgebra.blockSingle_apply_of_ne hst]
    rw [hrhs, mul_zero]; refine Finset.sum_eq_zero fun _ _ ↦ ?_
    by_cases hw : (w.init : Fin (m + 2) → V) = p.init
    · rw [ite_eq_right fun h ↦ hwz ⟨hw, h.2⟩, mul_zero]
    · rw [Finset.sum_eq_zero fun _ _ ↦ by rw [ite_eq_right fun h ↦ hw h.1, zero_mul], zero_mul]
private theorem blockSingle_mem_walkRep_range_of_mem_walkEndpoints
    {m : ℕ} (ih : Function.Surjective (walkRep G v₀ hr hδ (n := m + 1)))
    (t : G.walkEndpoints v₀ (m + 2)) (ht : t.1 ∈ G.walkEndpoints v₀ m)
    (p q : G.EndpointWalk v₀ (m + 2) t.1) :
    PathAlgebra.blockSingle t p q (1 : K) ∈ (walkRep G v₀ hr hδ (n := m + 2)).range := by
  obtain ⟨p₀⟩ := (G.mem_walkEndpoints_iff v₀).1 ht
  let u := p (Fin.last (m + 1)).castSucc; let u' := q (Fin.last (m + 1)).castSucc
  obtain ⟨a, ha⟩ := ih (PathAlgebra.blockSingle ⟨u, (G.mem_walkEndpoints_iff v₀).2 ⟨p.init⟩⟩
    p.init (p₀.snoc p.adj_init_last.symm) 1)
  obtain ⟨b, hb⟩ := ih (PathAlgebra.blockSingle ⟨u', (G.mem_walkEndpoints_iff v₀).2 ⟨q.init⟩⟩
    (p₀.snoc q.adj_init_last.symm) q.init 1)
  let R := (walkRep G v₀ hr hδ (n := m + 2)).range
  have hprod : walkRep G v₀ hr hδ (strandIncl a * e δ (Fin.last m) * strandIncl b) ∈ R :=
    ⟨_, rfl⟩
  simp only [map_mul, walkRep_strandIncl, ha, hb, walkRep_e] at hprod
  change (_ * walkGenerator G v₀ r (Fin.last m).castSucc.castSucc (Fin.last (m + 1)).castSucc
    (Fin.last (m + 2)) * _) ∈ R at hprod
  rw [walkExtend_blockSingle_mul_walkGenerator_mul_walkExtend_blockSingle t p₀ p q] at hprod
  have hc : r u * r u' / r t.1 ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (hr u) (hr u')) (pow_ne_zero 2 (hr t.1))
  have hsmul := R.smul_mem hprod (r u * r u' / r t.1 ^ 2)⁻¹
  dsimp only [u, u'] at hc hsmul; rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hsmul
include hr hδ in
theorem walkRep_surjective {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) :
    ∀ n : ℕ, Function.Surjective (walkRep G v₀ hr hδ (n := n))
  | 0 => fun X ↦ ⟨algebraMap K _ (X ⟨v₀, by simp⟩ (EndpointWalk.zero G v₀)
      (EndpointWalk.zero G v₀)), by
    ext ⟨v, hv⟩ p q; obtain rfl : v = v₀ := by simpa using hv
    rw [Subsingleton.elim p (EndpointWalk.zero G v), Subsingleton.elim q (EndpointWalk.zero G v)]
    simp [Algebra.algebraMap_eq_smul_one]⟩
  | 1 => fun X ↦ by
    by_cases hne : (G.walkEndpoints v₀ 1).Nonempty
    · obtain ⟨v₁, hv₁⟩ := hne; obtain ⟨p₁⟩ := (G.mem_walkEndpoints_iff v₀).1 hv₁
      refine ⟨algebraMap K _ (X ⟨v₁, hv₁⟩ p₁ p₁), ?_⟩; ext ⟨v, hv⟩ p q
      obtain rfl : v = v₁ :=
        Finset.card_le_one.1 (G.card_walkEndpoints_one_le_one v₀ hf hf₀ hadj) v hv v₁ hv₁
      rw [Subsingleton.elim p p₁, Subsingleton.elim q p₁]; simp [Algebra.algebraMap_eq_smul_one]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact ⟨0, by ext ⟨v, hv⟩; exact False.elim (by simp [hne] at hv)⟩
  | m + 2 => fun X ↦ (walkRep G v₀ hr hδ).mem_range.1 <| by
    have ih := walkRep_surjective hf hf₀ hadj (m + 1)
    let R := (walkRep G v₀ hr hδ (n := m + 2)).range
    have hunit (t : G.walkEndpoints v₀ (m + 2)) (p q : G.EndpointWalk v₀ (m + 2) t.1) :
        PathAlgebra.blockSingle t p q (1 : K) ∈ R := by
      by_cases ht : t.1 ∈ G.walkEndpoints v₀ m
      · exact blockSingle_mem_walkRep_range_of_mem_walkEndpoints hr hδ ih t ht p q
      · have hft : f t.1 = m + 2 :=
          (p.forall_eq_or_exists_endpointWalk hf hf₀ hadj).elim
            (fun hfwd ↦ by simpa [p.apply_last_eq] using hfwd (Fin.last (m + 2)))
            (fun hne ↦ False.elim (ht ((G.mem_walkEndpoints_iff v₀).2 hne)))
        have : Subsingleton (G.EndpointWalk v₀ (m + 2) t.1) :=
          EndpointWalk.subsingleton_of_last_eq hf hf₀ hadj hft
        obtain rfl : p = q := Subsingleton.elim _ _
        have hmem_erase {s : G.walkEndpoints v₀ (m + 2)} (hst : s ≠ t) :
            s.1 ∈ G.walkEndpoints v₀ m := by
          by_contra hns; obtain ⟨ws⟩ := (G.mem_walkEndpoints_iff v₀).1 s.2
          refine (ws.forall_eq_or_exists_endpointWalk hf hf₀ hadj).elim (fun hfwd ↦ hst <|
            Subtype.ext <| hf <| (by simpa [ws.apply_last_eq] using hfwd (Fin.last (m + 2)) :
              f s.1 = m + 2).trans hft.symm) fun hne ↦ hns ((G.mem_walkEndpoints_iff v₀).2 hne)
        have h1 : (1 : PathAlgebra K G v₀ (m + 2)) = PathAlgebra.blockSingle t p p 1 +
            ∑ s ∈ Finset.univ.erase t,
              ∑ w : G.EndpointWalk v₀ (m + 2) s.1, PathAlgebra.blockSingle s w w 1 := by
          rw [PathAlgebra.one_eq_sum_blockSingle, ← Finset.add_sum_erase _ _ (Finset.mem_univ t),
            Fintype.sum_subsingleton _ p]
        rw [eq_sub_of_add_eq h1.symm]
        exact R.sub_mem R.one_mem <| R.sum_mem fun s hs ↦ R.sum_mem fun w _ ↦
          blockSingle_mem_walkRep_range_of_mem_walkEndpoints hr hδ ih s
            (hmem_erase (Finset.ne_of_mem_erase hs)) w w
    rw [X.eq_sum_blockSingle]
    exact R.sum_mem fun t _ ↦ R.sum_mem fun p _ ↦ R.sum_mem fun q _ ↦
      R.smul_mem (hunit t p q) (X t p q)
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
  have hwb : w (Fin.last (n + 1)).castSucc = u := by simp [w, p.apply_last_eq]
  have hwc : w (Fin.last (n + 2)) = v := by simp [w]
  by_cases hpv : p a' = v
  · have hac : w a'.castSucc = w (Fin.last (n + 2)) := by rw [hwa, hwc, hpv]
    have humem : u ∈ G.neighborFinset (w a'.castSucc) := by
      rw [SimpleGraph.mem_neighborFinset, hwa, hpv]; exact huv.symm
    rw [dite_eq_left hac, ite_eq_left hpv,
      Finset.sum_eq_single_of_mem ⟨u, humem⟩ (Finset.mem_attach _ _) fun x _ hxu ↦ by
        set w' := w.update (b := (Fin.last (n + 1)).castSucc) (by simp [ha']) (by simp) hac
          ((G.mem_neighborFinset _ _).1 x.2)
        conv_lhs => rw [← w'.snoc_init]
        rw [walkExtend_apply_snoc, dite_eq_right (by
          simp only [w', EndpointWalk.coe_update, update_self]
          exact fun h ↦ hxu (Subtype.ext h)), mul_zero],
      show w.update (b := (Fin.last (n + 1)).castSucc) (by simp [ha']) (by simp) hac
          ((G.mem_neighborFinset _ _).1 humem) = w from
        EndpointWalk.ext fun i ↦ by
          simp only [EndpointWalk.coe_update]; exact congrFun (update_eq_self_iff.2 hwb.symm) i,
      walkExtend_apply_snoc_same, PathAlgebra.blockAt_of_mem ((G.mem_walkEndpoints_iff v₀).2 ⟨p⟩),
      hwb]
    dsimp only; rw [hwa, hpv]; have := hr v; have := hr v₀; field_simp
  · rw [dite_eq_right (by rw [hwa, hwc]; exact hpv), ite_eq_right hpv, mul_zero]
theorem walkTrace_walkExtend_mul_walkGenerator (hr : ∀ v, r v ≠ 0) {n : ℕ}
    (X : PathAlgebra K G v₀ (n + 1)) {a b c : Fin (n + 3)}
    (ha : a.val = n) (hb : b.val = n + 1) (hc : c.val = n + 2) :
    walkTrace G v₀ r (walkExtend G v₀ X * walkGenerator G v₀ r a b c) = walkTrace G v₀ r X := by
  obtain ⟨a', rfl, ha'⟩ : ∃ a' : Fin (n + 2), a = a'.castSucc ∧ a'.val = n :=
    ⟨⟨n, by omega⟩, Fin.ext ha, rfl⟩
  obtain rfl : b = (Fin.last (n + 1)).castSucc := Fin.ext hb
  obtain rfl : c = Fin.last (n + 2) := Fin.ext hc
  have ha'l : a'.val + 1 = (Fin.last (n + 1)).val := by simp [ha']
  rw [walkTrace_mul_comm, walkTrace_eq_sum_walkEndpoints, walkTrace_eq_sum_walkEndpoints]
  let g (v u : V) : K := ∑ p : G.EndpointWalk v₀ (n + 1) u,
    if p a' = v then (r u / r v₀) ^ 2 * PathAlgebra.blockAt u X p p else 0
  have hblock {v : V} (hv : v ∈ G.walkEndpoints v₀ (n + 2)) :
      (r v / r v₀) ^ 2 *
          (PathAlgebra.blockAt v
            (walkGenerator G v₀ r a'.castSucc (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) *
              walkExtend G v₀ X)).trace = ∑ u ∈ G.neighborFinset v, g v u := by
    rw [PathAlgebra.blockAt_of_mem hv, Pi.mul_apply, Matrix.trace,
      G.sum_endpointWalk_succ v₀ (n + 1) v, Finset.mul_sum]
    simp_rw [Finset.mul_sum, Matrix.diag_apply, walkGenerator_mul_walkExtend_snoc_diag hr X ha' hv]
    exact (G.neighborFinset v).sum_attach fun u ↦ g v u
  rw [Finset.sum_congr rfl fun _ hv ↦ hblock hv,
    G.sum_walkEndpoints_succ v₀ (n + 1) g fun _ u hu ↦ by
      have := not_nonempty_iff.1 ((G.mem_walkEndpoints_iff v₀).not.1 hu)
      exact Fintype.sum_empty _]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  dsimp only [g]; rw [Finset.sum_comm, Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hadj : p a' ∈ G.neighborFinset u := by
    rw [SimpleGraph.mem_neighborFinset]; have h := (p.adj ha'l).symm; rwa [p.apply_last_eq] at h
  rw [Finset.sum_eq_single_of_mem (p a') hadj fun _ _ hvp ↦ ite_eq_right hvp.symm,
    ite_eq_left rfl, Matrix.diag_apply]
variable (hr : ∀ v, r v ≠ 0) {δ : K} (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
variable (G v₀) in
theorem isMarkovTrace_walkTrace :
    IsMarkovTrace K δ (fun n ↦ (walkTrace G v₀ r).comp (walkRep G v₀ hr hδ (n := n)).toLinearMap) :=
  ⟨fun _ ↦ by simp [walkTrace_one hr hδ], fun _ _ _ ↦ by simp [walkTrace_mul_comm],
    fun _ x ↦ by simp [walkRep_strandIncl, walkTrace_walkExtend hδ],
    fun _ x ↦ by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, walkRep_strandIncl,
        walkRep_e]
      exact walkTrace_walkExtend_mul_walkGenerator hr _ rfl rfl rfl⟩
variable (G v₀) in
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
      Finset.sum_image fun _ _ _ _ h ↦ DFunLike.coe_injective h]
    · exact Finset.sum_congr rfl fun _ _ ↦ by rw [hx, hy]
    · intro u _ hu
      have hnot : ¬((G.IsWalkFrom v₀ ⇑p ↔ G.IsWalkFrom v₀ u) ∧
          p (Fin.last n) = u (Fin.last n)) := fun ⟨hp, hlast⟩ ↦
        hu (Finset.mem_image.2 ⟨⟨u, hp.1 p.isWalkFrom, hlast.symm.trans p.apply_last_eq⟩,
          Finset.mem_univ _, rfl⟩)
      rw [pathRep_apply_eq_zero hr hδ x hnot, zero_mul]
theorem walkTrace_walkRep_eq_pathTrace {n : ℕ} (x : TemperleyLieb K δ n) :
    walkTrace G v₀ r (walkRep G v₀ hr hδ x) = pathTrace G v₀ hr hδ x :=
  ((isMarkovTrace_pathTrace G v₀ hr hδ).eq_walkTrace_comp_walkRep G v₀ hr hδ n x).symm
end FiniteGraph
end TauCeti.TemperleyLieb
