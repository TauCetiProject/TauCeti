/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Decompositions of the complete graph into bicliques and the Graham–Pollak theorem

A biclique decomposition of the complete graph on a vertex type `V` consists of `m` complete
bipartite graphs, the `k`-th with sides `X k` and `Y k`, whose edge sets partition the edges of
the complete graph: every pair of distinct vertices is joined in exactly one of them.

The Graham–Pollak theorem says that this needs at least `n - 1` bicliques when `V` has `n`
vertices. The proof given here is Tverberg's. For real numbers `x v` indexed by the vertices, a
decomposition expresses the sum of the products `x u * x v` over the edges as the sum over `k` of
`(∑ u ∈ X k, x u) * (∑ v ∈ Y k, x v)`. If there were at most `n - 2` bicliques, the `m + 1`
linear equations `∑ v ∈ Y k, x v = 0` and `∑ v, x v = 0` in `n` unknowns would have a nonzero
solution, for which the identity would give `∑ v, x v ^ 2 = 0`.

## Main definitions

* `TauCeti.IsBicliqueDecomposition`: the families `X` and `Y` are the sides of a biclique
  decomposition of the complete graph.

## Main statements

* `TauCeti.IsBicliqueDecomposition.two_mul_sum_mul_sum`: the quadratic identity of a
  decomposition, over any commutative ring.
* `TauCeti.card_le_of_isBicliqueDecomposition`: the Graham–Pollak theorem.

## References

* Jiří Matoušek, *Thirty-three Miniatures: Mathematical and Algorithmic Applications of Linear
  Algebra*, Student Mathematical Library 53, American Mathematical Society, 2010, Miniature 8,
  where the theorem is attributed to Graham and Pollak and the proof to Tverberg.
-/

public section

open Finset

namespace TauCeti

variable {V : Type*} {m : ℕ} {X Y : Fin m → Finset V}

/-- The families `X` and `Y` are the sides of a decomposition of the complete graph on `V` into
`m` complete bipartite graphs: `X k` and `Y k` are disjoint for every `k`, and any two distinct
vertices are joined in exactly one of the bicliques, that is, there is exactly one `k` for which
one of them lies in `X k` and the other in `Y k`. A side may be empty. -/
def IsBicliqueDecomposition (X Y : Fin m → Finset V) : Prop :=
  (∀ k, Disjoint (X k) (Y k)) ∧
    ∀ u v : V, u ≠ v → ∃! k, (u ∈ X k ∧ v ∈ Y k) ∨ (v ∈ X k ∧ u ∈ Y k)

theorem isBicliqueDecomposition_iff :
    IsBicliqueDecomposition X Y ↔ (∀ k, Disjoint (X k) (Y k)) ∧
      ∀ u v : V, u ≠ v → ∃! k, (u ∈ X k ∧ v ∈ Y k) ∨ (v ∈ X k ∧ u ∈ Y k) :=
  Iff.rfl

namespace IsBicliqueDecomposition

/-- The two sides of each biclique of a decomposition are disjoint. -/
theorem disjoint (h : IsBicliqueDecomposition X Y) (k : Fin m) : Disjoint (X k) (Y k) :=
  h.1 k

/-- Two distinct vertices are joined in exactly one biclique of a decomposition. -/
theorem existsUnique (h : IsBicliqueDecomposition X Y) {u v : V} (huv : u ≠ v) :
    ∃! k, (u ∈ X k ∧ v ∈ Y k) ∨ (v ∈ X k ∧ u ∈ Y k) :=
  h.2 u v huv

/-- Exchanging the two sides of every biclique of a decomposition gives a decomposition. -/
theorem symm (h : IsBicliqueDecomposition X Y) : IsBicliqueDecomposition Y X :=
  ⟨fun k ↦ (h.disjoint k).symm, fun _ _ huv ↦ by
    simpa only [and_comm] using h.existsUnique huv.symm⟩

/-- In a biclique decomposition, the number of bicliques in which `u` lies on the first side and
`v` on the second, plus the number of those in which `v` lies on the first side and `u` on the
second, is `1` if `u` and `v` are distinct and `0` if they are equal. -/
private theorem sum_ite_add_ite [DecidableEq V] (h : IsBicliqueDecomposition X Y) (R : Type*)
    [NonAssocSemiring R] (u v : V) :
    ∑ k, ((if u ∈ X k ∧ v ∈ Y k then (1 : R) else 0) + if v ∈ X k ∧ u ∈ Y k then 1 else 0) =
      if u = v then 0 else 1 := by
  split_ifs with huv
  · subst huv
    have hk (k : Fin m) : ¬ (u ∈ X k ∧ u ∈ Y k) := fun hh ↦
      disjoint_left.mp (h.disjoint k) hh.1 hh.2
    simp [hk]
  · obtain ⟨k, hk, hk'⟩ := h.existsUnique huv
    rw [sum_eq_single k (fun j _ hjk ↦ ?_) (by simp)]
    · rcases hk with hk | hk
      · have hn : ¬ (v ∈ X k ∧ u ∈ Y k) := fun hh ↦ disjoint_left.mp (h.disjoint k) hk.1 hh.2
        simp [hk, hn]
      · have hn : ¬ (u ∈ X k ∧ v ∈ Y k) := fun hh ↦ disjoint_left.mp (h.disjoint k) hh.1 hk.2
        simp [hk, hn]
    · have hj := not_or.mp fun hh ↦ hjk (hk' j hh)
      simp [hj.1, hj.2]

/-- The quadratic identity of a biclique decomposition: twice the sum over the bicliques of the
product of the sums of `x` over the two sides is the sum of the products `x u * x v` over the
ordered pairs of distinct vertices, that is, `(∑ v, x v) ^ 2 - ∑ v, x v ^ 2`. -/
theorem two_mul_sum_mul_sum [Fintype V] (h : IsBicliqueDecomposition X Y) {R : Type*}
    [CommRing R] (x : V → R) :
    2 * ∑ k, (∑ u ∈ X k, x u) * ∑ v ∈ Y k, x v = (∑ v, x v) ^ 2 - ∑ v, x v ^ 2 := by
  classical
  have key (u v : V) : ∑ k, ((if u ∈ X k ∧ v ∈ Y k then x u * x v else 0) +
      if v ∈ X k ∧ u ∈ Y k then x u * x v else 0) = if u = v then 0 else x u * x v := by
    simpa [sum_mul, add_mul] using congrArg (· * (x u * x v)) (h.sum_ite_add_ite R u v)
  have h1 (k : Fin m) : (∑ u ∈ X k, x u) * ∑ v ∈ Y k, x v =
      ∑ u, ∑ v, if u ∈ X k ∧ v ∈ Y k then x u * x v else 0 := by
    simp [sum_mul_sum, ite_and]
  have h2 (k : Fin m) : (∑ u ∈ X k, x u) * ∑ v ∈ Y k, x v =
      ∑ u, ∑ v, if v ∈ X k ∧ u ∈ Y k then x u * x v else 0 := by
    rw [h1, sum_comm]
    simp only [mul_comm]
  calc 2 * ∑ k, (∑ u ∈ X k, x u) * ∑ v ∈ Y k, x v
      = ∑ k, ((∑ u, ∑ v, if u ∈ X k ∧ v ∈ Y k then x u * x v else 0) +
          ∑ u, ∑ v, if v ∈ X k ∧ u ∈ Y k then x u * x v else 0) := by
        rw [two_mul, ← sum_add_distrib]
        exact sum_congr rfl fun k _ ↦ by rw [← h1, ← h2]
    _ = ∑ u, ∑ v, if u = v then 0 else x u * x v := by
        simp only [← sum_add_distrib]
        rw [sum_comm]
        refine sum_congr rfl fun u _ ↦ ?_
        rw [sum_comm]
        exact sum_congr rfl fun v _ ↦ key u v
    _ = (∑ v, x v) ^ 2 - ∑ v, x v ^ 2 := by
        have hite (u v : V) : (if u = v then 0 else x u * x v) =
            x u * x v - if u = v then x u * x v else 0 := by split_ifs <;> simp
        simp only [hite, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, pow_two, sum_mul_sum]

end IsBicliqueDecomposition

/-- **The Graham–Pollak theorem.** A decomposition of the complete graph on `n` vertices into
`m` complete bipartite graphs has `n ≤ m + 1`, that is, at least `n - 1` bicliques. -/
theorem card_le_of_isBicliqueDecomposition [Fintype V] (h : IsBicliqueDecomposition X Y) :
    Fintype.card V ≤ m + 1 := by
  by_contra! hlt
  -- The linear map recording the sums over the second sides and the total sum.
  let L : (V → ℝ) →ₗ[ℝ] (Fin m → ℝ) × ℝ :=
    (LinearMap.pi fun k ↦ ∑ v ∈ Y k, LinearMap.proj v).prod (∑ v, LinearMap.proj v)
  -- It maps a space of dimension `n` to one of dimension `m + 1 < n`, so it has a kernel:
  -- `simp` computes the two dimensions.
  obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) (by simpa using hlt))
  have hY (k : Fin m) : ∑ v ∈ Y k, x v = 0 := by
    simpa [L] using congrFun (congrArg Prod.fst (LinearMap.mem_ker.mp hxL)) k
  have hsum : ∑ v, x v = 0 := by simpa [L] using congrArg Prod.snd (LinearMap.mem_ker.mp hxL)
  have hsq : ∑ v, x v ^ 2 = 0 := by simpa [hY, hsum] using h.two_mul_sum_mul_sum x
  exact hx0 (funext fun v ↦ (sum_sq_eq_zero_iff _ _).mp hsq v (mem_univ v))

end TauCeti
