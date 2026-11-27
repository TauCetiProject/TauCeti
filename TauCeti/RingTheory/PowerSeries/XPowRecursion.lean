/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Recursions `b k = f k + X ^ d k * b (k + 1)` of power series

Let `f : ℕ → R⟦X⟧` be a sequence of power series and `d : ℕ → ℕ` a sequence of positive exponents.
The recursion

`b k = f k + X ^ d k * b (k + 1)`

runs forward in `k`, so it cannot be solved by induction. It nevertheless has exactly one
solution (`PowerSeries.existsUnique_forall_eq_add_X_pow_mul`), the `X`-adically convergent series

`b k = ∑ j, X ^ (d k + ⋯ + d (k + j - 1)) * f (k + j)`,

whose `j`-th term has order at least `j`. Uniqueness is the vanishing of the solutions of the
homogeneous recursion `b k = X ^ d k * b (k + 1)`
(`PowerSeries.eq_zero_of_forall_eq_X_pow_mul`): each `b k` is divisible by every power of `X`.

Such recursions arise in chain complexes over `𝔽[[U]]` whose differential relates neighbouring
generators by powers of `U` that grow along the chain, as in the completed lattice complexes of
plumbings: solving them is the step that has no polynomial counterpart.

## Main results

* `PowerSeries.eq_zero_of_forall_eq_X_pow_mul`: the homogeneous recursion has only the zero
  solution.
* `PowerSeries.existsUnique_forall_eq_add_X_pow_mul`: the recursion has a unique solution.
-/

public section

open Finset
open scoped PowerSeries.WithPiTopology

namespace PowerSeries

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- **The homogeneous recursion has only the zero solution.** If `b k = X ^ d k * b (k + 1)` with
every `d k` positive, then by induction every `b k` is divisible by every power of `X`, so it
vanishes. -/
theorem eq_zero_of_forall_eq_X_pow_mul {b : ℕ → R⟦X⟧} {d : ℕ → ℕ} (hd : ∀ k, d k ≠ 0)
    (hb : ∀ k, b k = X ^ d k * b (k + 1)) (k : ℕ) : b k = 0 := by
  have hdvd : ∀ n k, (X : R⟦X⟧) ^ n ∣ b k := by
    intro n
    induction n with
    | zero => exact fun _ => one_dvd _
    | succ n ih =>
      intro k
      rw [hb k, pow_succ']
      exact mul_dvd_mul (dvd_pow_self X (hd k)) (ih (k + 1))
  ext n
  simpa using X_pow_dvd_iff.1 (hdvd (n + 1) k) n n.lt_succ_self

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- **The recursion `b k = f k + X ^ d k * b (k + 1)` has a unique solution** when every exponent
`d k` is positive. The solution is the `X`-adically convergent series
`b k = ∑ j, X ^ (d k + ⋯ + d (k + j - 1)) * f (k + j)`. -/
theorem existsUnique_forall_eq_add_X_pow_mul (f : ℕ → R⟦X⟧) {d : ℕ → ℕ} (hd : ∀ k, d k ≠ 0) :
    ∃! b : ℕ → R⟦X⟧, ∀ k, b k = f k + X ^ d k * b (k + 1) := by
  -- Sum the series in the topology of coefficientwise convergence, for the discrete topology
  -- on `R`.
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  -- The exponent of the `j`-th term of the solution at `k`.
  set e : ℕ → ℕ → ℕ := fun k j => ∑ i ∈ range j, d (k + i) with he
  have hej : ∀ k j, j ≤ e k j := fun k j =>
    calc j = ∑ _i ∈ range j, 1 := by simp
      _ ≤ e k j := sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.2 (hd _)
  have he_succ : ∀ k j, e k (j + 1) = d k + e (k + 1) j := fun k j => by
    simp only [he, sum_range_succ', add_zero]
    rw [add_comm]
    exact congrArg _ (sum_congr rfl fun i _ => by rw [add_assoc, add_comm i 1])
  -- Only the terms with `j ≤ n` contribute to the coefficient of `X ^ n`.
  have hsum : ∀ k, Summable fun j => (X : R⟦X⟧) ^ e k j * f (k + j) := fun k => by
    rw [WithPiTopology.summable_iff_summable_coeff]
    intro n
    refine summable_of_hasFiniteSupport <| (Set.finite_Iic n).subset fun j hj => ?_
    rw [Function.mem_support, coeff_X_pow_mul'] at hj
    split_ifs at hj with h
    · exact (hej k j).trans h
    · exact absurd rfl hj
  obtain ⟨b₀, hb₀⟩ : ∃ b : ℕ → R⟦X⟧, ∀ k, b k = f k + X ^ d k * b (k + 1) := by
    refine ⟨fun k => ∑' j, X ^ e k j * f (k + j), fun k => ?_⟩
    dsimp only
    rw [(hsum k).tsum_eq_zero_add, ← (hsum (k + 1)).tsum_mul_left]
    congr 1
    · simp [he]
    · refine tsum_congr fun j => ?_
      rw [he_succ, pow_add, mul_assoc, show k + (j + 1) = k + 1 + j by omega]
  -- The difference of two solutions solves the homogeneous recursion.
  refine ⟨b₀, hb₀, fun b hb => funext fun k => sub_eq_zero.1 <|
    eq_zero_of_forall_eq_X_pow_mul (b := fun k => b k - b₀ k) hd (fun k => ?_) k⟩
  rw [hb k, hb₀ k]
  ring

end CommRing

end PowerSeries
