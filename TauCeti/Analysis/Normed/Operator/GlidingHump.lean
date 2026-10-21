/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Tower

/-!
# The gliding hump along a tower of Banach spaces

Let `P n : E (n + 1) → E n` be continuous linear maps between Banach spaces and let
`U n : E n → G` be continuous linear maps with `U (n + 1) = U n ∘ P n`. If vectors `y n : E n`
are so small that their images under the tower composites `E (m + k) → E m` decay
geometrically in `k`, then the series `∑ U n (y n)` converges, and every tail of it factors
through `U m` with a small preimage. This is the summation step of gliding-hump arguments, such
as the proof of the stability lemma for separating spaces. The selection step chooses the humps:
a discontinuous linear map sends arbitrarily small vectors to vectors of arbitrarily large norm.

## Main declarations

* `LinearMap.exists_norm_le_le_norm_of_not_continuous`: small vectors with large images under a
  discontinuous linear map.
* `TauCeti.exists_norm_le_and_apply_eq_sub_sum`: the tails of the gliding-hump series factor
  through the maps `U m` with small preimages.
-/

public section

namespace LinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A discontinuous linear map between normed spaces sends arbitrarily small vectors to vectors
of arbitrarily large norm. -/
theorem exists_norm_le_le_norm_of_not_continuous (f : E →ₗ[𝕜] F) (hf : ¬Continuous f) {ε : ℝ}
    (hε : 0 < ε) (M : ℝ) : ∃ y, ‖y‖ ≤ ε ∧ M ≤ ‖f y‖ := by
  by_contra! h
  have hM : 0 < M := (norm_nonneg _).trans_lt (h 0 (by simpa using hε.le))
  obtain ⟨c, hc⟩ := NontriviallyNormedField.non_trivial (α := 𝕜)
  have hc0 : 0 < ‖c‖ := one_pos.trans hc
  have hb : ∀ x, ‖f x‖ ≤ M * ‖c‖ / ε * ‖x‖ := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    refine SemilinearMapClass.bound_of_shell_semi_normed f hε hc (fun x hx hx' ↦ ?_)
      (norm_ne_zero_iff.2 hx)
    calc ‖f x‖ ≤ M := (h x hx'.le).le
      _ = M * ‖c‖ / ε * (ε / ‖c‖) := by field_simp
      _ ≤ M * ‖c‖ / ε * ‖x‖ := by gcongr
  exact hf (AddMonoidHomClass.continuous_of_bound f _ hb)

end LinearMap

namespace TauCeti

variable {R G : Type*} [Semiring R] {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, Module R (E n)] [∀ n, CompleteSpace (E n)] [NormedAddCommGroup G] [Module R G]
  (P : ∀ n, E (n + 1) →L[R] E n) {U : ∀ n, E n →L[R] G}

/-- **The gliding hump.** If the vectors `y n : E n` are small enough that their images under
the tower composites `E (m + k) → E m` are dominated by `b m * (1 / 2) ^ k`, then the series
`∑ U n (y n)` converges to some `x`, and every tail of it factors through `U m` with a preimage
of norm at most `2 * b m`. -/
theorem exists_norm_le_and_apply_eq_sub_sum (hU : ∀ n, U (n + 1) = (U n).comp (P n))
    (y : ∀ n, E n) (b : ℕ → ℝ) (hb : ∀ m k, ‖towerComp P m k (y (m + k))‖ ≤ b m * (1 / 2) ^ k) :
    ∃ x : G, ∀ m, ∃ z : E m, ‖z‖ ≤ 2 * b m ∧
      U m z = x - ∑ k ∈ Finset.range m, U k (y k) := by
  have hsum : ∀ m, Summable fun k ↦ towerComp P m k (y (m + k)) := fun m ↦
    .of_norm_bounded (summable_geometric_two.mul_left (b m)) (hb m)
  set g : ℕ → G := fun j ↦ U j (y j)
  have hg : ∀ m, (fun k ↦ g (k + m)) = fun k ↦ U m (towerComp P m k (y (m + k))) := by
    intro m
    ext k
    rw [apply_towerComp P hU, Nat.add_comm k m]
  have hgs : Summable g := (summable_nat_add_iff 0).1 (hg 0 ▸ (U 0).summable (hsum 0))
  refine ⟨∑' k, g k, fun m ↦ ⟨∑' k, towerComp P m k (y (m + k)), ?_, ?_⟩⟩
  · rw [mul_comm]
    exact tsum_of_norm_bounded (hasSum_geometric_two.mul_left (b m)) (hb m)
  · rw [(U m).map_tsum (hsum m), ← hg, ← hgs.sum_add_tsum_nat_add m, add_sub_cancel_left]

end TauCeti
