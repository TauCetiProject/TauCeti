/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Pairing
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Flattening finitely supported sequences of finite tuples

`TauCeti.flattenFinsupp 𝕜 k` embeds `ℕ →₀ (Fin k → 𝕜)` linearly into `ℕ →₀ 𝕜` via Mathlib's
square-shell pairing function `(n, i) ↦ Nat.pair n i.1`, sending sequences supported in
`Finset.range N` into `Finset.range (max N k ^ 2)`. This flattens countable families of finite-rank
block coordinates on vector bundles into `ℕ →₀ 𝕜`-valued classifying coordinates while preserving
uniform initial-segment support bounds.
-/

public noncomputable section

namespace TauCeti
private theorem pair_fin_injective (k : ℕ) :
    Function.Injective (fun p : ℕ × Fin k ↦ Nat.pair p.1 p.2.val) := fun p q hpq ↦ by
  have h := congrArg Nat.unpair hpq; rw [Nat.unpair_pair, Nat.unpair_pair, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.ext h.2)

/-- The `𝕜`-linear injection sending `f : ℕ →₀ (Fin k → 𝕜)` to the finitely supported sequence
with value `f n i` at `Nat.pair n i.1` and `0` outside `{Nat.pair n i.1 | n : ℕ, i : Fin k}`. -/
def flattenFinsupp (𝕜 : Type*) [Semiring 𝕜] (k : ℕ) : (ℕ →₀ (Fin k → 𝕜)) →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  (Finsupp.lmapDomain 𝕜 𝕜 fun p : ℕ × Fin k ↦ Nat.pair p.1 p.2.val).comp <|
    (Finsupp.curryLinearEquiv 𝕜).symm.toLinearMap.comp
      (Finsupp.mapRange.linearEquiv (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin k)).symm).toLinearMap
theorem flattenFinsupp_apply_pair {𝕜 : Type*} [Semiring 𝕜] (k : ℕ) (f : ℕ →₀ (Fin k → 𝕜))
    (n : ℕ) (i : Fin k) : flattenFinsupp 𝕜 k f (Nat.pair n i.val) = f n i := by
  simp only [flattenFinsupp, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.lmapDomain_apply]
  exact (Finsupp.mapDomain_apply_of_injective (pair_fin_injective k) _ (n, i)).trans (by simp)
@[simp] theorem flattenFinsupp_apply {𝕜 : Type*} [Semiring 𝕜] (k : ℕ) (f : ℕ →₀ (Fin k → 𝕜))
    (m : ℕ) :
    flattenFinsupp 𝕜 k f m = if h : m.unpair.2 < k then f m.unpair.1 ⟨m.unpair.2, h⟩ else 0 := by
  split_ifs with hk
  · conv_lhs => rw [← Nat.pair_unpair m]
    exact flattenFinsupp_apply_pair k f m.unpair.1 ⟨m.unpair.2, hk⟩
  · simp only [flattenFinsupp, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Finsupp.lmapDomain_apply]
    refine Finsupp.mapDomain_of_notMem_range _ _ fun ⟨⟨_, i⟩, hm⟩ ↦ hk ?_
    simpa only [← hm, Nat.unpair_pair] using i.isLt
/-- Flattening `ℕ →₀ (Fin k → 𝕜)` into `ℕ →₀ 𝕜` is injective for every `k : ℕ`. -/
theorem flattenFinsupp_injective (𝕜 : Type*) [Semiring 𝕜] (k : ℕ) :
    Function.Injective (flattenFinsupp 𝕜 k) :=
  (Finsupp.mapDomain_injective (pair_fin_injective k)).comp <|
    (Finsupp.curryLinearEquiv 𝕜).symm.injective.comp
      (Finsupp.mapRange.linearEquiv (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin k)).symm).injective
/-- Sequences supported in `Finset.range N` flatten into `Finset.range (max N k ^ 2)`. -/
theorem support_flattenFinsupp_subset_range {𝕜 : Type*} [Semiring 𝕜] {k N : ℕ}
    {f : ℕ →₀ (Fin k → 𝕜)} (hf : f.support ⊆ Finset.range N) :
    (flattenFinsupp 𝕜 k f).support ⊆ Finset.range (max N k ^ 2) := fun m hm ↦ by
  rw [Finsupp.mem_support_iff, flattenFinsupp_apply] at hm; split_ifs at hm with hk
  · have hn : m.unpair.1 < N := Finset.mem_range.1 <| hf <|
      Finsupp.mem_support_iff.2 fun h0 ↦ hm (by simp [h0])
    have hmax : max m.unpair.1 m.unpair.2 + 1 ≤ max N k :=
      Nat.succ_le_of_lt (max_lt (hn.trans_le (le_max_left N k)) (hk.trans_le (le_max_right N k)))
    rw [Finset.mem_range, ← Nat.pair_unpair m]
    exact (Nat.pair_lt_max_add_one_sq _ _).trans_le (Nat.pow_le_pow_left hmax 2)
  · exact (hm rfl).elim
end TauCeti
