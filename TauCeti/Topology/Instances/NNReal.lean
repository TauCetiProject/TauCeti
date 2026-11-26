/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Strict bounds near one in `ℝ≥0` and continuous homomorphisms to `ℝ≥0`

A strict bound `c < a` persists for `c * C ^ n` when `C` is slightly greater than one. This
absorbs a small multiplicative loss in estimates with a fixed natural power.

The truncation `Real.toNNReal` maps `𝓝[>] 0` into `𝓝[≠] 0`
(`Real.tendsto_toNNReal_nhdsGT_zero_nhdsNE`), so a limit as a nonnegative scale `γ → 0` with
`γ ≠ 0` can be read off along a real parameter `y → 0⁺`.

A continuous homomorphism from a topological group to `ℝ≥0` is trivial on every compact subgroup
(`MonoidHom.eq_one_of_mem_of_isCompact`).

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Filter
open scoped NNReal Topology

namespace NNReal

/-- A strict coefficient bound persists after multiplication by a fixed natural power of some
factor greater than one. -/
theorem exists_one_lt_mul_pow_lt (c : ℝ≥0) {a : ℝ≥0} (hca : c < a) (n : ℕ) :
    ∃ C : ℝ≥0, 1 < C ∧ c * C ^ n < a := by
  have hcont : ContinuousAt (fun C : ℝ≥0 ↦ c * C ^ n) 1 := by fun_prop
  have hnear : ∀ᶠ C in 𝓝 (1 : ℝ≥0), c * C ^ n < a :=
    hcont.eventually_lt_const (by simpa only [one_pow, mul_one] using hca)
  obtain ⟨C, hCa, hC⟩ :=
    ((hnear.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists
      (f := 𝓝[>] (1 : ℝ≥0))
  exact ⟨C, hC, hCa⟩

end NNReal

/-- As `y → 0⁺` in `ℝ`, `y.toNNReal` tends to `0` in `ℝ≥0` while staying nonzero. -/
theorem Real.tendsto_toNNReal_nhdsGT_zero_nhdsNE :
    Tendsto Real.toNNReal (𝓝[>] 0) (𝓝[≠] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_real_toNNReal.tendsto' 0 0 (by simp)).mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun _ hy ↦ (Real.toNNReal_pos.2 hy).ne'⟩

/-- A continuous homomorphism `f : H →* ℝ≥0` is trivial on every compact subgroup: its image is
compact, hence bounded, and a value `≠ 1` would have unbounded powers or unbounded inverse
powers. -/
theorem MonoidHom.eq_one_of_mem_of_isCompact {H : Type*} [Group H] [TopologicalSpace H]
    (f : H →* ℝ≥0) (hf : Continuous f) {K : Subgroup H} (hK : IsCompact (K : Set H)) {k : H}
    (hk : k ∈ K) : f k = 1 := by
  obtain ⟨M, hM⟩ := (hK.image hf).isBounded.bddAbove
  have hbdd (x : H) (hx : x ∈ K) : ¬ 1 < f x := fun h1 => by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h1
    exact hn.not_ge <| hM ⟨x ^ n, K.pow_mem hx n, map_pow _ _ _⟩
  have hpos : 0 < f k := pos_iff_ne_zero.mpr ((Group.isUnit k).map f).ne_zero
  refine le_antisymm (not_lt.mp (hbdd k hk)) (not_lt.mp fun h => hbdd k⁻¹ (K.inv_mem hk) ?_)
  rw [map_inv]
  exact one_lt_inv_iff₀.mpr ⟨hpos, h⟩
