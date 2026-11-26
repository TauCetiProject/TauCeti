/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen, The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.WithTop
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Strict bounds, monotone approximations, and continuous homomorphisms in `ℝ≥0`

A strict bound `c < a` persists for `c * C ^ n` when `C` is slightly greater than one. This
absorbs a small multiplicative loss in estimates with a fixed natural power.

The truncation `Real.toNNReal` maps `𝓝[>] 0` into `𝓝[≠] 0`
(`Real.tendsto_toNNReal_nhdsGT_zero_nhdsNE`), so a limit as a nonnegative scale `γ → 0` with
`γ ≠ 0` can be read off along a real parameter `y → 0⁺`.

A continuous homomorphism from a topological group to `ℝ≥0` is trivial on every compact subgroup
(`MonoidHom.eq_one_of_mem_of_isCompact`).

We also collect elementary monotone approximations in `ℝ≥0` and `WithTop ℝ≥0`:
- the truncated left shifts `t - 1 / (n + 1 : ℝ≥0)` are monotone and converge to `t` both in `ℝ≥0`
  and after coercion to `WithTop ℝ≥0`;
- strict inequalities `x < (t : WithTop ℝ≥0)` are witnessed by positive reciprocal cushions
  `x + 1 / (k + 1) ≤ t`, and `{0}` is the complement of the union of positive reciprocal rays
  `Ici (1 / (k + 1))`.

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Filter Set
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

/-- Truncated left shifts `t - 1 / (n + 1)` form a monotone sequence in `ℝ≥0`. -/
theorem monotone_tsub_one_div_add_one (t : ℝ≥0) :
    Monotone (fun n : ℕ ↦ t - 1 / (n + 1 : ℝ≥0)) := by
  intro m n hmn
  refine tsub_le_tsub_left (one_div_le_one_div_of_le (by positivity) ?_) t
  exact add_le_add_left (Nat.cast_le.mpr hmn) 1

/-- Truncated left shifts `t - 1 / (n + 1)` converge to `t` in `ℝ≥0`. -/
theorem tendsto_tsub_one_div_add_one (t : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ t - 1 / (n + 1 : ℝ≥0)) atTop (𝓝 t) := by
  simpa only [tsub_zero] using
    tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))

/-- Truncated left shifts `t - 1 / (n + 1)` coerced to `WithTop ℝ≥0` converge to `t`. -/
theorem tendsto_coe_tsub_one_div_add_one (t : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ ((t - 1 / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0))
      atTop (𝓝 (t : WithTop ℝ≥0)) :=
  (WithTop.continuous_coe.tendsto t).comp (tendsto_tsub_one_div_add_one t)

/-- A strict upper bound `x < (t : WithTop ℝ≥0)` is witnessed by adding a reciprocal step
`1 / (k + 1)`. -/
theorem lt_coe_iff_exists_add_one_div_add_one_le {x : WithTop ℝ≥0} {t : ℝ≥0} :
    x < (t : WithTop ℝ≥0) ↔
      ∃ k : ℕ, x + ((1 / (k + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) := by
  cases x with
  | top =>
    exact ⟨fun h ↦ (not_top_lt h).elim,
      fun ⟨_, hk⟩ ↦ (WithTop.coe_ne_top (top_le_iff.mp (le_self_add.trans hk))).elim⟩
  | coe u =>
    have htend : Tendsto (fun k : ℕ ↦ u + 1 / (k + 1 : ℝ≥0)) atTop (𝓝 u) := by
      simpa only [add_zero] using
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
    have hgt (k : ℕ) : u < u + 1 / (k + 1 : ℝ≥0) := lt_add_of_pos_right u (by positivity)
    have hIoi := iUnion_Ici_eq_Ioi_of_lt_of_tendsto hgt htend
    simp only [WithTop.coe_lt_coe, ← WithTop.coe_add, WithTop.coe_le_coe]
    simpa only [mem_iUnion, mem_Ici, mem_Ioi] using (Set.ext_iff.mp hIoi t).symm

/-- The singleton `{0}` in `ℝ≥0` is the complement of the union of positive reciprocal closed rays
`Ici (1 / (k + 1))`. -/
theorem singleton_zero_eq_compl_iUnion_Ici_one_div_add_one :
    ({(0 : ℝ≥0)} : Set ℝ≥0) = (⋃ k : ℕ, Ici (1 / (k + 1 : ℝ≥0)))ᶜ := by
  rw [iUnion_Ici_eq_Ioi_of_lt_of_tendsto (fun _ ↦ by positivity)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)), compl_Ioi, ← bot_eq_zero, Iic_bot]

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

end
