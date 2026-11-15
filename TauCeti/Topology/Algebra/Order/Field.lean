/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Order.Field

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Ratios, reciprocals of vanishing powers, one-sided bounds and eventual positivity

Mathlib's `Mathlib/Topology/Algebra/Order/Field.lean` proves
`tendsto_bdd_div_atTop_nhds_zero`: a numerator confined to a fixed interval, divided by a
denominator that diverges to `atTop`, tends to `0`. This file records the companion statement
for a numerator that is *not* bounded but instead tracks the denominator: if `f` agrees with `g`
up to a two-sided additive bounded error and `g` diverges, then `f / g` tends to `1`.

It also records that the reciprocal of a positive power of `x - a` diverges to `atTop` as `x`
tends to `a` from the right, and likewise for `a - x` from the left. These are the one-sided
blow-ups of `tendsto_inv_nhdsGT_zero` along a vanishing power, and their consequence that
`x / (1 - x)` diverges as `x` tends to `1` from the left. It records the one-sided bound
`x ^ 2 < 1` for `x` sufficiently close to `1` from below. Finally, it records that `t f + g` is
eventually positive on a compact set when `f ≥ 0` there and `g > 0` at the zeros of `f`, the
scalar form of the case of Finsler's lemma where the first form is positive semidefinite.

## Main results

* `TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le` — if `g` tends to `atTop`
  along `l` and,
  eventually along `l`, `g - C₂ ≤ f ≤ g + C₁` for constants `C₁` and `C₂`, then `f / g` tends
  to `1`. No property of the denominator beyond divergence is used: the additive error washes
  out because `g` blows up.
* `TauCeti.tendsto_inv_pow_sub_nhdsGT`, `TauCeti.tendsto_inv_pow_sub_nhdsLT` — for `k ≠ 0`,
  `((x - a) ^ k)⁻¹` tends to `atTop` as `x` tends to `a` from the right, and `((a - x) ^ k)⁻¹`
  tends to `atTop` as `x` tends to `a` from the left.
* `TauCeti.tendsto_div_one_sub_nhdsLT_one` — `x / (1 - x)` tends to `atTop` as `x` tends to `1`
  from the left.

* `TauCeti.eventually_sq_lt_one_nhdsLT_one` — eventually `x ^ 2 < 1` along `𝓝[<] 1`.
* `IsCompact.eventually_forall_mul_add_pos` — if `f` and `g` are continuous on a compact set `K`,
  `f ≥ 0` on `K` and `g > 0` at the zeros of `f` in `K`, then for every sufficiently large `t`,
  `t f + g` is positive on `K`.

## Implementation notes

The two error bounds are taken as separate `∃ C, ∀ᶠ …` hypotheses rather than as a single
bound on `|f - g|`, because a caller that derives the two inequalities from different estimates
arrives holding them in that shape and would otherwise have to recombine them.

## References

Adapted from `tendsto_ratio_one_of_div_atTop_pm_bounded` in
`CebotarevDensity/ForMathlib/LogOneDivSubOne.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The source states it
over `ℝ`; the statement here is over an arbitrary linearly ordered topological field.
-/

public section

namespace TauCeti

open Filter Topology

/-- A ratio whose denominator diverges and whose numerator tracks it up to a two-sided additive
bounded error tends to `1`. Contrast `tendsto_bdd_div_atTop_nhds_zero`, whose numerator is confined
to a fixed interval and whose ratio tends to `0`. -/
theorem tendsto_div_nhds_one_of_le_add_const_of_sub_const_le {𝕜 α : Type*} [Field 𝕜]
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    {l : Filter α} {g f : α → 𝕜}
    (hg : Tendsto g l atTop) (h_le : ∃ C : 𝕜, ∀ᶠ s in l, f s ≤ g s + C)
    (h_lower : ∃ C : 𝕜, ∀ᶠ s in l, g s - C ≤ f s) : Tendsto (fun s ↦ f s / g s) l (𝓝 1) := by
  obtain ⟨C₁, hle⟩ := h_le
  obtain ⟨C₂, hlower⟩ := h_lower
  -- the additive error washes out under division because the denominator blows up
  have h0 : Tendsto (fun s ↦ (f s - g s) / g s) l (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (b := -C₂) (B := C₁)
      (hlower.mono fun s h ↦ by linarith) (hle.mono fun s h ↦ by linarith) hg
  exact (add_zero (1 : 𝕜) ▸ h0.const_add 1).congr' <|
    (hg.eventually_gt_atTop 0).mono fun s h ↦ by grind

/-- The square is strictly less than one sufficiently close to one from below. -/
theorem eventually_sq_lt_one_nhdsLT_one {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] :
    ∀ᶠ x : 𝕜 in 𝓝[<] 1, x ^ 2 < 1 := by
  filter_upwards [Ioo_mem_nhdsLT (by simp : (-1 : 𝕜) < 1)] with x hx
  nlinarith [hx.1, hx.2]

/-- **Eventual positivity of `t f + g` on a compact set.** Let `f` and `g` be continuous on a
compact set `K`, with `f ≥ 0` on `K` and `g > 0` at the points of `K` where `f` vanishes. Then for
every sufficiently large `t`, `t f + g` is positive on all of `K`. This is the scalar form of
the case of Finsler's lemma where the first form is positive semidefinite. -/
theorem _root_.IsCompact.eventually_forall_mul_add_pos {X 𝕜 : Type*} [TopologicalSpace X]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    {K : Set X} (hK : IsCompact K) {f g : X → 𝕜} (hf : ContinuousOn f K) (hg : ContinuousOn g K)
    (hf₀ : ∀ x ∈ K, 0 ≤ f x) (hg₀ : ∀ x ∈ K, f x = 0 → 0 < g x) :
    ∀ᶠ t in atTop, ∀ x ∈ K, 0 < t * f x + g x := by
  -- It suffices to find a threshold near each point of `K`; compactness then makes one work.
  have hmem := hK.mem_prod_nhdsSet_of_forall (l := atTop)
    (s := {z : 𝕜 × X | z.2 ∈ K → 0 < z.1 * f z.2 + g z.2}) fun p hp ↦ ?_
  · exact (Filter.Eventually.curry hmem).mono fun t ht x hx ↦ ht.self_of_nhdsSet x hx hx
  rcases (hf₀ p hp).eq_or_lt with h0 | h0
  · -- Near a zero of `f`, `g` stays positive and `t f ≥ 0` for `t ≥ 0`.
    have hG : ∀ᶠ q in 𝓝[K] p, 0 < g q :=
      (hg p hp).eventually (lt_mem_nhds (hg₀ p hp h0.symm))
    rw [eventually_nhdsWithin_iff] at hG
    filter_upwards [(eventually_ge_atTop 0).prod_mk hG] with z ⟨hz₁, hz₂⟩ hzK
    exact add_pos_of_nonneg_of_pos (mul_nonneg hz₁ (hf₀ _ hzK)) (hz₂ hzK)
  · -- Near a point where `f` is positive, `f > f p / 2` and `g > g p - 1`, so `t f` dominates
    -- `g` once `t ≥ T = 2 (|g p| + 1) / f p`.
    have hFG : ∀ᶠ q in 𝓝[K] p, f p / 2 < f q ∧ g p - 1 < g q :=
      ((hf p hp).eventually (lt_mem_nhds (half_lt_self h0))).and
        ((hg p hp).eventually (lt_mem_nhds (sub_one_lt _)))
    rw [eventually_nhdsWithin_iff] at hFG
    set T := 2 * (|g p| + 1) / f p
    have hT : 0 ≤ T := by positivity
    have hTf : T * (f p / 2) = |g p| + 1 := by
      simp only [T]
      field_simp
    filter_upwards [(eventually_ge_atTop T).prod_mk hFG] with z ⟨hz₁, hz₂⟩ hzK
    obtain ⟨hzf, hzg⟩ := hz₂ hzK
    have h₁ : z.1 * (f p / 2) ≤ z.1 * f z.2 := mul_le_mul_of_nonneg_left hzf.le (hT.trans hz₁)
    have h₂ : T * (f p / 2) ≤ z.1 * (f p / 2) := mul_le_mul_of_nonneg_right hz₁ (by positivity)
    linarith [neg_abs_le (g p)]

section InvPow

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] {a : 𝕜}

/-- The reciprocal of `(x - a) ^ k`, for `k ≠ 0`, tends to `+∞` from the right of `a`. -/
theorem tendsto_inv_pow_sub_nhdsGT {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun x ↦ ((x - a) ^ k)⁻¹) (𝓝[>] a) atTop := by
  refine tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · exact (Continuous.tendsto' (f := fun x : 𝕜 ↦ (x - a) ^ k) (by fun_prop) a 0
      (by simp [zero_pow hk])).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact pow_pos (sub_pos.2 hx) k

/-- The reciprocal of `(a - x) ^ k`, for `k ≠ 0`, tends to `+∞` from the left of `a`. -/
theorem tendsto_inv_pow_sub_nhdsLT {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun x ↦ ((a - x) ^ k)⁻¹) (𝓝[<] a) atTop := by
  refine tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · exact (Continuous.tendsto' (f := fun x : 𝕜 ↦ (a - x) ^ k) (by fun_prop) a 0
      (by simp [zero_pow hk])).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact pow_pos (sub_pos.2 hx) k

/-- The ratio `x / (1 - x)` tends to `+∞` from the left of `1`. -/
theorem tendsto_div_one_sub_nhdsLT_one :
    Tendsto (fun x : 𝕜 ↦ x / (1 - x)) (𝓝[<] 1) atTop := by
  have h := (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).pos_mul_atTop one_pos
    (tendsto_inv_pow_sub_nhdsLT (a := (1 : 𝕜)) one_ne_zero)
  simpa [div_eq_mul_inv] using h

end InvPow

end TauCeti
