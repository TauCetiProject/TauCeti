/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# High-frequency behaviour of symbols

Testing a pseudodifferential operator on rapidly oscillating functions `exp(i t ⟪y, ξ⟫) φ(y)`
with `t → ∞` probes its symbol at the rescaled frequencies `t ξ`. After normalizing by `t ^ (-m)`,
only the part of order `m` of the symbol survives: lower-order remainders of an asymptotic
expansion are discarded. This file collects the symbol estimates behind such limits.

* `TauCeti.Symbol.tendsto_rpow_neg_smul_coefficient_smul_zero`: a symbol of order `m'` is
  negligible at high frequency against every order `m > m'`. At a nonzero frequency `ξ`,
  `t ^ (-m) a(y, t ζ) → 0` as `t → ∞` and `(y, ζ) → (x, ξ)` jointly. Letting the frequency `ζ`
  vary near `ξ` covers the shifted frequencies `t ξ + 2π η = t (ξ + t⁻¹ 2π η)` that appear in
  wave-packet limits. With it, `TauCeti.ClassicalSymbol.tendsto_rpow_neg_smul_coefficient_smul`
  recovers the principal symbol of a classical symbol as a high-frequency limit.
* `TauCeti.Symbol.exists_norm_rpow_neg_smul_coefficient_smul_add_le`: for a symbol of order `m`,
  a nonzero frequency `ξ` and positions `y` in a compact set,
  `t ^ (-m) ‖a(y, t ξ + ζ)‖ ≤ B ⟨ζ⟩ ^ |m|` uniformly in `t ≥ 1` and in the shift `ζ`. This
  dominates the integrands of such limits.

Both proofs start from the symbol estimate `‖a(y, ζ)‖ ≤ C ⟨ζ⟩ ^ m` for `y` in a compact set. In
the first, `y` ranges over a closed ball around `x`, `t ≥ 1` and `ζ` lies in the ball of radius
`‖ξ‖ / 2` around `ξ`, so the rescaled frequencies `t ζ` lie in an annulus of radii comparable to
`t`, where `⟨t ζ⟩ ^ m'` is at most a constant multiple of `t ^ m'`. In the second, Peetre's
inequality bounds `⟨t ξ + ζ⟩ ^ m` by a multiple of `⟨t ξ⟩ ^ m ⟨ζ⟩ ^ |m|`, and `⟨t ξ⟩ ^ m` is at
most a constant multiple of `t ^ m` for `t ≥ 1`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Topology Metric

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- **Lower-order symbols are negligible at high frequency.** For a symbol `a` of order `m'`, an
order `m > m'` and a nonzero frequency `ξ`, `t ^ (-m) a(y, t ζ) → 0` as `t → ∞` and
`(y, ζ) → (x, ξ)`. -/
theorem tendsto_rpow_neg_smul_coefficient_smul_zero {m' : ℝ} (a : Symbol n V W m')
    (hm : m' < m) {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    Tendsto (fun p : ℝ × (CoordinateSpace n × CoordinateSpace n) ↦
        p.1 ^ (-m) • a.coefficient (p.2.1, p.1 • p.2.2)) (atTop ×ˢ 𝓝 (x, ξ)) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := a.exists_bound_coefficient _ (isCompact_closedBall x 1)
  set r := ‖ξ‖
  have hr : 0 < r := norm_pos_iff.2 hξ
  set M := max (((r / 2) ^ 2) ^ (m' / 2)) ((1 + (3 * r / 2) ^ 2) ^ (m' / 2))
  have hlim : Tendsto (fun p : ℝ × (CoordinateSpace n × CoordinateSpace n) ↦
      C * M * p.1 ^ (-(m - m'))) (atTop ×ˢ 𝓝 (x, ξ)) (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (sub_pos.2 hm)).comp tendsto_fst).const_mul (C * M)
  refine squeeze_zero_norm' ?_ hlim
  have hN : closedBall x 1 ×ˢ ball ξ (r / 2) ∈ 𝓝 (x, ξ) :=
    prod_mem_nhds (closedBall_mem_nhds x one_pos) (ball_mem_nhds ξ (half_pos hr))
  filter_upwards [prod_mem_prod (eventually_ge_atTop 1) hN]
  rintro ⟨t, y, ζ⟩ ⟨ht, hy, hζ⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  -- On the annulus `r / 2 ≤ ‖ζ‖ ≤ 3 r / 2`, `⟨t ζ⟩ ^ m' ≤ M t ^ m'`.
  rw [mem_ball, dist_eq_norm] at hζ
  have hζ1 : r / 2 ≤ ‖ζ‖ := by
    have := norm_sub_norm_le ξ ζ
    rw [norm_sub_rev] at this
    linarith
  have hζ2 : ‖ζ‖ ≤ 3 * r / 2 := by
    have := norm_le_norm_add_norm_sub' ζ ξ
    linarith
  have hbr : (1 + ‖t • ζ‖ ^ 2) ^ (m' / 2) ≤ M * t ^ m' :=
    one_add_norm_smul_sq_rpow_half_le (half_pos hr) ht ⟨hζ1, hζ2⟩ _
  calc ‖t ^ (-m) • a.coefficient (y, t • ζ)‖
      = t ^ (-m) * ‖a.coefficient (y, t • ζ)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ t ^ (-m) * (C * (M * t ^ m')) := by
        gcongr
        exact (hC y hy _).trans (mul_le_mul_of_nonneg_left hbr hC0)
    _ = C * M * t ^ (-(m - m')) := by
        rw [neg_sub, Real.rpow_sub ht0, Real.rpow_neg ht0.le]
        field_simp

/-- **Uniform high-frequency bound.** For a symbol `a` of order `m`, a nonzero frequency `ξ` and
positions `y` in a compact set, `t ^ (-m) ‖a(y, t ξ + ζ)‖` is at most a multiple of `⟨ζ⟩ ^ |m|`
for all `t ≥ 1` and all shifts `ζ`. -/
theorem exists_norm_rpow_neg_smul_coefficient_smul_add_le (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ∃ B, ∀ y ∈ K, ∀ t : ℝ, 1 ≤ t → ∀ ζ : CoordinateSpace n,
      ‖t ^ (-m) • a.coefficient (y, t • ξ + ζ)‖ ≤ B * (1 + ‖ζ‖ ^ 2) ^ (|m| / 2) := by
  obtain ⟨C, hC⟩ := a.exists_norm_coefficient_le K hK
  set M := max ((‖ξ‖ ^ 2) ^ (m / 2)) ((1 + ‖ξ‖ ^ 2) ^ (m / 2))
  refine ⟨C * 2 ^ (|m| / 2) * M, fun y hy t ht ζ ↦ ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  have hbr : (1 + ‖t • ξ‖ ^ 2) ^ (m / 2) ≤ M * t ^ m :=
    one_add_norm_smul_sq_rpow_half_le (norm_pos_iff.2 hξ) ht ⟨le_rfl, le_rfl⟩ m
  have hle := hC y hy (t • ξ + ζ)
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hle) (by positivity)
  have htm : t ^ (-m) * t ^ m = 1 := by rw [← Real.rpow_add ht0]; simp
  calc ‖t ^ (-m) • a.coefficient (y, t • ξ + ζ)‖
      = t ^ (-m) * ‖a.coefficient (y, t • ξ + ζ)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ t ^ (-m) * (C * (2 ^ (|m| / 2) * (M * t ^ m) * (1 + ‖ζ‖ ^ 2) ^ (|m| / 2))) := by
        gcongr
        refine hle.trans (mul_le_mul_of_nonneg_left ?_ hC0)
        refine (one_add_norm_add_sq_rpow_le_mul m _ _).trans ?_
        gcongr
    _ = C * 2 ^ (|m| / 2) * M * (1 + ‖ζ‖ ^ 2) ^ (|m| / 2) := by
        linear_combination (C * 2 ^ (|m| / 2) * M * (1 + ‖ζ‖ ^ 2) ^ (|m| / 2)) * htm

end Symbol

end TauCeti
