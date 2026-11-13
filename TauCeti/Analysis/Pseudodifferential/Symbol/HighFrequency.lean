/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# High-frequency behaviour of symbols

A symbol of order `m'` is negligible at high frequency against every order `m > m'`: at a nonzero
frequency `ξ`, `t ^ (-m) a(y, t ζ) → 0` as `t → ∞` and `(y, ζ) → (x, ξ)`
(`TauCeti.Symbol.tendsto_rpow_neg_smul_coefficient_smul_zero`). On a small ball around `ξ` the
rescaled frequencies `t ζ` stay in an annulus of radius comparable to `t`, where the symbol
estimate gives `‖a(y, t ζ)‖ ≤ C t ^ m'`.

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

end Symbol

end TauCeti
