/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Quasilinear.Kirchhoff
public import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The coefficient `1 + u²` on an interval: no strong monotonicity, yet a unique solution

On `(0, 1)` consider the quasilinear operator `Q u = -((1 + u²) u')'` with zero boundary values,
whose weak form on `H¹₀(0, 1)` is `⟨Q u, φ⟩ = ∫_0^1 (1 + ū²) u' φ'`, `ū` the continuous
representative of `u`. Its flux `(1 + s²) ξ` is monotone in the gradient variable `ξ` for each
fixed value `s`, since `(1 + s²) (ξ - η) (ξ - η) ≥ 0`. The operator itself is not monotone: there
are `u, v ∈ H¹₀(0, 1)` with

`⟨Q u - Q v, u - v⟩ = ∫_0^1 ((1 + u²) u' - (1 + v²) v') (u' - v') < 0`

(`TauCeti.PDE.exists_intervalTraceL_eq_zero_and_setIntegral_one_add_sq_mul_gradient_sub_lt_zero`).
So no strong monotonicity estimate `c ‖(u - v)'‖²_{L²} ≤ ⟨Q u - Q v, u - v⟩` holds on `H¹₀(0, 1)`,
for any `c ≥ 0`
(`TauCeti.PDE.not_exists_nonneg_forall_mul_norm_gradient_sub_sq_le_setIntegral_one_add_sq`), and
the uniqueness and Lipschitz dependence on the data that such an estimate provides are not
available for this operator. (The strong monotonicity estimate
`TauCeti.PDE.mul_norm_gradient_sub_sq_le_energyFormH1_quasilinear_sub` is stated for coefficients
that are bounded and Lipschitz in `u`, which `1 + u²` is not.)

Uniqueness holds nonetheless, for a different reason. Kirchhoff's transformation
`Φ(s) = ∫_0^s (1 + y²) dy = s + s³ / 3` turns `Q u = 1` into the linear equation `-(Φ ∘ ū)'' = 1`,
so by `TauCeti.PDE.existsUnique_intervalTraceL_eq_and_forall_setIntegral_eq` the problem
`-((1 + u²) u')' = 1`, `u(0) = u(1) = 0` has exactly one weak solution, and it is determined by
`ū + ū³ / 3 = x (1 - x) / 2`
(`TauCeti.PDE.intervalRepresentativeL_add_pow_three_div_three_eq_of_forall_setIntegral_one_add_sq`).

## The witness

Both functions are piecewise affine with nodes `0, 1/3, 2/3, 1`: `u` takes the values
`0, 1, 6, 0` there and `v` the values `0, -2, 5, 0`. On a piece where `u` and `v` have slopes `α`
and `β`, the integrand is `(α - β) ((Φ ∘ u)' - (Φ ∘ v)')`, so the integral over the piece is
`(α - β)` times the increment of `Φ ∘ u - Φ ∘ v`. The three pieces contribute `54`, `-152` and
`94`, and the integral is `-4`. Summing by parts instead, the integral is the sum over the
interior nodes of `Φ(u) - Φ(v)` times the downward jump of `(u - v)'`. The difference `u - v`
takes the values `0, 3, 1, 0`. Its concave kink at `1/3`, where `u` and `v` are small and
`Φ(u) - Φ(v) = 6`, contributes `6 · 15 = 90`; its convex kink at `2/3`, where `u` and `v` are large
and `Φ(u) - Φ(v) = 94 / 3`, contributes `-(94 / 3) · 3 = -94`. The factor
`1 + (u² + u v + v²) / 3` relating `Φ(u) - Φ(v)` to `u - v` is what lets the convex kink win.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.4 (one-dimensional boundary value problems).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Distributions Topology NNReal Interval

namespace TauCeti.PDE

variable {p : ENNReal} [Fact (1 ≤ p)]

/-- On an interval `[x, y]` where `U` and `V` are affine with slopes `α` and `β`, the integrand
`((1 + U²) U' - (1 + V²) V') (U' - V')` is integrable, and its integral is the increment of
`(α - β) (Φ ∘ U - Φ ∘ V)`, `Φ(s) = s + s³ / 3`. -/
private theorem intervalIntegrable_and_integral_one_add_sq_mul_deriv_sub_eq {U V : ℝ → ℝ}
    {x y a α b β : ℝ} (hxy : x ≤ y) (hU : EqOn U (fun t ↦ a + α * t) (Icc x y))
    (hV : EqOn V (fun t ↦ b + β * t) (Icc x y)) :
    IntervalIntegrable (fun t ↦ ((1 + U t ^ 2) * deriv U t - (1 + V t ^ 2) * deriv V t) *
        (deriv U t - deriv V t)) volume x y ∧
      ∫ t in x..y, ((1 + U t ^ 2) * deriv U t - (1 + V t ^ 2) * deriv V t) *
          (deriv U t - deriv V t) =
        (α - β) * (U y + U y ^ 3 / 3 - (V y + V y ^ 3 / 3)) -
          (α - β) * (U x + U x ^ 3 / 3 - (V x + V x ^ 3 / 3)) := by
  have haff (c γ t : ℝ) : HasDerivAt (fun t ↦ c + γ * t) γ t := by
    simpa using ((hasDerivAt_id t).const_mul γ).const_add c
  -- `Φ(s) = s + s³ / 3` has derivative `1 + s²`.
  have hΦ (c γ t : ℝ) : HasDerivAt (fun t ↦ c + γ * t + (c + γ * t) ^ 3 / 3)
      ((1 + (c + γ * t) ^ 2) * γ) t := by
    refine ((haff c γ t).add (((hasDerivAt_pow 3 (c + γ * t)).comp t
      (haff c γ t)).div_const 3)).congr_deriv ?_
    norm_num
    ring
  set g : ℝ → ℝ := fun t ↦ (α - β) * ((1 + (a + α * t) ^ 2) * α - (1 + (b + β * t) ^ 2) * β)
    with hg_def
  have hg : Continuous g := by fun_prop
  -- On the open piece the derivatives are the slopes, so the integrand is `g`.
  have hae : ∀ᵐ t, t ∈ Ι x y → ((1 + U t ^ 2) * deriv U t - (1 + V t ^ 2) * deriv V t) *
      (deriv U t - deriv V t) = g t := by
    have hne : ∀ᵐ t ∂volume, t ≠ y := by simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t hty ht
    rw [uIoc_of_le hxy] at ht
    have htI : t ∈ Ioo x y := ⟨ht.1, lt_of_le_of_ne ht.2 hty⟩
    have hIcc : Icc x y ∈ 𝓝 t := Icc_mem_nhds htI.1 htI.2
    have hdU : deriv U t = α :=
      ((haff a α t).congr_of_eventuallyEq (eventually_of_mem hIcc hU)).deriv
    have hdV : deriv V t = β :=
      ((haff b β t).congr_of_eventuallyEq (eventually_of_mem hIcc hV)).deriv
    rw [hdU, hdV, hU (Ioo_subset_Icc_self htI), hV (Ioo_subset_Icc_self htI), hg_def]
    ring
  refine ⟨(hg.intervalIntegrable x y).congr_ae ?_, ?_⟩
  · rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with t ht hmem
    exact (ht hmem).symm
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t ↦ (α - β) * (a + α * t + (a + α * t) ^ 3 / 3 - (b + β * t + (b + β * t) ^ 3 / 3)))
    (fun t _ ↦ by convert ((hΦ a α t).sub (hΦ b β t)).const_mul (α - β) using 1)
    (hg.intervalIntegrable x y), hU (right_mem_Icc.2 hxy), hU (left_mem_Icc.2 hxy),
    hV (right_mem_Icc.2 hxy), hV (left_mem_Icc.2 hxy)]

/-- The first witness: piecewise affine, with values `0, 1, 6, 0` at `0, 1/3, 2/3, 1`. -/
private def oneAddSqWitnessFst (t : ℝ) : ℝ := min (max (3 * t + 0) (15 * t + -4)) (-18 * t + 18)

/-- The second witness: piecewise affine, with values `0, -2, 5, 0` at `0, 1/3, 2/3, 1`. -/
private def oneAddSqWitnessSnd (t : ℝ) : ℝ := min (max (-6 * t + 0) (21 * t + -9)) (-15 * t + 15)

/-- For the two witnesses `U` and `V`, `∫_0^1 ((1 + U²) U' - (1 + V²) V') (U' - V') = -4`: the
three thirds contribute `54`, `-152` and `94`. -/
private theorem integral_one_add_sq_mul_deriv_sub_oneAddSqWitness :
    ∫ t in (0 : ℝ)..1,
      ((1 + oneAddSqWitnessFst t ^ 2) * deriv oneAddSqWitnessFst t -
          (1 + oneAddSqWitnessSnd t ^ 2) * deriv oneAddSqWitnessSnd t) *
        (deriv oneAddSqWitnessFst t - deriv oneAddSqWitnessSnd t) = -4 := by
  have h₁ := intervalIntegrable_and_integral_one_add_sq_mul_deriv_sub_eq
    (U := oneAddSqWitnessFst) (V := oneAddSqWitnessSnd) (x := 0) (y := 1 / 3) (a := 0) (α := 3)
    (b := 0) (β := -6) (by norm_num)
    (fun t ht ↦ by
      rw [oneAddSqWitnessFst, max_eq_left (by linarith [ht.2]), min_eq_left (by linarith [ht.2])]
      ring)
    (fun t ht ↦ by
      rw [oneAddSqWitnessSnd, max_eq_left (by linarith [ht.2]), min_eq_left (by linarith [ht.2])]
      ring)
  have h₂ := intervalIntegrable_and_integral_one_add_sq_mul_deriv_sub_eq
    (U := oneAddSqWitnessFst) (V := oneAddSqWitnessSnd) (x := 1 / 3) (y := 2 / 3) (a := -4)
    (α := 15) (b := -9) (β := 21) (by norm_num)
    (fun t ht ↦ by
      rw [oneAddSqWitnessFst, max_eq_right (by linarith [ht.1]),
        min_eq_left (by linarith [ht.2])]
      ring)
    (fun t ht ↦ by
      rw [oneAddSqWitnessSnd, max_eq_right (by linarith [ht.1]),
        min_eq_left (by linarith [ht.2])]
      ring)
  have h₃ := intervalIntegrable_and_integral_one_add_sq_mul_deriv_sub_eq
    (U := oneAddSqWitnessFst) (V := oneAddSqWitnessSnd) (x := 2 / 3) (y := 1) (a := 18) (α := -18)
    (b := 15) (β := -15) (by norm_num)
    (fun t ht ↦ by
      rw [oneAddSqWitnessFst, min_eq_right (le_max_of_le_right (by linarith [ht.1]))]
      ring)
    (fun t ht ↦ by
      rw [oneAddSqWitnessSnd, min_eq_right (le_max_of_le_right (by linarith [ht.1]))]
      ring)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 2 / 3) (h₁.1.trans h₂.1) h₃.1,
    ← intervalIntegral.integral_add_adjacent_intervals h₁.1 h₂.1, h₁.2, h₂.2, h₃.2]
  norm_num [oneAddSqWitnessFst, oneAddSqWitnessSnd]

/-- **The operator `-((1 + u²) u')'` is not monotone on `H¹₀(0, 1)`.** There are
`u, v ∈ H¹(0, 1)` vanishing at both endpoints with

`∫_0^1 ((1 + u²) u' - (1 + v²) v') (u' - v') < 0`,

with `u` and `v` evaluated through their continuous representatives: the pairing
`⟨Q u - Q v, u - v⟩` of the weak operator `⟨Q u, φ⟩ = ∫_0^1 (1 + ū²) u' φ'` is negative. -/
theorem exists_intervalTraceL_eq_zero_and_setIntegral_one_add_sq_mul_gradient_sub_lt_zero :
    ∃ u v : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2,
      W1p.intervalTraceL zero_lt_one u = (0, 0) ∧ W1p.intervalTraceL zero_lt_one v = (0, 0) ∧
      ∫ t in Ioo (0 : ℝ) 1,
          ((1 + W1p.intervalRepresentativeL zero_lt_one u (projIcc 0 1 zero_le_one t) ^ 2) *
              W1p.gradient u t -
            (1 + W1p.intervalRepresentativeL zero_lt_one v (projIcc 0 1 zero_le_one t) ^ 2) *
              W1p.gradient v t) * (W1p.gradient u t - W1p.gradient v t) < 0 := by
  -- Affine functions are Lipschitz, hence so are the piecewise affine witnesses.
  have haff (c d : ℝ) : LipschitzWith ‖c‖₊ fun t : ℝ ↦ c * t + d := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [Real.dist_eq, Real.dist_eq, coe_nnNorm, Real.norm_eq_abs, ← abs_mul]
    exact le_of_eq (congrArg abs (by ring))
  -- A Lipschitz function represents a class in `H¹(0, 1)` with its derivative as weak gradient.
  have hclass {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
      ∃ u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2,
        (∀ t : Icc (0 : ℝ) 1, W1p.intervalRepresentativeL zero_lt_one u t = f t) ∧
        W1p.gradient u =ᵐ[volume.restrict (Ioo 0 1)] deriv f := by
    obtain ⟨u, hu, -, hg⟩ := W1p.exists_intervalRepresentativeL_eq_and_value_gradient_ae_eq
      (p := 2) zero_lt_one hf.lipschitzOnWith.absolutelyContinuousOnInterval
      (MemLp.of_bound (measurable_deriv f).aestronglyMeasurable K
        (ae_of_all _ fun _ ↦ norm_deriv_le_of_lipschitz hf))
    exact ⟨u, hu, hg⟩
  obtain ⟨u, hu, hgu⟩ := hclass (f := oneAddSqWitnessFst)
    (((haff 3 0).max (haff 15 (-4))).min (haff (-18) 18))
  obtain ⟨v, hv, hgv⟩ := hclass (f := oneAddSqWitnessSnd)
    (((haff (-6) 0).max (haff 21 (-9))).min (haff (-15) 15))
  refine ⟨u, v, ?_, ?_, ?_⟩
  · rw [W1p.intervalTraceL_apply, hu, hu]
    norm_num [oneAddSqWitnessFst]
  · rw [W1p.intervalTraceL_apply, hv, hv]
    norm_num [oneAddSqWitnessSnd]
  -- Replace the representatives and gradients by the witnesses and their derivatives.
  calc _ = ∫ t in (0 : ℝ)..1,
          ((1 + oneAddSqWitnessFst t ^ 2) * deriv oneAddSqWitnessFst t -
              (1 + oneAddSqWitnessSnd t ^ 2) * deriv oneAddSqWitnessSnd t) *
            (deriv oneAddSqWitnessFst t - deriv oneAddSqWitnessSnd t) := by
        rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo, hgu, hgv] with t ht htu htv
        rw [projIcc_of_mem zero_le_one (Ioo_subset_Icc_self ht), hu, hv, htu, htv]
    _ < 0 := by
        rw [integral_one_add_sq_mul_deriv_sub_oneAddSqWitness]
        norm_num

/-- **No strong monotonicity for `-((1 + u²) u')'` on `H¹₀(0, 1)`.** There is no constant
`c ≥ 0` with

`c ‖(u - v)'‖²_{L²} ≤ ∫_0^1 ((1 + u²) u' - (1 + v²) v') (u' - v')`

with `u` and `v` evaluated through their continuous representatives, for all `u, v ∈ H¹(0, 1)`
vanishing at both endpoints: the operator is neither strongly monotone (`c > 0`) nor monotone
(`c = 0`). -/
theorem not_exists_nonneg_forall_mul_norm_gradient_sub_sq_le_setIntegral_one_add_sq :
    ¬ ∃ c : ℝ, 0 ≤ c ∧ ∀ u v : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2,
      W1p.intervalTraceL zero_lt_one u = (0, 0) → W1p.intervalTraceL zero_lt_one v = (0, 0) →
      c * ‖W1p.gradient (u - v)‖ ^ 2 ≤
        ∫ t in Ioo (0 : ℝ) 1,
          ((1 + W1p.intervalRepresentativeL zero_lt_one u (projIcc 0 1 zero_le_one t) ^ 2) *
              W1p.gradient u t -
            (1 + W1p.intervalRepresentativeL zero_lt_one v (projIcc 0 1 zero_le_one t) ^ 2) *
              W1p.gradient v t) * (W1p.gradient u t - W1p.gradient v t) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨u, v, hu, hv, hlt⟩ :=
    exists_intervalTraceL_eq_zero_and_setIntegral_one_add_sq_mul_gradient_sub_lt_zero
  exact (hlt.trans_le' (h u v hu hv)).not_ge (by positivity)

/-- **The solution of `-((1 + u²) u')' = 1` on `(0, 1)` with zero boundary values.** If
`u ∈ W^{1,p}(0, 1)` vanishes at both endpoints and solves the equation weakly,

`∫_0^1 (1 + ū²) u' φ' = ∫_0^1 φ` for every `φ ∈ C_c^∞(0, 1)`,

then its continuous representative satisfies `ū x + ū x³ / 3 = x (1 - x) / 2` on `[0, 1]`. Since
`s ↦ s + s³ / 3` is injective, this determines `ū`; a solution exists and is unique by
`TauCeti.PDE.existsUnique_intervalTraceL_eq_and_forall_setIntegral_eq`. -/
theorem intervalRepresentativeL_add_pow_three_div_three_eq_of_forall_setIntegral_one_add_sq
    {u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p}
    (htr : W1p.intervalTraceL zero_lt_one u = (0, 0))
    (hu : ∀ φ : 𝓓(⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo (0 : ℝ) 1,
          (1 + W1p.intervalRepresentativeL zero_lt_one u (projIcc 0 1 zero_le_one t) ^ 2) *
            W1p.gradient u t * deriv φ t =
        ∫ t in Ioo (0 : ℝ) 1, φ t)
    (x : Icc (0 : ℝ) 1) :
    W1p.intervalRepresentativeL zero_lt_one u x +
        W1p.intervalRepresentativeL zero_lt_one u x ^ 3 / 3 = x * (1 - x) / 2 := by
  obtain ⟨k, hk⟩ := exists_forall_intervalIntegral_intervalRepresentativeL_eq
    (A := fun y ↦ 1 + y ^ 2) (f := fun _ ↦ 1) (F := fun _ ↦ 0) zero_lt_one (by fun_prop)
    (integrableOn_const measure_Ioo_lt_top.ne) integrableOn_zero (fun φ ↦ by simpa using hu φ)
  -- Kirchhoff's transformation is `Φ(s) = ∫_0^s (1 + y²) dy = s + s³ / 3`.
  have hΦ (s : ℝ) : ∫ y in (0 : ℝ)..s, (1 + y ^ 2) = s + s ^ 3 / 3 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((continuous_pow 2).intervalIntegrable _ _), integral_pow]
    norm_num
  have hG (t : ℝ) : ∫ r in (0 : ℝ)..t, ((∫ _ in (0 : ℝ)..r, (1 : ℝ)) + 0) = t ^ 2 / 2 := by
    simp [integral_id]
  rw [W1p.intervalTraceL_apply, Prod.mk.injEq] at htr
  have h₁ := hk ⟨1, right_mem_Icc.2 zero_le_one⟩
  have hx := hk x
  simp only [hΦ, hG, htr.1, htr.2] at h₁ hx
  -- At `x = 1` the boundary value fixes `k = 1 / 2`.
  have hk' : k = 1 / 2 := by linarith
  rw [hx, hk']
  ring

end TauCeti.PDE
