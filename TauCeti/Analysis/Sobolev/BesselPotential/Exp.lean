/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.Series

/-!
# The exponential as a smooth map of `H^s`, `s > n / 2`

Let `E` be a finite-dimensional real inner product space of dimension `n` and `s > n / 2`. For
`u ∈ H^s(E)`, the function `exp u - 1` lies in `H^s(E)`
(`TemperedDistribution.exists_memSobolev_ae_eq_exp_sub_one`). This file bundles it as a map
`BesselPotentialSpace.expSubOne hs : H^s(E) → H^s(E)` and shows that it is smooth, with derivative

`D(exp u - 1) v = (exp u - 1) v + v = exp u · v`,

where the product is the multiplication `BesselPotentialSpace.mulCLM` of the algebra `H^s(E)`
(`BesselPotentialSpace.hasFDerivAt_expSubOne`, `BesselPotentialSpace.contDiff_expSubOne`).

The derivative comes from the exact identity

`(exp (u + v) - 1) - (exp u - 1) - ((exp u - 1) v + v) = (exp u - 1) r + r`,  `r = exp v - 1 - v`,

and the quadratic bound `‖r‖_{H^s} ≤ exp C ‖v‖²_{H^s}` for `‖v‖_{H^s} ≤ 1`, where `C` is the
constant of the power-series estimate `TemperedDistribution.exists_hasSum_mul_pow`: `r` is the
power series `∑_{n ≥ 1} v ^ (n + 1) / (n + 1)!` without its linear term. Since the derivative
`u ↦ mulCLM (exp u - 1) + id` is built from `expSubOne` itself by a bounded linear map, induction
on the order gives smoothness.

Nonlinear elliptic equations with an exponential nonlinearity, such as Taubes's reduced vortex
equation `Δw = h (exp (2w) - 1) / 8 + k` with bounded coefficient `h` and source `k`, therefore
define smooth maps between Sobolev spaces: this is the smoothness input of the implicit function
theorem, which also needs an invertible linearization.

## Main declarations

* `BesselPotentialSpace.expSubOne hs u`: the element `exp u - 1` of `H^s(E)`, characterized by
  its `L²` function (`BesselPotentialSpace.coeFn_inclusionLp_expSubOne`,
  `BesselPotentialSpace.eq_expSubOne_iff`).
* `BesselPotentialSpace.hasFDerivAt_expSubOne`: its derivative is `v ↦ (exp u - 1) v + v`.
* `BesselPotentialSpace.contDiff_expSubOne`: it is smooth.
-/

public section

noncomputable section

open MeasureTheory Module Filter Asymptotics TemperedDistribution
open scoped Nat ENNReal Topology BesselPotentialSpace ContDiff SchwartzMap

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace BesselPotentialSpace

variable {s : ℝ}

/-- **The exponential on `H^s(E)`, `s > dim E / 2`.** The element `exp u - 1` of `H^s(E)` for
`u ∈ H^s(E)` (`TemperedDistribution.exists_memSobolev_ae_eq_exp_sub_one`): its `L²` function is
almost everywhere `x ↦ exp (u x) - 1` (`BesselPotentialSpace.coeFn_inclusionLp_expSubOne`). -/
def expSubOne (hs : finrank ℝ E < 2 * s) (u : H^{s}(E)) : H^{s}(E) :=
  (exists_memSobolev_ae_eq_exp_sub_one hs
    (memSobolev_toLp_inclusion (nonneg_of_finrank_lt hs) u)).choose_spec.2.toBesselPotentialSpace

/-- The `L²` function of `expSubOne hs u` is almost everywhere `x ↦ exp (u x) - 1`. -/
theorem coeFn_inclusionLp_expSubOne (hs : finrank ℝ E < 2 * s) (h : 0 ≤ s) (u : H^{s}(E)) :
    ⇑(inclusionLp h (expSubOne hs u)) =ᵐ[volume]
      fun x ↦ Complex.exp (inclusionLp h u x) - 1 := by
  have hspec := (exists_memSobolev_ae_eq_exp_sub_one hs
    (memSobolev_toLp_inclusion (nonneg_of_finrank_lt hs) u)).choose_spec
  rw [expSubOne, ← toLp_inclusion,
    toLp_inclusion_toBesselPotentialSpace h hspec.2 rfl, ← toLp_inclusion]
  exact hspec.1

/-- An element of `H^s(E)` whose `L²` function is almost everywhere `exp u - 1` is
`expSubOne hs u`. -/
theorem eq_expSubOne_iff (hs : finrank ℝ E < 2 * s) (h : 0 ≤ s) {u w : H^{s}(E)} :
    w = expSubOne hs u ↔
      ⇑(inclusionLp h w) =ᵐ[volume] fun x ↦ Complex.exp (inclusionLp h u x) - 1 := by
  refine ⟨fun hw ↦ hw ▸ coeFn_inclusionLp_expSubOne hs h u, fun hw ↦ ?_⟩
  exact inclusionLp_injective h (Lp.ext (hw.trans (coeFn_inclusionLp_expSubOne hs h u).symm))

/-- The coefficients `aₙ` of `exp z - 1 - z = ∑ₙ aₙ z ^ (n + 1)`, `a₀ = 0`, satisfy
`|aₙ| (C t) ^ n ≤ t Cⁿ / n!` for `0 ≤ t ≤ 1`: the majorant of the remainder is quadratic in `t`. -/
private theorem norm_expRemainderCoeff_mul_pow_le {C t : ℝ} (hC : 0 ≤ C) (ht₀ : 0 ≤ t)
    (ht : t ≤ 1) (n : ℕ) :
    ‖(if n = 0 then 0 else (((n + 1)! : ℂ))⁻¹)‖ * (C * t) ^ n ≤ t * (C ^ n / n !) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using ht₀
  · simp only [hn.ne', ↓reduceIte, norm_inv, Complex.norm_natCast]
    have hfac : (n ! : ℝ) ≤ ((n + 1)! : ℝ) := by exact_mod_cast Nat.factorial_le n.le_succ
    have htn : t ^ n ≤ t := pow_le_of_le_one ht₀ ht hn.ne'
    rw [mul_pow, inv_mul_eq_div, div_le_iff₀ (by positivity)]
    calc C ^ n * t ^ n ≤ C ^ n * t := by gcongr
      _ = t * (C ^ n / n !) * n ! := by field_simp
      _ ≤ t * (C ^ n / n !) * ((n + 1)! : ℝ) := by gcongr

/-- **The quadratic remainder of the exponential.** There is a constant `K` such that for every
`v ∈ H^s(E)` with `‖v‖_{H^s} ≤ 1` the function `exp v - 1 - v` lies in `H^s(E)` with
`‖exp v - 1 - v‖_{H^s} ≤ K ‖v‖²_{H^s}`. -/
private theorem exists_norm_expSubOne_sub_le (hs : finrank ℝ E < 2 * s) :
    ∃ K, ∀ v : H^{s}(E), ‖v‖ ≤ 1 → ‖expSubOne hs v - v‖ ≤ K * ‖v‖ ^ 2 := by
  have h := nonneg_of_finrank_lt hs
  obtain ⟨C, hC0, hC⟩ := exists_hasSum_mul_pow (E := E) hs
  refine ⟨Real.exp C, fun v hv ↦ ?_⟩
  set U : Lp ℂ 2 (volume : Measure E) := (inclusion h v).toLp
  have hU : MemSobolev s 2 (U : 𝓢'(E, ℂ)) := memSobolev_toLp_inclusion h v
  have hUv : hU.toBesselPotentialSpace = v := toBesselPotentialSpace_memSobolev_toLp_inclusion h v
  set t := ‖v‖
  -- The series `∑_{n ≥ 1} z ^ (n + 1) / (n + 1)!` of `exp z - 1 - z`.
  set a : ℕ → ℂ := fun n ↦ if n = 0 then 0 else (((n + 1)! : ℂ))⁻¹
  have ha (n : ℕ) : ‖a n‖ * (C * t) ^ n ≤ t * (C ^ n / n !) :=
    norm_expRemainderCoeff_mul_pow_le hC0 (norm_nonneg v) hv n
  have hsum : Summable fun n ↦ ‖a n‖ * (C * ‖hU.toBesselPotentialSpace‖) ^ n := by
    rw [hUv]
    exact ((Real.summable_pow_div_factorial C).mul_left t).of_nonneg_of_le
      (fun n ↦ by positivity) ha
  obtain ⟨r, hr, hrs, hrn⟩ := hC hU hsum
  -- `r` is `exp v - 1 - v`.
  have hreq : hrs.toBesselPotentialSpace = expSubOne hs v - v := by
    refine inclusionLp_injective h (Lp.ext ?_)
    rw [← toLp_inclusion, toLp_inclusion_toBesselPotentialSpace h hrs rfl]
    filter_upwards [hr, coeFn_inclusionLp_expSubOne hs h v,
      coeFn_inclusionLp_sub_ae_eq h (u := expSubOne hs v) (v := v) .rfl .rfl] with x hx he hsub
    rw [hsub, he]
    have hexp := Complex.hasSum_exp_sub_one (inclusionLp h v x)
    rw [← hasSum_nat_add_iff' 1] at hexp
    have hx' := (hasSum_nat_add_iff' 1).2 hx
    simp only [a, Finset.range_one, Finset.sum_singleton, ↓reduceIte, zero_mul, sub_zero,
      Nat.add_eq_zero_iff, one_ne_zero, and_false] at hx'
    simp only [Finset.range_one, Finset.sum_singleton, zero_add, Nat.factorial_one, Nat.cast_one,
      inv_one, pow_one, one_mul] at hexp
    rw [← toLp_inclusion] at hexp ⊢
    exact hx'.unique (by simpa only [U] using hexp)
  rw [← hreq]
  refine hrn.trans ?_
  rw [hUv]
  calc t * ∑' n, ‖a n‖ * (C * t) ^ n ≤ t * ∑' n, t * (C ^ n / n !) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg v)
        exact (((Real.summable_pow_div_factorial C).mul_left t).of_nonneg_of_le
          (fun n ↦ by positivity) ha).tsum_mono
            ((Real.summable_pow_div_factorial C).mul_left t) ha
    _ = Real.exp C * t ^ 2 := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
        ring

/-- The pointwise identity behind the derivative of the exponential:
`(exp (u + v) - 1) - (exp u - 1) - ((exp u - 1) v + v) = (exp u - 1) r + r` with
`r = exp v - 1 - v`. -/
private theorem expSubOne_add_sub (hs : finrank ℝ E < 2 * s) (u v : H^{s}(E)) :
    expSubOne hs (u + v) - expSubOne hs u - (mulCLM hs (expSubOne hs u) v + v) =
      mulCLM hs (expSubOne hs u) (expSubOne hs v - v) + (expSubOne hs v - v) := by
  have h := nonneg_of_finrank_lt hs
  refine inclusionLp_injective h (Lp.ext ?_)
  set U := expSubOne hs u
  set V := expSubOne hs v
  filter_upwards [coeFn_inclusionLp_sub_ae_eq h (u := expSubOne hs (u + v) - U)
      (v := mulCLM hs U v + v) .rfl .rfl,
    coeFn_inclusionLp_sub_ae_eq h (u := expSubOne hs (u + v)) (v := U) .rfl .rfl,
    coeFn_inclusionLp_add_ae_eq h (u := mulCLM hs U v) (v := v) .rfl .rfl,
    coeFn_inclusionLp_add_ae_eq h (u := mulCLM hs U (V - v)) (v := V - v) .rfl .rfl,
    coeFn_inclusionLp_sub_ae_eq h (u := V) (v := v) .rfl .rfl,
    coeFn_inclusionLp_mulCLM hs h U v, coeFn_inclusionLp_mulCLM hs h U (V - v),
    coeFn_inclusionLp_expSubOne hs h (u + v), coeFn_inclusionLp_expSubOne hs h u,
    coeFn_inclusionLp_expSubOne hs h v, coeFn_inclusionLp_add_ae_eq h (u := u) (v := v) .rfl .rfl]
    with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ e₁ e₂ e₃ h₈
  rw [h₁, h₂, h₃, h₄, h₆, h₇, h₅, e₁, e₂, e₃, h₈, Complex.exp_add]
  ring

/-- **The derivative of the exponential on `H^s(E)`, `s > dim E / 2`.** The map
`u ↦ exp u - 1` has derivative `v ↦ (exp u - 1) v + v` at `u`. -/
theorem hasFDerivAt_expSubOne (hs : finrank ℝ E < 2 * s) (u : H^{s}(E)) :
    HasFDerivAt (expSubOne hs) (mulCLM hs (expSubOne hs u) + ContinuousLinearMap.id ℂ _) u := by
  obtain ⟨K, hK⟩ := exists_norm_expSubOne_sub_le (E := E) hs
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO (g := fun v : H^{s}(E) ↦ ‖v‖ ^ 2) ?_
    (isLittleO_norm_pow_id one_lt_two)
  refine IsBigO.of_bound ((‖mulCLM hs (expSubOne hs u)‖ + 1) * K) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : H^{s}(E)) zero_lt_one] with v hv
  rw [mem_closedBall_zero_iff] at hv
  simp only [add_apply, ContinuousLinearMap.coe_id', id_eq, norm_pow,
    norm_norm]
  rw [expSubOne_add_sub hs u v]
  calc ‖mulCLM hs (expSubOne hs u) (expSubOne hs v - v) + (expSubOne hs v - v)‖
      ≤ ‖mulCLM hs (expSubOne hs u)‖ * ‖expSubOne hs v - v‖ + ‖expSubOne hs v - v‖ :=
        (norm_add_le _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
    _ = (‖mulCLM hs (expSubOne hs u)‖ + 1) * ‖expSubOne hs v - v‖ := by ring
    _ ≤ (‖mulCLM hs (expSubOne hs u)‖ + 1) * (K * ‖v‖ ^ 2) := by gcongr; exact hK v hv
    _ = (‖mulCLM hs (expSubOne hs u)‖ + 1) * K * ‖v‖ ^ 2 := by ring

/-- The exponential on `H^s(E)`, `s > dim E / 2`, is differentiable. -/
theorem differentiable_expSubOne (hs : finrank ℝ E < 2 * s) :
    Differentiable ℂ (expSubOne (E := E) hs) :=
  fun u ↦ (hasFDerivAt_expSubOne hs u).differentiableAt

/-- **The exponential on `H^s(E)`, `s > dim E / 2`, is smooth.** -/
theorem contDiff_expSubOne (hs : finrank ℝ E < 2 * s) :
    ContDiff ℂ ∞ (expSubOne (E := E) hs) := by
  refine contDiff_infty.2 fun n ↦ ?_
  induction n with
  | zero => exact contDiff_zero.2 (differentiable_expSubOne hs).continuous
  | succ n ih =>
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨_,
      ((mulCLM hs).contDiff.comp ih).add contDiff_const, hasFDerivAt_expSubOne hs⟩

end BesselPotentialSpace
