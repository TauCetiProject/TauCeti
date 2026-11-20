/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Basic
public import TauCeti.MeasureTheory.Integral.RieszPotential.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Integral.MeanInequalities
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.MeasureTheory.Integral.SchurTest
import TauCeti.MeasureTheory.Measure.Restrict.Basic
import TauCeti.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Bounded-domain diameter estimates for Riesz potentials and weakly singular integral operators

On a nontrivial space `E` of finite dimension `n = finrank ℝ E`, for orders `0 < α < n` the
whole-space Hardy–Littlewood–Sobolev inequality (`TauCeti.exists_eLpNorm_rieszPotential_le`) bounds
the Riesz potential `rieszPotential μ α f x = ∫⁻ y, ‖x - y‖ₑ ^ (α - n) * ‖f y‖ₑ ∂μ` from `Lᵖ(E)`
to `L^q(E)` for `1 < p < n / α` at the scaling exponent `1/q = 1/p - α/n` (`p < q < ∞`), while on
measurable sets of finite measure the rearrangement estimate
`TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le` covers `0 < α ≤ n` and finite exponents
`1 ≤ p ≤ q < ∞` with `n * (1/p - 1/q) < α`.

When integration is restricted to a bounded set `Ω` (`μ.restrict Ω`), there is no far-field tail:
for every `x ∈ closure Ω` the domain `Ω` lies inside `closedBall x (diam Ω)`, where the radial
integral of `‖x - y‖ ^ s` converges for every `s > -n`
(`TauCeti.setLIntegral_enorm_sub_rpow_le_of_mem_closure`). Consequently,
`rieszPotential (μ.restrict Ω) α` satisfies explicit diameter-weighted estimates across all orders
`α > 0` (including `α > n`, where the kernel `‖x - y‖ ^ (α - n)` grows with distance) and all
exponent pairs `1 ≤ p ≤ q ≤ ∞` above the scaling threshold (including `α = n` at
`(p, q) = (1, ∞)`):

* **Pointwise `Lᵖ → L^∞` estimates on closed balls and `closure Ω`**
  (`TauCeti.rieszPotential_restrict_le_of_subset_closedBall` and
  `TauCeti.rieszPotential_restrict_le_of_mem_closure`, Brenner–Scott, Lemma 4.3.1): if `n / p < α`,
  or `p = 1` and `n ≤ α`, then whenever `Ω ⊆ closedBall x D` we have
  `rieszPotential (μ.restrict Ω) α f x ≤ rieszDiamConst μ α p ∞ * D ^ (α - n / p) * ‖f‖_{Lᵖ(Ω)}`
  (generalizing the `α = 1`, `n < p < ∞` estimate
  `TauCeti.setLIntegral_mul_enorm_sub_rpow_one_sub_finrank_le`), and in particular for every
  `x ∈ closure Ω` one may take `D = diam Ω`.
* **Sharpness below the threshold** (`TauCeti.exists_memLp_rieszPotential_restrict_eq_top`): on a
  nontrivial space, for any `p : ℝ≥0∞`, if `α < n * p.toReal⁻¹` and `x ∈ interior Ω`, there exists
  `f ∈ Lᵖ(Ω)` with `rieszPotential (μ.restrict Ω) α f x = ∞`.
* **`Lᵖ → L^q` and `Lᵖ → Lᵖ` norm estimates** (`TauCeti.eLpNorm_rieszPotential_restrict_le_of_le`
  and `TauCeti.eLpNorm_rieszPotential_restrict_le`, Brenner–Scott, Lemma 4.3.6): if `1 ≤ p ≤ q ≤ ∞`
  and `n * (1/p - 1/q) < α` (or `p = 1`, `q = ∞`, `n ≤ α`), then
  `‖rieszPotential (μ.restrict Ω) α f‖_{L^q(Ω)}` is bounded by
  `rieszDiamConst μ α p q * (diam Ω) ^ (α - n * (1/p - 1/q)) * ‖f‖_{Lᵖ(Ω)}`.
  In particular, for `p = q` (`1 ≤ p ≤ ∞`) and every `α > 0`, the prefactor is
  `(n * μ.real (ball 0 1) / α) * (diam Ω) ^ α`.
* **Operator-valued Bochner kernels dominated by a Riesz kernel**
  (`TauCeti.norm_setIntegral_apply_le_of_riesz_bound`,
  `TauCeti.eLpNorm_setIntegral_apply_le_of_riesz_bound`,
  `TauCeti.lpNorm_setIntegral_apply_le_of_riesz_bound_of_le`,
  `TauCeti.lpNorm_setIntegral_apply_le_of_riesz_bound`, and
  `TauCeti.integralOperatorLpOfRieszBound`): on a measurable bounded set `Ω`, at a fixed point
  `x ∈ closure Ω`, if `T : E → (G →L[𝕜] H)` satisfies `‖T y‖ ≤ C * ‖x - y‖ ^ (α - n)` for all
  `y ∈ Ω` with `x ≠ y` and `u ∈ Lᵖ(Ω)` above the scaling threshold, then `∫ y in Ω, T y (u y) ∂μ`
  satisfies the corresponding pointwise norm bound; and if `K : E → E → (G →L[𝕜] H)` is jointly
  a.e. strongly measurable on `Ω × Ω` and satisfies `‖K x y‖ ≤ C * ‖x - y‖ ^ (α - n)` off the
  diagonal on `Ω × Ω`, then `x ↦ ∫ y in Ω, K x y (u y) ∂μ` satisfies the corresponding `Lᵖ → L^q`
  `eLpNorm` and `lpNorm` bounds (with `TauCeti.lpNorm_setIntegral_apply_le_of_riesz_bound` as the
  `Lᵖ → Lᵖ` real `lpNorm` specialization) and induces a bundled continuous linear operator
  `Lp G p (μ.restrict Ω) →L[𝕜] Lp H p (μ.restrict Ω)`.

The `ℝ≥0∞` potential estimates require neither measurability of `Ω` (since `closure Ω` and
`closedBall x D` are closed) nor measurability of `f`.

## Main declarations

* `TauCeti.rieszDiamConst`, `TauCeti.rieszDiamConst_def`: the geometric constant in the
  bounded-domain `Lᵖ → L^q` Riesz bound.
* `TauCeti.rieszPotential_restrict_le_of_subset_closedBall`,
  `TauCeti.rieszPotential_restrict_le_of_mem_closure`: pointwise `Lᵖ → L^∞` bounds.
* `TauCeti.eLpNorm_rieszPotential_restrict_le_of_le`,
  `TauCeti.eLpNorm_rieszPotential_restrict_le`: `Lᵖ → L^q` and `Lᵖ → Lᵖ` norm bounds on bounded
  sets.
* `TauCeti.norm_setIntegral_apply_le_of_riesz_bound`,
  `TauCeti.eLpNorm_setIntegral_apply_le_of_riesz_bound`,
  `TauCeti.lpNorm_setIntegral_apply_le_of_riesz_bound_of_le`,
  `TauCeti.lpNorm_setIntegral_apply_le_of_riesz_bound`,
  `TauCeti.integralOperatorLpOfRieszBound`: pointwise `closure Ω` bound, `Lᵖ → L^q` `eLpNorm` and
  `lpNorm` bounds, `Lᵖ → Lᵖ` `lpNorm` specialization, and bundled operator on `Lᵖ(Ω)` for Bochner
  integral operators with Riesz-dominated kernels.
* `TauCeti.exists_memLp_rieszPotential_restrict_eq_top`: divergence at interior poles when
  `α < n * p.toReal⁻¹`.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, Chapter 4, Lemmas 4.3.1 and 4.3.6.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001, §7.8.
-/

public section

noncomputable section

open Function MeasureTheory Metric Module Set
open scoped ENNReal NNReal

namespace TauCeti

section DiamConst

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- The geometric constant in the bounded-domain `Lᵖ → L^q` Riesz potential bound of order `α` for
a measure `μ` on `E` of dimension `n = finrank ℝ E`. Writing `δ = p.toReal⁻¹ - q.toReal⁻¹` and
`ω = μ.real (ball 0 1)`,
`rieszDiamConst μ α p q = (n * ω * (1 - δ) / (α - n * δ)) ^ (1 - δ)`.

For `p = q` (`δ = 0`) this simplifies to `n * ω / α`; for `(p, q) = (1, ∞)` (`δ = 1`) it
simplifies to `1`; and for `q = ∞`, `1 < p < ∞` it gives the Hölder radial constant
`(n * ω * (1 - 1/p) / (α - n/p)) ^ (1 - 1/p)`. -/
def rieszDiamConst (μ : Measure E) (α : ℝ) (p q : ℝ≥0∞) : ℝ :=
  let δ := p.toReal⁻¹ - q.toReal⁻¹
  ((finrank ℝ E : ℝ) * μ.real (ball 0 1) * (1 - δ) / (α - (finrank ℝ E : ℝ) * δ)) ^ (1 - δ)

/-- Explicit formula for `TauCeti.rieszDiamConst`. -/
theorem rieszDiamConst_def (μ : Measure E) (α : ℝ) (p q : ℝ≥0∞) :
    rieszDiamConst μ α p q =
      ((finrank ℝ E : ℝ) * μ.real (ball 0 1) * (1 - (p.toReal⁻¹ - q.toReal⁻¹)) /
        (α - (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹))) ^
      (1 - (p.toReal⁻¹ - q.toReal⁻¹)) :=
  (rfl)

/-- At `p = q`, the bounded-domain Riesz constant is `n * μ.real (ball 0 1) / α`. -/
@[simp]
theorem rieszDiamConst_self (μ : Measure E) (α : ℝ) (p : ℝ≥0∞) :
    rieszDiamConst μ α p p = (finrank ℝ E : ℝ) * μ.real (ball 0 1) / α := by
  simp [rieszDiamConst]

/-- At `(p, q) = (1, ∞)`, the bounded-domain Riesz constant is `1`. -/
@[simp]
theorem rieszDiamConst_one_top (μ : Measure E) (α : ℝ) :
    rieszDiamConst μ α 1 ∞ = 1 := by
  simp [rieszDiamConst]

/-- On a zero-dimensional space, `rieszDiamConst μ α p q` vanishes whenever
`p.toReal⁻¹ - q.toReal⁻¹ ≠ 1`. -/
theorem rieszDiamConst_of_subsingleton [Subsingleton E] (μ : Measure E) (α : ℝ) {p q : ℝ≥0∞}
    (hδ : p.toReal⁻¹ - q.toReal⁻¹ ≠ 1) : rieszDiamConst μ α p q = 0 := by
  have h1 : 1 - (p.toReal⁻¹ - q.toReal⁻¹) ≠ 0 := sub_ne_zero.2 hδ.symm
  simp [rieszDiamConst, finrank_zero_of_subsingleton, Real.zero_rpow h1]

/-- The constant `rieszDiamConst μ α p q` is nonnegative for `1 ≤ p` and
`n * (1/p - 1/q) ≤ α`. -/
theorem rieszDiamConst_nonneg (μ : Measure E) {α : ℝ} {p q : ℝ≥0∞} (hp : 1 ≤ p)
    (hα : (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹) ≤ α) :
    0 ≤ rieszDiamConst μ α p q := by
  apply Real.rpow_nonneg
  exact div_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg)
      (sub_nonneg.2 (ENNReal.toReal_inv_sub_toReal_inv_le_one hp q)))
    (sub_nonneg.2 hα)

/-- On a nontrivial space with an additive Haar measure, `rieszDiamConst μ α p q` is strictly
positive when `1 ≤ p` and `n * (1/p - 1/q) < α`. -/
theorem rieszDiamConst_pos [Nontrivial E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} {p q : ℝ≥0∞} (hp : 1 ≤ p)
    (hα : (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹) < α) :
    0 < rieszDiamConst μ α p q := by
  rw [rieszDiamConst]
  rcases (ENNReal.toReal_inv_sub_toReal_inv_le_one hp q).eq_or_lt with h1 | hlt
  · simp [h1]
  have hn : (0 : ℝ) < finrank ℝ E := Nat.cast_pos.2 finrank_pos
  have hω : 0 < μ.real (ball 0 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  exact Real.rpow_pos_of_pos (div_pos (mul_pos (mul_pos hn hω) (sub_pos.2 hlt)) (sub_pos.2 hα)) _

end DiamConst

private theorem add_sub_mul_one_sub_inv_eq {n α δ : ℝ} (hδ : δ < 1) :
    n + (α - n) * (1 - δ)⁻¹ = (α - n * δ) / (1 - δ) := by
  have : 1 - δ ≠ 0 := (sub_pos.2 hδ).ne'
  rw [← div_eq_mul_inv]
  field_simp
  ring

private theorem neg_lt_sub_mul_one_sub_inv {n α δ : ℝ} (hδ : δ < 1) (hα : n * δ < α) :
    -n < (α - n) * (1 - δ)⁻¹ := by
  have hpos : 0 < n + (α - n) * (1 - δ)⁻¹ := by
    rw [add_sub_mul_one_sub_inv_eq hδ]
    exact div_pos (sub_pos.2 hα) (sub_pos.2 hδ)
  linarith

section Estimates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [TopologicalSpace F] [ContinuousENorm F]

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Rewriting the `(1 - δ)`-th power of the closed-ball kernel integral with exponent
`s = (α - n) * (1 - δ)⁻¹` into `rieszDiamConst μ α p q * D ^ (α - n * δ)`. -/
private theorem ofReal_kernel_integral_rpow_eq {α D : ℝ} {p q : ℝ≥0∞}
    (hD : 0 ≤ D) (hδ : p.toReal⁻¹ - q.toReal⁻¹ < 1)
    (hα : (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹) < α) :
    ENNReal.ofReal ((finrank ℝ E : ℝ) * μ.real (ball 0 1) *
        (D ^ ((finrank ℝ E : ℝ) + (α - finrank ℝ E) * (1 - (p.toReal⁻¹ - q.toReal⁻¹))⁻¹) /
          ((finrank ℝ E : ℝ) + (α - finrank ℝ E) * (1 - (p.toReal⁻¹ - q.toReal⁻¹))⁻¹))) ^
      (1 - (p.toReal⁻¹ - q.toReal⁻¹)) =
    ENNReal.ofReal (rieszDiamConst μ α p q *
      D ^ (α - (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹))) := by
  set n := (finrank ℝ E : ℝ)
  set δ := p.toReal⁻¹ - q.toReal⁻¹
  set s := (α - n) * (1 - δ)⁻¹
  have h1δ : 0 < 1 - δ := sub_pos.2 hδ
  have h1δ_ne : 1 - δ ≠ 0 := h1δ.ne'
  have hαn : 0 < α - n * δ := sub_pos.2 hα
  have hns_eq : n + s = (α - n * δ) / (1 - δ) := add_sub_mul_one_sub_inv_eq hδ
  have hns : 0 < n + s := hns_eq ▸ div_pos hαn h1δ
  have hbase : 0 ≤ n * μ.real (ball 0 1) * (D ^ (n + s) / (n + s)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg)
      (div_nonneg (Real.rpow_nonneg hD _) hns.le)
  rw [ENNReal.ofReal_rpow_of_nonneg hbase h1δ.le]
  congr 1
  have hcoeff :
      n * μ.real (ball 0 1) / (n + s) = n * μ.real (ball 0 1) * (1 - δ) / (α - n * δ) := by
    rw [hns_eq]; field_simp
  have hexp : (n + s) * (1 - δ) = α - n * δ := by
    rw [hns_eq, div_mul_cancel₀ _ h1δ_ne]
  calc (n * μ.real (ball 0 1) * (D ^ (n + s) / (n + s))) ^ (1 - δ)
      = (n * μ.real (ball 0 1) / (n + s) * D ^ (n + s)) ^ (1 - δ) := by ring_nf
    _ = (n * μ.real (ball 0 1) / (n + s)) ^ (1 - δ) * (D ^ (n + s)) ^ (1 - δ) :=
        Real.mul_rpow (div_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg) hns.le)
          (Real.rpow_nonneg hD _)
    _ = rieszDiamConst μ α p q * D ^ (α - n * δ) := by
        rw [hcoeff, ← Real.rpow_mul hD, hexp, rieszDiamConst]

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- Endpoint `p = 1`, `n ≤ α` of `rieszPotential_restrict_le_of_subset_closedBall`: on
`closedBall x D`, `‖x - y‖ ^ (α - n) ≤ D ^ (α - n)`. -/
private theorem rieszPotential_restrict_le_one_of_subset_closedBall {Ω : Set E} {x : E} {D α : ℝ}
    (hΩ : Ω ⊆ closedBall x D) (hαn : (finrank ℝ E : ℝ) ≤ α) (f : E → F) :
    rieszPotential (μ.restrict Ω) α f x ≤
      ENNReal.ofReal (D ^ (α - finrank ℝ E)) * eLpNorm f 1 (μ.restrict Ω) := by
  rw [rieszPotential_def]
  calc ∫⁻ y in Ω, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ
      ≤ ∫⁻ y in Ω, ENNReal.ofReal (D ^ (α - finrank ℝ E)) * ‖f y‖ₑ ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hΩ
          (ae_restrict_mem measurableSet_closedBall)] with y hy
        have hxy : ‖x - y‖ ≤ D := by simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hy
        gcongr
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (sub_nonneg.2 hαn)]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hxy (sub_nonneg.2 hαn))
    _ = ENNReal.ofReal (D ^ (α - finrank ℝ E)) * ∫⁻ y in Ω, ‖f y‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (D ^ (α - finrank ℝ E)) * eLpNorm f 1 (μ.restrict Ω) :=
        mul_le_mul_right lintegral_eNorm_le_eLpNorm_one _

/-- Case `1 < p ≤ ∞`, `n * p.toReal⁻¹ < α` of `rieszPotential_restrict_le_of_subset_closedBall`,
by Hölder's inequality (`TauCeti.lintegral_mul_le_rpow_mul_eLpNorm`) and the exact closed-ball
radial integral (`TauCeti.setLIntegral_closedBall_enorm_sub_rpow`). -/
private theorem rieszPotential_restrict_le_of_one_lt_of_subset_closedBall [Nontrivial E]
    {Ω : Set E} {x : E} {D α : ℝ} {p : ℝ≥0∞} (hΩ : Ω ⊆ closedBall x D) (hD_pos : 0 < D)
    (hp1 : 1 < p) (hαp : (finrank ℝ E : ℝ) * p.toReal⁻¹ < α) (f : E → F) :
    rieszPotential (μ.restrict Ω) α f x ≤
      ENNReal.ofReal (rieszDiamConst μ α p ∞ * D ^ (α - (finrank ℝ E : ℝ) * p.toReal⁻¹)) *
        eLpNorm f p (μ.restrict Ω) := by
  have hp_inv_lt : p.toReal⁻¹ < 1 := ENNReal.toReal_inv_lt_one hp1
  have hC_pos : 0 < rieszDiamConst μ α p ∞ * D ^ (α - (finrank ℝ E : ℝ) * p.toReal⁻¹) :=
    mul_pos (rieszDiamConst_pos μ hp1.le (by simpa using hαp)) (Real.rpow_pos_of_pos hD_pos _)
  rcases eq_or_ne (eLpNorm f p (μ.restrict Ω)) ∞ with hN | hN
  · rw [hN, ENNReal.mul_top (ENNReal.ofReal_pos.2 hC_pos).ne']; exact le_top
  have hf : AEStronglyMeasurable f (μ.restrict Ω) := aestronglyMeasurable_of_eLpNorm_ne_top hN
  have hk : Measurable fun y : E => ‖x - y‖ₑ ^ (α - finrank ℝ E) := by fun_prop
  set δ := p.toReal⁻¹
  set s := (α - finrank ℝ E) * (1 - δ)⁻¹
  have hs : -(finrank ℝ E : ℝ) < s := neg_lt_sub_mul_one_sub_inv hp_inv_lt hαp
  have hker : ∫⁻ y in Ω, (‖x - y‖ₑ ^ (α - finrank ℝ E)) ^ (1 - p.toReal⁻¹)⁻¹ ∂μ ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ) * μ.real (ball 0 1) *
        (D ^ ((finrank ℝ E : ℝ) + s) / ((finrank ℝ E : ℝ) + s))) := by
    simp_rw [← ENNReal.rpow_mul]
    exact (lintegral_mono_set hΩ).trans (setLIntegral_closedBall_enorm_sub_rpow hs hD_pos.le x).le
  rw [rieszPotential_def]
  calc ∫⁻ y in Ω, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ
      ≤ (∫⁻ y in Ω, (‖x - y‖ₑ ^ (α - finrank ℝ E)) ^ (1 - p.toReal⁻¹)⁻¹ ∂μ) ^ (1 - p.toReal⁻¹) *
          eLpNorm (fun y => ‖f y‖ₑ) p (μ.restrict Ω) :=
        lintegral_mul_le_rpow_mul_eLpNorm hk.aemeasurable hp1
    _ ≤ ENNReal.ofReal ((finrank ℝ E : ℝ) * μ.real (ball 0 1) *
            (D ^ ((finrank ℝ E : ℝ) + s) / ((finrank ℝ E : ℝ) + s))) ^ (1 - p.toReal⁻¹) *
          eLpNorm f p (μ.restrict Ω) := by
        rw [eLpNorm_eNorm _ hf]
        exact mul_le_mul_left (ENNReal.rpow_le_rpow hker (sub_pos.2 hp_inv_lt).le) _
    _ = _ := by
        have hid := ofReal_kernel_integral_rpow_eq (μ := μ) (α := α) (p := p) (q := ∞) hD_pos.le
          (by simpa using hp_inv_lt) (by simpa using hαp)
        simpa only [ENNReal.toReal_top, inv_zero, sub_zero] using
          congrArg (· * eLpNorm f p (μ.restrict Ω)) hid

/-- **Pointwise `Lᵖ → L^∞` bound on a set inside a closed ball.** If `Ω ⊆ closedBall x D`,
`1 ≤ p ≤ ∞`, and either `n / p < α` or `p = 1` and `n ≤ α`, then
`rieszPotential (μ.restrict Ω) α f x ≤ rieszDiamConst μ α p ∞ * D ^ (α - n / p) * ‖f‖_{Lᵖ(Ω)}`.
Neither measurability of `Ω` nor measurability of `f` is required. -/
theorem rieszPotential_restrict_le_of_subset_closedBall {Ω : Set E} {x : E} {D α : ℝ} {p : ℝ≥0∞}
    (hΩ : Ω ⊆ closedBall x D) (hp : 1 ≤ p)
    (hα : (finrank ℝ E : ℝ) * p.toReal⁻¹ < α ∨ (p = 1 ∧ (finrank ℝ E : ℝ) ≤ α)) (f : E → F) :
    rieszPotential (μ.restrict Ω) α f x ≤
      ENNReal.ofReal (rieszDiamConst μ α p ∞ * D ^ (α - (finrank ℝ E : ℝ) * p.toReal⁻¹)) *
        eLpNorm f p (μ.restrict Ω) := by
  rcases Ω.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · simp [rieszPotential_def]
  have hD : 0 ≤ D := dist_nonneg.trans (mem_closedBall.1 (hΩ hy₀))
  rcases eq_or_ne p 1 with rfl | hp_ne_one
  · have hαn : (finrank ℝ E : ℝ) ≤ α :=
      hα.elim (fun h => by simpa using h.le) And.right
    simpa using rieszPotential_restrict_le_one_of_subset_closedBall (μ := μ) hΩ hαn f
  have hαp : (finrank ℝ E : ℝ) * p.toReal⁻¹ < α := hα.resolve_right fun h => hp_ne_one h.1
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact (rieszPotential_eq_zero_of_subsingleton _
      (by simpa [finrank_zero_of_subsingleton] using hαp) f).symm ▸ by simp
  rcases hD.eq_or_lt with rfl | hD_pos
  · have hzero : μ.restrict Ω = 0 := Measure.measure_univ_eq_zero.1 <|
      Measure.restrict_apply_univ Ω ▸ measure_mono_null (hΩ.trans (by simp)) (measure_singleton x)
    simp [hzero, rieszPotential_def]
  exact rieszPotential_restrict_le_of_one_lt_of_subset_closedBall hΩ hD_pos
    (hp.lt_of_ne' hp_ne_one) hαp f

/-- Finiteness form of `TauCeti.rieszPotential_restrict_le_of_subset_closedBall`. -/
theorem rieszPotential_restrict_lt_top_of_subset_closedBall {Ω : Set E} {x : E} {D α : ℝ}
    {p : ℝ≥0∞} {f : E → F} (hΩ : Ω ⊆ closedBall x D) (hp : 1 ≤ p)
    (hα : (finrank ℝ E : ℝ) * p.toReal⁻¹ < α ∨ (p = 1 ∧ (finrank ℝ E : ℝ) ≤ α))
    (hf : MemLp f p (μ.restrict Ω)) :
    rieszPotential (μ.restrict Ω) α f x < ∞ :=
  (rieszPotential_restrict_le_of_subset_closedBall hΩ hp hα f).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

/-- **Pointwise `Lᵖ → L^∞` Riesz potential bound on `closure Ω`** (Brenner–Scott, Lemma 4.3.1).
For a bounded set `Ω`, `x ∈ closure Ω`, `1 ≤ p ≤ ∞`, and `n / p < α` (or `p = 1` and `n ≤ α`),
`rieszPotential (μ.restrict Ω) α f x` is bounded by
`rieszDiamConst μ α p ∞ * (diam Ω) ^ (α - n / p) * ‖f‖_{Lᵖ(Ω)}`. -/
theorem rieszPotential_restrict_le_of_mem_closure {Ω : Set E} {x : E} {α : ℝ} {p : ℝ≥0∞}
    (hb : Bornology.IsBounded Ω) (hx : x ∈ closure Ω) (hp : 1 ≤ p)
    (hα : (finrank ℝ E : ℝ) * p.toReal⁻¹ < α ∨ (p = 1 ∧ (finrank ℝ E : ℝ) ≤ α)) (f : E → F) :
    rieszPotential (μ.restrict Ω) α f x ≤
      ENNReal.ofReal (rieszDiamConst μ α p ∞ * diam Ω ^ (α - (finrank ℝ E : ℝ) * p.toReal⁻¹)) *
        eLpNorm f p (μ.restrict Ω) :=
  rieszPotential_restrict_le_of_subset_closedBall
    (fun _ hy => mem_closedBall.2
      ((dist_le_diam_of_mem hb.closure (subset_closure hy) hx).trans_eq (diam_closure Ω)))
    hp hα f

/-- Finiteness of `rieszPotential (μ.restrict Ω) α f x` at every `x ∈ closure Ω` when `f ∈ Lᵖ(Ω)`
and `n / p < α` (or `p = 1` and `n ≤ α`). -/
theorem rieszPotential_restrict_lt_top_of_mem_closure {Ω : Set E} {x : E} {α : ℝ} {p : ℝ≥0∞}
    {f : E → F} (hb : Bornology.IsBounded Ω) (hx : x ∈ closure Ω) (hp : 1 ≤ p)
    (hα : (finrank ℝ E : ℝ) * p.toReal⁻¹ < α ∨ (p = 1 ∧ (finrank ℝ E : ℝ) ≤ α))
    (hf : MemLp f p (μ.restrict Ω)) :
    rieszPotential (μ.restrict Ω) α f x < ∞ :=
  (rieszPotential_restrict_le_of_mem_closure hb hx hp hα f).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

/-- Natural-number order specialization of `TauCeti.rieszPotential_restrict_le_of_mem_closure`
written in terms of `(finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k)`. -/
theorem rieszPotential_restrict_natCast_le_of_mem_closure {Ω : Set E} {x : E} {k : ℕ} {p : ℝ≥0∞}
    (hb : Bornology.IsBounded Ω) (hx : x ∈ closure Ω) (hp : 1 ≤ p)
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k)) (f : E → F) :
    rieszPotential (μ.restrict Ω) k f x ≤
      ENNReal.ofReal
        (rieszDiamConst μ k p ∞ * diam Ω ^ ((k : ℝ) - (finrank ℝ E : ℝ) * p.toReal⁻¹)) *
        eLpNorm f p (μ.restrict Ω) :=
  rieszPotential_restrict_le_of_mem_closure hb hx hp
    (hkp.imp (ENNReal.natCast_lt_natCast_mul_iff (zero_lt_one.trans_le hp).ne').1
      (And.imp_right Nat.cast_le.2)) f

/-- Endpoint `L¹ → L^∞` Riesz potential bound for `(p, q) = (1, ∞)` on a bounded set. -/
private theorem eLpNorm_top_rieszPotential_restrict_le_one {Ω : Set E}
    (hb : Bornology.IsBounded Ω) {α : ℝ} (hα : (finrank ℝ E : ℝ) ≤ α) (f : E → F) :
    eLpNorm (rieszPotential (μ.restrict Ω) α f) ∞ (μ.restrict Ω) ≤
      ENNReal.ofReal (diam Ω ^ (α - finrank ℝ E)) * eLpNorm f 1 (μ.restrict Ω) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hα_nn : 0 ≤ α := by simpa [finrank_zero_of_subsingleton] using hα
    rcases hα_nn.eq_or_lt with rfl | hα0
    · have hconst : rieszPotential (μ.restrict Ω) 0 f = fun _ => ∫⁻ y in Ω, ‖f y‖ₑ ∂μ := by
        funext x; simp [rieszPotential_def, finrank_zero_of_subsingleton]
      rw [hconst, eLpNorm_exponent_top aestronglyMeasurable_const]
      simp only [finrank_zero_of_subsingleton, Nat.cast_zero, sub_self, Real.rpow_zero,
        ENNReal.ofReal_one, one_mul]
      exact (eLpNormEssSup_le_of_ae_eNorm_bound
        (.of_forall fun _ => by simp)).trans lintegral_eNorm_le_eLpNorm_one
    · simp [rieszPotential_eq_zero_of_subsingleton _ hα0]
  rcases (diam_nonneg (s := Ω)).eq_or_lt with hd0 | hd_pos
  · simp [Measure.restrict_eq_zero_of_diam_eq_zero hb hd0.symm]
  rcases eq_or_ne (eLpNorm f 1 (μ.restrict Ω)) ∞ with hN | hN
  · rw [hN, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hd_pos _)).ne']
    exact le_top
  have hf : AEStronglyMeasurable f (μ.restrict Ω) := aestronglyMeasurable_of_eLpNorm_ne_top hN
  have hmeas := (aemeasurable_rieszPotential (α := α) hf.eNorm).aestronglyMeasurable
  rw [eLpNorm_exponent_top hmeas]
  refine eLpNormEssSup_le_of_ae_eNorm_bound ?_
  filter_upwards [ae_restrict_mem_closure Ω] with x hx
  rw [eNorm_eq_self]
  simpa using rieszPotential_restrict_le_of_mem_closure hb hx le_rfl (Or.inr ⟨rfl, hα⟩) f

/-- Non-endpoint `Lᵖ → L^q` Riesz potential bound (`1/p - 1/q < 1`) via Young's inequality for
integral kernels (`TauCeti.eLpNorm_lintegral_mul_le_of_le`). -/
private theorem eLpNorm_rieszPotential_restrict_le_of_sub_lt_one {Ω : Set E}
    (hb : Bornology.IsBounded Ω) {α : ℝ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hδ : p.toReal⁻¹ - q.toReal⁻¹ < 1)
    (hα' : (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹) < α) (f : E → F) :
    eLpNorm (rieszPotential (μ.restrict Ω) α f) q (μ.restrict Ω) ≤
      ENNReal.ofReal (rieszDiamConst μ α p q *
        diam Ω ^ (α - (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹))) *
        eLpNorm f p (μ.restrict Ω) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact (rieszPotential_eq_zero_of_subsingleton _
      (by simpa [finrank_zero_of_subsingleton] using hα') f).symm ▸ by simp
  rcases (diam_nonneg (s := Ω)).eq_or_lt with hd0 | hd_pos
  · simp [Measure.restrict_eq_zero_of_diam_eq_zero hb hd0.symm]
  have hC_pos : 0 < rieszDiamConst μ α p q *
      diam Ω ^ (α - (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹)) :=
    mul_pos (rieszDiamConst_pos μ hp hα') (Real.rpow_pos_of_pos hd_pos _)
  rcases eq_or_ne (eLpNorm f p (μ.restrict Ω)) ∞ with hN | hN
  · rw [hN, ENNReal.mul_top (ENNReal.ofReal_pos.2 hC_pos).ne']; exact le_top
  have hf : AEStronglyMeasurable f (μ.restrict Ω) := aestronglyMeasurable_of_eLpNorm_ne_top hN
  set δ := p.toReal⁻¹ - q.toReal⁻¹
  set s := (α - finrank ℝ E) * (1 - δ)⁻¹
  have hs : -(finrank ℝ E : ℝ) < s := neg_lt_sub_mul_one_sub_inv hδ hα'
  set A := ENNReal.ofReal ((finrank ℝ E : ℝ) * μ.real (ball 0 1) *
    (diam Ω ^ ((finrank ℝ E : ℝ) + s) / ((finrank ℝ E : ℝ) + s)))
  have hrow : ∀ᵐ x ∂μ.restrict Ω,
      ∫⁻ y in Ω, (‖x - y‖ₑ ^ (α - finrank ℝ E)) ^ (1 - δ)⁻¹ ∂μ ≤ A := by
    filter_upwards [ae_restrict_mem_closure Ω] with x hx
    simp_rw [← ENNReal.rpow_mul]
    exact setLIntegral_enorm_sub_rpow_le_of_mem_closure hs hb hx
  have hcol : ∀ᵐ y ∂μ.restrict Ω,
      ∫⁻ x in Ω, (‖x - y‖ₑ ^ (α - finrank ℝ E)) ^ (1 - δ)⁻¹ ∂μ ≤ A := by
    filter_upwards [ae_restrict_mem_closure Ω] with y hy
    simp_rw [← ENNReal.rpow_mul, eNorm_sub_rev]
    exact setLIntegral_enorm_sub_rpow_le_of_mem_closure hs hb hy
  have hk : Measurable (uncurry fun x y : E => ‖x - y‖ₑ ^ (α - finrank ℝ E)) := by fun_prop
  have hexp : (1 - p.toReal⁻¹) + q.toReal⁻¹ = 1 - δ := by dsimp [δ]; ring
  have h1p : 0 ≤ 1 - p.toReal⁻¹ := by
    simpa only [one_div] using ENNReal.one_sub_one_div_toReal_nonneg hp
  rw [funext (rieszPotential_def (μ.restrict Ω) α f)]
  calc eLpNorm (fun x => ∫⁻ y in Ω, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ) q (μ.restrict Ω)
      ≤ A ^ (1 - p.toReal⁻¹) * A ^ q.toReal⁻¹ *
          eLpNorm (fun y => ‖f y‖ₑ) p (μ.restrict Ω) :=
        eLpNorm_lintegral_mul_le_of_le hk.aemeasurable hf.eNorm hp hpq hδ hrow hcol
    _ = A ^ (1 - δ) * eLpNorm f p (μ.restrict Ω) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ h1p (by positivity), hexp, eLpNorm_eNorm _ hf]
    _ = _ := by rw [ofReal_kernel_integral_rpow_eq diam_nonneg hδ hα']

/-- **`Lᵖ → L^q` norm bound for the Riesz potential on a bounded set.** For `1 ≤ p ≤ q ≤ ∞` and
`n * (1/p - 1/q) < α` (or `p = 1`, `q = ∞`, `n ≤ α`),
`‖rieszPotential (μ.restrict Ω) α f‖_{L^q(Ω)}` is bounded by
`rieszDiamConst μ α p q * (diam Ω) ^ (α - n * (1/p - 1/q)) * ‖f‖_{Lᵖ(Ω)}`.
Neither measurability of `Ω` nor measurability of `f` is required. -/
theorem eLpNorm_rieszPotential_restrict_le_of_le {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {α : ℝ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hα : (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹) < α ∨
      (p = 1 ∧ q = ∞ ∧ (finrank ℝ E : ℝ) ≤ α))
    (f : E → F) :
    eLpNorm (rieszPotential (μ.restrict Ω) α f) q (μ.restrict Ω) ≤
      ENNReal.ofReal (rieszDiamConst μ α p q *
        diam Ω ^ (α - (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹))) *
        eLpNorm f p (μ.restrict Ω) := by
  by_cases hp1q : p = 1 ∧ q = ∞
  · rcases hp1q with ⟨rfl, rfl⟩
    have hαn : (finrank ℝ E : ℝ) ≤ α :=
      hα.elim (fun h => by simpa using h.le) fun h => h.2.2
    simpa using eLpNorm_top_rieszPotential_restrict_le_one hb hαn f
  exact eLpNorm_rieszPotential_restrict_le_of_sub_lt_one hb hp hpq
    (ENNReal.toReal_inv_sub_toReal_inv_lt_one hp (zero_lt_one.trans_le (hp.trans hpq)).ne' hp1q)
    (hα.resolve_right fun h => hp1q ⟨h.1, h.2.1⟩) f

/-- **`Lᵖ → Lᵖ` diameter bound for the Riesz potential on a bounded set**
(Brenner–Scott, Lemma 4.3.6). For every `1 ≤ p ≤ ∞` and every `0 < α` (including `α ≥ dim E`),
`‖rieszPotential (μ.restrict Ω) α f‖_{Lᵖ(Ω)}` is bounded by
`(n * μ.real (ball 0 1) / α) * (diam Ω) ^ α * ‖f‖_{Lᵖ(Ω)}`. -/
theorem eLpNorm_rieszPotential_restrict_le {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {α : ℝ} (hα : 0 < α) {p : ℝ≥0∞} (hp : 1 ≤ p) (f : E → F) :
    eLpNorm (rieszPotential (μ.restrict Ω) α f) p (μ.restrict Ω) ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ) * μ.real (ball 0 1) / α * diam Ω ^ α) *
        eLpNorm f p (μ.restrict Ω) := by
  simpa using eLpNorm_rieszPotential_restrict_le_of_le hb hp le_rfl (Or.inl (by simpa using hα)) f

/-- `MemLp` form of `TauCeti.eLpNorm_rieszPotential_restrict_le_of_le`. -/
theorem memLp_rieszPotential_restrict_of_le {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {α : ℝ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hα : (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹) < α ∨
      (p = 1 ∧ q = ∞ ∧ (finrank ℝ E : ℝ) ≤ α))
    {f : E → F} (hf : MemLp f p (μ.restrict Ω)) :
    MemLp (rieszPotential (μ.restrict Ω) α f) q (μ.restrict Ω) :=
  (eLpNorm_rieszPotential_restrict_le_of_le hb hp hpq hα f).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

/-- `MemLp` form of `TauCeti.eLpNorm_rieszPotential_restrict_le`: for `1 ≤ p ≤ ∞` and `0 < α`,
`rieszPotential (μ.restrict Ω) α` maps `Lᵖ(Ω)` into `Lᵖ(Ω)` on every bounded set `Ω`. -/
theorem memLp_rieszPotential_restrict {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {α : ℝ} (hα : 0 < α) {p : ℝ≥0∞} (hp : 1 ≤ p) {f : E → F}
    (hf : MemLp f p (μ.restrict Ω)) :
    MemLp (rieszPotential (μ.restrict Ω) α f) p (μ.restrict Ω) :=
  (eLpNorm_rieszPotential_restrict_le hb hα hp f).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

end Estimates

section OperatorKernel

variable {E 𝕜 G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Row operator-norm integral bound for a Riesz-dominated kernel on `μ.restrict Ω`. -/
private theorem ae_row_lintegral_enorm_le_of_riesz_bound [Nontrivial E] {Ω : Set E}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) {K : E → E → G →L[𝕜] H} {α C : ℝ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (hK : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖K x y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E)) :
    ∀ᵐ x ∂μ.restrict Ω, ∫⁻ y in Ω, ‖K x y‖ₑ ∂μ ≤
      ((C * ((finrank ℝ E : ℝ) * μ.real (ball 0 1) / α) * diam Ω ^ α).toNNReal : ℝ≥0∞) := by
  have hs : -(finrank ℝ E : ℝ) < α - finrank ℝ E := by linarith
  filter_upwards [ae_restrict_mem hΩ] with x hx
  calc ∫⁻ y in Ω, ‖K x y‖ₑ ∂μ
      ≤ ∫⁻ y in Ω, ENNReal.ofReal C * ‖x - y‖ₑ ^ (α - finrank ℝ E) ∂μ :=
        lintegral_mono_ae
          (ae_enorm_le_ofReal_mul_enorm_sub_rpow_of_norm_le (μ := μ) hΩ hC (hK x hx))
    _ = ENNReal.ofReal C * ∫⁻ y in Ω, ‖x - y‖ₑ ^ (α - finrank ℝ E) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((finrank ℝ E : ℝ) * μ.real (ball 0 1) *
          (diam Ω ^ ((finrank ℝ E : ℝ) + (α - finrank ℝ E)) /
            ((finrank ℝ E : ℝ) + (α - finrank ℝ E)))) :=
        mul_le_mul_right (setLIntegral_enorm_sub_rpow_le_of_mem_closure hs hb (subset_closure hx)) _
    _ = ENNReal.ofReal (C * ((finrank ℝ E : ℝ) * μ.real (ball 0 1) / α) * diam Ω ^ α) := by
        rw [add_sub_cancel, ← ENNReal.ofReal_mul hC]
        congr 1; ring
    _ = _ := (ENNReal.ofNNReal_toNNReal _).symm

/-- Column operator-norm integral bound for a Riesz-dominated kernel on `μ.restrict Ω`. -/
private theorem ae_col_lintegral_enorm_le_of_riesz_bound [Nontrivial E] {Ω : Set E}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) {K : E → E → G →L[𝕜] H} {α C : ℝ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (hK : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖K x y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E)) :
    ∀ᵐ y ∂μ.restrict Ω, ∫⁻ x in Ω, ‖K x y‖ₑ ∂μ ≤
      ((C * ((finrank ℝ E : ℝ) * μ.real (ball 0 1) / α) * diam Ω ^ α).toNNReal : ℝ≥0∞) :=
  ae_row_lintegral_enorm_le_of_riesz_bound (K := fun y x => K x y) hΩ hb hα hC
    fun y hy x hx hyx => by rw [norm_sub_rev]; exact hK x hx y hy hyx.symm

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem lintegral_enorm_apply_le_mul_rieszPotential {T : E → G →L[𝕜] H}
    {u : E → G} {x : E} {α : ℝ} {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hT : ∀ᵐ y ∂μ, ‖T y‖ₑ ≤ c * ‖x - y‖ₑ ^ (α - finrank ℝ E)) :
    ∫⁻ y, ‖T y (u y)‖ₑ ∂μ ≤ c * rieszPotential μ α u x := by
  calc ∫⁻ y, ‖T y (u y)‖ₑ ∂μ
      ≤ ∫⁻ y, c * (‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖u y‖ₑ) ∂μ := by
        refine lintegral_mono_ae (hT.mono fun y hy => (T y).le_opENorm (u y) |>.trans ?_)
        rw [← mul_assoc]
        exact mul_le_mul_left hy _
    _ = c * rieszPotential μ α u x := by
        rw [lintegral_const_mul' _ _ hc, rieszPotential_def]

/-- Pointwise Bochner integrability at `x ∈ closure Ω` for an operator-valued family `T` dominated
by a Riesz kernel of order `α` above the critical threshold `n / p` (or `p = 1` and `n ≤ α`). -/
theorem integrableOn_apply_of_riesz_bound_of_mem_closure [Nontrivial E] {Ω : Set E}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) {T : E → G →L[𝕜] H} {u : E → G}
    {x : E} (hx : x ∈ closure Ω) (hT_meas : AEStronglyMeasurable T (μ.restrict Ω))
    {α C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ y ∈ Ω, x ≠ y → ‖T y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E))
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hα : (finrank ℝ E : ℝ) * p.toReal⁻¹ < α ∨ (p = 1 ∧ (finrank ℝ E : ℝ) ≤ α))
    (hu : MemLp u p (μ.restrict Ω)) :
    IntegrableOn (fun y => T y (u y)) Ω μ :=
  ⟨isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hT_meas
    hu.aestronglyMeasurable,
    (lintegral_enorm_apply_le_mul_rieszPotential ENNReal.ofReal_ne_top
      (ae_enorm_le_ofReal_mul_enorm_sub_rpow_of_norm_le (μ := μ) hΩ hC hT)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (rieszPotential_restrict_lt_top_of_mem_closure hb hx hp hα hu))⟩

/-- Almost-everywhere Bochner integrability on `Ω` for `u ∈ Lᵖ(Ω)` (`1 ≤ p ≤ ∞`) against a
Riesz-dominated operator kernel of any positive order `α > 0`. -/
theorem ae_integrableOn_apply_of_riesz_bound [Nontrivial E] {Ω : Set E}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) {K : E → E → G →L[𝕜] H} {u : E → G}
    (hK_meas : AEStronglyMeasurable (uncurry K) ((μ.restrict Ω).prod (μ.restrict Ω)))
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hK : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖K x y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hu : MemLp u p (μ.restrict Ω)) :
    ∀ᵐ x ∂μ.restrict Ω, IntegrableOn (fun y => K x y (u y)) Ω μ :=
  ae_integrable_apply_of_memLp hK_meas hu hp
    (ae_row_lintegral_enorm_le_of_riesz_bound hΩ hb hα hC hK)
    (ae_col_lintegral_enorm_le_of_riesz_bound hΩ hb hα hC hK)

variable [NormedSpace ℝ H]

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- If an operator-valued family `T` satisfies `‖T y‖ₑ ≤ c * ‖x - y‖ₑ ^ (α - n)` a.e. under `μ` for
finite `c`, then `‖∫ y, T y (u y) ∂μ‖ₑ ≤ c * rieszPotential μ α u x`. -/
theorem enorm_integral_apply_le_mul_rieszPotential {T : E → G →L[𝕜] H}
    {u : E → G} {x : E} {α : ℝ} {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hT : ∀ᵐ y ∂μ, ‖T y‖ₑ ≤ c * ‖x - y‖ₑ ^ (α - finrank ℝ E)) :
    ‖∫ y, T y (u y) ∂μ‖ₑ ≤ c * rieszPotential μ α u x :=
  (eNorm_integral_le_lintegral_eNorm _).trans
    (lintegral_enorm_apply_le_mul_rieszPotential hc hT)

/-- **Pointwise `Lᵖ → L^∞` bound for a Riesz-dominated operator kernel on `closure Ω`.** If `Ω` is
measurable and bounded, `‖T y‖ ≤ C * ‖x - y‖ ^ (α - n)` for `y ∈ Ω` with `x ≠ y`, `u ∈ Lᵖ(Ω)`,
`1 ≤ p ≤ ∞`, and `n / p < α` (or `p = 1` and `n ≤ α`), then at `x ∈ closure Ω`,
`‖∫ y in Ω, T y (u y) ∂μ‖` is bounded by
`C * rieszDiamConst μ α p ∞ * (diam Ω) ^ (α - n / p) * lpNorm u p (μ.restrict Ω)`. -/
theorem norm_setIntegral_apply_le_of_riesz_bound [Nontrivial E] {Ω : Set E}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) {T : E → G →L[𝕜] H} {u : E → G}
    {x : E} (hx : x ∈ closure Ω) {α C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ y ∈ Ω, x ≠ y → ‖T y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E))
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hα : (finrank ℝ E : ℝ) * p.toReal⁻¹ < α ∨ (p = 1 ∧ (finrank ℝ E : ℝ) ≤ α))
    (hu : MemLp u p (μ.restrict Ω)) :
    ‖∫ y in Ω, T y (u y) ∂μ‖ ≤
      C * rieszDiamConst μ α p ∞ * diam Ω ^ (α - (finrank ℝ E : ℝ) * p.toReal⁻¹) *
        lpNorm u p (μ.restrict Ω) := by
  have hα_le : (finrank ℝ E : ℝ) * (p.toReal⁻¹ - (∞ : ℝ≥0∞).toReal⁻¹) ≤ α := by
    rcases hα with h | ⟨rfl, h⟩ <;> [simpa using h.le; simpa using h]
  have hconst_nn :
      0 ≤ C * rieszDiamConst μ α p ∞ * diam Ω ^ (α - (finrank ℝ E : ℝ) * p.toReal⁻¹) :=
    mul_nonneg (mul_nonneg hC (rieszDiamConst_nonneg μ hp hα_le)) (Real.rpow_nonneg diam_nonneg _)
  rw [← toReal_eLpNorm, ← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hconst_nn ENNReal.toReal_nonneg),
    ofReal_norm, ENNReal.ofReal_mul hconst_nn, ENNReal.ofReal_toReal hu.eLpNorm_lt_top.ne,
    mul_assoc C, ENNReal.ofReal_mul hC, mul_assoc]
  exact (enorm_integral_apply_le_mul_rieszPotential ENNReal.ofReal_ne_top
    (ae_enorm_le_ofReal_mul_enorm_sub_rpow_of_norm_le (μ := μ) hΩ hC hT)).trans
    (mul_le_mul_right (rieszPotential_restrict_le_of_mem_closure hb hx hp hα u) _)

/-- **`Lᵖ → L^q` `eLpNorm` bound for a Riesz-dominated operator kernel on a bounded measurable
set.** -/
theorem eLpNorm_setIntegral_apply_le_of_riesz_bound [Nontrivial E] {Ω : Set E}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) {K : E → E → G →L[𝕜] H} {u : E → G}
    (hK_meas : AEStronglyMeasurable (uncurry K) ((μ.restrict Ω).prod (μ.restrict Ω)))
    {α C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖K x y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E))
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hα : (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹) < α ∨
      (p = 1 ∧ q = ∞ ∧ (finrank ℝ E : ℝ) ≤ α)) :
    eLpNorm (fun x => ∫ y in Ω, K x y (u y) ∂μ) q (μ.restrict Ω) ≤
      ENNReal.ofReal (C * rieszDiamConst μ α p q *
        diam Ω ^ (α - (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹))) *
        eLpNorm u p (μ.restrict Ω) := by
  rcases eq_or_ne (eLpNorm u p (μ.restrict Ω)) ∞ with hN | hN
  · rcases hC.eq_or_lt with rfl | hC_pos
    · have hzero : (fun x => ∫ y in Ω, K x y (u y) ∂μ) =ᵐ[μ.restrict Ω] 0 := by
        filter_upwards [ae_restrict_mem hΩ] with x hx
        have hdom : ∀ᵐ y ∂μ.restrict Ω, ‖K x y‖ₑ ≤ 0 * ‖x - y‖ₑ ^ (α - finrank ℝ E) := by
          simpa using
            ae_enorm_le_ofReal_mul_enorm_sub_rpow_of_norm_le (μ := μ) hΩ le_rfl (hK x hx)
        simpa using enorm_integral_apply_le_mul_rieszPotential (u := u) ENNReal.zero_ne_top hdom
      rw [eLpNorm_congr_ae hzero]
      simp
    · rcases (diam_nonneg (s := Ω)).eq_or_lt with hd0 | hd_pos
      · simp [Measure.restrict_eq_zero_of_diam_eq_zero hb hd0.symm]
      · have hconst_pos : 0 < rieszDiamConst μ α p q := by
          rcases hα with hα' | ⟨rfl, rfl, _⟩
          · exact rieszDiamConst_pos μ hp hα'
          · simp
        have hrhs_pos : 0 < C * rieszDiamConst μ α p q *
            diam Ω ^ (α - (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹)) :=
          mul_pos (mul_pos hC_pos hconst_pos) (Real.rpow_pos_of_pos hd_pos _)
        rw [hN, ENNReal.mul_top (ENNReal.ofReal_pos.2 hrhs_pos).ne']
        exact le_top
  have hu_meas : AEStronglyMeasurable u (μ.restrict Ω) := aestronglyMeasurable_of_eLpNorm_ne_top hN
  have hq0 : 0 < q := zero_lt_one.trans_le (hp.trans hpq)
  have hmeas_int := aestronglyMeasurable_integral_apply hK_meas hu_meas
  have hpoint : ∀ᵐ x ∂μ.restrict Ω,
      ‖∫ y in Ω, K x y (u y) ∂μ‖ₑ ≤
        ‖ENNReal.ofReal C * rieszPotential (μ.restrict Ω) α u x‖ₑ := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    rw [eNorm_eq_self]
    exact enorm_integral_apply_le_mul_rieszPotential ENNReal.ofReal_ne_top
      (ae_enorm_le_ofReal_mul_enorm_sub_rpow_of_norm_le (μ := μ) hΩ hC (hK x hx))
  calc eLpNorm (fun x => ∫ y in Ω, K x y (u y) ∂μ) q (μ.restrict Ω)
      ≤ eLpNorm (fun x => ENNReal.ofReal C * rieszPotential (μ.restrict Ω) α u x)
          q (μ.restrict Ω) :=
        eLpNorm_mono_eNorm_ae hmeas_int hpoint
    _ = ENNReal.ofReal C * eLpNorm (rieszPotential (μ.restrict Ω) α u) q (μ.restrict Ω) :=
        eLpNorm_const_mul_ennreal_of_pos hq0
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (rieszDiamConst μ α p q *
          diam Ω ^ (α - (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹))) *
            eLpNorm u p (μ.restrict Ω)) :=
        mul_le_mul_right (eLpNorm_rieszPotential_restrict_le_of_le hb hp hpq hα u) _
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hC, mul_assoc C]

/-- **Real `lpNorm` `Lᵖ → L^q` bound for a Riesz-dominated operator kernel on a bounded measurable
set.** -/
theorem lpNorm_setIntegral_apply_le_of_riesz_bound_of_le [Nontrivial E] {Ω : Set E}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) {K : E → E → G →L[𝕜] H} {u : E → G}
    (hK_meas : AEStronglyMeasurable (uncurry K) ((μ.restrict Ω).prod (μ.restrict Ω)))
    {α C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖K x y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E))
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hα : (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹) < α ∨
      (p = 1 ∧ q = ∞ ∧ (finrank ℝ E : ℝ) ≤ α))
    (hu : MemLp u p (μ.restrict Ω)) :
    lpNorm (fun x => ∫ y in Ω, K x y (u y) ∂μ) q (μ.restrict Ω) ≤
      C * rieszDiamConst μ α p q *
        diam Ω ^ (α - (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹)) *
        lpNorm u p (μ.restrict Ω) := by
  have hα_le : (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹) ≤ α := by
    rcases hα with h | ⟨rfl, rfl, h⟩
    · exact h.le
    · simpa using h
  have hconst_nn : 0 ≤ C * rieszDiamConst μ α p q *
      diam Ω ^ (α - (finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹)) :=
    mul_nonneg (mul_nonneg hC (rieszDiamConst_nonneg μ hp hα_le)) (Real.rpow_nonneg diam_nonneg _)
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hconst_nn ENNReal.toReal_nonneg) ?_
  rw [ENNReal.ofReal_mul hconst_nn, ENNReal.ofReal_toReal hu.eLpNorm_lt_top.ne]
  exact eLpNorm_setIntegral_apply_le_of_riesz_bound hΩ hb hK_meas hC hK hp hpq hα

/-- Real `lpNorm` `Lᵖ → Lᵖ` bound for a Riesz-dominated operator kernel on a bounded measurable set
(the operator-kernel form of Brenner–Scott, Lemma 4.3.6). -/
theorem lpNorm_setIntegral_apply_le_of_riesz_bound [Nontrivial E] {Ω : Set E}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) {K : E → E → G →L[𝕜] H} {u : E → G}
    (hK_meas : AEStronglyMeasurable (uncurry K) ((μ.restrict Ω).prod (μ.restrict Ω)))
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hK : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖K x y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hu : MemLp u p (μ.restrict Ω)) :
    lpNorm (fun x => ∫ y in Ω, K x y (u y) ∂μ) p (μ.restrict Ω) ≤
      C * ((finrank ℝ E : ℝ) * μ.real (ball 0 1) / α) * diam Ω ^ α *
        lpNorm u p (μ.restrict Ω) := by
  simpa using lpNorm_setIntegral_apply_le_of_riesz_bound_of_le hΩ hb hK_meas hC hK hp le_rfl
    (Or.inl (by simpa using hα)) hu

variable [SMulCommClass ℝ 𝕜 H]

/-- The integral operator `u ↦ (x ↦ ∫ y in Ω, K x y (u y) ∂μ)` on `Lᵖ(Ω)` (`1 ≤ p ≤ ∞`) induced by
an a.e. strongly measurable kernel `K` satisfying `‖K x y‖ ≤ C * ‖x - y‖ ^ (α - n)` off the
diagonal on `Ω` for `α > 0`, constructed via `TauCeti.integralOperatorLp`. -/
def integralOperatorLpOfRieszBound [Nontrivial E] {Ω : Set E} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (K : E → E → G →L[𝕜] H) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hK_meas : AEStronglyMeasurable (uncurry K) ((μ.restrict Ω).prod (μ.restrict Ω)))
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hK : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖K x y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E)) :
    Lp G p (μ.restrict Ω) →L[𝕜] Lp H p (μ.restrict Ω) :=
  integralOperatorLp K p hK_meas
    (ae_row_lintegral_enorm_le_of_riesz_bound hΩ hb hα hC hK)
    (ae_col_lintegral_enorm_le_of_riesz_bound hΩ hb hα hC hK)

/-- `TauCeti.integralOperatorLpOfRieszBound` acts almost everywhere on `Ω` by
`x ↦ ∫ y in Ω, K x y (u y) ∂μ`. -/
theorem coeFn_integralOperatorLpOfRieszBound [Nontrivial E] {Ω : Set E} {hΩ : MeasurableSet Ω}
    {hb : Bornology.IsBounded Ω} {K : E → E → G →L[𝕜] H} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {hK_meas : AEStronglyMeasurable (uncurry K) ((μ.restrict Ω).prod (μ.restrict Ω))}
    {α C : ℝ} {hα : 0 < α} {hC : 0 ≤ C}
    {hK : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖K x y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E)}
    (u : Lp G p (μ.restrict Ω)) :
    integralOperatorLpOfRieszBound hΩ hb K p hK_meas hα hC hK u =ᵐ[μ.restrict Ω]
      fun x => ∫ y in Ω, K x y (u y) ∂μ :=
  coeFn_integralOperatorLp u

/-- An `Lᵖ(Ω)` class equal almost everywhere to `x ↦ ∫ y in Ω, K x y (u y) ∂μ` is the image of `u`
under `TauCeti.integralOperatorLpOfRieszBound`. -/
theorem integralOperatorLpOfRieszBound_eq_iff [Nontrivial E] {Ω : Set E} {hΩ : MeasurableSet Ω}
    {hb : Bornology.IsBounded Ω} {K : E → E → G →L[𝕜] H} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {hK_meas : AEStronglyMeasurable (uncurry K) ((μ.restrict Ω).prod (μ.restrict Ω))}
    {α C : ℝ} {hα : 0 < α} {hC : 0 ≤ C}
    {hK : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖K x y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E)}
    {u : Lp G p (μ.restrict Ω)} {v : Lp H p (μ.restrict Ω)} :
    integralOperatorLpOfRieszBound hΩ hb K p hK_meas hα hC hK u = v ↔
      (fun x => ∫ y in Ω, K x y (u y) ∂μ) =ᵐ[μ.restrict Ω] v :=
  integralOperatorLp_eq_iff

/-- Operator-norm bound for `TauCeti.integralOperatorLpOfRieszBound`: its norm on `Lᵖ(Ω)` is at most
`C * (n * μ.real (ball 0 1) / α) * (diam Ω) ^ α`. -/
theorem norm_integralOperatorLpOfRieszBound_le [Nontrivial E] {Ω : Set E} {hΩ : MeasurableSet Ω}
    {hb : Bornology.IsBounded Ω} {K : E → E → G →L[𝕜] H} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {hK_meas : AEStronglyMeasurable (uncurry K) ((μ.restrict Ω).prod (μ.restrict Ω))}
    {α C : ℝ} {hα : 0 < α} {hC : 0 ≤ C}
    {hK : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖K x y‖ ≤ C * ‖x - y‖ ^ (α - finrank ℝ E)} :
    ‖integralOperatorLpOfRieszBound hΩ hb K p hK_meas hα hC hK‖ ≤
      C * ((finrank ℝ E : ℝ) * μ.real (ball 0 1) / α) * diam Ω ^ α := by
  refine norm_integralOperatorLp_le_max.trans ?_
  rw [max_self, Real.coe_toNNReal _ (by positivity)]

end OperatorKernel

section Sharpness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Sharpness of the `n / p` threshold for pointwise finiteness.** On a nontrivial space, for any
`p : ℝ≥0∞`, if `α < n * p.toReal⁻¹` and `x ∈ interior Ω`, there exists `f ∈ Lᵖ(Ω; ℝ)` whose Riesz
potential `rieszPotential (μ.restrict Ω) α f x` is infinite. -/
theorem exists_memLp_rieszPotential_restrict_eq_top [Nontrivial E] {Ω : Set E} {x : E}
    (hx : x ∈ interior Ω) {p : ℝ≥0∞} {α : ℝ}
    (hα : α < (finrank ℝ E : ℝ) * p.toReal⁻¹) :
    ∃ f : E → ℝ, MemLp f p (μ.restrict Ω) ∧ rieszPotential (μ.restrict Ω) α f x = ∞ := by
  by_cases hp_ext : p = 0 ∨ p = ∞
  · have hα0 : α < 0 := by rcases hp_ext with rfl | rfl <;> simpa using hα
    refine ⟨fun _ => 1, ?_, ?_⟩
    · rcases hp_ext with rfl | rfl
      · exact memLp_zero_iff_aestronglyMeasurable.2 aestronglyMeasurable_const
      · exact memLp_top_const 1
    · simpa [rieszPotential_def] using
        setLIntegral_enorm_sub_rpow_eq_top_of_mem_interior (mu := μ)
          (s := α - finrank ℝ E) (by linarith) hx
  obtain ⟨hp0, hp_top⟩ := not_or.1 hp_ext
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hs : -(finrank ℝ E : ℝ) < -α * p.toReal := by
    have : α * p.toReal < finrank ℝ E := by
      calc α * p.toReal < ((finrank ℝ E : ℝ) * p.toReal⁻¹) * p.toReal := by gcongr
        _ = finrank ℝ E := by field_simp
    linarith
  let f : E → ℝ := (ball x r).indicator fun y => ‖x - y‖ ^ (-α)
  have hf_meas : AEStronglyMeasurable f μ :=
    ((by fun_prop : Measurable fun y : E => ‖x - y‖ ^ (-α)).indicator
      measurableSet_ball).aestronglyMeasurable
  have hf_mem : MemLp f p (μ.restrict Ω) := by
    refine MemLp.mono_measure Measure.restrict_le_self ?_
    rw [← integrable_norm_rpow_iff hf_meas hp0 hp_top]
    have heq : (fun y : E => ‖f y‖ ^ p.toReal) =
        (ball x r).indicator fun y => ‖x - y‖ ^ (-α * p.toReal) := by
      funext y
      by_cases hy : y ∈ ball x r
      · simp only [f, indicator_of_mem hy, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
          ← Real.rpow_mul (norm_nonneg _)]
      · simp [f, hy, Real.zero_rpow hp_pos.ne']
    rw [heq, integrable_indicator_iff measurableSet_ball]
    exact integrableOn_norm_sub_rpow_ball hs x
  refine ⟨f, hf_mem, top_unique ?_⟩
  have hdiv : ∫⁻ y in ball x r, ‖x - y‖ₑ ^ (-(finrank ℝ E : ℝ)) ∂μ = ∞ :=
    setLIntegral_enorm_sub_rpow_eq_top_of_mem_interior le_rfl
      (by rw [isOpen_ball.interior_eq]; exact mem_ball_self hr)
  rw [← hdiv, rieszPotential_def]
  refine (lintegral_mono_ae ?_).trans (lintegral_mono_set hball)
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (μ := μ) x))] with y hy hyx
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hyx))
  have hpos_e : 0 < ‖x - y‖ₑ := by rw [← ofReal_norm]; exact ENNReal.ofReal_pos.2 hpos
  have htop_e : ‖x - y‖ₑ ≠ ∞ := eNorm_ne_top
  simp only [f, indicator_of_mem hy]
  rw [← ofReal_norm (‖x - y‖ ^ (-α)), Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _),
    ← ENNReal.ofReal_rpow_of_pos hpos, ofReal_norm,
    ← ENNReal.rpow_add _ _ hpos_e.ne' htop_e]
  ring_nf
  exact le_rfl

end Sharpness

section Examples

-- Concrete 1D sanity check at `(p, q) = (1, ∞)` on `(-1, 1)` with `α = 1` and `f = 1`:
-- at `x = 0`, `rieszPotential` evaluates to `2`, and `rieszDiamConst volume 1 1 ∞ = 1`,
-- `diam (-1, 1) ^ 0 = 1`, `‖1‖_{L¹(-1, 1)} = 2`, so the bound `2 ≤ 1 * 1 * 2` holds with equality.
example : rieszPotential (volume.restrict (Ioo (-1 : ℝ) 1)) 1 (fun _ : ℝ => (1 : ℝ)) 0 ≤
    ENNReal.ofReal (rieszDiamConst (volume : Measure ℝ) 1 1 ∞ *
      diam (Ioo (-1 : ℝ) 1) ^ ((1 : ℝ) - (finrank ℝ ℝ : ℝ) * (1 : ℝ≥0∞).toReal⁻¹)) *
      eLpNorm (fun _ : ℝ => (1 : ℝ)) 1 (volume.restrict (Ioo (-1 : ℝ) 1)) :=
  rieszPotential_restrict_le_of_mem_closure (Metric.isBounded_Ioo (-1 : ℝ) 1)
    (subset_closure (by norm_num)) le_rfl (Or.inr ⟨rfl, by simp⟩) _

-- Concrete boundary-point `p = ∞` sanity check at `x = 1 ∈ closure (0, 1)` with integer order `1`.
example : rieszPotential (volume.restrict (Ioo (0 : ℝ) 1)) (1 : ℕ) (fun _ : ℝ => (1 : ℝ)) 1 ≤
    ENNReal.ofReal (rieszDiamConst (volume : Measure ℝ) (1 : ℕ) ∞ ∞ *
      diam (Ioo (0 : ℝ) 1) ^ (((1 : ℕ) : ℝ) - (finrank ℝ ℝ : ℝ) * (∞ : ℝ≥0∞).toReal⁻¹)) *
      eLpNorm (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Ioo (0 : ℝ) 1)) :=
  rieszPotential_restrict_natCast_le_of_mem_closure (Metric.isBounded_Ioo (0 : ℝ) 1)
    (by rw [closure_Ioo zero_ne_one]; exact right_mem_Icc.2 zero_le_one) le_top
    (Or.inl (by simp)) _

-- Concrete 1D `Lᵖ → Lᵖ` sanity check on `(0, 1)` with `α = 1` and `f = 1` for every `1 ≤ p ≤ ∞`.
example (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (rieszPotential (volume.restrict (Ioo (0 : ℝ) 1)) 1 (fun _ : ℝ => (1 : ℝ)))
      p (volume.restrict (Ioo (0 : ℝ) 1)) ≤
    ENNReal.ofReal ((finrank ℝ ℝ : ℝ) * volume.real (ball (0 : ℝ) 1) / 1 *
      diam (Ioo (0 : ℝ) 1) ^ (1 : ℝ)) *
      eLpNorm (fun _ : ℝ => (1 : ℝ)) p (volume.restrict (Ioo (0 : ℝ) 1)) :=
  eLpNorm_rieszPotential_restrict_le (Metric.isBounded_Ioo (0 : ℝ) 1) zero_lt_one hp _

end Examples

end TauCeti
