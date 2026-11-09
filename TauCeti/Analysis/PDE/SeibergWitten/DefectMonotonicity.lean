/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSetCovering
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Integrating the monotonicity inequality for the defect energy

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `χ`, and its *defect energy* in a ball is
`E(σ) = r ∫_{B_σ} |1 - |χ|²| / 4`. By the coarea formula `E` is an absolutely continuous function
of the radius. Taubes's monotonicity argument proves the differential inequality

`E(σ) ≤ (σ / 2) (1 + C σ) (1 + C₁ r^(-1/2)) E'(σ) + K σ⁴`

for almost every radius `σ` below a fixed geometric radius `σ₀`. This file integrates that
inequality.

**The monotone quantity.** Write `θ = 2 / (1 + C₁ r^(-1/2))`. The inequality says
`E ≤ σ (1 + C σ) E' / θ + K σ⁴`, and for every `0 < θ ≤ 2` this makes

`σ ↦ (E(σ) + K σ⁴) (C + σ⁻¹) ^ θ`

nondecreasing (`TauCeti.SeibergWitten.monotoneOn_add_mul_rpow_of_ae_le`). The factor
`(C + σ⁻¹) ^ θ = ((1 + C σ) / σ) ^ θ` is the integrating factor of the linear part, and the
correction `K σ⁴` absorbs the error term because `θ ≤ 2`. For `θ = 2` and `C = K = 0` this is the
classical statement that `E(σ) / σ²` is nondecreasing.

**Quadratic upper and lower bounds.** On the range `c₀ r^(-1/2) ≤ σ ≤ σ₀` the power `σ ^ θ` is
comparable with `σ²` uniformly in `r ≥ 1`, because `2 - θ ≤ 2 C₁ r^(-1/2)` while
`log (1 / σ) ≤ log (r^(1/2) / c₀)`. Hence:

* a bound `E(σ₀) ≤ B` gives `E(σ) ≤ M σ²` on that range, with `M` independent of `r`
  (`TauCeti.SeibergWitten.exists_forall_le_mul_sq_of_ae_le`);
* a lower bound `E(c₀ r^(-1/2)) ≥ c₁ / r` at the smallest scale propagates to
  `E(σ) ≥ c σ²` for `c₀ r^(-1/2) ≤ σ ≤ ρ₀`, with `c > 0` and `ρ₀ > 0` independent of `r`
  (`TauCeti.SeibergWitten.exists_forall_mul_sq_le_of_ae_le`).

At a zero of `α` the smallest-scale lower bound comes from the rescaled analysis at scale
`r^(-1/2)`, which is not part of this file. Applied to `E(σ) = μ (closedBall x σ)` at every point
`x` of the zero set, the lower bound is the input `μ (closedBall x ρ) ≥ c ρ²` of the covering
estimate `TauCeti.coveringNumber_le_of_mul_sq_le_measure_closedBall_of_sq_le`, which then covers
the zero set by `N(σ) ≤ C σ⁻²` balls of radius `σ` for `r ≥ (2 c₀ / σ)²`
(`TauCeti.SeibergWitten.exists_forall_coveringNumber_le_of_ae_le`).

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

open MeasureTheory Set

namespace TauCeti.SeibergWitten

variable {f : ℝ → ℝ} {a b C K θ : ℝ}

/-- The derivative of the monotone quantity `(f σ + K σ⁴) (C + σ⁻¹) ^ θ` is nonnegative at every
point where `f` is differentiable and satisfies the differential inequality. -/
private theorem hasDerivAt_add_mul_rpow {σ : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hθ : 0 < θ) (hθ2 : θ ≤ 2) (hf : DifferentiableAt ℝ f σ)
    (hle : f σ ≤ σ * (1 + C * σ) / θ * deriv f σ + K * σ ^ 4) :
    ∃ d, 0 ≤ d ∧ HasDerivAt (fun σ ↦ (f σ + K * σ ^ 4) * (C + σ⁻¹) ^ θ) d σ := by
  have hu : 0 < C + σ⁻¹ := by positivity
  have hφ := ((hasDerivAt_inv hσ.ne').const_add C).rpow_const (p := θ) (Or.inl hu.ne')
  refine ⟨_, ?_, (hf.hasDerivAt.add ((hasDerivAt_pow 4 σ).const_mul K)).mul hφ⟩
  -- Factor out `(C + σ⁻¹) ^ (θ - 1) / σ ^ 2 > 0`; the remaining factor is nonnegative by the
  -- differential inequality, `θ ≤ 2` and `K, C ≥ 0`.
  have hw : 0 < (C + σ⁻¹) ^ (θ - 1) := Real.rpow_pos_of_pos hu _
  have hsplit : (C + σ⁻¹) ^ θ = (C + σ⁻¹) * (C + σ⁻¹) ^ (θ - 1) := by
    rw [← Real.rpow_one_add' hu.le (by linarith), add_sub_cancel]
  have hkey : θ * (f σ + K * σ ^ 4) ≤ (deriv f σ + K * (4 * σ ^ 3)) * (1 + C * σ) * σ := by
    have h1 : θ * f σ ≤ σ * (1 + C * σ) * deriv f σ + θ * (K * σ ^ 4) := by
      have := mul_le_mul_of_nonneg_left hle hθ.le
      rwa [mul_add, ← mul_assoc θ, mul_div_assoc', mul_div_cancel_left₀ _ hθ.ne'] at this
    have h2 : θ * (K * σ ^ 4) ≤ 2 * (K * σ ^ 4) := by gcongr
    have h3 : 0 ≤ K * σ ^ 4 * (C * σ) := by positivity
    nlinarith
  have hrw : (deriv f σ + K * (4 * σ ^ (4 - 1))) * (C + σ⁻¹) ^ θ +
      (f σ + K * σ ^ 4) * (-(σ ^ 2)⁻¹ * θ * (C + σ⁻¹) ^ (θ - 1)) =
      (C + σ⁻¹) ^ (θ - 1) / σ ^ 2 *
        ((deriv f σ + K * (4 * σ ^ 3)) * (1 + C * σ) * σ - θ * (f σ + K * σ ^ 4)) := by
    rw [hsplit]
    field_simp
    ring
  simp only [Pi.add_apply, Nat.cast_ofNat]
  rw [hrw]
  exact mul_nonneg (by positivity) (sub_nonneg.2 hkey)

/-- **Monotonicity formula.** Let `f` be absolutely continuous on `[a, b]` with `0 < a`, and
suppose that at almost every `σ ∈ [a, b]` it satisfies the differential inequality
`f σ ≤ σ (1 + C σ) f'(σ) / θ + K σ⁴` with `C, K ≥ 0` and `0 < θ ≤ 2`. Then
`σ ↦ (f σ + K σ⁴) (C + σ⁻¹) ^ θ` is nondecreasing on `[a, b]`. No sign condition on `f` is
needed. -/
theorem monotoneOn_add_mul_rpow_of_ae_le (hf : AbsolutelyContinuousOnInterval f a b)
    (ha : 0 < a) (hC : 0 ≤ C) (hK : 0 ≤ K) (hθ : 0 < θ) (hθ2 : θ ≤ 2)
    (hle : ∀ᵐ σ, σ ∈ Icc a b → f σ ≤ σ * (1 + C * σ) / θ * deriv f σ + K * σ ^ 4) :
    MonotoneOn (fun σ ↦ (f σ + K * σ ^ 4) * (C + σ⁻¹) ^ θ) (Icc a b) := by
  rcases le_or_gt a b with hab | hab
  swap
  · rw [Icc_eq_empty_of_lt hab]
    exact fun _ h ↦ h.elim
  rw [← uIcc_of_le hab]
  have hpos : ∀ σ ∈ uIcc a b, 0 < σ := fun σ hσ ↦ ha.trans_le (uIcc_of_le hab ▸ hσ).1
  -- The integrating factor is `C¹` on `[a, b] ⊆ (0, ∞)`, hence absolutely continuous.
  have hφ : AbsolutelyContinuousOnInterval (fun σ ↦ (C + σ⁻¹) ^ θ) a b := by
    refine ContDiffOn.absolutelyContinuousOnInterval fun σ hσ ↦ ?_
    have hσ0 := hpos σ hσ
    have hu : C + σ⁻¹ ≠ 0 := (by positivity : 0 < C + σ⁻¹).ne'
    exact ((contDiffAt_const.add (contDiffAt_inv ℝ hσ0.ne')).rpow_const_of_ne
      hu).contDiffWithinAt
  have hpoly : AbsolutelyContinuousOnInterval (fun σ ↦ K * σ ^ 4) a b :=
    ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
  refine ((hf.fun_add hpoly).fun_mul hφ).monotoneOn_of_ae_deriv_nonneg ?_
  filter_upwards [hle, hf.ae_differentiableAt] with σ hσle hσd hσ
  obtain ⟨d, hd, hderiv⟩ := hasDerivAt_add_mul_rpow (hpos σ hσ) hC hK hθ hθ2 (hσd hσ)
    (hσle (uIcc_of_le hab ▸ hσ))
  rwa [hderiv.deriv]

/-- Taubes's form of the differential inequality, with the factor `(σ / 2) (1 + δ)`, is the
inequality of `monotoneOn_add_mul_rpow_of_ae_le` for the exponent `θ = 2 / (1 + δ)`. -/
private theorem monotoneOn_add_mul_rpow_of_ae_le_one_add {δ : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (ha : 0 < a) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hδ : 0 ≤ δ)
    (hle : ∀ᵐ σ, σ ∈ Icc a b →
      f σ ≤ σ / 2 * (1 + C * σ) * (1 + δ) * deriv f σ + K * σ ^ 4) :
    MonotoneOn (fun σ ↦ (f σ + K * σ ^ 4) * (C + σ⁻¹) ^ (2 / (1 + δ))) (Icc a b) := by
  refine monotoneOn_add_mul_rpow_of_ae_le hf ha hC hK (by positivity)
    ((div_le_iff₀ (by positivity)).2 (by linarith)) ?_
  filter_upwards [hle] with σ hσ hmem
  convert hσ hmem using 3
  field_simp

/-- The exponent `θ = 2 / (1 + δ)` satisfies `0 ≤ 2 - θ ≤ 2 δ`. -/
private theorem two_sub_div_one_add_mem {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ 2 - 2 / (1 + δ) ∧ 2 - 2 / (1 + δ) ≤ 2 * δ := by
  have h : 2 - 2 / (1 + δ) = 2 * δ / (1 + δ) := by field_simp; ring
  rw [h]
  exact ⟨by positivity, div_le_self (by positivity) (by linarith)⟩

/-- On the range `σ ≥ c₀ r^(-1/2)` with `r ≥ 1`, a power `σ ^ (-ε)` with
`0 ≤ ε ≤ 2 C₁ r^(-1/2)` is bounded independently of `r`: the exponent is small enough to absorb
`log (1 / σ) ≤ log (r^(1/2) / c₀)`. -/
private theorem rpow_neg_le_exp {C₁ c₀ r ε : ℝ} (hC₁ : 0 ≤ C₁) (hc₀ : 0 < c₀) (hr : 1 ≤ r)
    (hε : 0 ≤ ε) (hεle : ε ≤ 2 * (C₁ / √r)) :
    (c₀ / √r) ^ (-ε) ≤ Real.exp (2 * C₁ * (1 + |Real.log c₀|)) := by
  have hs : 1 ≤ √r := Real.one_le_sqrt.2 hr
  have hs0 : 0 < √r := by positivity
  rw [Real.rpow_def_of_pos (by positivity), Real.exp_le_exp,
    Real.log_div hc₀.ne' hs0.ne']
  have hlog : Real.log √r ≤ √r := Real.log_le_self hs0.le
  have habs : -Real.log c₀ ≤ |Real.log c₀| := neg_le_abs _
  -- `ε (log √r - log c₀) ≤ (2 C₁ / √r) (√r + |log c₀|) ≤ 2 C₁ (1 + |log c₀|)`.
  have h1 : (Real.log c₀ - Real.log √r) * -ε ≤ ε * (√r + |Real.log c₀|) := by
    nlinarith
  have h2 : ε * (√r + |Real.log c₀|) ≤ 2 * (C₁ / √r) * (√r + |Real.log c₀|) :=
    mul_le_mul_of_nonneg_right hεle (by positivity)
  have h3 : 2 * (C₁ / √r) * (√r + |Real.log c₀|) ≤ 2 * C₁ * (1 + |Real.log c₀|) := by
    rw [mul_add, mul_assoc, div_mul_cancel₀ _ hs0.ne', mul_add (2 * C₁)]
    have : C₁ / √r * |Real.log c₀| ≤ C₁ * |Real.log c₀| := by
      gcongr
      exact div_le_self hC₁ hs
    nlinarith
  linarith

/-- The integrating factor `(C + σ⁻¹) ^ θ` is at least `(σ ^ θ)⁻¹`. -/
private theorem inv_rpow_le_add_inv_rpow {σ : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C) (hθ : 0 ≤ θ) :
    (σ ^ θ)⁻¹ ≤ (C + σ⁻¹) ^ θ := by
  rw [← Real.inv_rpow hσ.le]
  exact Real.rpow_le_rpow (by positivity) (le_add_of_nonneg_left hC) hθ

/-- For `σ ≤ 1` and `θ ≤ 2` the integrating factor `(C + σ⁻¹) ^ θ` is at most
`(1 + C)² / σ²`. -/
private theorem add_inv_rpow_le_mul_inv_sq {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C)
    (hθ : 0 ≤ θ) (hθ2 : θ ≤ 2) : (C + σ⁻¹) ^ θ ≤ (1 + C) ^ 2 * (σ ^ 2)⁻¹ := by
  have h1 : 1 ≤ σ⁻¹ := one_le_inv₀ hσ |>.2 hσ1
  have h2 : C + σ⁻¹ ≤ (1 + C) * σ⁻¹ := by nlinarith
  calc (C + σ⁻¹) ^ θ ≤ ((1 + C) * σ⁻¹) ^ θ := Real.rpow_le_rpow (by positivity) h2 hθ
    _ ≤ ((1 + C) * σ⁻¹) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by nlinarith) hθ2
    _ = (1 + C) ^ 2 * (σ ^ 2)⁻¹ := by rw [Real.rpow_two, mul_pow, inv_pow]

/-- A power `x ^ θ` with `0 ≤ θ ≤ 2` and `x ≥ 0` is at most `max 1 (x ^ 2)`. -/
private theorem rpow_le_max_one_sq {x θ : ℝ} (hx : 0 ≤ x) (hθ : 0 ≤ θ) (hθ2 : θ ≤ 2) :
    x ^ θ ≤ max 1 (x ^ 2) := by
  rcases le_or_gt 1 x with h | h
  · exact le_max_of_le_right <| (Real.rpow_le_rpow_of_exponent_le h hθ2).trans_eq
      (Real.rpow_two x)
  · exact le_max_of_le_left (Real.rpow_le_one hx h.le hθ)

/-- **Quadratic upper bound from the monotonicity inequality.** Fix `C, C₁, K ≥ 0`, `c₀ > 0`
and `B`. There is a constant `M` such that for every `r ≥ 1` and every `f` absolutely
continuous on `[c₀ r^(-1/2), σ₀]` satisfying Taubes's differential inequality
`f σ ≤ (σ / 2) (1 + C σ) (1 + C₁ r^(-1/2)) f'(σ) + K σ⁴` almost everywhere there, the bound
`f σ₀ ≤ B` implies `f σ ≤ M σ²` for all `c₀ r^(-1/2) ≤ σ ≤ σ₀`. The constant `M` does not depend
on `r` or `f`. -/
theorem exists_forall_le_mul_sq_of_ae_le {C C₁ K c₀ σ₀ B : ℝ} (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hK : 0 ≤ K) (hc₀ : 0 < c₀) :
    ∃ M, ∀ r, 1 ≤ r → ∀ f : ℝ → ℝ, AbsolutelyContinuousOnInterval f (c₀ / √r) σ₀ →
      (∀ᵐ σ, σ ∈ Icc (c₀ / √r) σ₀ →
        f σ ≤ σ / 2 * (1 + C * σ) * (1 + C₁ / √r) * deriv f σ + K * σ ^ 4) →
      f σ₀ ≤ B → ∀ σ ∈ Icc (c₀ / √r) σ₀, f σ ≤ M * σ ^ 2 := by
  set E := Real.exp (2 * C₁ * (1 + |Real.log c₀|))
  set R := (max B 0 + K * σ₀ ^ 4) * max 1 ((C + σ₀⁻¹) ^ 2)
  refine ⟨E * R, fun r hr f hf hle hfB σ hσ ↦ ?_⟩
  have ha : 0 < c₀ / √r := by positivity
  have hσ0 : 0 < σ := ha.trans_le hσ.1
  have hσ₀ : 0 < σ₀ := hσ0.trans_le hσ.2
  have hδ : 0 ≤ C₁ / √r := by positivity
  set θ := 2 / (1 + C₁ / √r)
  obtain ⟨hθ2, hθδ⟩ := two_sub_div_one_add_mem hδ
  have hθ : 0 ≤ θ := by positivity
  have hR : 0 ≤ R := by positivity
  -- Compare the monotone quantity at `σ` and at `σ₀`.
  have hmono := monotoneOn_add_mul_rpow_of_ae_le_one_add hf ha hC hK hδ hle hσ
    ⟨hσ.1.trans hσ.2, le_rfl⟩ hσ.2
  have hend : (f σ₀ + K * σ₀ ^ 4) * (C + σ₀⁻¹) ^ θ ≤ R :=
    mul_le_mul (by linarith [le_max_left B 0])
      (rpow_le_max_one_sq (by positivity) hθ (by linarith)) (by positivity) (by positivity)
  -- On the range `σ ≥ c₀ r^(-1/2)`, `σ ^ θ ≤ E σ²`.
  have hpow : σ ^ θ ≤ E * σ ^ 2 := by
    have h1 : σ ^ θ = σ ^ 2 * σ ^ (-(2 - θ)) := by
      rw [← Real.rpow_two, ← Real.rpow_add hσ0]
      ring_nf
    have h2 : σ ^ (-(2 - θ)) ≤ (c₀ / √r) ^ (-(2 - θ)) :=
      Real.rpow_le_rpow_of_nonpos ha hσ.1 (by linarith)
    have h3 := rpow_neg_le_exp hC₁ hc₀ hr hθ2 hθδ
    rw [h1, mul_comm E]
    gcongr
    exact h2.trans h3
  rcases le_or_gt 0 (f σ + K * σ ^ 4) with hnn | hneg
  · have h1 : f σ + K * σ ^ 4 ≤ σ ^ θ * R := by
      have h := (mul_le_mul_of_nonneg_left (inv_rpow_le_add_inv_rpow hσ0 hC hθ) hnn).trans
        (hmono.trans hend)
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)] at h
      linarith
    have h2 : σ ^ θ * R ≤ E * σ ^ 2 * R := mul_le_mul_of_nonneg_right hpow hR
    nlinarith [pow_nonneg hσ0.le 4]
  · have : 0 ≤ E * R * σ ^ 2 := by positivity
    nlinarith [pow_nonneg hσ0.le 4]

/-- At the smallest scale `a = c₀ r^(-1/2)`, a lower bound `f a ≥ c₁ / r` gives a lower bound,
independent of `r`, for the monotone quantity `(f a + K a⁴) (C + a⁻¹) ^ θ` when
`0 ≤ 2 - θ ≤ 2 C₁ r^(-1/2)`. -/
private theorem le_add_mul_rpow_of_div_le {C₁ c₀ c₁ r : ℝ} (hC₁ : 0 ≤ C₁) (hc₀ : 0 < c₀)
    (hc₁ : 0 ≤ c₁) (hr : 1 ≤ r) (hK : 0 ≤ K) (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hθ2 : 0 ≤ 2 - θ)
    (hθδ : 2 - θ ≤ 2 * (C₁ / √r)) (hbase : c₁ / r ≤ f (c₀ / √r)) :
    c₁ / c₀ ^ 2 * (Real.exp (2 * C₁ * (1 + |Real.log c₀|)))⁻¹ ≤
      (f (c₀ / √r) + K * (c₀ / √r) ^ 4) * (C + (c₀ / √r)⁻¹) ^ θ := by
  set a := c₀ / √r
  have ha : 0 < a := by positivity
  have hfa : c₁ / c₀ ^ 2 * a ^ 2 ≤ f a := by
    rw [div_pow, Real.sq_sqrt (by linarith)]
    convert hbase using 1
    field_simp
  have hpow : (Real.exp (2 * C₁ * (1 + |Real.log c₀|)))⁻¹ ≤ a ^ 2 * (a ^ θ)⁻¹ := by
    have h := rpow_neg_le_exp hC₁ hc₀ hr hθ2 hθδ
    rw [Real.rpow_neg ha.le, inv_le_comm₀ (by positivity) (by positivity)] at h
    convert h using 1
    rw [Real.rpow_sub ha, Real.rpow_two, div_eq_mul_inv]
  calc c₁ / c₀ ^ 2 * (Real.exp (2 * C₁ * (1 + |Real.log c₀|)))⁻¹
      ≤ c₁ / c₀ ^ 2 * (a ^ 2 * (a ^ θ)⁻¹) := by gcongr
    _ = c₁ / c₀ ^ 2 * a ^ 2 * (a ^ θ)⁻¹ := by ring
    _ ≤ f a * (C + a⁻¹) ^ θ :=
      mul_le_mul hfa (inv_rpow_le_add_inv_rpow ha hC hθ) (by positivity)
        ((by positivity : (0 : ℝ) ≤ c₁ / c₀ ^ 2 * a ^ 2).trans hfa)
    _ ≤ (f a + K * a ^ 4) * (C + a⁻¹) ^ θ := by
      gcongr
      exact le_add_of_nonneg_right (by positivity)

/-- **Quadratic lower bound from the monotonicity inequality.** Fix `C, C₁, K ≥ 0` and
`c₀, c₁, σ₀ > 0`. There are constants `c > 0` and `0 < ρ₀ ≤ σ₀` such that for every `r ≥ 1` and
every `f` absolutely continuous on `[c₀ r^(-1/2), σ₀]` satisfying Taubes's differential inequality
`f σ ≤ (σ / 2) (1 + C σ) (1 + C₁ r^(-1/2)) f'(σ) + K σ⁴` almost everywhere there, a lower bound
`f (c₀ r^(-1/2)) ≥ c₁ / r` at the smallest scale implies `f σ ≥ c σ²` for all
`c₀ r^(-1/2) ≤ σ ≤ ρ₀`. The constants do not depend on `r` or `f`. -/
theorem exists_forall_mul_sq_le_of_ae_le {C C₁ K c₀ c₁ σ₀ : ℝ} (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hK : 0 ≤ K) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hσ₀ : 0 < σ₀) :
    ∃ c > 0, ∃ ρ₀ > 0, ρ₀ ≤ σ₀ ∧ ∀ r, 1 ≤ r → ∀ f : ℝ → ℝ,
      AbsolutelyContinuousOnInterval f (c₀ / √r) σ₀ →
      (∀ᵐ σ, σ ∈ Icc (c₀ / √r) σ₀ →
        f σ ≤ σ / 2 * (1 + C * σ) * (1 + C₁ / √r) * deriv f σ + K * σ ^ 4) →
      c₁ / r ≤ f (c₀ / √r) → ∀ σ ∈ Icc (c₀ / √r) ρ₀, c * σ ^ 2 ≤ f σ := by
  set E := Real.exp (2 * C₁ * (1 + |Real.log c₀|))
  set c₂ := c₁ / c₀ ^ 2 / E / (1 + C) ^ 2
  have hc₂ : 0 < c₂ := by positivity
  set ρ₀ := min σ₀ (min 1 √(c₂ / (2 * (K + 1))))
  have hρ₀ : 0 < ρ₀ := lt_min hσ₀ (lt_min one_pos (by positivity))
  refine ⟨c₂ / 2, by positivity, ρ₀, hρ₀, min_le_left _ _, fun r hr f hf hle hbase σ hσ ↦ ?_⟩
  have ha : 0 < c₀ / √r := by positivity
  have hσ0 : 0 < σ := ha.trans_le hσ.1
  have hσ1 : σ ≤ 1 := hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσσ₀ : σ ≤ σ₀ := hσ.2.trans (min_le_left _ _)
  have hδ : 0 ≤ C₁ / √r := by positivity
  set θ := 2 / (1 + C₁ / √r)
  obtain ⟨hθ2, hθδ⟩ := two_sub_div_one_add_mem hδ
  have hθ : 0 ≤ θ := by positivity
  set a := c₀ / √r
  -- Compare the monotone quantity at the smallest scale `a` and at `σ`.
  have hmono := monotoneOn_add_mul_rpow_of_ae_le_one_add hf ha hC hK hδ hle
    ⟨le_rfl, hσ.1.trans hσσ₀⟩ ⟨hσ.1, hσσ₀⟩ hσ.1
  have hlow : c₂ * (1 + C) ^ 2 ≤ (f a + K * a ^ 4) * (C + a⁻¹) ^ θ := by
    have hc2 : c₂ * (1 + C) ^ 2 = c₁ / c₀ ^ 2 * E⁻¹ := by
      simp only [c₂]
      field_simp
    rw [hc2]
    exact le_add_mul_rpow_of_div_le hC₁ hc₀ hc₁.le hr hK hC hθ hθ2 hθδ hbase
  have hfac := add_inv_rpow_le_mul_inv_sq hσ0 hσ1 hC hθ (by linarith)
  have hupper := hlow.trans hmono
  -- Hence `c₂ σ² ≤ f σ + K σ⁴`.
  have hnn : 0 ≤ f σ + K * σ ^ 4 := by
    by_contra h
    have : (f σ + K * σ ^ 4) * (C + σ⁻¹) ^ θ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_le.1 h).le (by positivity)
    nlinarith [(by positivity : 0 < c₂ * (1 + C) ^ 2)]
  have hmain : c₂ * σ ^ 2 ≤ f σ + K * σ ^ 4 := by
    have h := mul_le_mul_of_nonneg_right (hupper.trans (mul_le_mul_of_nonneg_left hfac hnn))
      (sq_nonneg σ)
    have key : c₂ * σ ^ 2 * (1 + C) ^ 2 ≤ (f σ + K * σ ^ 4) * (1 + C) ^ 2 := by
      calc c₂ * σ ^ 2 * (1 + C) ^ 2 = c₂ * (1 + C) ^ 2 * σ ^ 2 := by ring
        _ ≤ (f σ + K * σ ^ 4) * ((1 + C) ^ 2 * (σ ^ 2)⁻¹) * σ ^ 2 := h
        _ = (f σ + K * σ ^ 4) * (1 + C) ^ 2 := by field_simp
    exact le_of_mul_le_mul_right key (by positivity)
  -- The error term `K σ⁴` is at most `c₂ σ² / 2` because `σ² ≤ c₂ / (2 (K + 1))`.
  have hsq : σ ^ 2 ≤ c₂ / (2 * (K + 1)) := by
    have h : σ ≤ √(c₂ / (2 * (K + 1))) :=
      hσ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
    calc σ ^ 2 ≤ √(c₂ / (2 * (K + 1))) ^ 2 := by gcongr
      _ = c₂ / (2 * (K + 1)) := Real.sq_sqrt (by positivity)
  have hK2 : K * σ ^ 2 ≤ c₂ / 2 := by
    rw [le_div_iff₀ (by positivity)] at hsq
    nlinarith
  nlinarith [pow_nonneg hσ0.le 2]

/-- **Covering the zero set from the monotonicity inequality.** Fix `C, C₁, K ≥ 0` and
`c₀, c₁, σ₀ > 0`. There are constants `c > 0` and `ρ₀ > 0` with the following property. Let
`r ≥ 1`, let `μ` be a measure and `A` a set, and suppose that for every `x ∈ A` the function
`E(σ) = μ (closedBall x σ)` is absolutely continuous on `[c₀ r^(-1/2), σ₀]`, satisfies Taubes's
differential inequality almost everywhere there, and is at least `c₁ / r` at the smallest scale.
Then for every `σ ≤ 2 ρ₀`, once `r ≥ (2 c₀ / σ)²`, the set `A` is covered by at most
`4 μ (cthickening (σ / 2) A) / (c σ²)` closed balls of radius `σ` centred in `A`. -/
theorem exists_forall_coveringNumber_le_of_ae_le {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {C C₁ K c₀ c₁ σ₀ : ℝ} (hC : 0 ≤ C)
    (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hσ₀ : 0 < σ₀) :
    ∃ c > 0, ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ r, 1 ≤ r → ∀ (μ : Measure X) (A : Set X),
      (∀ x ∈ A, AbsolutelyContinuousOnInterval (fun σ ↦ (μ (Metric.closedBall x σ)).toReal)
          (c₀ / √r) σ₀ ∧
        (∀ᵐ σ, σ ∈ Icc (c₀ / √r) σ₀ →
          (μ (Metric.closedBall x σ)).toReal ≤ σ / 2 * (1 + C * σ) * (1 + C₁ / √r) *
            deriv (fun σ ↦ (μ (Metric.closedBall x σ)).toReal) σ + K * σ ^ 4) ∧
        c₁ / r ≤ (μ (Metric.closedBall x (c₀ / √r))).toReal) →
      ∀ σ : NNReal, σ ≠ 0 → (σ : ℝ) ≤ 2 * ρ₀ → (2 * c₀ / σ) ^ 2 ≤ r →
        (Metric.coveringNumber σ A : ENNReal) ≤
          ENNReal.ofReal (4 / (c * σ ^ 2)) * μ (Metric.cthickening (σ / 2) A) := by
  obtain ⟨c, hc, ρ₀, hρ₀, -, h⟩ := exists_forall_mul_sq_le_of_ae_le hC hC₁ hK hc₀ hc₁ hσ₀
  refine ⟨c, hc, ρ₀, hρ₀, fun r hr μ A hA σ hσ hσρ₀ hrσ ↦ ?_⟩
  refine TauCeti.coveringNumber_le_of_mul_sq_le_measure_closedBall_of_sq_le hc
    (fun x hx ρ hρ hρρ₀ ↦ ?_) hσ hσρ₀ hrσ
  obtain ⟨hac, hle, hbase⟩ := hA x hx
  exact ENNReal.ofReal_le_of_le_toReal (h r hr _ hac hle hbase ρ ⟨hρ, hρρ₀⟩)

end TauCeti.SeibergWitten
