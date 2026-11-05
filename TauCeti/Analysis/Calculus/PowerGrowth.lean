/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Power growth from a differential inequality

The inequality `α f(t) ≤ t f'(t)` makes `f(t) / t^α` nondecreasing on positive
intervals. It gives power bounds at smaller radii from data at a larger radius,
including when `f` vanishes. No division by `f` or positivity assumption on `f` is needed.

Conversely, the inequality `m(ρ) ^ (1 - a) ≤ K m'(ρ)`, holding only at almost every `ρ`, forces a
monotone function `m` which is positive on `(0, r)` to grow at least like a power:
`a r ≤ K m(r) ^ a` (`TauCeti.mul_le_mul_rpow_of_rpow_one_sub_le_mul_deriv`). No continuity of `m` is
needed: the derivative of the monotone function `m ^ a` integrates to at most its increment. This
is the integration step of the lower density estimates for sets of finite perimeter, where
`m(ρ)` is the volume of the set in the ball of radius `ρ`.

The forced almost-Euler inequality `α f(σ) ≤ σ (1 + C σ) f'(σ) + A σ ^ n`, again only at almost
every `σ` and for monotone `f`, makes `((1 + C σ) / σ) ^ α (f σ + A σ ^ n / (n - α))`
nondecreasing (`TauCeti.rpow_mul_add_le_rpow_mul_add_of_mul_le_mul_deriv_add`). It follows from
the almost-everywhere Grönwall inequality for monotone functions in
`TauCeti.Analysis.ODE.Gronwall`: `g s exp (∫ₛᵗ k) ≤ g t` whenever `k g ≤ g'`
(`TauCeti.mul_exp_integral_le_of_mul_le_deriv`), with
`∫ₛᵗ 1 / (σ (1 + C σ)) = log (t / (1 + C t)) - log (s / (1 + C s))`
(`TauCeti.integral_inv_mul_one_add_mul`).

In the normalization `f(σ) ≤ (σ / 2) (1 + C σ) (1 + δ) f'(σ) + A σ ^ 4` the exponent is
`2 / (1 + δ)` (`TauCeti.rpow_mul_le_rpow_mul_add_of_le_mul_deriv_add`). When `0 < h ≤ 1` and
`δ ≤ K h`, the power `σ ^ (2 / (1 + δ))` is bounded by a constant times `σ ^ 2` for
`c h ≤ σ ≤ 1`, with a constant independent of `h` (`TauCeti.rpow_two_div_one_add_le_exp_mul_sq`).
Consequently a bound on `f` at a fixed radius `σ₀ ≤ 1` gives the quadratic upper bound
`f σ ≤ K' σ ^ 2` for `c h ≤ σ ≤ σ₀` (`TauCeti.le_mul_sq_of_le_mul_deriv_add`), and a lower bound
`m h ^ 2 ≤ f (c h)` gives a quadratic lower bound `m' σ ^ 2 ≤ f σ + A σ ^ 4` for `c h ≤ σ ≤ 1`
(`TauCeti.mul_sq_le_add_of_le_mul_deriv_add`), both uniformly in `h`. This is the integration step
of Taubes's monotonicity estimate for the local defect energy `r ∫_{B_σ} |1 - |ψ|²|` of the
Seiberg–Witten equations on a symplectic four-manifold perturbed by a large multiple `r` of the
symplectic form, where `h = r^(-1/2)`.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. **9** (1996), 845–918.
-/

public section

open Set MeasureTheory

namespace TauCeti

/-- An Euler differential inequality makes the power-normalized function nondecreasing
on any convex set of positive real numbers. Only continuity is required at boundary points;
the derivative and differential inequality are needed only on the interior. -/
theorem monotoneOn_div_rpow_of_mul_le_mul_deriv {f f' : ℝ → ℝ} {s : Set ℝ} {α : ℝ}
    (hs : Convex ℝ s) (hpos : ∀ t ∈ s, 0 < t)
    (hcont : ContinuousOn f s)
    (hf : ∀ t ∈ interior s, HasDerivAt f (f' t) t)
    (hle : ∀ t ∈ interior s, α * f t ≤ t * f' t) :
    MonotoneOn (fun t ↦ f t / t ^ α) s := by
  have hd (t : ℝ) (ht : t ∈ interior s) :=
    (hf t ht).div (Real.hasDerivAt_rpow_const (Or.inl (hpos t (interior_subset ht)).ne'))
      (Real.rpow_pos_of_pos (hpos t (interior_subset ht)) α).ne'
  have hpow : ContinuousOn (fun t : ℝ ↦ t ^ α) s :=
    continuousOn_id.rpow_const (fun t ht ↦ Or.inl (hpos t ht).ne')
  apply monotoneOn_of_deriv_nonneg hs
    (hcont.div hpow
      (fun t ht ↦ (Real.rpow_pos_of_pos (hpos t ht) α).ne'))
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hd t ht).deriv]
  apply div_nonneg _ (sq_nonneg _)
  rw [Real.rpow_sub_one (hpos t (interior_subset ht)).ne']
  have h := hle t ht
  have hp := Real.rpow_pos_of_pos (hpos t (interior_subset ht)) α
  have htpos := hpos t (interior_subset ht)
  convert div_nonneg (mul_nonneg (sub_nonneg.mpr h) hp.le) htpos.le using 1
  field_simp

/-- **Power growth from an almost-everywhere differential inequality.** Let `m` be monotone on
`[0, r]`, nonnegative at `0` and positive on `(0, r)`. If `m(ρ) ^ (1 - a) ≤ K m'(ρ)` for almost
every `ρ ∈ (0, r)`, where `a > 0` and `K ≥ 0`, then `a r ≤ K m(r) ^ a`. -/
theorem mul_le_mul_rpow_of_rpow_one_sub_le_mul_deriv {m : ℝ → ℝ} {a K r : ℝ} (hr : 0 ≤ r)
    (hm : MonotoneOn m (Icc 0 r)) (hm0 : 0 ≤ m 0) (hpos : ∀ ρ ∈ Ioo 0 r, 0 < m ρ)
    (ha : 0 < a) (hK : 0 ≤ K)
    (h : ∀ᵐ ρ, ρ ∈ Ioo 0 r → m ρ ^ (1 - a) ≤ K * deriv m ρ) :
    a * r ≤ K * m r ^ a := by
  rcases hr.eq_or_lt with rfl | hr'
  · simpa using mul_nonneg hK (Real.rpow_nonneg hm0 a)
  -- The inequality at a single point of `(0, r)` forces `K > 0`.
  replace hK : 0 < K := by
    refine hK.lt_of_ne fun hK0 => ?_
    have : (ae (volume.restrict (Ioo (0 : ℝ) r))).NeBot := ae_restrict_neBot.2 (by simp [hr'])
    have hev : ∀ᵐ ρ ∂volume.restrict (Ioo 0 r),
        ρ ∈ Ioo 0 r ∧ (ρ ∈ Ioo 0 r → m ρ ^ (1 - a) ≤ K * deriv m ρ) :=
      (ae_restrict_mem measurableSet_Ioo).and (ae_restrict_of_ae h)
    obtain ⟨ρ, hρ, hρ'⟩ := hev.exists
    have h0 := hρ' hρ
    rw [← hK0, zero_mul] at h0
    exact (Real.rpow_pos_of_pos (hpos ρ hρ) _).not_ge h0
  set g : ℝ → ℝ := fun ρ => m ρ ^ a
  have hg : MonotoneOn g (uIcc 0 r) := by
    rw [uIcc_of_le hr]
    intro ρ hρ ρ' hρ' hle
    exact Real.rpow_le_rpow (hm0.trans (hm ⟨le_rfl, hr⟩ hρ hρ.1)) (hm hρ hρ' hle) ha.le
  -- `a / K ≤ g'` at almost every point of `[0, r]`, where
  -- `K g' = a m ^ (a - 1) (K m') ≥ a m ^ (a - 1) m ^ (1 - a) = a`.
  have hlow : (fun _ => a / K) ≤ᵐ[volume.restrict (Icc 0 r)] deriv g := by
    rw [Filter.EventuallyLE, Measure.restrict_congr_set Ioo_ae_eq_Icc.symm,
      ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [h, (hm.mono Ioo_subset_Icc_self).ae_differentiableWithinAt_of_mem]
      with ρ hρ hd hρI
    have hmρ := hpos ρ hρI
    have hd' := (hd hρI).differentiableAt (Ioo_mem_nhds hρI.1 hρI.2)
    rw [deriv_rpow_const hd' (Or.inl hmρ.ne'), div_le_iff₀ hK]
    calc a = a * (m ρ ^ (a - 1) * m ρ ^ (1 - a)) := by
          rw [← Real.rpow_add hmρ, sub_add_sub_cancel', sub_self, Real.rpow_zero, mul_one]
      _ ≤ a * (m ρ ^ (a - 1) * (K * deriv m ρ)) := by
          gcongr
          exact hρ hρI
      _ = deriv m ρ * a * m ρ ^ (a - 1) * K := by ring
  -- Integrating, `a r / K ≤ ∫₀^r g' ≤ g r - g 0 ≤ g r`.
  have hint := intervalIntegral.integral_mono_ae_restrict hr intervalIntegrable_const
    hg.intervalIntegrable_deriv hlow
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  have hup := hg.intervalIntegral_deriv_mem_uIcc
  rw [uIcc_of_le (sub_nonneg.2 (hg (by simp) (by simp [hr]) (by simp [hr])))] at hup
  have hgr := hint.trans (hup.2.trans (sub_le_self _ (Real.rpow_nonneg hm0 a)))
  rw [mul_div_assoc', div_le_iff₀ hK] at hgr
  linarith

/-! ### Almost-Euler inequalities with a forcing term -/

/-- **Integrated almost-Euler inequality with a forcing term.** Let `C ≥ 0`, `A ≥ 0` and
`α < n`. If `f` is monotone on `[s, t] ⊆ (0, ∞)`, `f s ≥ 0`, and
`α f(σ) ≤ σ (1 + C σ) f'(σ) + A σ ^ n` at almost every `σ ∈ (s, t)`, then, with
`B = A / (n - α)`,
`(t / (1 + C t)) ^ α (f s + B s ^ n) ≤ (s / (1 + C s)) ^ α (f t + B t ^ n)`.

That is, `((1 + C σ) / σ) ^ α (f σ + B σ ^ n)` is nondecreasing. For `C = A = 0` this is the
monotonicity of `f σ / σ ^ α`, as in `TauCeti.monotoneOn_div_rpow_of_mul_le_mul_deriv`; here the
inequality is only required almost everywhere and `f` need not be continuous. -/
theorem rpow_mul_add_le_rpow_mul_add_of_mul_le_mul_deriv_add {f : ℝ → ℝ} {s t C α A : ℝ}
    {n : ℕ} (hs : 0 < s) (hst : s ≤ t) (hC : 0 ≤ C) (hαn : α < n) (hA : 0 ≤ A)
    (hf : MonotoneOn f (Icc s t)) (hfs : 0 ≤ f s)
    (h : ∀ᵐ σ, σ ∈ Ioo s t → α * f σ ≤ σ * (1 + C * σ) * deriv f σ + A * σ ^ n) :
    (t / (1 + C * t)) ^ α * (f s + A / (n - α) * s ^ n) ≤
      (s / (1 + C * s)) ^ α * (f t + A / (n - α) * t ^ n) := by
  obtain ⟨B, hB_def⟩ : ∃ B, B = A / (n - α) := ⟨_, rfl⟩
  rw [← hB_def]
  have hnα : 0 < (n : ℝ) - α := sub_pos.2 hαn
  have hB : 0 ≤ B := hB_def ▸ div_nonneg hA hnα.le
  have hBA : B * (n - α) = A := hB_def ▸ div_mul_cancel₀ A hnα.ne'
  set g : ℝ → ℝ := fun σ => f σ + B * σ ^ n
  set k : ℝ → ℝ := fun σ => α * (σ * (1 + C * σ))⁻¹
  have hσpos (σ : ℝ) (hσ : σ ∈ Icc s t) : 0 < σ := hs.trans_le hσ.1
  have hg : MonotoneOn g (Icc s t) := fun x hx y hy hxy =>
    add_le_add (hf hx hy hxy) (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hσpos x hx).le hxy n) hB)
  have hgs : 0 ≤ g s := add_nonneg hfs (mul_nonneg hB (pow_nonneg hs.le n))
  have hk : IntervalIntegrable k volume s t := by
    refine ContinuousOn.intervalIntegrable
      (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun σ hσ => ?_))
    rw [uIcc_of_le hst] at hσ
    have := hσpos σ hσ
    positivity
  -- The forcing term is absorbed into `g = f + B σ ^ n`: `k g ≤ g'` almost everywhere.
  have hkg : ∀ᵐ σ, σ ∈ Ioo s t → k σ * g σ ≤ deriv g σ := by
    filter_upwards [h, (hf.mono Ioo_subset_Icc_self).ae_differentiableWithinAt_of_mem]
      with σ hσ hd hσI
    have hσ0 : 0 < σ := hσpos σ (Ioo_subset_Icc_self hσI)
    have hD : 0 < σ * (1 + C * σ) := by positivity
    have hd' := (hd hσI).differentiableAt (Ioo_mem_nhds hσI.1 hσI.2)
    have hgd : HasDerivAt g (deriv f σ + B * (n * σ ^ (n - 1))) σ :=
      hd'.hasDerivAt.add ((hasDerivAt_pow n σ).const_mul B)
    rw [hgd.deriv]
    simp only [k, g]
    rw [← div_eq_mul_inv, div_mul_eq_mul_div, div_le_iff₀ hD]
    have hfσ := hσ hσI
    rw [← hBA] at hfσ
    -- `n σ ^ (n - 1) σ = n σ ^ n`, also for `n = 0`.
    have hpow : (n : ℝ) * σ ^ (n - 1) * σ = n * σ ^ n := by
      rcases n with _ | m
      · simp
      · rw [Nat.add_sub_cancel, mul_assoc, ← pow_succ]
    have hgap : 0 ≤ C * σ * (n * B * σ ^ n) :=
      mul_nonneg (mul_nonneg hC hσ0.le) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB)
        (pow_nonneg hσ0.le _))
    have e : (deriv f σ + B * (n * σ ^ (n - 1))) * (σ * (1 + C * σ)) -
        α * (f σ + B * σ ^ n) = (σ * (1 + C * σ) * deriv f σ + B * (n - α) * σ ^ n - α * f σ) +
          C * σ * (n * B * σ ^ n) := by
      linear_combination (B * (1 + C * σ)) * hpow
    linarith
  have ht : 0 < t := hs.trans_le hst
  have hexp : Real.exp (∫ σ in s..t, k σ) = (t / (1 + C * t)) ^ α / (s / (1 + C * s)) ^ α := by
    rw [intervalIntegral.integral_const_mul, integral_inv_mul_one_add_mul hs ht hC,
      Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity), ← Real.exp_sub]
    ring_nf
  have key := mul_exp_integral_le_of_mul_le_deriv hst hg hgs hk hkg
  rw [hexp, mul_div_assoc', div_le_iff₀ (by positivity)] at key
  simp only [g] at key
  linarith

/-- **Integrated monotonicity inequality.** Let `C, δ, A ≥ 0` and `p = 2 / (1 + δ)`. If `f` is
monotone on `[s, t] ⊆ (0, ∞)`, `f s ≥ 0`, and
`f(σ) ≤ (σ / 2) (1 + C σ) (1 + δ) f'(σ) + A σ ^ 4` at almost every `σ ∈ (s, t)`, then
`(t / (1 + C t)) ^ p f(s) ≤ (s / (1 + C s)) ^ p (f(t) + A t ^ 4)`.

This is the form in which the local defect energy `E(σ)` of the large-parameter Seiberg–Witten
equations on balls of radius `σ` obeys its monotonicity inequality, with `δ` of order `r^(-1/2)`.
-/
theorem rpow_mul_le_rpow_mul_add_of_le_mul_deriv_add {f : ℝ → ℝ} {s t C δ A : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hA : 0 ≤ A)
    (hf : MonotoneOn f (Icc s t)) (hfs : 0 ≤ f s)
    (h : ∀ᵐ σ, σ ∈ Ioo s t → f σ ≤ σ / 2 * (1 + C * σ) * (1 + δ) * deriv f σ + A * σ ^ 4) :
    (t / (1 + C * t)) ^ (2 / (1 + δ)) * f s ≤
      (s / (1 + C * s)) ^ (2 / (1 + δ)) * (f t + A * t ^ 4) := by
  set p := 2 / (1 + δ) with hp_def
  have hp0 : 0 ≤ p := by positivity
  have hp2 : p ≤ 2 := div_le_self zero_le_two (le_add_of_nonneg_right hδ)
  have hp4 : p < ((4 : ℕ) : ℝ) := by push_cast; linarith
  have h' : ∀ᵐ σ, σ ∈ Ioo s t →
      p * f σ ≤ σ * (1 + C * σ) * deriv f σ + p * A * σ ^ 4 := by
    filter_upwards [h] with σ hσ hσI
    have := mul_le_mul_of_nonneg_left (hσ hσI) hp0
    convert this using 1
    simp only [hp_def]
    field_simp
  have key := rpow_mul_add_le_rpow_mul_add_of_mul_le_mul_deriv_add hs hst hC hp4
    (mul_nonneg hp0 hA) hf hfs h'
  -- The constant `B = p A / (4 - p)` lies in `[0, A]` because `p ≤ 2`.
  set B := p * A / (((4 : ℕ) : ℝ) - p)
  have hB0 : 0 ≤ B := div_nonneg (mul_nonneg hp0 hA) (by linarith)
  have hBA : B ≤ A := by
    rw [div_le_iff₀ (by linarith)]
    push_cast
    nlinarith
  have ht : 0 < t := hs.trans_le hst
  calc (t / (1 + C * t)) ^ p * f s ≤ (t / (1 + C * t)) ^ p * (f s + B * s ^ 4) := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
    _ ≤ (s / (1 + C * s)) ^ p * (f t + B * t ^ 4) := key
    _ ≤ (s / (1 + C * s)) ^ p * (f t + A * t ^ 4) := by
        gcongr

/-- The power `s ^ (2 / (1 + δ))` is bounded by a constant times `s ^ 2`, uniformly on scales
`c h ≤ s ≤ 1`, as long as `δ ≤ K h`: for `0 < h ≤ 1` and `c h ≤ s ≤ 1`,
`s ^ (2 / (1 + δ)) ≤ exp (2 K (1 + |log c|)) s ^ 2`. The constant does not depend on `h`. -/
theorem rpow_two_div_one_add_le_exp_mul_sq {s c h δ K : ℝ} (hc : 0 < c) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 ≤ δ) (hδh : δ ≤ K * h) (hs : c * h ≤ s) (hs1 : s ≤ 1) :
    s ^ (2 / (1 + δ)) ≤ Real.exp (2 * K * (1 + |Real.log c|)) * s ^ 2 := by
  have hch : 0 < c * h := mul_pos hc hh
  have hs0 : 0 < s := hch.trans_le hs
  have hK : 0 ≤ K := (mul_nonneg_iff_of_pos_right hh).1 (hδ.trans hδh)
  rw [Real.rpow_def_of_pos hs0, ← Real.exp_log (pow_pos hs0 2), ← Real.exp_add, Real.log_pow]
  gcongr
  -- With `L = -log s ≥ 0`, the claim is `L δ / (1 + δ) ≤ K (1 + |log c|)`.
  have hL : 0 ≤ -Real.log s := neg_nonneg.2 (Real.log_nonpos hs0.le hs1)
  have hLM : -Real.log s ≤ -Real.log c - Real.log h := by
    have := Real.log_le_log hch hs
    rw [Real.log_mul hc.ne' hh.ne'] at this
    linarith
  have hhlog : -(h * Real.log h) ≤ 1 := by linarith [Real.self_sub_one_le_mul_log hh.le]
  have hclog : -(h * Real.log c) ≤ |Real.log c| := by
    calc -(h * Real.log c) = h * -Real.log c := by ring
      _ ≤ h * |Real.log c| := mul_le_mul_of_nonneg_left (neg_le_abs _) hh.le
      _ ≤ |Real.log c| := mul_le_of_le_one_left (abs_nonneg _) hh1
  have hδ' : δ / (1 + δ) ≤ δ := div_le_self hδ (le_add_of_nonneg_right hδ)
  have e : Real.log s * (2 / (1 + δ)) = 2 * Real.log s + 2 * (-Real.log s) * (δ / (1 + δ)) := by
    field_simp
    ring
  rw [e]
  have : -Real.log s * (δ / (1 + δ)) ≤ K * (1 + |Real.log c|) :=
    calc -Real.log s * (δ / (1 + δ)) ≤ -Real.log s * δ := mul_le_mul_of_nonneg_left hδ' hL
      _ ≤ (-Real.log c - Real.log h) * (K * h) :=
          mul_le_mul hLM hδh hδ (hL.trans hLM)
      _ = K * (-(h * Real.log c) + -(h * Real.log h)) := by ring
      _ ≤ K * (1 + |Real.log c|) := mul_le_mul_of_nonneg_left (by linarith) hK
  nlinarith

/-- The bound `rpow_two_div_one_add_le_exp_mul_sq` survives the factor `1 / (1 + C s)` for
`C ≥ 0`: `(s / (1 + C s)) ^ (2 / (1 + δ)) ≤ exp (2 K (1 + |log c|)) s ^ 2` for `c h ≤ s ≤ 1`. -/
private theorem div_one_add_mul_rpow_two_div_one_add_le_exp_mul_sq {s c h δ K C : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hh : 0 < h) (hh1 : h ≤ 1) (hδ : 0 ≤ δ) (hδh : δ ≤ K * h)
    (hs : c * h ≤ s) (hs1 : s ≤ 1) :
    (s / (1 + C * s)) ^ (2 / (1 + δ)) ≤ Real.exp (2 * K * (1 + |Real.log c|)) * s ^ 2 := by
  have hs0 : 0 < s := (mul_pos hc hh).trans_le hs
  exact (Real.rpow_le_rpow (by positivity)
    (div_le_self hs0.le (le_add_of_nonneg_right (by positivity))) (by positivity)).trans
    (rpow_two_div_one_add_le_exp_mul_sq hc hh hh1 hδ hδh hs hs1)

/-- **Quadratic upper bound from the monotonicity inequality.** Let `C, δ, A ≥ 0`,
`0 < h ≤ 1`, `c > 0` and `δ ≤ K h`. Suppose `f` is monotone on `[σ, σ₀]`, where
`c h ≤ σ ≤ σ₀ ≤ 1`, with `0 ≤ f σ` and `f σ₀ ≤ M`, and satisfies
`f(τ) ≤ (τ / 2) (1 + C τ) (1 + δ) f'(τ) + A τ ^ 4` at almost every `τ ∈ (σ, σ₀)`. Then
`f σ ≤ exp (2 K (1 + |log c|)) ((1 + C σ₀) / σ₀) ^ 2 (M + A) σ ^ 2`.

The constant depends neither on `h` nor on `δ`: with `h = r^(-1/2)`, a bound on the defect energy
of the ball of fixed radius `σ₀` gives the quadratic bound on balls of radius between
`c r^(-1/2)` and `σ₀`, uniformly in `r`. -/
theorem le_mul_sq_of_le_mul_deriv_add {f : ℝ → ℝ} {σ σ₀ C δ A c h K M : ℝ} (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hc : 0 < c) (hh : 0 < h) (hh1 : h ≤ 1) (hδh : δ ≤ K * h)
    (hσ : c * h ≤ σ) (hσσ₀ : σ ≤ σ₀) (hσ₀ : σ₀ ≤ 1) (hf : MonotoneOn f (Icc σ σ₀))
    (hfσ : 0 ≤ f σ) (hM : f σ₀ ≤ M)
    (hf' : ∀ᵐ τ, τ ∈ Ioo σ σ₀ → f τ ≤ τ / 2 * (1 + C * τ) * (1 + δ) * deriv f τ + A * τ ^ 4) :
    f σ ≤ Real.exp (2 * K * (1 + |Real.log c|)) * ((1 + C * σ₀) / σ₀) ^ 2 * (M + A) * σ ^ 2 := by
  set p := 2 / (1 + δ) with hp_def
  set Λ := Real.exp (2 * K * (1 + |Real.log c|))
  have hσ0 : 0 < σ := (mul_pos hc hh).trans_le hσ
  have hσ₀0 : 0 < σ₀ := hσ0.trans_le hσσ₀
  have hp2 : p ≤ 2 := div_le_self zero_le_two (le_add_of_nonneg_right hδ)
  have key := rpow_mul_le_rpow_mul_add_of_le_mul_deriv_add hσ0 hσσ₀ hC hδ hA hf hfσ hf'
  have hfσ₀ : f σ ≤ f σ₀ := hf ⟨le_rfl, hσσ₀⟩ ⟨hσσ₀, le_rfl⟩ hσσ₀
  have hMA : f σ₀ + A * σ₀ ^ 4 ≤ M + A := by
    gcongr
    exact mul_le_of_le_one_right hA (pow_le_one₀ hσ₀0.le hσ₀)
  -- `(σ / (1 + C σ)) ^ p ≤ σ ^ p ≤ Λ σ ^ 2`.
  have hb : (σ / (1 + C * σ)) ^ p ≤ Λ * σ ^ 2 :=
    div_one_add_mul_rpow_two_div_one_add_le_exp_mul_sq hC hc hh hh1 hδ hδh hσ (hσσ₀.trans hσ₀)
  -- `(σ₀ / (1 + C σ₀)) ^ (-p) = ((1 + C σ₀) / σ₀) ^ p ≤ ((1 + C σ₀) / σ₀) ^ 2`.
  have ha : ((σ₀ / (1 + C * σ₀)) ^ p)⁻¹ ≤ ((1 + C * σ₀) / σ₀) ^ 2 := by
    rw [← Real.inv_rpow (by positivity), inv_div, ← Real.rpow_two]
    refine Real.rpow_le_rpow_of_exponent_le ?_ hp2
    rw [le_div_iff₀ hσ₀0, one_mul]
    nlinarith
  calc f σ = ((σ₀ / (1 + C * σ₀)) ^ p)⁻¹ * ((σ₀ / (1 + C * σ₀)) ^ p * f σ) := by
        field_simp
    _ ≤ ((σ₀ / (1 + C * σ₀)) ^ p)⁻¹ * ((σ / (1 + C * σ)) ^ p * (f σ₀ + A * σ₀ ^ 4)) := by
        gcongr
    _ ≤ ((1 + C * σ₀) / σ₀) ^ 2 * (Λ * σ ^ 2 * (M + A)) := by
        have hMA0 : 0 ≤ f σ₀ + A * σ₀ ^ 4 := by
          have := hfσ.trans hfσ₀
          positivity
        gcongr
    _ = Λ * ((1 + C * σ₀) / σ₀) ^ 2 * (M + A) * σ ^ 2 := by ring

/-- **Quadratic lower bound from the monotonicity inequality.** Let `C, δ, A ≥ 0`,
`0 < h ≤ 1`, `c > 0`, `m ≥ 0` and `δ ≤ K h`. Suppose `f` is monotone on `[c h, σ]`, where
`c h ≤ σ ≤ 1`, with `m h ^ 2 ≤ f (c h)`, and satisfies
`f(τ) ≤ (τ / 2) (1 + C τ) (1 + δ) f'(τ) + A τ ^ 4` at almost every `τ ∈ (c h, σ)`. Then
`m / (c ^ 2 (1 + C) ^ 2 exp (2 K (1 + |log c|))) σ ^ 2 ≤ f σ + A σ ^ 4`.

With `h = r^(-1/2)`, a lower bound of order `r⁻¹` for the defect energy on the ball of radius
`c r^(-1/2)` about a zero propagates to a quadratic lower bound for `E(σ) + A σ ^ 4` on the balls
of radius between `c r^(-1/2)` and `1`, uniformly in `r`. -/
theorem mul_sq_le_add_of_le_mul_deriv_add {f : ℝ → ℝ} {σ C δ A c h K m : ℝ} (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hc : 0 < c) (hh : 0 < h) (hh1 : h ≤ 1) (hδh : δ ≤ K * h)
    (hσ : c * h ≤ σ) (hσ1 : σ ≤ 1) (hf : MonotoneOn f (Icc (c * h) σ)) (hm : 0 ≤ m)
    (hfm : m * h ^ 2 ≤ f (c * h))
    (hf' : ∀ᵐ τ, τ ∈ Ioo (c * h) σ →
      f τ ≤ τ / 2 * (1 + C * τ) * (1 + δ) * deriv f τ + A * τ ^ 4) :
    m / (c ^ 2 * (1 + C) ^ 2 * Real.exp (2 * K * (1 + |Real.log c|))) * σ ^ 2 ≤
      f σ + A * σ ^ 4 := by
  set p := 2 / (1 + δ) with hp_def
  set Λ := Real.exp (2 * K * (1 + |Real.log c|))
  have hch : 0 < c * h := mul_pos hc hh
  have hσ0 : 0 < σ := hch.trans_le hσ
  have hp2 : p ≤ 2 := div_le_self zero_le_two (le_add_of_nonneg_right hδ)
  have hfs : 0 ≤ f (c * h) := (by positivity : 0 ≤ m * h ^ 2).trans hfm
  have key := rpow_mul_le_rpow_mul_add_of_le_mul_deriv_add hch hσ hC hδ hA hf hfs hf'
  have hfσ : 0 ≤ f σ + A * σ ^ 4 := by
    have := hfs.trans (hf ⟨le_rfl, hσ⟩ ⟨hσ, le_rfl⟩ hσ)
    positivity
  -- `(σ / (1 + C)) ^ 2 ≤ (σ / (1 + C σ)) ^ 2 ≤ (σ / (1 + C σ)) ^ p`.
  have hb : (σ / (1 + C)) ^ 2 ≤ (σ / (1 + C * σ)) ^ p := by
    have h1 : σ / (1 + C * σ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    calc (σ / (1 + C)) ^ 2 ≤ (σ / (1 + C * σ)) ^ 2 := by
          gcongr
          nlinarith
      _ = (σ / (1 + C * σ)) ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ ≤ (σ / (1 + C * σ)) ^ p :=
          Real.rpow_le_rpow_of_exponent_ge (by positivity) h1 hp2
  -- `(c h / (1 + C c h)) ^ p ≤ (c h) ^ p ≤ Λ (c h) ^ 2`.
  have ha : (c * h / (1 + C * (c * h))) ^ p ≤ Λ * (c * h) ^ 2 :=
    div_one_add_mul_rpow_two_div_one_add_le_exp_mul_sq hC hc hh hh1 hδ hδh le_rfl (hσ.trans hσ1)
  have hineq : (σ / (1 + C)) ^ 2 * (m * h ^ 2) ≤ Λ * (c * h) ^ 2 * (f σ + A * σ ^ 4) :=
    calc (σ / (1 + C)) ^ 2 * (m * h ^ 2) ≤ (σ / (1 + C * σ)) ^ p * f (c * h) := by
          gcongr
      _ ≤ (c * h / (1 + C * (c * h))) ^ p * (f σ + A * σ ^ 4) := key
      _ ≤ Λ * (c * h) ^ 2 * (f σ + A * σ ^ 4) := by gcongr
  have h1C : 0 < 1 + C := by positivity
  -- Multiply `hineq` by `(1 + C) ^ 2` and cancel `h ^ 2`.
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  refine le_of_mul_le_mul_right ?_ (pow_pos hh 2)
  calc m * σ ^ 2 * h ^ 2 = (σ / (1 + C)) ^ 2 * (m * h ^ 2) * (1 + C) ^ 2 := by
        rw [div_pow]
        field_simp
    _ ≤ Λ * (c * h) ^ 2 * (f σ + A * σ ^ 4) * (1 + C) ^ 2 := by gcongr
    _ = (f σ + A * σ ^ 4) * (c ^ 2 * (1 + C) ^ 2 * Λ) * h ^ 2 := by ring

end TauCeti

end
