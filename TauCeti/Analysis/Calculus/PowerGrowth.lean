/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

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

Finally, a monotone nonnegative `f` with `f(t) ≤ t (1 + C t) / β · f'(t) + D t ^ p` at almost every
`t` satisfies an almost-monotonicity formula: `(f(t) + β D / (p - β) · t ^ p) / (t / (1 + C t)) ^ β`
is nondecreasing (`TauCeti.monotoneOn_add_mul_rpow_div_rpow_of_le_mul_deriv_add`). This is the
integrated form of Taubes's monotonicity inequality
`E(σ) ≤ (σ / 2) (1 + C σ) (1 + ε) E'(σ) + D σ ^ 4` for the energy `E(σ)` of balls of radius `σ`.
When `ε` is at most a fixed multiple of the inner radius `a`, it gives the two-sided quadratic
bounds `E(σ) ≤ K σ ^ 2` (`TauCeti.le_mul_sq_of_le_half_mul_deriv_add_mul_pow_four`) and, from
quadratic size at the inner radius, `E(σ) ≥ c' σ ^ 2`
(`TauCeti.mul_sq_le_of_le_half_mul_deriv_add_mul_pow_four`), with constants independent of `ε`
and `a`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
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

/-! ### Almost-monotonicity with a curvature factor and a forcing term -/

/-- The logarithmic integration step: if `β f(t) ≤ t (1 + C t) f'(t)` at almost every
`t ∈ (x, y)` for a function `f` monotone on `[x, y]` and positive at `x`, then `log f` increases
on `[x, y]` at least as much as `β log (t / (1 + C t))`. -/
private theorem mul_log_sub_log_le_log_sub_log {f : ℝ → ℝ} {x y β C : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) (hC : 0 ≤ C) (hf : MonotoneOn f (Icc x y)) (hfx : 0 < f x)
    (h : ∀ᵐ t, t ∈ Ioo x y → β * f t ≤ t * (1 + C * t) * deriv f t) :
    β * (Real.log (y / (1 + C * y)) - Real.log (x / (1 + C * x))) ≤
      Real.log (f y) - Real.log (f x) := by
  have hpos : ∀ t ∈ Icc x y, 0 < f t := fun t ht => hfx.trans_le (hf ⟨le_rfl, hxy⟩ ht ht.1)
  have hL : MonotoneOn (fun t => Real.log (f t)) (uIcc x y) := by
    rw [uIcc_of_le hxy]
    exact fun s hs t ht hst => Real.log_le_log (hpos s hs) (hf hs ht hst)
  -- The integrating factor `g = β log (t / (1 + C t))` has derivative `β / (t (1 + C t))`.
  set g' : ℝ → ℝ := fun t => β * (t⁻¹ - C / (1 + C * t))
  have hg : ∀ t ∈ uIcc x y,
      HasDerivAt (fun t => β * (Real.log t - Real.log (1 + C * t))) (g' t) t := by
    intro t ht
    rw [uIcc_of_le hxy] at ht
    have ht0 : 0 < t := hx.trans_le ht.1
    have h1 : 0 < 1 + C * t := by positivity
    have hlin : HasDerivAt (fun t => 1 + C * t) C t := by
      simpa using ((hasDerivAt_id t).const_mul C).const_add 1
    simpa [g', div_eq_mul_inv, mul_comm] using
      ((Real.hasDerivAt_log ht0.ne').sub (hlin.log h1.ne')).const_mul β
  have hg'cont : ContinuousOn g' (uIcc x y) := by
    rw [uIcc_of_le hxy]
    refine continuousOn_const.mul (ContinuousOn.sub ?_ ?_)
    · exact continuousOn_inv₀.mono fun t ht => (hx.trans_le ht.1).ne'
    · exact continuousOn_const.div (by fun_prop) fun t ht => (by
        have := hx.trans_le ht.1; positivity)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hg hg'cont.intervalIntegrable
  -- At almost every point, `g' = β / (t (1 + C t)) ≤ f' / f = (log f)'`.
  have hle : g' ≤ᵐ[volume.restrict (Icc x y)] deriv fun t => Real.log (f t) := by
    rw [Filter.EventuallyLE, Measure.restrict_congr_set Ioo_ae_eq_Icc.symm,
      ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [h, (hf.mono Ioo_subset_Icc_self).ae_differentiableWithinAt_of_mem]
      with t ht hd htI
    have ht0 : 0 < t := hx.trans htI.1
    have h1 : 0 < 1 + C * t := by positivity
    have hft := hpos t (Ioo_subset_Icc_self htI)
    rw [deriv.log ((hd htI).differentiableAt (Ioo_mem_nhds htI.1 htI.2)) hft.ne']
    have hg't : g' t = β / (t * (1 + C * t)) := by
      simp only [g']
      field_simp
      ring
    rw [hg't, div_le_div_iff₀ (by positivity) hft]
    linarith [ht htI]
  have hmono := intervalIntegral.integral_mono_ae_restrict hxy hg'cont.intervalIntegrable
    hL.intervalIntegrable_deriv hle
  have hup := hL.intervalIntegral_deriv_mem_uIcc
  rw [uIcc_of_le (sub_nonneg.2 (Real.log_le_log hfx (hf ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy)))]
    at hup
  have hx1 : 0 < 1 + C * x := by positivity
  have hy1 : 0 < 1 + C * y := by have := hx.trans_le hxy; positivity
  rw [Real.log_div hx.ne' hx1.ne', Real.log_div (hx.trans_le hxy).ne' hy1.ne']
  linarith [hup.2]

/-- **Almost-monotonicity from an almost-everywhere differential inequality.** Let `f` be monotone
on `[a, b]`, with `0 < a` and `0 ≤ f a`. If `β f(t) ≤ t (1 + C t) f'(t)` at almost every
`t ∈ (a, b)`, where `C ≥ 0`, then `f(t) / (t / (1 + C t)) ^ β` is nondecreasing on `[a, b]`.
No continuity of `f` is assumed. -/
theorem monotoneOn_div_rpow_of_mul_le_mul_deriv_ae {f : ℝ → ℝ} {a b β C : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hf : MonotoneOn f (Icc a b)) (hfa : 0 ≤ f a)
    (h : ∀ᵐ t, t ∈ Ioo a b → β * f t ≤ t * (1 + C * t) * deriv f t) :
    MonotoneOn (fun t ↦ f t / (t / (1 + C * t)) ^ β) (Icc a b) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := ha.trans_le hx.1
  have hy0 : 0 < y := ha.trans_le hy.1
  have hψ : ∀ t, 0 < t → 0 < (t / (1 + C * t)) ^ β := fun t ht =>
    Real.rpow_pos_of_pos (by positivity) β
  have hfx : 0 ≤ f x := hfa.trans (hf ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1)
  have hfxy : f x ≤ f y := hf hx hy hxy
  rcases hfx.eq_or_lt with hfx | hfx
  · simp only [← hfx, zero_div]
    exact div_nonneg (hfx.le.trans hfxy) (hψ y hy0).le
  have key := mul_log_sub_log_le_log_sub_log hx0 hxy hC (hf.mono (Icc_subset_Icc hx.1 hy.2)) hfx
    (h.mono fun t ht ht' => ht ⟨hx.1.trans_lt ht'.1, ht'.2.trans_le hy.2⟩)
  have hfy : 0 < f y := hfx.trans_le hfxy
  have hx1 : 0 < x / (1 + C * x) := by positivity
  have hy1 : 0 < y / (1 + C * y) := by positivity
  rw [div_le_div_iff₀ (hψ x hx0) (hψ y hy0), ← Real.log_le_log_iff (by positivity)
    (by positivity), Real.log_mul hfx.ne' (hψ y hy0).ne', Real.log_mul hfy.ne' (hψ x hx0).ne',
    Real.log_rpow hx1, Real.log_rpow hy1]
  linarith

/-- **Almost-monotonicity with a power forcing term.** Let `f` be monotone on `[a, b]`, with
`0 < a` and `0 ≤ f a`. If `f(t) ≤ t (1 + C t) / β · f'(t) + D t ^ p` at almost every `t ∈ (a, b)`,
where `C, D ≥ 0` and `0 < β < p`, then the forced function `f(t) + β D / (p - β) · t ^ p` divided
by `(t / (1 + C t)) ^ β` is nondecreasing on `[a, b]`.

This is the integrated form of a monotonicity inequality
`E(σ) ≤ (σ / 2) (1 + C σ) (1 + ε) E'(σ) + D σ ^ 4` for the energy `E(σ)` in balls of radius `σ`. -/
theorem monotoneOn_add_mul_rpow_div_rpow_of_le_mul_deriv_add {f : ℝ → ℝ} {a b β C D p : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D) (hβ : 0 < β) (hβp : β < p)
    (hf : MonotoneOn f (Icc a b)) (hfa : 0 ≤ f a)
    (h : ∀ᵐ t, t ∈ Ioo a b → f t ≤ t * (1 + C * t) / β * deriv f t + D * t ^ p) :
    MonotoneOn (fun t ↦ (f t + β * D / (p - β) * t ^ p) / (t / (1 + C * t)) ^ β)
      (Icc a b) := by
  have hpβ : 0 < p - β := sub_pos.2 hβp
  set D' := β * D / (p - β) with hD'_def
  have hD' : 0 ≤ D' := by positivity
  have hp : 0 < p := hβ.trans hβp
  refine monotoneOn_div_rpow_of_mul_le_mul_deriv_ae (f := fun t ↦ f t + D' * t ^ p) ha hC
    (fun s hs t ht hst => add_le_add (hf hs ht hst)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (ha.le.trans hs.1) hst hp.le) hD'))
    (add_nonneg hfa (mul_nonneg hD' (Real.rpow_nonneg ha.le _))) ?_
  filter_upwards [h, (hf.mono Ioo_subset_Icc_self).ae_differentiableWithinAt_of_mem]
    with t ht hd htI
  have ht0 : 0 < t := ha.trans htI.1
  have hd' := (hd htI).differentiableAt (Ioo_mem_nhds htI.1 htI.2)
  have hderiv : HasDerivAt (fun t ↦ f t + D' * t ^ p) (deriv f t + D' * (p * t ^ (p - 1))) t :=
    hd'.hasDerivAt.add ((Real.hasDerivAt_rpow_const (Or.inl ht0.ne')).const_mul D')
  rw [hderiv.deriv, Real.rpow_sub_one ht0.ne']
  have htp : 0 ≤ t ^ p := Real.rpow_nonneg ht0.le p
  -- Multiplying the hypothesis by `β`: `β f ≤ t (1 + C t) f' + β D t ^ p`.
  have h1 : β * f t ≤ t * (1 + C * t) * deriv f t + β * D * t ^ p := by
    have := mul_le_mul_of_nonneg_left (ht htI) hβ.le
    have hβ' : β * (t * (1 + C * t) / β * deriv f t) = t * (1 + C * t) * deriv f t := by
      field_simp
    linarith
  -- The forcing correction absorbs the forcing: `β (D + D') = p D'`.
  have h2 : β * D + β * D' = D' * p := by
    rw [hD'_def]
    field_simp
    ring
  have h3 : D' * p * t ^ p ≤ t * (1 + C * t) * (D' * (p * (t ^ p / t))) := by
    have : t * (1 + C * t) * (D' * (p * (t ^ p / t))) = (1 + C * t) * (D' * p * t ^ p) := by
      field_simp
    rw [this]
    nlinarith [mul_nonneg (mul_nonneg hD' hp.le) htp, mul_nonneg hC ht0.le]
  nlinarith

/-- The exponent `2 / (1 + ε)` falls short of `2` by at most `2 ε`. -/
private theorem two_sub_two_div_one_add_le {ε : ℝ} (hε : 0 ≤ ε) : 2 - 2 / (1 + ε) ≤ 2 * ε := by
  have : 2 - 2 / (1 + ε) = 2 * ε / (1 + ε) := by
    field_simp
    ring
  rw [this]
  exact div_le_self (by positivity) (by linarith)

/-- The normalization `β = 2 / (1 + ε)`, `p = 4` of
`monotoneOn_add_mul_rpow_div_rpow_of_le_mul_deriv_add`, with denominators cleared and the forcing
correction bounded by the forcing term: for `x ≤ y` in `[a, b]`,
`f x ψ(y) ≤ (f y + D y ^ 4) ψ(x)`, where `ψ(s) = (s / (1 + C s)) ^ (2 / (1 + ε))`. -/
private theorem mul_rpow_le_of_le_half_mul_deriv_add_mul_pow_four {f : ℝ → ℝ} {a b C D ε x y : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hf : MonotoneOn f (Icc a b))
    (hfa : 0 ≤ f a)
    (h : ∀ᵐ t, t ∈ Ioo a b → f t ≤ t / 2 * (1 + C * t) * (1 + ε) * deriv f t + D * t ^ 4)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    f x * (y / (1 + C * y)) ^ (2 / (1 + ε)) ≤
      (f y + D * y ^ 4) * (x / (1 + C * x)) ^ (2 / (1 + ε)) := by
  have hβ2 : 2 / (1 + ε) ≤ 2 := div_le_self zero_le_two (by linarith)
  have hmono := monotoneOn_add_mul_rpow_div_rpow_of_le_mul_deriv_add
    (β := 2 / (1 + ε)) (p := 4) ha hC hD (by positivity) (by linarith) hf hfa (by
      filter_upwards [h] with t ht htI
      convert ht htI using 2
      · field_simp
      · norm_cast) hx hy hxy
  set β := 2 / (1 + ε) with hβ_def
  have hβ : 0 < β := by positivity
  have hx0 : 0 < x := ha.trans_le hx.1
  have hy0 : 0 < y := ha.trans_le hy.1
  have hψx : 0 < (x / (1 + C * x)) ^ β := Real.rpow_pos_of_pos (by positivity) _
  have hψy : 0 < (y / (1 + C * y)) ^ β := Real.rpow_pos_of_pos (by positivity) _
  simp only [Real.rpow_ofNat] at hmono
  rw [div_le_div_iff₀ hψx hψy] at hmono
  -- The forcing correction `β D / (4 - β)` is nonnegative and at most `D`.
  have hD' : 0 ≤ β * D / (4 - β) := div_nonneg (by positivity) (by linarith)
  have hD'D : β * D / (4 - β) ≤ D := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith [mul_nonneg (mul_nonneg hD' (pow_nonneg hx0.le 4)) hψy.le,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD'D (pow_nonneg hy0.le 4)) hψx.le]

/-- For `a ≤ t ≤ 1` with `0 < a` and `ε ≤ A a`, the normalized power
`(t / (1 + C t)) ^ (2 / (1 + ε))` is at most `e ^ (2 A) t ^ 2`. -/
private theorem rpow_div_one_add_mul_le_exp_mul_sq {a t C ε A : ℝ} (ha : 0 < a) (hat : a ≤ t)
    (ht1 : t ≤ 1) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hεa : ε ≤ A * a) :
    (t / (1 + C * t)) ^ (2 / (1 + ε)) ≤ Real.exp (2 * A) * t ^ 2 := by
  have hA : 0 ≤ A := (mul_nonneg_iff_of_pos_right ha).1 (hε.trans hεa)
  have ht0 : 0 < t := ha.trans_le hat
  have h2β := two_sub_two_div_one_add_le hε
  set β := 2 / (1 + ε) with hβ_def
  have hβ : 0 < β := by positivity
  calc (t / (1 + C * t)) ^ β ≤ t ^ β :=
        Real.rpow_le_rpow (by positivity) (div_le_self ht0.le (by nlinarith)) hβ.le
    _ = t ^ (2 : ℝ) * t ^ (β - 2) := by rw [← Real.rpow_add ht0]; ring_nf
    _ ≤ t ^ (2 : ℝ) * t ^ (-(2 * ε)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith))
          (by positivity)
    _ ≤ t ^ (2 : ℝ) * Real.exp (2 * A) :=
        mul_le_mul_of_nonneg_left (rpow_neg_le_exp ht0 ht1 (by positivity)
          (by nlinarith)) (by positivity)
    _ = Real.exp (2 * A) * t ^ 2 := by rw [Real.rpow_two, mul_comm]

/-- For `0 < b ≤ 1` and `β ≤ 2`, `((b / (1 + C b)) ^ β)⁻¹ ≤ ((1 + C b) / b) ^ 2`. -/
private theorem inv_rpow_div_one_add_mul_le_sq {b C β : ℝ} (hb0 : 0 < b) (hb : b ≤ 1)
    (hC : 0 ≤ C) (hβ2 : β ≤ 2) : ((b / (1 + C * b)) ^ β)⁻¹ ≤ ((1 + C * b) / b) ^ 2 := by
  rw [← Real.inv_rpow (by positivity), inv_div, ← Real.rpow_two]
  exact Real.rpow_le_rpow_of_exponent_le ((one_le_div hb0).2 (by nlinarith)) hβ2

/-- For `0 < t ≤ b`, `t ≤ 1` and `0 ≤ β ≤ 2`, `t ^ 2 ≤ (1 + C b) ^ 2 (t / (1 + C t)) ^ β`. -/
private theorem sq_le_mul_rpow_div_one_add_mul {t b C β : ℝ} (ht0 : 0 < t) (htb : t ≤ b)
    (ht1 : t ≤ 1) (hC : 0 ≤ C) (hβ : 0 ≤ β) (hβ2 : β ≤ 2) :
    t ^ 2 ≤ (1 + C * b) ^ 2 * (t / (1 + C * t)) ^ β := by
  have hCb : 1 ≤ 1 + C * b := by nlinarith [mul_nonneg hC (ht0.le.trans htb)]
  have ht2 : t ^ 2 ≤ t ^ β := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hβ2
  have hCt : (1 + C * t) ^ β ≤ (1 + C * b) ^ 2 := by
    calc (1 + C * t) ^ β ≤ (1 + C * b) ^ β :=
          Real.rpow_le_rpow (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left htb hC]) hβ
      _ ≤ (1 + C * b) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hCb hβ2
      _ = (1 + C * b) ^ 2 := Real.rpow_two _
  rw [Real.div_rpow ht0.le (by positivity), mul_div_assoc', le_div_iff₀ (by positivity)]
  calc t ^ 2 * (1 + C * t) ^ β ≤ t ^ β * (1 + C * b) ^ 2 :=
        mul_le_mul ht2 hCt (by positivity) (by positivity)
    _ = (1 + C * b) ^ 2 * t ^ β := mul_comm _ _

/-- For `0 < a ≤ 1` and `ε ≤ A a`, `e ^ (-2 A) (a / (1 + C a)) ^ (2 / (1 + ε)) ≤ a ^ 2`. -/
private theorem exp_neg_mul_rpow_div_one_add_mul_le_sq {a C ε A : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hεa : ε ≤ A * a) :
    Real.exp (-(2 * A)) * (a / (1 + C * a)) ^ (2 / (1 + ε)) ≤ a ^ 2 := by
  calc Real.exp (-(2 * A)) * (a / (1 + C * a)) ^ (2 / (1 + ε))
      ≤ Real.exp (-(2 * A)) * (Real.exp (2 * A) * a ^ 2) := by
        gcongr
        exact rpow_div_one_add_mul_le_exp_mul_sq ha le_rfl ha1 hC hε hεa
    _ = a ^ 2 := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- **Quadratic upper bound from a monotonicity inequality.** Let `f` be monotone on `[a, b]` with
`0 < a`, `b ≤ 1` and `0 ≤ f a`, and suppose that at almost every `t ∈ (a, b)`
`f(t) ≤ (t / 2) (1 + C t) (1 + ε) f'(t) + D t ^ 4` with `C, D, ε ≥ 0`. If `ε ≤ A a`, then
`f t ≤ K t ^ 2` on `[a, b]`, where `K = (f b + D b ^ 4) ((1 + C b) / b) ^ 2 e ^ (2 A)` depends on
`ε` and `a` only through `A`.

For the defect energy `E(σ)` of balls of radius `σ`, with `ε = C₀ r ^ (-1/2)` and
`a = c₀ r ^ (-1/2)` (so that `A = C₀ / c₀`), this is the bound `E(σ) ≤ K σ ^ 2` with `K`
controlled by `E(b)` independently of the large parameter `r`. -/
theorem le_mul_sq_of_le_half_mul_deriv_add_mul_pow_four {f : ℝ → ℝ} {a b C D ε A t : ℝ}
    (ha : 0 < a) (hb : b ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hεa : ε ≤ A * a) (hf : MonotoneOn f (Icc a b)) (hfa : 0 ≤ f a)
    (h : ∀ᵐ s, s ∈ Ioo a b → f s ≤ s / 2 * (1 + C * s) * (1 + ε) * deriv f s + D * s ^ 4)
    (ht : t ∈ Icc a b) :
    f t ≤ (f b + D * b ^ 4) * ((1 + C * b) / b) ^ 2 * Real.exp (2 * A) * t ^ 2 := by
  have hb0 : 0 < b := ha.trans_le (ht.1.trans ht.2)
  have hbI : b ∈ Icc a b := ⟨ht.1.trans ht.2, le_rfl⟩
  have hfb : 0 ≤ f b := hfa.trans (hf ⟨le_rfl, hbI.1⟩ hbI hbI.1)
  -- `f t ψ(b) ≤ (f b + D b ^ 4) ψ(t)`, `ψ(t) ≤ e ^ (2 A) t ^ 2` and
  -- `ψ(b)⁻¹ ≤ ((1 + C b) / b) ^ 2`, where `ψ(s) = (s / (1 + C s)) ^ (2 / (1 + ε))`.
  have h1 := mul_rpow_le_of_le_half_mul_deriv_add_mul_pow_four ha hC hD hε hf hfa h ht hbI ht.2
  have h2 := rpow_div_one_add_mul_le_exp_mul_sq ha ht.1 (ht.2.trans hb) hC hε hεa
  have h3 := inv_rpow_div_one_add_mul_le_sq hb0 hb hC
    (div_le_self zero_le_two (by linarith) : 2 / (1 + ε) ≤ 2)
  have hψb : 0 < (b / (1 + C * b)) ^ (2 / (1 + ε)) := Real.rpow_pos_of_pos (by positivity) _
  calc f t = f t * (b / (1 + C * b)) ^ (2 / (1 + ε)) * ((b / (1 + C * b)) ^ (2 / (1 + ε)))⁻¹ := by
        field_simp
    _ ≤ (f b + D * b ^ 4) * (Real.exp (2 * A) * t ^ 2) * ((1 + C * b) / b) ^ 2 :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) h3 (by positivity)
          (by positivity)
    _ = (f b + D * b ^ 4) * ((1 + C * b) / b) ^ 2 * Real.exp (2 * A) * t ^ 2 := by ring

/-- **Quadratic lower bound from a monotonicity inequality.** Let `f` be monotone on `[a, b]` with
`0 < a` and `b ≤ 1`, and suppose that at almost every `t ∈ (a, b)`
`f(t) ≤ (t / 2) (1 + C t) (1 + ε) f'(t) + D t ^ 4` with `C, D, ε ≥ 0`. If `ε ≤ A a` and
`f` has quadratic size `c a ^ 2 ≤ f a` at the inner radius, with `c ≥ 0`, then on `[a, b]`
`(c e ^ (-2 A) / (1 + C b) ^ 2 - D b ^ 2) t ^ 2 ≤ f t`.

For the defect energy `E(σ)` of balls of radius `σ` centered at a zero, with
`ε = C₀ r ^ (-1/2)` and `a = c₀ r ^ (-1/2)` (so that `A = C₀ / c₀`), this propagates a lower
bound at the microscopic radius to the bound `E(σ) ≥ c' σ ^ 2` up to a fixed radius `b`, once `b`
is small enough that the constant is positive. -/
theorem mul_sq_le_of_le_half_mul_deriv_add_mul_pow_four {f : ℝ → ℝ} {a b C D ε A c t : ℝ}
    (ha : 0 < a) (hb : b ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hεa : ε ≤ A * a) (hf : MonotoneOn f (Icc a b)) (hc : 0 ≤ c) (hfa : c * a ^ 2 ≤ f a)
    (h : ∀ᵐ s, s ∈ Ioo a b → f s ≤ s / 2 * (1 + C * s) * (1 + ε) * deriv f s + D * s ^ 4)
    (ht : t ∈ Icc a b) :
    (c * Real.exp (-(2 * A)) / (1 + C * b) ^ 2 - D * b ^ 2) * t ^ 2 ≤ f t := by
  have ht0 : 0 < t := ha.trans_le ht.1
  have hb0 : 0 ≤ b := ht0.le.trans ht.2
  have haI : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hfa0 : 0 ≤ f a := (by positivity : 0 ≤ c * a ^ 2).trans hfa
  -- `f a ψ(t) ≤ (f t + D t ^ 4) ψ(a)`, `t ^ 2 ≤ (1 + C b) ^ 2 ψ(t)` and
  -- `e ^ (-2 A) ψ(a) ≤ a ^ 2`, where `ψ(s) = (s / (1 + C s)) ^ (2 / (1 + ε))`.
  have h1 := mul_rpow_le_of_le_half_mul_deriv_add_mul_pow_four ha hC hD hε hf hfa0 h haI ht ht.1
  have h2 := sq_le_mul_rpow_div_one_add_mul ht0 ht.2 (ht.2.trans hb) hC (by positivity)
    (div_le_self zero_le_two (by linarith) : 2 / (1 + ε) ≤ 2)
  have h3 := exp_neg_mul_rpow_div_one_add_mul_le_sq ha (ht.1.trans (ht.2.trans hb)) hC hε hεa
  set β := 2 / (1 + ε) with hβ_def
  have hψa : 0 < (a / (1 + C * a)) ^ β := Real.rpow_pos_of_pos (by positivity) _
  -- Hence `c e ^ (-2 A) t ^ 2 / (1 + C b) ^ 2 ≤ f t + D t ^ 4`.
  have h4 : c * Real.exp (-(2 * A)) / (1 + C * b) ^ 2 * t ^ 2 ≤ f t + D * t ^ 4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity), ← mul_le_mul_iff_of_pos_right hψa]
    calc c * Real.exp (-(2 * A)) * t ^ 2 * (a / (1 + C * a)) ^ β
        = c * t ^ 2 * (Real.exp (-(2 * A)) * (a / (1 + C * a)) ^ β) := by ring
      _ ≤ c * ((1 + C * b) ^ 2 * (t / (1 + C * t)) ^ β) * a ^ 2 := by gcongr
      _ = c * a ^ 2 * (t / (1 + C * t)) ^ β * (1 + C * b) ^ 2 := by ring
      _ ≤ f a * (t / (1 + C * t)) ^ β * (1 + C * b) ^ 2 := by gcongr
      _ ≤ (f t + D * t ^ 4) * (a / (1 + C * a)) ^ β * (1 + C * b) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (f t + D * t ^ 4) * (1 + C * b) ^ 2 * (a / (1 + C * a)) ^ β := by ring
  -- The forcing term is `D t ^ 4 ≤ D b ^ 2 t ^ 2`.
  have h5 : D * t ^ 4 ≤ D * b ^ 2 * t ^ 2 := by
    have htb : t ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ht0.le ht.2 2
    calc D * t ^ 4 = D * t ^ 2 * t ^ 2 := by ring
      _ ≤ D * b ^ 2 * t ^ 2 := by gcongr
  linarith

end TauCeti

end
